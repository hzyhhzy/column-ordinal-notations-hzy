/* Formula renderer. NODE_PATH may point at existing local dependencies. */
const fs = require('node:fs');
const path = require('node:path');
const {mathjax} = require('mathjax-full/js/mathjax.js');
const {TeX} = require('mathjax-full/js/input/tex.js');
const {SVG} = require('mathjax-full/js/output/svg.js');
const {liteAdaptor} = require('mathjax-full/js/adaptors/liteAdaptor.js');
const {RegisterHTMLHandler} = require('mathjax-full/js/handlers/html.js');
const {AllPackages} = require('mathjax-full/js/input/tex/AllPackages.js');
const sharp = require('sharp');

async function main() {
  const [input, output] = process.argv.slice(2);
  if (!input || !output) throw new Error('Usage: node math.cjs formulas.json cache-directory');
  fs.mkdirSync(output, {recursive: true});
  const adaptor = liteAdaptor();
  RegisterHTMLHandler(adaptor);
  const engine = mathjax.document('', {
    InputJax: new TeX({packages: AllPackages}),
    OutputJax: new SVG({fontCache: 'none'})
  });
  sharp.concurrency(1);
  const formulas = JSON.parse(fs.readFileSync(input, 'utf8'));
  const result = {};
  for (const {key, tex, display} of formulas) {
    // Standalone equation tags use a nested, full-width SVG layout. Keep the
    // mathematical body at natural size and place its tag separately in the PDF.
    let tag = null;
    const body = tex.replace(/\\tag\{([^{}]*)\}/g, (_all, value) => { tag = value; return ''; });
    let markup = adaptor.outerHTML(engine.convert(body, {display}));
    if (/data-mjx-error|<merror/.test(markup)) throw new Error(`Invalid TeX: ${tex}\n${markup}`);
    const match = markup.match(/<svg\b[^>]*>[\s\S]*<\/svg>/);
    if (!match) throw new Error(`No SVG for ${tex}`);
    let svg = match[0];
    const viewBox = svg.match(/viewBox="([^"]+)"/)[1].split(/\s+/).map(Number);
    // MathJax uses 1000 SVG units per em; 1000 units = requested font size.
    const emWidth = viewBox[2] / 1000;
    const emHeight = viewBox[3] / 1000;
    const emDepth = Math.max(0, (viewBox[1] + viewBox[3]) / 1000);
    const scale = 52; // >300 dpi at the final 10-12 pt formula size.
    const width = Math.max(1, Math.ceil(emWidth * scale));
    const height = Math.max(1, Math.ceil(emHeight * scale));
    if (width * height > 24000000) throw new Error(`Formula raster too large: ${tex}`);
    svg = svg.replace(/\bwidth="[^"]*"/, `width="${width}"`)
      .replace(/\bheight="[^"]*"/, `height="${height}"`)
      .replace(/currentColor/g, '#15283b');
    const png = path.join(output, `${key}.png`);
    await sharp(Buffer.from(svg)).png().toFile(png);
    result[key] = {png: path.resolve(png), emWidth, emHeight, emDepth, tag};
  }
  fs.writeFileSync(path.join(output, 'index.json'), JSON.stringify(result));
  process.stdout.write(`Rendered ${formulas.length} distinct formulas.\n`);
}
main().catch(e => { console.error(e); process.exitCode = 1; });
