"""Render the eight bilingual definition/proof PDFs; no network is used.

Requires Pandoc, Node with mathjax-full/sharp, reportlab, pypdf, and local fonts.
The output files sit beside their Markdown sources. Formula PNGs are temporary.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import uuid

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,
    Image, KeepTogether, HRFlowable,
)
import reportlab.platypus.paragraph as paragraph_module
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[1]
BLUE = colors.HexColor('#234f6b')
INK = colors.HexColor('#15283b')
PAGE_W, PAGE_H = A4
TEXT_W = PAGE_W - 100

# ReportLab's CJK splitter calls ord() on the empty string of an image
# callback. A nonprinting object-replacement unit preserves the callback's
# actual width while providing a character to the CJK line-breaking rules.
_cjk_unit = paragraph_module.cjkU


def safe_cjk_unit(value, frag, encoding):
    unit = _cjk_unit(value or '\ufffc', frag, encoding)
    if not value and not hasattr(frag, 'cbDefn'):
        unit._width = 0
    return unit


paragraph_module.cjkU = safe_cjk_unit


def run(args, **kwargs):
    result = subprocess.run(args, check=False, encoding='utf-8',
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=180, **kwargs)
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}): {args}\n{result.stdout}\n{result.stderr}')
    return result


def register_fonts(folder):
    folder = Path(folder)
    choices = {
        'Body': [('cambria.ttc', 0), ('DejaVuSerif.ttf', 0)],
        'BodyBold': [('cambriab.ttf', 0), ('DejaVuSerif-Bold.ttf', 0)],
        'BodyItalic': [('cambriai.ttf', 0), ('DejaVuSerif-Italic.ttf', 0)],
        'CJK': [('msyh.ttc', 0), ('NotoSansCJK-Regular.ttc', 2)],
        'CJKBold': [('msyhbd.ttc', 0), ('NotoSansCJK-Bold.ttc', 2)],
        'Code': [('consola.ttf', 0), ('DejaVuSansMono.ttf', 0)],
        'MathFallback': [('cambria.ttc', 1), ('DejaVuSans.ttf', 0)],
    }
    for name, candidates in choices.items():
        for filename, index in candidates:
            candidate = folder / filename
            if candidate.exists():
                pdfmetrics.registerFont(TTFont(name, str(candidate), subfontIndex=index))
                break
        else:
            raise RuntimeError(f'Missing font {name}: choose --font-dir containing {candidates}')
    pdfmetrics.registerFontFamily('Body', normal='Body', bold='BodyBold',
                                  italic='BodyItalic', boldItalic='BodyBold')
    pdfmetrics.registerFontFamily('CJK', normal='CJK', bold='CJKBold',
                                  italic='CJK', boldItalic='CJKBold')


def literal(text, font):
    """Use real glyphs, failing instead of quietly printing missing-glyph boxes."""
    text = text.translate(str.maketrans({'\u2010': '-', '\u2011': '-', '\u2012': '-', '\u2013': '-', '\u2014': '-'}))
    groups = []
    for char in text:
        if char in '\n\t':
            char = ' '
        candidates = [font, 'CJK', 'MathFallback', 'Body']
        chosen = next((f for f in candidates if ord(char) in pdfmetrics.getFont(f).face.charToGlyph), None)
        if chosen is None:
            raise ValueError(f'No font for U+{ord(char):04X}: {char!r}')
        if groups and groups[-1][0] == chosen:
            groups[-1][1] += char
        else:
            groups.append([chosen, char])
    return ''.join(f'<font name="{f}">{html.escape(s)}</font>' for f, s in groups)


def math_key(tex, display):
    return hashlib.sha256((str(display) + tex).encode('utf-8')).hexdigest()[:24]


def collect_math(node, found):
    if isinstance(node, list):
        for child in node:
            collect_math(child, found)
    elif isinstance(node, dict):
        if node.get('t') == 'Math':
            kind, tex = node['c']
            display = kind['t'] == 'DisplayMath'
            key = math_key(tex, display)
            found[key] = {'key': key, 'tex': tex, 'display': display}
        else:
            for value in node.values():
                collect_math(value, found)


class Renderer:
    def __init__(self, source, index):
        self.source = source
        self.index = index
        self.zh = '.zh-CN.' in source.name
        self.body_font = 'CJK' if self.zh else 'Body'
        self.font_size = 9.4 if self.zh else 10.2
        self.heading_count = 0
        self.warnings = []
        self.styles = {
            'body': ParagraphStyle('body', fontName=self.body_font, fontSize=self.font_size,
                                   leading=16.1, textColor=INK, spaceAfter=6.0,
                                   wordWrap='CJK' if self.zh else None, splitLongWords=True,
                                   autoLeading='max'),
            'small': ParagraphStyle('small', fontName=self.body_font, fontSize=8.5,
                                    leading=13, textColor=INK, spaceAfter=4,
                                    wordWrap='CJK' if self.zh else None, splitLongWords=True, autoLeading='max'),
            'code': ParagraphStyle('code', fontName='Code', fontSize=8.0, leading=11.5,
                                   textColor=INK, spaceAfter=0, wordWrap='CJK'),
        }
        if self.zh and source.parent.name == 'paper':
            # A slightly tighter scholarly leading avoids a two-line final page.
            self.styles['body'].leading = 15.1
            self.styles['body'].spaceAfter = 5.0
        for level, size in [(1, 22), (2, 15), (3, 12), (4, 10.8), (5, 10.2)]:
            self.styles[f'h{level}'] = ParagraphStyle(
                f'h{level}', fontName='CJKBold' if self.zh else 'BodyBold',
                fontSize=size, leading=size*1.4, textColor=BLUE,
                spaceBefore=14 if level > 1 else 0, spaceAfter=8,
                keepWithNext=True, wordWrap='CJK')

    def inlines(self, items, size=None, font=None, links=True):
        size = size or self.font_size
        font = font or self.body_font
        result = []
        for node in items:
            tag, data = node['t'], node.get('c')
            if tag == 'Str':
                result.append(literal(data, font))
            elif tag in ('Space', 'SoftBreak'):
                result.append(' ')
            elif tag == 'LineBreak':
                result.append('<br/>')
            elif tag in ('Strong', 'Emph', 'Underline', 'Strikeout', 'SmallCaps'):
                target = ('CJKBold' if font.startswith('CJK') else 'BodyBold') if tag == 'Strong' else font
                if tag == 'Emph' and font == 'Body':
                    target = 'BodyItalic'
                result.append(self.inlines(data, size, target, links))
            elif tag == 'Code':
                result.append(f'<font size="{size*0.9}">{literal(data[1], "Code")}</font>')
            elif tag == 'Math':
                kind, tex = data
                info = self.index[math_key(tex, kind['t'] == 'DisplayMath')]
                math_size = size * 1.01
                width, height = info['emWidth'] * math_size, info['emHeight'] * math_size
                if width > TEXT_W:
                    self.warnings.append(f'Long inline math shrunk: {tex}')
                    height *= TEXT_W / width
                    math_size *= TEXT_W / width
                    width = TEXT_W
                result.append(f'<img src="{html.escape(info["png"], quote=True)}" width="{width:.3f}" height="{height:.3f}" valign="{-info["emDepth"]*math_size:.3f}"/>')
            elif tag == 'Link':
                label = self.inlines(data[1], size, font, links=False)
                url = data[2][0]
                if links and re.match(r'^https?://', url):
                    result.append(f'<a href="{html.escape(url, quote=True)}" color="#235b7c">{label}</a>')
                else:
                    # Relative Markdown paths belong to the repository, not a web server.
                    result.append(label)
            elif tag == 'Quoted':
                result.append('“' + self.inlines(data[1], size, font, links) + '”')
            elif tag in ('Superscript', 'Subscript'):
                htmltag = 'super' if tag == 'Superscript' else 'sub'
                result.append(f'<{htmltag}>{self.inlines(data, size*0.8, font, links)}</{htmltag}>')
            elif tag == 'Span':
                result.append(self.inlines(data[1], size, font, links))
            elif tag == 'Note':
                raise ValueError('Footnotes need explicit rendering support.')
            elif tag == 'RawInline':
                raise ValueError(f'Raw inline content not silently omitted: {data}')
            else:
                raise ValueError(f'Unknown inline {tag}: {data}')
        return ''.join(result)

    def paragraph(self, nodes, style='body'):
        return Paragraph(self.inlines(nodes, self.styles[style].fontSize), self.styles[style])

    def blocks(self, blocks, width=TEXT_W):
        result = []
        for block in blocks:
            tag, data = block['t'], block.get('c')
            if tag == 'Header':
                level, attr, nodes = data
                style = f'h{min(level, 5)}'
                if level == 1:
                    # Language links remain in the body and repository, not in a giant title.
                    nodes = [n for n in nodes if n['t'] != 'Link']
                    while nodes and (nodes[-1]['t'] == 'Space' or
                                     (nodes[-1]['t'] == 'Str' and nodes[-1]['c'] in ('-', '—', '–', '·', '|'))):
                        nodes.pop()
                result.append(self.paragraph(nodes, style))
                if level == 1:
                    label = '定义与证明资料  /  中文版' if self.zh else 'DEFINITIONS & PROOFS  /  ENGLISH EDITION'
                    result.append(Paragraph(literal(label, self.body_font), self.styles['small']))
                    result.append(HRFlowable(width='100%', thickness=0.7, color=BLUE, spaceAfter=12))
            elif tag in ('Para', 'Plain'):
                if len(data) == 1 and data[0]['t'] == 'Math' and data[0]['c'][0]['t'] == 'DisplayMath':
                    tex = data[0]['c'][1]
                    info = self.index[math_key(tex, True)]
                    size = 11.1
                    available = width - 42 if info.get('tag') else width
                    factor = min(1, available / (info['emWidth']*size))
                    if factor < 0.72:
                        self.warnings.append(f'Wide display math (scale {factor:.2f}): {tex}')
                    image = Image(info['png'], info['emWidth']*size*factor, info['emHeight']*size*factor)
                    image.hAlign = 'CENTER'
                    if info.get('tag'):
                        tag_style = ParagraphStyle('equation-number', parent=self.styles['small'], alignment=2)
                        number = Paragraph(literal('('+info['tag']+')', self.body_font), tag_style)
                        equation = Table([[image, number]], colWidths=[available, 42])
                        equation.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'MIDDLE'),
                                                      ('ALIGN',(0,0),(0,0),'CENTER'),
                                                      ('LEFTPADDING',(0,0),(-1,-1),0),
                                                      ('RIGHTPADDING',(0,0),(-1,-1),0),
                                                      ('TOPPADDING',(0,0),(-1,-1),0),
                                                      ('BOTTOMPADDING',(0,0),(-1,-1),0)]))
                    else:
                        equation = image
                    result.extend([Spacer(1, 5), equation, Spacer(1, 9)])
                else:
                    result.append(self.paragraph(data))
            elif tag in ('BulletList', 'OrderedList'):
                start, items = (1, data) if tag == 'BulletList' else (data[0][0], data[1])
                for number, item in enumerate(items, start):
                    nested = self.blocks(item, width-17)
                    label = '•' if tag == 'BulletList' else f'{number}.'
                    # A two-column table keeps the bullet aligned to the first body line.
                    row = [[Paragraph(literal(label, self.body_font), self.styles['body']), nested]]
                    table = Table(row, colWidths=[17, width-17], hAlign='LEFT', splitInRow=1)
                    table.setStyle(TableStyle([('VALIGN', (0,0),(-1,-1),'TOP'),
                                              ('LEFTPADDING',(0,0),(-1,-1),0),
                                              ('RIGHTPADDING',(0,0),(-1,-1),0),
                                              ('TOPPADDING',(0,0),(-1,-1),0),
                                              ('BOTTOMPADDING',(0,0),(-1,-1),0)]))
                    result.append(table)
            elif tag == 'CodeBlock':
                text = data[1]
                rows = [Paragraph(literal(line.replace(' ', '\u00a0'), 'Code'), self.styles['code'])
                        for line in text.splitlines()]
                table = Table([[r] for r in rows], colWidths=[width], hAlign='LEFT')
                table.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,-1),colors.HexColor('#f1f5f8')),
                                          ('BOX',(0,0),(-1,-1),0.4,colors.HexColor('#d4dee6')),
                                          ('LEFTPADDING',(0,0),(-1,-1),8),
                                          ('RIGHTPADDING',(0,0),(-1,-1),8),
                                          ('TOPPADDING',(0,0),(-1,-1),2),
                                          ('BOTTOMPADDING',(0,0),(-1,-1),2)]))
                result.extend([table, Spacer(1, 8)])
            elif tag == 'HorizontalRule':
                result.append(HRFlowable(width='100%', thickness=0.4, color=colors.HexColor('#ced8df'),
                                         spaceBefore=7, spaceAfter=7))
            elif tag == 'BlockQuote':
                nested = self.blocks(data, width-18)
                table = Table([[nested]], colWidths=[width], hAlign='LEFT')
                table.setStyle(TableStyle([('LINEBEFORE',(0,0),(-1,-1),2,BLUE),
                                          ('LEFTPADDING',(0,0),(-1,-1),10)]))
                result.extend([table, Spacer(1, 6)])
            elif tag == 'Table':
                # Pandoc 2.10+ six-part table AST.
                attr, caption, colspecs, head, bodies, foot = data
                rawrows = list(head[1])
                for body in bodies:
                    rawrows.extend(body[2]); rawrows.extend(body[3])
                rawrows.extend(foot[1])
                rows = []
                for row in rawrows:
                    cells = []
                    for cell in row[1]:
                        if cell[2] != 1 or cell[3] != 1:
                            raise ValueError('Merged table cells require explicit rendering support.')
                        body = []
                        for child in cell[4]:
                            if child['t'] in ('Plain', 'Para'):
                                body.append(Paragraph(self.inlines(child['c'], 8.5), self.styles['small']))
                            else:
                                body.extend(self.blocks([child], width/len(colspecs)-14))
                        cells.append(body)
                    rows.append(cells)
                ncols = len(colspecs)
                widths = [width / ncols]*ncols
                if ncols == 2:
                    widths = [width*0.25, width*0.75]
                table = Table(rows, colWidths=widths, repeatRows=len(head[1]), hAlign='LEFT')
                table.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,max(0,len(head[1])-1)),colors.HexColor('#e8f0f5')),
                                          ('GRID',(0,0),(-1,-1),0.35,colors.HexColor('#d0dce4')),
                                          ('VALIGN',(0,0),(-1,-1),'TOP'),
                                          ('LEFTPADDING',(0,0),(-1,-1),6),
                                          ('RIGHTPADDING',(0,0),(-1,-1),6),
                                          ('TOPPADDING',(0,0),(-1,-1),5),
                                          ('BOTTOMPADDING',(0,0),(-1,-1),4)]))
                result.extend([table, Spacer(1, 9)])
            elif tag == 'Div':
                result.extend(self.blocks(data[1], width))
            elif tag == 'Null':
                pass
            else:
                raise ValueError(f'Unknown block {tag}; content will not be silently omitted.')
        return result

    def render(self, ast):
        destination = self.source.with_suffix('.pdf')
        label = self.source.parent.name
        if label == 'paper':
            label = 'Y · RPD · LRD · Ω-LRD3'
        doc = SimpleDocTemplate(str(destination), pagesize=A4,
                                leftMargin=50, rightMargin=50, topMargin=48, bottomMargin=48,
                                title=label + (' - 中文' if self.zh else ' - English'),
                                author='Ordinal Notations research project')

        def footer(canvas, document):
            canvas.setStrokeColor(colors.HexColor('#d0dce4'))
            canvas.setLineWidth(0.4)
            canvas.line(50, 35, PAGE_W-50, 35)
            canvas.setFillColor(colors.HexColor('#607284'))
            canvas.setFont('CJK', 7.4)
            canvas.drawString(50, 23, label + '  |  2026-09-13')
            canvas.drawRightString(PAGE_W-50, 23, str(document.page))

        doc.build(self.blocks(ast['blocks']), onFirstPage=footer, onLaterPages=footer)
        reader = PdfReader(destination)
        if not reader.pages:
            raise RuntimeError(f'Empty PDF: {destination}')
        for number, page in enumerate(reader.pages, 1):
            text = page.extract_text() or ''
            if '\ufffd' in text or '\x00' in text:
                raise RuntimeError(f'Broken text on page {number}: {destination}')
        return {'source': self.source.relative_to(ROOT).as_posix(), 'pdf': destination.relative_to(ROOT).as_posix(),
                'pages': len(reader.pages), 'bytes': destination.stat().st_size,
                'sha256': hashlib.sha256(destination.read_bytes()).hexdigest(), 'warnings': self.warnings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sources', nargs='*', help='Markdown paths relative to the release root')
    parser.add_argument('--pandoc', default='pandoc')
    parser.add_argument('--node', default='node')
    parser.add_argument('--font-dir', default=os.environ.get('ORDINAL_PDF_FONTS', 'C:/Windows/Fonts'))
    parser.add_argument('--keep-cache', action='store_true')
    args = parser.parse_args()
    sources = [ROOT / p for p in args.sources] if args.sources else [
        ROOT / f'notations/{notation}/definition{lang}.md'
        for notation in ('RPD', 'LRD', 'Omega-LRD3') for lang in ('', '.zh-CN')
    ] + [ROOT / f'proofs/paper/well-ordering{lang}.md' for lang in ('', '.zh-CN')]
    for source in sources:
        if not source.is_file():
            raise FileNotFoundError(source)
    register_fonts(args.font_dir)
    cache_root = (ROOT / 'tmp/pdfs').resolve()
    cache = cache_root / ('build-' + uuid.uuid4().hex)
    cache.mkdir(parents=True, exist_ok=False)
    try:
        asts, formulas = [], {}
        for source in sources:
            result = run([args.pandoc, '-f', 'markdown+tex_math_dollars+tex_math_single_backslash',
                          '-t', 'json', str(source)])
            ast = json.loads(result.stdout)
            collect_math(ast, formulas)
            asts.append(ast)
        formula_input = cache / 'formulas.json'
        formula_input.write_text(json.dumps(list(formulas.values()), ensure_ascii=False), encoding='utf-8')
        result = run([args.node, str(ROOT/'tools/math.cjs'), str(formula_input), str(cache)])
        print(result.stdout.strip())
        index = json.loads((cache / 'index.json').read_text(encoding='utf-8'))
        reports = []
        for source, ast in zip(sources, asts):
            report = Renderer(source, index).render(ast)
            reports.append(report)
            print(f'{report["pdf"]}: {report["pages"]} pages, {report["bytes"]} bytes')
            for warning in report['warnings']:
                print('  REVIEW:', warning)
        report_path = ROOT / 'tools/pdf-build-report.json'
        report_path.write_text(json.dumps(reports, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
        print('Review rendered page images before publishing. Build report:', report_path)
    finally:
        if args.keep_cache:
            print('Formula cache retained at', cache)
        else:
            # Only this script's fresh, resolved child directory is removed.
            resolved = cache.resolve()
            if resolved.parent != cache_root or not resolved.name.startswith('build-'):
                raise RuntimeError('Refusing to remove an unexpected cache path.')
            shutil.rmtree(resolved)


if __name__ == '__main__':
    main()
