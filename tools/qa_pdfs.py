"""Render all delivered PDF pages and make contact sheets for visual review.

Requires Poppler's pdftoppm, Pillow, and pdfplumber. No source document is edited.
Outputs are temporary and ignored by Git. Inspect the images after running.
"""
from pathlib import Path
import argparse
import json
import subprocess

from PIL import Image, ImageDraw
import pdfplumber

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sources', nargs='*', help='Only these PDF paths, relative to the release root')
    parser.add_argument('--pdftoppm', default='pdftoppm')
    args = parser.parse_args()
    sources = [ROOT / p for p in args.sources] if args.sources else (
        sorted(ROOT.glob('notations/*/*.pdf')) + sorted(ROOT.glob('proofs/paper/*.pdf')))
    for pdf in sources:
        if not pdf.resolve().is_relative_to(ROOT.resolve()) or pdf.suffix.lower() != '.pdf':
            raise ValueError(f'Expected a PDF inside the release: {pdf}')
        if not pdf.is_file():
            raise FileNotFoundError(pdf)
    output = ROOT / 'tmp/pdf-qa'
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for pdf in sources:
        key = pdf.parent.name + '-' + pdf.stem
        folder = output / key
        folder.mkdir(exist_ok=True)
        subprocess.run([args.pdftoppm, '-r', '95', '-png', str(pdf), str(folder/'page')],
                       check=True, timeout=120, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        issues = []
        with pdfplumber.open(pdf) as doc:
            # Poppler changes zero-padding when the page count crosses 10.
            # Select this run's exact filenames, never stale PNGs from old layouts.
            digits = len(str(len(doc.pages)))
            pages = [folder / f'page-{number:0{digits}d}.png'
                     for number in range(1, len(doc.pages)+1)]
            if not all(p.is_file() for p in pages):
                raise RuntimeError(f'Incomplete page rendering: {pdf}')
            for number, page in enumerate(doc.pages, 1):
                for element in page.chars + page.images:
                    if element['x0'] < 40 or element['x1'] > page.width - 40:
                        issues.append({'page': number, 'kind': 'horizontal overflow',
                                       'text': element.get('text', '[formula]'),
                                       'bbox': [element['x0'], element['top'], element['x1'], element['bottom']]})
                    if element['top'] < 20 or element['bottom'] > page.height - 15:
                        issues.append({'page': number, 'kind': 'vertical overflow',
                                       'text': element.get('text', '[formula]')})
        for start in range(0, len(pages), 6):
            chunk = pages[start:start+6]
            thumb_w, thumb_h = 500, 708
            sheet = Image.new('RGB', (2*(thumb_w+16), 3*(thumb_h+32)), '#dfe5ea')
            draw = ImageDraw.Draw(sheet)
            for pos, path in enumerate(chunk):
                image = Image.open(path).convert('RGB')
                image.thumbnail((thumb_w, thumb_h))
                x, y = (pos % 2)*(thumb_w+16)+8, (pos//2)*(thumb_h+32)+24
                sheet.paste(image, (x, y))
                draw.text((x,y-18), f'{key} / page {start+pos+1}', fill='black')
            sheet.save(folder/f'contact-{start//6+1}.png')
        reports.append({'pdf': str(pdf.relative_to(ROOT)), 'pages': len(pages), 'issues': issues,
                        'render_directory': str(folder.relative_to(ROOT))})
        print(f'{pdf.relative_to(ROOT)}: {len(pages)} pages rendered, {len(issues)} bounds issues')
    (output/'report.json').write_text(json.dumps(reports, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    if any(r['issues'] for r in reports):
        raise SystemExit('Bounds check found issues. Inspect report and rendered pages.')
    print('Programmatic bounds checks passed. Visual inspection is still required.')


if __name__ == '__main__':
    main()
