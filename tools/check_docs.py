#!/usr/bin/env python3
"""Check local file targets in maintained Markdown documentation."""
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]


def main():
    files = [ROOT / 'README.md', ROOT / 'CONTRIBUTING.md']
    for directory in ['docs', 'lean', 'tools', 'experiments', 'results', 'papers']:
        files.extend(p for p in (ROOT / directory).rglob('*.md') if '.lake' not in p.parts)
    bad = []
    checked = 0
    for path in files:
        text = re.sub(r'(?ms)^```.*?^```[^\n]*', '', path.read_text())
        for match in re.finditer(r'\]\(([^)]+)\)', text):
            target = match[1].split(' "', 1)[0].strip('<>')
            if urlsplit(target).scheme or target.startswith('#'):
                continue
            target = unquote(target.split('#', 1)[0])
            if target and not (path.parent / target).exists():
                bad.append(f'{path.relative_to(ROOT)}: missing {target}')
            checked += 1
    if bad:
        sys.exit('\n'.join(bad))
    print(f'Checked {checked} local link targets in {len(files)} Markdown documents.')


if __name__ == '__main__':
    main()
