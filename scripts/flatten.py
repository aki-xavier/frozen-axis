#!/usr/bin/env python3
"""Flatten the JMLR LaTeX version into a single self-contained .tex file.

JMLR's final-preparation instructions ask for an archive that "should
ideally contain only one .tex file" (they suggest latexpand). This script
does the same job without an external dependency: it expands every
\\input{...} in main.tex recursively and writes paper.tex next to it.

Usage:  python3 scripts/flatten.py
"""

import os
import re

PAPER_DIR = os.path.abspath(os.path.join(
    os.path.dirname(os.path.abspath(__file__)), os.pardir, 'paper'))
ENTRY = os.path.join(PAPER_DIR, 'main.tex')
OUTPUT = os.path.join(PAPER_DIR, 'paper.tex')

INPUT_RE = re.compile(r'^[ \t]*\\input\{([^}]+)\}[ \t]*$', re.M)


def expand(path, depth=0):
    if depth > 8:
        raise RuntimeError('input nesting too deep: ' + path)
    text = open(path, encoding='utf-8').read()
    base = os.path.dirname(path)

    def repl(m):
        target = m.group(1)
        if not target.endswith('.tex'):
            target += '.tex'
        child = os.path.join(base, target)
        if not os.path.isfile(child):
            raise FileNotFoundError(child)
        rel = os.path.relpath(child, PAPER_DIR)
        body = expand(child, depth + 1)
        bar = '%' * 70
        return (bar + '\n%% --- inlined from ' + rel + '\n' + bar + '\n' + body)

    return INPUT_RE.sub(repl, text)


def main():
    out = expand(ENTRY)
    header = (
        '%%=======================================================================\n'
        '%% GENERATED FILE -- do not edit by hand.\n'
        '%% Produced by flatten.py from main.tex and sections/*.tex, so that the\n'
        '%% archive submitted to JMLR contains a single .tex file as its final\n'
        '%% preparation instructions request.\n'
        '%% Edit main.tex / sections/*.tex and re-run:  python3 scripts/flatten.py\n'
        '%%=======================================================================\n'
    )
    # keep the "% !TeX program" line first if present
    lines = out.split('\n')
    if lines and lines[0].startswith('% !TeX'):
        header = lines[0] + '\n' + header
        out = '\n'.join(lines[1:])
    open(OUTPUT, 'w', encoding='utf-8').write(header + out)
    print('wrote %s (%d bytes)' % (OUTPUT, len(header + out)))


if __name__ == '__main__':
    main()
