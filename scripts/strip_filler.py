#!/usr/bin/env python3
"""Phase F10, first pass: remove filler adjectives from docstrings, comments and section names.

Removes the words actual, original, canonical, ordinary, literal, intrinsic, prescribed, genuine,
genuinely, usual, existing, corrected (and "actually") inside `/-- … -/`, `/-! … -/` and `--`
comments, fixes the resulting double spaces and dangling articles, and renames sections such as
`ActualUpper`. It never touches code. Run, then rewrite the docstrings by hand."""
import re, glob, sys

WORDS = r'(actual|actually|original|originally|canonical|canonically|ordinary|literal|literally|intrinsic|intrinsically|prescribed|genuine|genuinely|usual|existing|corrected|true|proved|displayed|chosen)'
ARTICLE_FIX = [(r'\ba ((?:[aeiouAEIOU])\w)', r'an \1'), (r'\ban ((?:[^aeiouAEIOU\s])\w)', r'a \1')]

def clean(txt: str) -> str:
    t = re.sub(r'\b[Tt]he same ' + WORDS + r' ', 'the same ', txt)
    t = re.sub(r'\b' + WORDS + r' ', '', t)
    t = re.sub(r' ' + WORDS + r'\b(?=[.,;:])', '', t)
    t = re.sub(r'[ \t]{2,}', ' ', t)
    for a, b in ARTICLE_FIX: t = re.sub(a, b, t)
    return t

def process(path):
    s = open(path).read(); orig = s
    s = re.sub(r'/-[-!]?.*?-/', lambda m: clean(m.group(0)), s, flags=re.S)
    s = re.sub(r'--[^\n]*', lambda m: clean(m.group(0)), s)
    s = re.sub(r'^section (Actual|Original|Literal)(\w+)', lambda m: 'section ' + m.group(2), s, flags=re.M)
    s = re.sub(r'^end (Actual|Original|Literal)(\w+)', lambda m: 'end ' + m.group(2), s, flags=re.M)
    if s != orig:
        open(path, 'w').write(s); return 1
    return 0

if __name__ == '__main__':
    root = sys.argv[1] if len(sys.argv) > 1 else '.'
    n = sum(process(f) for f in glob.glob(root + '/**/*.lean', recursive=True))
    print(n, 'files changed')
