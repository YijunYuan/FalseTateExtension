#!/usr/bin/env python3
"""Phase F10, first pass: remove filler adjectives from docstrings, comments and section names.

Removes the words actual, original, canonical, ordinary, literal, intrinsic, prescribed, genuine,
genuinely, usual, existing, corrected (and "actually") inside `/-- … -/`, `/-! … -/` and `--`
comments, fixes the resulting double spaces and dangling articles, and renames sections such as
`ActualUpper`. It never touches code. Run, then rewrite the docstrings by hand."""
import re, glob, sys

WORDS = r'(actual|actually|original|originally|canonical|canonically|ordinary|literal|literally|intrinsic|intrinsically|prescribed|genuine|genuinely|usual|existing|corrected|true|proved|displayed|chosen)'
VOWEL_WORDS = r'(actual|actually|original|originally|ordinary|intrinsic|intrinsically|existing)'
CONS_WORDS = r'(canonical|canonically|literal|literally|prescribed|genuine|genuinely|usual|corrected|true|proved|displayed|chosen)'
CONSONANT_SOUND = ('uniformizer', 'unit', 'union', 'unique', 'usual', 'one', 'universal', 'unramified')

def article(word):
    return 'a' if word.lower().startswith(CONSONANT_SOUND) or word[0].lower() not in 'aeiou' else 'an'

def clean(txt: str) -> str:
    # articles before a deleted adjective
    t = re.sub(r'\b([Aa])n ' + VOWEL_WORDS + r'\s+(\w+)', lambda m: (m.group(1) if article(m.group(3)) == 'a' else m.group(1) + 'n') + ' ' + m.group(3), txt)
    t = re.sub(r'\b([Aa]) ' + CONS_WORDS + r'\s+(\w+)', lambda m: (m.group(1) if article(m.group(3)) == 'a' else m.group(1) + 'n') + ' ' + m.group(3), t)
    t = re.sub(r'\b(original|actual)-base\b', 'base', t)
    t = re.sub(r'\b' + WORDS + r'\s+', lambda m: '' if m.group(0).endswith(' ') else '\n', t)
    # sentence-initial capitalized filler: drop it and capitalize the next word
    t = re.sub(r'\b(Actual|Actually|Original|Originally|Canonical|Ordinary|Literal|Intrinsic|Genuine|Genuinely|Prescribed|Usual|Existing|Corrected)\s+(\w)', lambda m: m.group(2).upper(), t)
    t = re.sub(r' ' + WORDS + r'\b(?=[.,;:])', '', t)
    t = re.sub(r'[ \t]{2,}', ' ', t)
    t = re.sub(r'[ \t]+\n', '\n', t)
    t = re.sub(r'\n[ \t]*\n(?=[^\n])', '\n', t) if False else t
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
