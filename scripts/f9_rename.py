#!/usr/bin/env python3
"""Phase F9: batch renaming (design decision A6). Usage: f9_rename.py [--dry] MAP.json
MAP maps old identifier (short name) to new. Replacement is whole-word, in code and comments,
across the library, the root module and docs/README. Longer names are replaced first so that
`radical` does not clobber `radicalLayer`."""
import json, re, sys, glob
dry = '--dry' in sys.argv; spec = [a for a in sys.argv[1:] if not a.startswith('--')][0]
mapping = json.load(open(spec))
files = glob.glob('FalseTateExtension/**/*.lean', recursive=True) + glob.glob('*.lean') + ['README.md']
total = {}
def rename_text(s):
    for old in sorted(mapping, key=len, reverse=True):
        new = mapping[old]
        pat = r"(?<![\w₀-₉'])" + re.escape(old) + r"(?![\w₀-₉'])"
        n = len(re.findall(pat, s))
        if n: total[old] = total.get(old, 0) + n
        s = re.sub(pat, new, s)
    return s
def rename_comment(c):
    # only backticked identifiers inside comments
    return re.sub(r'`([^`\n]*)`', lambda m: '`' + rename_text(m.group(1)) + '`', c)
for f in files:
    s = open(f).read(); o = s
    if f.endswith('.md'):
        s = rename_comment(s)
    else:
        parts = re.split(r'(/-.*?-/|--[^\n]*)', s, flags=re.S)
        s = ''.join(rename_comment(x) if (x.startswith('/-') or x.startswith('--')) else rename_text(x) for x in parts)
    if s != o and not dry: open(f, 'w').write(s)
for k, v in sorted(total.items(), key=lambda x: -x[1]): print(f'{v:5d} {k} -> {mapping[k]}')
