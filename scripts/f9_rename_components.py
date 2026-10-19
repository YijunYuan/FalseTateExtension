#!/usr/bin/env python3
"""Phase F9, second pass: rename identifier *components* (parts separated by `_`), e.g.
`tau_extensionRadical` -> `kummerGenerator_pPowRootExt`. Usage: f9_rename_components.py [--dry] MAP.json"""
import json, re, sys, glob
dry = '--dry' in sys.argv; spec = [a for a in sys.argv[1:] if not a.startswith('--')][0]
comp = json.load(open(spec))
IDENT = re.compile(r"(?<![\w₀-₉'.])([A-Za-z][\w₀-₉']*(?:_[\w₀-₉']+)+)(?![\w₀-₉'])")
total = {}
def fix(name):
    parts = name.split('_')
    new = [comp.get(x, x) for x in parts]
    if new != parts: total[name] = total.get(name, 0) + 1
    return '_'.join(new)
def rename_text(s): return IDENT.sub(lambda m: fix(m.group(1)), s)
def rename_comment(c): return re.sub(r'`([^`\n]*)`', lambda m: '`' + rename_text(m.group(1)) + '`', c)
for f in glob.glob('FalseTateExtension/**/*.lean', recursive=True) + glob.glob('*.lean') + ['README.md']:
    s = open(f).read(); o = s
    if f.endswith('.md'): s = rename_comment(s)
    else:
        parts = re.split(r'(/-.*?-/|--[^\n]*)', s, flags=re.S)
        s = ''.join(rename_comment(x) if (x.startswith('/-') or x.startswith('--')) else rename_text(x) for x in parts)
    if s != o and not dry: open(f, 'w').write(s)
for k, v in sorted(total.items(), key=lambda x: -x[1]): print(f'{v:4d} {k} -> {fix(k)}')
