#!/usr/bin/env python3
"""Phase F8: move modules to the layered tree and rewrite imports. Usage: f8_move.py MAP.json
MAP = {"Old.Module": "New.Module", ...} (module names relative to the library prefix)."""
import json, re, sys, subprocess, pathlib, glob
root = pathlib.Path('.'); root_file = next(root.glob('*.lean')); LIB = root_file.stem
mapping = json.load(open(sys.argv[1]))
for old, new in mapping.items():
    src = root / LIB / (old.replace('.', '/') + '.lean'); dst = root / LIB / (new.replace('.', '/') + '.lean')
    dst.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(['git', 'mv', str(src), str(dst)], check=True)
files = glob.glob(f'{LIB}/**/*.lean', recursive=True) + [str(root_file)]
for f in files:
    s = open(f).read(); o = s
    for old, new in mapping.items():
        s = re.sub(r'^public import ' + re.escape(LIB + '.' + old) + r'$', 'public import ' + LIB + '.' + new, s, flags=re.M)
    if s != o: open(f, 'w').write(s)
print('moved', len(mapping), 'modules')
