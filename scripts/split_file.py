#!/usr/bin/env python3
"""Split a Lean source file into several modules along `section` boundaries (phase F8).

Usage: split_file.py SPEC.json
SPEC = {"src": "Lib/Old.lean",
        "parts": [{"dst": "Lib/New/A.lean", "sections": ["Foo", "Bar"], "title": "...",
                   "doc": "...", "imports": ["Lib.New.Base"]}, ...],
        "delete_src": true}
Each part receives the header of the source (copyright, `module`, the source's `public import`
lines plus the part's own `imports`), a module docstring from `title`/`doc`, `@[expose] public
section`, the namespace/`noncomputable section`/`open` lines that precede the first section of
the source, the file-level `variable` lines, and the named sections in order. Top-level
declarations outside any section go to the part whose `sections` list contains "_toplevel".
The script does not try to compute minimal imports; later parts import the earlier ones."""
import json, re, sys, pathlib

def main(spec_path):
    spec = json.load(open(spec_path))
    src = pathlib.Path(spec['src']); text = src.read_text(); lines = text.split('\n')
    # header: up to and including '@[expose] public section'
    i_expose = next(i for i,l in enumerate(lines) if l.strip() == '@[expose] public section')
    copyright = lines[:lines.index('module')]
    imports = [l for l in lines[:i_expose] if l.startswith('public import ')]
    # preamble after expose until first 'section <Name>' or first declaration: namespace/open/noncomputable/variable
    body = lines[i_expose+1:]
    pre = []; j = 0
    while j < len(body):
        l = body[j]
        if re.match(r'section\s+\S', l) or re.match(r'(/--|@\[|theorem|lemma|def|instance|abbrev|noncomputable def|private|protected|local|attribute|structure|class)', l):
            break
        pre.append(l); j += 1
    # collect named sections (top-level only) and top-level chunks
    chunks = {}  # name -> lines
    toplevel = []
    k = j
    while k < len(body):
        l = body[k]
        m = re.match(r'section\s+(\S+)\s*$', l)
        if m:
            name = m.group(1); depth = 1; e = k+1
            while e < len(body):
                if re.match(r'section\b', body[e]): depth += 1
                elif re.match(r'end\s+' + re.escape(name) + r'\s*$', body[e]) and depth == 1: break
                elif re.match(r'end\b', body[e]): depth -= 1
                e += 1
            chunks[name] = body[k:e+1]; k = e+1; continue
        if re.match(r'end\s*$', l) or re.match(r'end\s+\S+', l):
            k += 1; continue   # closing of namespace / noncomputable section
        toplevel.append(l); k += 1
    used = set()
    prev_modules = []
    for part in spec['parts']:
        base = [l for l in imports if not l.startswith('public import ' + spec.get('lib_prefix', 'FalseTateExtension') + '.')] if part.get('drop_project_imports') else imports
        out = copyright + ['module', ''] + sorted(set(base + ['public import ' + m for m in part.get('imports', []) + prev_modules]))
        out += ['', '/-!', '# ' + part['title'], '', part.get('doc', ''), '-/', '', '@[expose] public section'] + pre
        for s in part['sections']:
            if s == '_toplevel':
                out += toplevel
            else:
                out += chunks[s]; used.add(s)
            out.append('')
        # close namespace/noncomputable section in reverse order of the preamble
        closers = []
        for l in pre:
            if l.startswith('noncomputable section'): closers.append('end')
            m = re.match(r'namespace (\S+)', l)
            if m: closers.append('end ' + m.group(1))
        out += list(reversed(closers)) + ['']
        dst = pathlib.Path(part['dst']); dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(re.sub(r'\n{3,}', '\n\n', '\n'.join(out)))
        prev_modules.append(part['module'])
        print('wrote', dst, 'sections', part['sections'])
    missing = set(chunks) - used
    if missing: print('WARNING: sections not assigned:', missing)
    if spec.get('delete_src'): src.unlink(); print('deleted', src)

if __name__ == '__main__':
    main(sys.argv[1])
