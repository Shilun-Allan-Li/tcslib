#!/usr/bin/env python3
"""Explicit-unfold scan, step 1: collect every identifier passed to rw/rwa/nth_rw/simp/simp only/
simpa/simp_rw/dsimp/unfold/delta in a Lean file, and write a scan module that resolves them in the
file's namespace with the file's `open`s.

Usage: rwids.py <worktree> <src.lean> <out module (relative, no .lean)>
Prints `<n> identifiers`."""
import re, sys, os

wt, src, out = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(os.path.join(wt, src)).read()
# drop comments (block and line), keep code
code = re.sub(r'/-.*?-/', lambda m: ' ' * len(m.group(0)), text, flags=re.S)
code = re.sub(r'--[^\n]*', '', code)

ids = set()
KW = r'(?:rw|rwa|nth_rw\s+\d+(?:\s+\d+)*|nth_rewrite\s+\d+|rewrite|erw|simp|simp only|simp_all|simp_all only|simpa|simpa only|dsimp|dsimp only|simp_rw|field_simp|norm_num|conv_lhs\s*=>\s*rw|conv_rhs\s*=>\s*rw)'
for m in re.finditer(r'\b' + KW + r'(?:\s*\(config[^)]*\))?\s*\[', code):
    i = m.end()
    depth = 1
    j = i
    while j < len(code) and depth:
        c = code[j]
        if c in '[(⟨{':
            depth += 1
        elif c in '])⟩}':
            depth -= 1
        j += 1
    body = code[i:j - 1]
    # split at depth-0 commas
    items, cur, d = [], '', 0
    for c in body:
        if c in '[(⟨{':
            d += 1
        elif c in '])⟩}':
            d -= 1
        if c == ',' and d == 0:
            items.append(cur); cur = ''
        else:
            cur += c
    items.append(cur)
    for it in items:
        it = it.strip()
        it = re.sub(r'^(←|<-|-|↓)\s*', '', it).strip()
        it = it.lstrip('(').strip()
        it = re.sub(r'^(←|<-)\s*', '', it).strip()
        mm = re.match(r"[A-Za-z_\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2070-\u209F][\w.'\u00C0-\u024F\u0370-\u03FF\u2070-\u209F₀-₉!?]*", it)
        if mm:
            ids.add(mm.group(0).rstrip('.'))
for m in re.finditer(r'\b(?:unfold|delta)\s+([^\n]*)', code):
    for tok in m.group(1).split():
        if tok in ('at', '⊢', 'in'):
            break
        if re.match(r"[A-Za-z_]", tok):
            ids.add(tok)
ids.discard('')
# namespace and opens
ns = re.search(r'^namespace\s+(\S+)', text, re.M)
opens = re.findall(r'^\s*open\s+([^\n]+)', code, re.M)
# every namespace of the file, with its full name (namespace/section/end stack)
stack, nested = [], []
for line in code.split('\n'):
    m1 = re.match(r'^\s*namespace\s+(\S+)', line)
    m2 = re.match(r'^\s*section\b', line)
    m3 = re.match(r'^\s*end\b\s*(\S*)', line)
    if m1:
        stack.append(('ns', m1.group(1)))
        full = '.'.join(x for k, x in stack if k == 'ns')
        nested.append(full)
    elif m2:
        stack.append(('sec', ''))
    elif m3 and stack:
        stack.pop()
nested = [x for x in dict.fromkeys(nested) if not ns or x != ns.group(1)]
modname = src[:-5].replace('/', '.')
lines = [f'import {modname}', 'open Lean Elab Command', '']
if ns:
    lines.append(f'namespace {ns.group(1)}')
for o in opens:
    o = re.sub(r'\bin\b.*', '', o).strip()
    if o:
        lines.append(f'open {o}')
for x in nested:
    lines.append(f'open {x}')
lines.append('')
lines.append('def idsToCheck : List String := [' + ','.join('"%s"' % s.replace('"', '') for s in sorted(ids)) + ']')
lines.append(f'def scannedModule : Name := `{modname}')
lines.append('''
#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    if cands.isEmpty then IO.println s!"{s}\\t-\\tlocal/unresolved\\t-"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some (.opaqueInfo _) => "opaque"
        | some (.inductInfo _) => "inductive"
        | some (.ctorInfo _) => "ctor"
        | some _ => "other"
        | none => "?"
      let m := modOf c
      let tag := if k == "DEF" then
          (if m == scannedModule then "own-def" else if (`TCSlib).isPrefixOf m then "FOREIGN-TCSLIB-DEF" else "core/mathlib-def")
        else k
      IO.println s!"{s}\\t{c}\\t{tag}\\t{m}"
''')
if ns:
    lines.append(f'end {ns.group(1)}')
os.makedirs(os.path.dirname(os.path.join(wt, out)), exist_ok=True)
open(os.path.join(wt, out + '.lean'), 'w').write('\n'.join(lines) + '\n')
print(len(ids), 'identifiers')
