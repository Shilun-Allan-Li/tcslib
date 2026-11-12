#!/usr/bin/env python3
"""Type comparison modulo the name map.

Usage: typecmp_gen.py <base|final> <namemap.txt> <names.txt> <imports.txt> <out.lean>

Writes a Lean file that, for every listed constant present in the environment, prints
`name | hash` where `hash` is the hash of its type after renaming every constant by the name map
(base side: old -> new; final side: identity). Equal hashes on the two sides mean the same
statement up to the renaming of moved declarations."""
import sys
side, nm, names, imps, out = sys.argv[1:6]
pairs = []
for l in open(nm):
    l = l.strip()
    if not l or l.startswith('#'):
        continue
    a, b = [x.strip() for x in l.split('->')]
    if a != '-' and side == 'base':
        pairs.append((a, b))
ns = [l.strip() for l in open(names) if l.strip()]
im = [l.strip() for l in open(imps) if l.strip()]
def lit(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'
src = '\n'.join('import ' + m for m in im) + '''
open Lean Elab Command

/-- Parse a dotted name, numeric components as numbers (private prefixes). -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => match c.toNat? with
    | some k => if c.all Char.isDigit then .num n k else .str n c
    | none => .str n c) .anonymous

def renames : List (String × String) := [''' + ', '.join(f'({lit(a)}, {lit(b)})' for a, b in pairs) + ''']
def toCheck : List String := [''' + ', '.join(lit(n) for n in ns) + ''']

#eval show CommandElabM Unit from do
  let env ← getEnv
  let m : Std.HashMap Name Name := renames.foldl (fun m (a, b) => m.insert (parseName a) (parseName b)) {}
  for s in toCheck do
    let n := parseName s
    match env.find? n with
    | none => IO.println s!"{s} | absent"
    | some ci =>
      let t := ci.type.replace fun e => match e with
        | .const c ls => (m.get? c).map fun c' => Expr.const c' ls
        | _ => none
      IO.println s!"{s} | {t.hash}"
'''
open(out, 'w').write(src)
print(out, len(ns), 'names', len(pairs), 'renames')
