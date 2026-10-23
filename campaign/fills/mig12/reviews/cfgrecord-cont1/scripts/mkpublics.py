import sys
# usage: mkpublics.py <module> <out>: append a command listing every non-private constant this module adds
src, out = sys.argv[1:3]
tail = r'''
open Lean Elab Command in
elab "#own_publics" : command => do
  let env ← getEnv
  let mut ns : Array Name := #[]
  for (n, _) in env.constants.map₂.toList do
    if (env.getModuleIdxFor? n).isNone && !isPrivateName n then ns := ns.push n
  let s := (ns.map toString).qsort (· < ·)
  logInfo m!"OWNPUBLICS {s.size}: {s}"
#own_publics
'''
open(out, 'w', encoding='utf-8').write(open(src, encoding='utf-8').read().rstrip('\n') + '\n' + tail)
