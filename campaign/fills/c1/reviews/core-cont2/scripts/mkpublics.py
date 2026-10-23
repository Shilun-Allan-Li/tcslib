import sys
# usage: mkpublics.py <module> <out>: the module followed by a listing of its own non-private constants
src, out = sys.argv[1], sys.argv[2]
t = open(src, encoding='utf-8').read().rstrip('\n')
tail = r'''

open Lean Elab Command in
/-- The module's own constants (not imported), non-private ones listed (maintainer's read-only probe). -/
elab "#module_publics" : command => do
  let env ← getEnv
  let mut pubs : Array String := #[]
  let mut privs : Nat := 0
  for (n, _) in env.constants.map₂.toList do
    if (env.getModuleIdxFor? n).isNone then
      if isPrivateName n then privs := privs + 1 else pubs := pubs.push n.toString
  let sorted := pubs.qsort (· < ·)
  logInfo m!"PUBLICS {sorted.size} (private constants {privs}): {sorted}"

#module_publics
'''
open(out, 'w', encoding='utf-8').write(t + tail)
