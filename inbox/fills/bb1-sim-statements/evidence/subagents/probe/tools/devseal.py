# COPIED (bb1-sim-statements, sub-agent probe, 2026-11-16) from exchange
# outbox/fills/bb1-machine/checkpoint/tools/dev/devseal.py (SHA-256
# 5673db0bd3c7a58ddc1d367955ecfd5edc325427d2041eaacee49bb1fedc0b8e). Changes: this header; the
# harness line `Lean.Elab.Command.elabCommand (← …)` (103 characters) is split after
# `elabCommand` so that every line of a sealed variant has at most 100 characters (2026-11-17).
# The earlier sealed scratch variants (`PlProbe/Scratch/*_A.lean`) were made before this split.
# It seals definitions of modules under `TCSlib` only, so the readers probe `PlProbe.BB1SimReaders`
# (the owners' stand-in) stays open, as intended.
"""devseal.py <src.lean> <out.lean> <A|B>: development seal (not evidence): insert after the imports a
run_cmd that makes every imported TCSlib definition (non-reducible or matcher) locally irreducible,
except PolyExpr.eval in variant A."""
import sys, re
src, out, var = sys.argv[1:4]
s = open(src, encoding='utf-8').read()
lines = s.split('\n')
last = max(i for i, l in enumerate(lines) if l.startswith('import '))
harness = f'''import Lean
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let mut k : Nat := 0
  for (n, ci) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    unless ci.isDefinition do continue
    if n == `Complexity.PolyExpr.eval && {'true' if var == 'A' else 'false'} then continue
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    let isM := Lean.Meta.isMatcherCore env n
    if st == .reducible && !isM then continue
    if st == .irreducible then continue
    Lean.Elab.Command.elabCommand
      (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    k := k + 1
  Lean.logInfo m!"DEVSEAL {var} sealed {{k}}"
'''
out_lines = lines[:last + 1] + harness.split('\n') + lines[last + 1:]
open(out, 'w', encoding='utf-8').write('\n'.join(out_lines))
