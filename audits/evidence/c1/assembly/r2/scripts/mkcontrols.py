"""Controls of round 2's fail-closed checks (stdlib only). Usage: python3 -I mkcontrols.py <outdir>

Writes under <outdir>/work/ (each edit asserted):
  ctrl_pending.lean       a pending file declaring `Turing.guessRunTM` (the name screen must fail);
  ctrl_iso_unit.lean      the unit with the writer's argument parenthesized, `(j)` (syntax-
                          equivalent; the isolation builder's replacement assertion must fail and
                          leave no target);
  ctrl_freeze_Embed.lean  the landed Embed with one existing statement changed (the freeze must
                          fail).
"""
import sys

O = sys.argv[1]
open(f"{O}/work/ctrl_pending.lean", "w", encoding="utf-8").write(
    "namespace Turing\ndef guessRunTM := 0\nend Turing\n")
u = open(f"{O}/C1Assembly.lean", encoding="utf-8").read()
o = "ndWriterTM_run_block j cW"
assert u.count(o) == 1
open(f"{O}/work/ctrl_iso_unit.lean", "w", encoding="utf-8").write(
    u.replace(o, "ndWriterTM_run_block (j) cW"))
e = open(f"{O}/landed/TCSlib/Complexity/TuringMachine/Build/Embed.lean", encoding="utf-8").read()
o = ("    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =\n"
     "      c.workTapePos i := by")
assert e.count(o) == 1
open(f"{O}/work/ctrl_freeze_Embed.lean", "w", encoding="utf-8").write(
    e.replace(o, "    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =\n"
              "      c.workTapePos i + 0 := by"))
print("controls written")
