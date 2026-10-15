"""Build the probe files of the C1 assembly gate from the unit and the tails (stdlib only).

Usage: python3 -I mkprobes.py <outdir>

Writes, from <outdir>/C1Assembly.lean and <outdir>/scripts/*_tail.lean.txt:
  probes/C1AssemblySanity.lean   the unit followed by the sanity tail;
  probes/C1AssemblyAxioms.lean   the unit followed by the axiom-print tail;
  AssemblyConsumerProbe.lean     the unit with two extra imports (`NDCodeSimulator`, for the
                                 interpreter core, and `ClassNP.NTIME`, for acceptance and the
                                 class) followed by the consumer tail;
  work/neg{1..4}.lean            negative controls: copies of the sanity file with one example
                                 made false (each must fail to elaborate);
  work/screen_ctrl.lean          a name-screen positive control with two existing full names.
Every edit is asserted to match exactly once.
"""
import sys

O = sys.argv[1]
unit = open(f"{O}/C1Assembly.lean", encoding="utf-8").read()
tail = lambda n: open(f"{O}/scripts/{n}_tail.lean.txt", encoding="utf-8").read()
san = unit + tail("sanity")
open(f"{O}/probes/C1AssemblySanity.lean", "w", encoding="utf-8").write(san)
open(f"{O}/probes/C1AssemblyAxioms.lean", "w", encoding="utf-8").write(unit + tail("axioms"))
a = "import TCSlib.Complexity.TuringMachine.Build.Catalog\n"
assert unit.count(a) == 1
cons = unit.replace(a, a + "import TCSlib.Complexity.TuringMachine.NDCodeSimulator\n"
                    "import TCSlib.Complexity.ClassNP.NTIME\n") + tail("consumer")
open(f"{O}/AssemblyConsumerProbe.lean", "w", encoding="utf-8").write(cons)
negs = {
    # the stream read one bit early: not the writer's word
    "neg1": ("      ((guessRunTM sanPBlock2 2 0 (sanQRead false) 0 2 3).runWith "
             "(pre ++ [true, false] ++ post)",
             "      ((guessRunTM sanPBlock2 2 0 (sanQRead false) 0 2 3).runWith "
             "(pre.take 2 ++ [true, false] ++ post ++ [false])"),
    # capture claimed absent: the captured host's output is not the noisy one
    "neg2": ("        [])).output = [true] := by\n  decide",
             "        [])).output = [true, true, true] := by\n  decide"),
    # the halting time one step early
    "neg3": ("((guessRunTM sanPStay () 0 sanQStay true true false).runWith (List.replicate 10 false)\n"
             "    ((guessRunTM sanPStay () 0 sanQStay true true false).initCfg [])).state ≠ none"
             " := by decide",
             "((guessRunTM sanPStay () 0 sanQStay true true false).runWith (List.replicate 10 false)\n"
             "    ((guessRunTM sanPStay () 0 sanQStay true true false).initCfg [])).state = none"
             " := by decide"),
    # liveness claimed after a known halt: the accepting two-cell branch at length 19
    "neg4": ("    ((guessRunTM sanPBlock2 2 0 (sanQRead false) 0 2 3).initCfg [])).state = none := by\n"
             "  decide",
             "    ((guessRunTM sanPBlock2 2 0 (sanQRead false) 0 2 3).initCfg [])).state ≠ none := by\n"
             "  decide"),
}
for n, (o, r) in negs.items():
    assert san.count(o) == 1, n
    open(f"{O}/work/{n}.lean", "w", encoding="utf-8").write(san.replace(o, r))
open(f"{O}/work/screen_ctrl.lean", "w", encoding="utf-8").write(
    "namespace Turing\nnamespace NDTM\ndef phaseHostND := 0\nend NDTM\n"
    "theorem skipBackTM_run_ofCfg : True := trivial\nend Turing\n")
print("probes written")
