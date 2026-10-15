"""Cut check and landing form of the C1 assembly unit (read-only on the sources; stdlib only).

Usage: python3 -I mklanded.py <tip source tree> <unit.lean> <outdir>

Writes
  <outdir>/cut/NDHost.check.lean: the tip's `Build/NDHost.lean`, byte for byte, with the
    part's extra import (`Build.Catalog`) inserted after its last import line and the part's body
    (everything after the unit's last `-- @imports` line) appended. It imports exactly
    `NDHost`'s imports plus `Build.Catalog`, and not `NDHost`.
  <outdir>/landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean: the same, with the module
    docstring's title, design, lists and references extended for the new names (comment edits).
Every edit is asserted to match exactly once.
"""
import os
import sys

wt, unit, out = sys.argv[1], sys.argv[2], sys.argv[3]
rel = "TCSlib/Complexity/TuringMachine/Build/NDHost.lean"
base = open(os.path.join(wt, rel), encoding="utf-8").read()
u = open(unit, encoding="utf-8").read().split("\n")
land = [l for l in u if l.startswith("-- @landing ")]
assert land == ["-- @landing TCSlib.Complexity.TuringMachine.Build.NDHost"], land
imps = [w for l in u if l.startswith("-- @imports ") for w in l.split()[2:]]
assert imps == ["TCSlib.Complexity.TuringMachine.Build.NDHost",
                "TCSlib.Complexity.TuringMachine.Build.Catalog"], imps
last = max(i for i, l in enumerate(u) if l.startswith("-- @imports "))
body = "\n".join(u[last + 1:]).strip("\n") + "\n"

anchor = "import TCSlib.Complexity.TuringMachine.Nondeterministic\n"
assert base.count(anchor) == 1
cut = base.replace(anchor, anchor + "import TCSlib.Complexity.TuringMachine.Build.Catalog\n")
assert cut.endswith("end Turing\n")
cut = cut + "\n" + body

edits = [
    ("# The nondeterministic phase host and the choice writer\n",
     "# The nondeterministic phase host, the choice writer, and the guess-then-run assembly\n"),
    ("""  the diagonalizer; the controller flavor, the linear normal form's display guess.
""", """  the diagonalizer; the controller flavor, the linear normal form's display guess.
* **The guess-then-run assembly** `Turing.guessRunTM` composes the phase host over a
  deterministic setup, the bounded writer, a rewind by the catalog's `Turing.skipTM` and
  `Turing.skipBackTM`, a deterministic run ending in a live verdict, and a verdict leaf (ruling 2
  of the C1 host-contracts gate). Its contract identifies the writer's word, transfers the
  deterministic phases, and gives all-branch halting and exact-budget acceptance; with the
  interpreter core run silently (`Turing.embedSilentTM`), the core's precondition and live
  verdicts (`Turing.guessRunTM_silent_spec`).
"""),
    ("""* `Turing.NDWriterState`, `Turing.ndWriterTM` — the choice writer. [AB09, §2.1.2]
""", """* `Turing.NDWriterState`, `Turing.ndWriterTM` — the choice writer. [AB09, §2.1.2]
* `Turing.GuessRunPhase`, `Turing.guessRunPhases`, `Turing.guessRunRed`, `Turing.guessRunTM` —
  the guess-then-run host. [AB09, §2.1.2, proof of Theorem 2.6]
* `Turing.guessRunCfg`, `Turing.streamStartCfg` — the run's entry configuration after a guess,
  and the interpreter core's start configuration.
"""),
    ("""* `Turing.ndWriterTM_run_block` — the bounded flavor's contract (sorried).
""", """* `Turing.ndWriterTM_run_block` — the bounded flavor's contract (sorried).
* `Turing.guessRunTM_runWith_handoff`, `Turing.guessRunTM_runWith_live`,
  `Turing.guessRunTM_runWith`, `Turing.guessRunTM_haltsWithin`, `Turing.guessRunTM_accepts_iff` —
  the guess-then-run assembly (proved modulo `Turing.ndWriterTM_run_block`);
  `Turing.guessRunTM_runWith_setup_halt` — a halting setup (proved).
* `Turing.guessRunCfg_clean` (proved), `Turing.guessRunTM_silent_spec` (proved modulo the
  writer) — the interpreter core's interface: precondition, emission capture, live verdicts.
"""),
    ("""  Cambridge University Press, 2009. (§2.1.2: an NDTM chooses one of its two transition
  functions at every step.)
""", """  Cambridge University Press, 2009. (§2.1.2: an NDTM chooses one of its two transition
  functions at every step; the proof of Theorem 2.6: guess a string, then verify it
  deterministically; Exercise 2.6.)
"""),
]
landed = cut
for o, n in edits:
    assert landed.count(o) == 1, o
    landed = landed.replace(o, n)

os.makedirs(os.path.join(out, "cut"), exist_ok=True)
p1 = os.path.join(out, "cut", "NDHost.check.lean")
open(p1, "w", encoding="utf-8").write(cut)
p2 = os.path.join(out, "landed", rel)
os.makedirs(os.path.dirname(p2), exist_ok=True)
open(p2, "w", encoding="utf-8").write(landed)
n = lambda s: s.count("\n")
print(f"tip NDHost: {n(base)} lines; part body: {n(body)} lines; "
      f"cut file: {n(cut)} lines; landed file: {n(landed)} lines")
print("cut imports:", [l.split()[1] for l in cut.split("\n") if l.startswith("import ")])
