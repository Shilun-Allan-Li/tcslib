"""Build the U2 statement unit's landed files from the base (asserted edits; standard library).

Usage: python3 -I mklanded.py <base root> <unit dir> <out root>

Writes, under <out root>, the five landing files:
  TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean   (H2-F appended)
  TCSlib/Complexity/TuringMachine/Codes2Tape.lean            (one private lemma promoted)
  TCSlib/Complexity/TuringMachine/UniversalK.lean            (new; copied from <unit dir>)
  TCSlib/Complexity/TuringMachine/SelfUniversal.lean         (B6's two statements re-proved as
                                                              the k = 1 corollaries)
  TCSlib/Complexity/TuringMachine.lean                        (facade: import and entries)
Every old text must occur exactly once; every base file must have its expected SHA-256.
"""
import hashlib
import os
import sys

TM = "TCSlib/Complexity/TuringMachine"
BASE_SHA = {
    f"{TM}/Build/StepBlockLoop.lean": None,
    f"{TM}/Codes2Tape.lean": None,
    f"{TM}/SelfUniversal.lean": None,
    "TCSlib/Complexity/TuringMachine.lean": None,
}
EXPECTED = os.path.join(os.path.dirname(__file__), "base-sha256.txt")


def load_expected():
    exp = {}
    for line in open(EXPECTED, encoding="utf-8"):
        h, p = line.split()
        exp[p] = h
    return exp


class Edit:
    def __init__(self, text, label):
        self.s, self.label, self.n = text, label, 0

    def rep(self, old, new, what):
        c = self.s.count(old)
        assert c == 1, f"{self.label}: {what}: expected 1 occurrence, found {c}"
        self.s = self.s.replace(old, new)
        self.n += 1
        print(f"  {self.label}: {what}")


H2F = '''/-! ## The forwarding round loop (H2-F) -/

/-- **The forwarding round loop's configuration for a source configuration** (H2-F's encoding):
for a `k`-work-tape binary machine `M` with `n + 1` states and a configuration `c` of `M` on the
input `x`, the `(k + 2)`-tape configuration whose input head and mirrored tapes `0, …, k - 1`
(contents and heads) are `c`'s, whose tape `k` holds the table `tableBitsK M.tr` and tape
`k + 1` the blank summary cell followed by the unary current state (empty when `c` is halted),
both auxiliary heads at `0`, whose output is `c`'s output, and whose control is `entry` while
`c` is live and halted once `c` is. It is the step block's seam relation `Turing.StepBlock.Rep`
for `c` with its output erased (so the summary cell is blank), with the physical output
restored: the reset invariant of `Turing.exists_selfUniversal`'s sketch (the H2-S gate's
finding 4). [AB09, §1.4.1, proof of Theorem 1.9] -/
def forwardLoopCfg {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    Cfg (k + 2) Bool Q x where
  state := c.state.map fun _ => entry
  inputPos := c.inputPos
  workTapes := Fin.addCases (motive := fun _ => ℤ → Option Bool) c.workTapes fun j =>
    if j = 0 then FinTM.bufferTape (tableBitsK M.tr)
    else summaryCells none ((c.state.map unaryFin).getD [])
  workTapePos := Fin.addCases (motive := fun _ => ℤ) c.workTapePos fun _ => 0
  output := c.output

/-- **H2-F, the forwarding round loop** (host H2's unclocked loop form; `machine-library-design.md`
§14; U2 design note `audits/evidence/u2/U2-design.md` §2.2). For each work-tape count `k` there
is one finite `(k + 2)`-tape binary machine `L`, with an entry state and a constant `C`, such
that for every `k`-work-tape binary machine `M` with `n + 1` states and every input `x`, `L`
simulates `M` step by step through `forwardLoopCfg`: there is a cost function on `M`'s
configurations with
* **a macro-step lockstep** (`Turing.Lockstep`, exits `{none}` on both sides): from the encoding
  of a live configuration `c`, `L` reaches the encoding of `M.step c` after exactly `cost c`
  steps, without halting before; the encoding of a halted configuration is halted. So `L` halts
  exactly when `M` does, with `M`'s output, which it emits step by step
  (`Turing.Lockstep.runFrom`, `Turing.Lockstep.cut`);
* **a per-step bound**: `0 < cost c ≤ 50 · (|tableBitsK M.tr| + 1) + C` for live `c`, a constant
  for a fixed table (the step block's bound plus the leaf's);
* **a space ledger**: over `t` source steps that are live before `t`, each mirrored head visits
  only cells that `M`'s head visits, and the two auxiliary heads stay within
  `50 · (|tableBitsK M.tr| + 1) + C` of their home.

The control of `L` does not depend on `M`, `n` or `x`. [AB09, §1.4.1, proof of Theorem 1.9:
each step of `M` is simulated in a number of steps depending only on `M`'s table]

**Proof sketch.** `L` is the step block `roundTM k` followed, at either of its exits, by a
forwarding leaf on the summary tape: read the summary cell, emit its bit if it holds one, blank
it, then return to the block's entry (exit `entry`) or halt (exit `halt`). For a live `c`, the
block-control part of `forwardLoopCfg entry M c` represents `{c with output := []}` (`Rep`: a blank
summary, the unary state word, both auxiliary heads home), so `roundTM_effect` gives a first exit
after `T ≤ 50 · (|tableBitsK M.tr| + 1)` steps at the representation of
`a.apply {c with output := []}`, silent before, with summary cell
`summaryEmit none a.output = a.output` (`summaryEmit_none`); the exit time is unique
(`roundTM_firstExit_unique`). The leaf emits `a.output`, making the physical output
`(a.apply c).output`, blanks the cell, and enters `entry` or halts according to the exit: the
result is exactly `forwardLoopCfg entry M (M.step c)`. Take `cost c` the block's exit time plus the
leaf's length (at most `C`); the inner times are live by the block's cut and the leaf's. The space
ledger is `roundTM_visited` per round, summed by `MultiTapeTM.visitedByTapeHead_add_subset`; the
leaf moves no head. -/
theorem exists_forwardLoopTM (k : ℕ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM (k + 2) Bool Q)
      (entry : Q) (C : ℕ),
      ∀ {n : ℕ} {x : List Bool} (M : MultiTapeTM k Bool (Fin (n + 1))),
        ∃ cost : Cfg k Bool (Fin (n + 1)) x → ℕ,
          Lockstep M L (forwardLoopCfg entry M) cost {none} {none} ∧
          (∀ c, c.state ≠ none → 0 < cost c ∧
            cost c ≤ 50 * ((tableBitsK M.tr).length + 1) + C) ∧
          ∀ (c : Cfg k Bool (Fin (n + 1)) x) (t : ℕ), (∀ u < t, (M.runFrom c u).state ≠ none) →
            (∀ i : Fin k, L.visitedByTapeHead (forwardLoopCfg entry M c)
                (∑ u ∈ Finset.range t, cost (M.runFrom c u)) (Fin.castAdd 2 i) ⊆
              M.visitedByTapeHead c t i) ∧
            ∀ j : Fin (k + 2), k ≤ j.val →
              L.visitedByTapeHead (forwardLoopCfg entry M c)
                  (∑ u ∈ Finset.range t, cost (M.runFrom c u)) j ⊆
                Finset.Icc (-((50 * ((tableBitsK M.tr).length + 1) + C : ℕ) : ℤ))
                  ((50 * ((tableBitsK M.tr).length + 1) + C : ℕ) : ℤ) := by
  sorry

'''


def stepblockloop(s):
    e = Edit(s, "StepBlockLoop")
    e.rep("""`audits/h1-harvest-statements-resolutions.md`).
""", """`audits/h1-harvest-statements-resolutions.md`). **Addition for the two-tape universal (U2):**
the forwarding round loop H2-F (`Turing.StepBlock.forwardLoopCfg`,
`Turing.StepBlock.exists_forwardLoopTM`), the step block's *unclocked* loop form with the
emissions forwarded, is sorried with its proof sketch, statement gate pending
(`audits/u2-statements-pack.md`).
""", "status: the H2-F addition")
    e.rep("""* `Turing.StepBlock.hostedLoopTM` — the loop on a buffered input (formerly `h1HostedClockTM`).
""", """* `Turing.StepBlock.hostedLoopTM` — the loop on a buffered input (formerly `h1HostedClockTM`).
* `Turing.StepBlock.forwardLoopCfg` — H2-F's encoding of a source configuration.
""", "main definitions: forwardLoopCfg")
    e.rep("""* `Turing.StepBlock.hostedLoop_read` — the control, native head, output and verdict cell of a
  hosted loop configuration.
""", """* `Turing.StepBlock.hostedLoop_read` — the control, native head, output and verdict cell of a
  hosted loop configuration.
* `Turing.StepBlock.exists_forwardLoopTM` — H2-F, the forwarding round loop: a macro-step
  lockstep of any `k`-tape table with its emissions forwarded, per-step cost
  `≤ 50 · (|table| + 1) + C`, and the space ledger (sorried).
""", "main results: exists_forwardLoopTM")
    e.rep("""
end StepBlock

end Turing
""", "\n" + H2F + """end StepBlock

end Turing
""", "H2-F appended before `end StepBlock`")
    return e


def codes2tape(s):
    e = Edit(s, "Codes2Tape")
    e.rep("""/-- The frozen two-tape writer is the generic writer at two work tapes. -/
private lemma twoTape_serialize_eq (M : Code2TM) : M.serialize = serializeK M.tm := by
""", """/-- **The two-tape serialization is the generic one** [AB09, §1.4]: for every coded two-tape
machine `M`, the frozen serialization `M.serialize` is the fixed `k`-record serialization
`serializeK M.tm` at two work tapes. (Promoted from the private `twoTape_serialize_eq` for the
two-tape scheme's `k`-tape view `Turing.EffectiveMachineCode2.toK`; statement and proof
unchanged.) -/
lemma Code2TM.serialize_eq_serializeK (M : Code2TM) : M.serialize = serializeK M.tm := by
""", "promote twoTape_serialize_eq as Code2TM.serialize_eq_serializeK")
    e.rep("""    twoTape_serialize_eq codeSkipTable2_eq_codeSkipTableK
""", """    Code2TM.serialize_eq_serializeK codeSkipTable2_eq_codeSkipTableK
""", "re-point its one use")
    e.rep("""* `Turing.exists_effectiveMachineCode2`,
""", """* `Turing.Code2TM.serialize_eq_serializeK` — the frozen serialization is the generic
  `k`-record one at two work tapes.
* `Turing.exists_effectiveMachineCode2`,
""", "main results: the promoted lemma")
    return e


def selfuniversal(s):
    e = Edit(s, "SelfUniversal")
    e.rep("""import TCSlib.Complexity.TuringMachine.CodeSimulator
""", """import TCSlib.Complexity.TuringMachine.CodeSimulator
import TCSlib.Complexity.TuringMachine.UniversalK
""", "import UniversalK")
    e.rep("""**Status: statement gate passed 2026-10-14** (round 1, 0/0/5;
`audits/b6-hosts-statements-findings.md`). Both contracts are sorried with their proof
sketches.
""", """**Status: statement gate passed 2026-10-14** (round 1, 0/0/5;
`audits/b6-hosts-statements-findings.md`). Both statements are the `k = 1` cases of the
`k`-generic `Turing.exists_selfStartupTMK` and `Turing.exists_selfUniversalK`
(`TuringMachine/UniversalK.lean`, U2 statement gate pending; user decision (a), 2026-10-14), and
are proved from them here, with their statements unchanged; the construction, its sketch and its
fill are the generic ones.
""", "status")
    e.rep("""* `Turing.exists_selfStartupTM` — the startup, ending at the step block's seam (sorried).
* `Turing.exists_selfUniversal` — `U₀`, with its forward space ledger (sorried).
""", """* `Turing.exists_selfStartupTM` — the startup, ending at the step block's seam (the `k = 1`
  case of `Turing.exists_selfStartupTMK`).
* `Turing.exists_selfUniversal` — `U₀`, with its forward space ledger (the `k = 1` case of
  `Turing.exists_selfUniversalK`).
""", "main results")
    i = e.s.index("**Proof sketch.** Extract and canonize: `Turing.universalCanonTM c`")
    j = e.s.index("time bounds its cells). -/\n", i) + len("time bounds its cells). -/\n")
    e.rep(e.s[i:j], """**Proof sketch.** The case `k = 1`, `E := c.toK` of `Turing.exists_selfStartupTMK`, whose
sketch is this construction at `k` mirrored tapes (extract and canonize, install the table and
the unary state, rewind the input head). The generic tape indices `k` and `k + 1` are `1` and
`2`, and `c.toK` decodes to the same machines (`Turing.EffectiveMachineCode.toK_toFinTM`). -/
""", "exists_selfStartupTM: sketch")
    old = """        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  sorry
"""
    new = """        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  obtain ⟨K, P, hP, dP, R, exit, h⟩ := exists_selfStartupTMK 1 c.toK
  refine ⟨K, P, hP, dP, R, exit, fun α => ?_⟩
  obtain ⟨T, B, hT⟩ := h α
  refine ⟨T, B, fun w => ?_⟩
  obtain ⟨hrun, hcut, hout, hspace⟩ := hT w
  refine ⟨?_, hcut, hout, hspace⟩
  rw [hrun]
  congr 1
  funext j
  have m1 : 1 % (K + 3) = 1 := Nat.mod_eq_of_lt (by omega)
  have m2 : 2 % (K + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  have h1 : (j = 1) ↔ j.val = 1 := by
    rw [Fin.ext_iff]; simp [m1]
  have h2 : (j = 2) ↔ j.val = 2 := by
    rw [Fin.ext_iff]; simp [m2]
  by_cases a : j.val = 1
  · simp [h1.mpr a, EffectiveMachineCode.toK_machine]
  · by_cases b : j.val = 2
    · have hne : (2 : Fin (K + (1 + 2))) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp [m1, m2] at this
      simp [h2.mpr b, hne, m2, EffectiveMachineCode.toK_machine]
    · simp [a, b, h1, h2]
"""
    e.rep(old, new, "exists_selfStartupTM: the k = 1 corollary")
    i = e.s.index("**Proof sketch.** Startup, then wrapped rounds.")
    j = e.s.index("≤ C_α · (s + 1)`. -/\n", i) + len("≤ C_α · (s + 1)`. -/\n")
    e.rep(e.s[i:j], """**Proof sketch.** The case `k = 1`, `E := c.toK` of `Turing.exists_selfUniversalK`, whose
sketch is this construction at `k` mirrored tapes (the startup, then H2-F's forwarding round loop
`Turing.StepBlock.exists_forwardLoopTM`, the wrapped rounds with the reset invariant, made a public
host). Its forward clause gives the halting run within `C · (t + 1)` steps, so `t' := C · (t + 1)`,
and the space `≤ C · (spaceUsed + 1) ≤ C · (s + 1)`; its time clause and converse are dropped. -/
""", "exists_selfUniversal: sketch")
    old = """          ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
            U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1) := by
  sorry
"""
    new = """          ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
            U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1) := by
  obtain ⟨U, hU⟩ := exists_selfUniversalK 1 c.toK
  refine ⟨U, fun α => ?_⟩
  obtain ⟨C, hC, h⟩ := hU α
  refine ⟨C, hC, fun w output t s hrun hs => ⟨C * (t + 1), ((h w).1 output t hrun).1, ?_⟩⟩
  have hsp := ((h w).1 output t hrun).2
  rw [EffectiveMachineCode.toK_toFinTM] at hsp
  exact hsp.trans (Nat.mul_le_mul_left C (by omega))
"""
    e.rep(old, new, "exists_selfUniversal: the k = 1 corollary")
    return e


def facade(s):
    e = Edit(s, "TuringMachine facade")
    e.rep("""import TCSlib.Complexity.TuringMachine.SelfUniversal
""", """import TCSlib.Complexity.TuringMachine.UniversalK
import TCSlib.Complexity.TuringMachine.SelfUniversal
""", "import UniversalK")
    e.rep("""  exits. Proved; harvested from `CodeSimulator` (H1 harvest gate passed, 2026-10-14).
""", """  exits. Proved; harvested from `CodeSimulator` (H1 harvest gate passed, 2026-10-14). Also H2-F,
  the forwarding round loop (the unclocked loop form with the emissions forwarded), sorried,
  statement gate pending.
""", "contents: StepBlockLoop entry")
    e.rep("""* `SelfUniversal` — the self-application universal machine `U₀` and its startup
  [AB09, Exercise 4.1], the universal machine of the space hierarchy's window route.
  Statement gate passed 2026-10-14; both contracts are sorried.
""", """* `UniversalK` — the `k`-generic universal machine (U2) [AB09, Theorem 1.9]: the `k`-tape
  scheme interface `EffectiveCodeK` with the one- and two-tape schemes as instances, the startup,
  the self-application universal machine with time and space ledgers, and the code-first
  evaluator. Statement gate pending; the three contracts are sorried.
* `SelfUniversal` — the self-application universal machine `U₀` and its startup
  [AB09, Exercise 4.1], the universal machine of the space hierarchy's window route.
  Statement gate passed 2026-10-14; both are the `k = 1` cases of `UniversalK`'s statements.
""", "contents: UniversalK entry, SelfUniversal entry")
    return e


def main():
    base, unit, out = sys.argv[1:4]
    exp = load_expected()
    jobs = [(f"{TM}/Build/StepBlockLoop.lean", stepblockloop),
            (f"{TM}/Codes2Tape.lean", codes2tape),
            (f"{TM}/SelfUniversal.lean", selfuniversal),
            ("TCSlib/Complexity/TuringMachine.lean", facade)]
    total = 0
    for rel, fn in jobs:
        src = open(os.path.join(base, rel), encoding="utf-8").read()
        h = hashlib.sha256(src.encode("utf-8")).hexdigest()
        assert h == exp[rel], f"{rel}: base SHA-256 {h} != expected {exp[rel]}"
        e = fn(src)
        total += e.n
        dst = os.path.join(out, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, "w", encoding="utf-8").write(e.s)
    new = f"{TM}/UniversalK.lean"
    dst = os.path.join(out, new)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, "w", encoding="utf-8").write(open(os.path.join(unit, "UniversalK.lean"),
                                                encoding="utf-8").read())
    print(f"asserted edits: {total}; new file: {new}")


if __name__ == "__main__":
    main()
