"""The core specification API PR (user, 2026-10-16: "Everything" — every definition a brief's route
reads gets a published equation lemma). Every edit is asserted unique.
Usage: python3 -I mkcapi.py <worktree root>"""
import os, sys

root = sys.argv[1]
T = os.path.join(root, 'TCSlib/Complexity/TuringMachine')
NS = '{ isSimp := false }'


def edit(rel, pairs):
    p = os.path.join(T, rel)
    t = open(p).read()
    for old, new in pairs:
        n = t.count(old)
        assert n == 1, (rel, n, old[:90])
        t = t.replace(old, new)
    open(p, 'w').write(t)


def note_before_refs(text):
    return ("\n\n## References", "\n\n" + text + "\n\n## References")


# Configuration: the initial configuration's fields.
edit('Configuration.lean', [
    ("def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=\n"
     "  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩\n",
     "def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=\n"
     "  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩\n\n"
     "/-! The specification API (user, 2026-10-16): `Turing.Cfg.init`'s fields as equations\n"
     "(`Cfg.init_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`), without the\n"
     "`simp` attribute. -/\n"
     f"attribute [simps (config := {NS})] Cfg.init\n"),
    note_before_refs(
        "**The specification API** (user, 2026-10-16): `Turing.Cfg.init_state`, `_inputPos`,\n"
        "`_workTapes`, `_workTapePos` and `_output`, the initial configuration's fields as equations."),
])

# Deterministic: the visited sets, read and split (the split lemmas moved from Build/StepBlock).
VIS = '''
/-- **Membership in a visited set** (the specification API, user 2026-10-16): a cell is visited by
head `i` within `t` steps exactly when the head stands on it at some time `u ≤ t`.

**Proof sketch.** `Turing.MultiTapeTM.visitedByTapeHead` is the image of the head positions over
`Finset.range (t + 1)`. -/
theorem mem_visitedByTapeHead_iff (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) (p : ℤ) :
    p ∈ tm.visitedByTapeHead cfg t i ↔ ∃ u ≤ t, (tm.runFrom cfg u).workTapePos i = p := by
  simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]

/-- **Visited cells split at an intermediate time** (moved here from `Build/StepBlock`, design
note O9, with the specification API, user 2026-10-16): the cells visited by head `j` in
`T₁ + T₂` steps from `d` are those visited in the first `T₁` steps, together with those visited
in `T₂` steps from where the run is at time `T₁`.

**Proof sketch.** A visiting time `u ≤ T₁ + T₂` is either at most `T₁`, or `T₁ + v` with
`v ≤ T₂`, and then run additivity identifies the configuration. -/
lemma visitedByTapeHead_add_subset {m : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (d : Cfg m Bool S x) (T₁ T₂ : ℕ) (j : Fin m) :
    M.visitedByTapeHead d (T₁ + T₂) j ⊆
      M.visitedByTapeHead d T₁ j ∪ M.visitedByTapeHead (M.runFrom d T₁) T₂ j := by
  intro p hp
  simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_union, Finset.mem_image,
    Finset.mem_range] at hp ⊢
  obtain ⟨u, hu, rfl⟩ := hp
  by_cases hle : u ≤ T₁
  · exact Or.inl ⟨u, by omega, rfl⟩
  · refine Or.inr ⟨u - T₁, by omega, ?_⟩
    rw [← MultiTapeTM.runFrom_add]
    congr 2
    omega

/-- **Visited cells after the first step** (moved here from `Build/StepBlock`, with the
specification API): the cells visited in `t` steps from the successor of `c`, and `c`'s own head
cell, are among those visited in `t + 1` steps from `c`.

**Proof sketch.** Shift every visiting time by one; time `0` gives `c`'s cell. -/
lemma visitedByTapeHead_step_subset {m : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM m Bool S) (c : Cfg m Bool S x) (t : ℕ) (j : Fin m) :
    insert (c.workTapePos j) (M.visitedByTapeHead (M.step c) t j) ⊆
      M.visitedByTapeHead c (t + 1) j := by
  intro p hp
  simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_insert, Finset.mem_image,
    Finset.mem_range] at hp ⊢
  rcases hp with rfl | ⟨v, hv, rfl⟩
  · exact ⟨0, by omega, by rw [MultiTapeTM.runFrom_zero]⟩
  · exact ⟨v + 1, by omega, by rw [MultiTapeTM.runFrom_succ_eq_step]⟩

end Space'''
p = os.path.join(T, 'Deterministic.lean')
t = open(p).read()
assert t.count('\nend Space\n') == 1
t = t.replace('\nend Space\n', VIS + '\n', 1)
open(p, 'w').write(t)
edit('Deterministic.lean', [note_before_refs(
    "**The specification API** (user, 2026-10-16): `Turing.MultiTapeTM.mem_visitedByTapeHead_iff`,\n"
    "and the split lemmas `visitedByTapeHead_add_subset` and `visitedByTapeHead_step_subset` (moved\n"
    "here from `Build/StepBlock`, design note O9).")])

# Build/StepBlock: the two lemmas move out; the docstring points to their new home.
p = os.path.join(T, 'Build/StepBlock.lean')
t = open(p).read()
i = t.index("/-- **Visited cells split at an intermediate time** (additive; generic, a candidate for\n")
j = t.index("/-- **The per-round space ledger** (additive)")
block = t[i:j]
assert block.count('lemma _root_.Turing.MultiTapeTM.visitedByTapeHead_add_subset') == 1
assert block.count('lemma _root_.Turing.MultiTapeTM.visitedByTapeHead_step_subset') == 1
assert block.count('lemma ') == 2 and block.count('theorem ') == 0
t = t[:i] + t[j:]
for old, new in [
    ("* **Additive results**, gated with the move and proved here: `summaryEmit_none`,\n"
     "  `Turing.MultiTapeTM.visitedByTapeHead_add_subset`,\n"
     "  `Turing.MultiTapeTM.visitedByTapeHead_step_subset`, `roundTM_visited`, `roundTM_iterate`,\n"
     "  `roundTM_firstExit_unique`.",
     "* **Additive results**, gated with the move and proved here: `summaryEmit_none`,\n"
     "  `roundTM_visited`, `roundTM_iterate`, `roundTM_firstExit_unique`. The two generic\n"
     "  visited-set splits `Turing.MultiTapeTM.visitedByTapeHead_add_subset` and\n"
     "  `visitedByTapeHead_step_subset`, first proved here, moved to `Deterministic.lean` with the\n"
     "  specification API (user, 2026-10-16)."),
    ("`roundTM_firstExit_unique` (the round time is the unique first positive exit), and the\n"
     "  generic `Turing.MultiTapeTM.visitedByTapeHead_add_subset`, `visitedByTapeHead_step_subset`.",
     "`roundTM_firstExit_unique` (the round time is the unique first positive exit). The generic\n"
     "  `Turing.MultiTapeTM.visitedByTapeHead_add_subset` and `visitedByTapeHead_step_subset` are\n"
     "  in `Deterministic.lean`."),
]:
    assert t.count(old) == 1, old[:60]
    t = t.replace(old, new)
open(p, 'w').write(t)

# Encoding: the two encodings as equations.
edit('Encoding.lean', [
    ("def pairEncode (x α : List Bool) : List Bool :=\n  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α\n",
     "def pairEncode (x α : List Bool) : List Bool :=\n  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α\n\n"
     "/-- **The pairing as an equation** (the specification API, user 2026-10-16): the code doubled,\n"
     "the separator `false, true`, then the second word. -/\n"
     "theorem pairEncode_eq (x α : List Bool) :\n"
     "    pairEncode x α = (x.flatMap fun b => [b, b]) ++ [false, true] ++ α :=\n"
     "  rfl\n"),
    ("def unaryFin {n : ℕ} (s : Fin n) : List Bool :=\n  List.replicate (s : ℕ) true ++ [false]\n",
     "def unaryFin {n : ℕ} (s : Fin n) : List Bool :=\n  List.replicate (s : ℕ) true ++ [false]\n\n"
     "/-- **The unary state word as an equation** (the specification API, user 2026-10-16): `s`\n"
     "`true`s, then the delimiter `false`. -/\n"
     "theorem unaryFin_eq {n : ℕ} (s : Fin n) : unaryFin s = List.replicate (s : ℕ) true ++ [false] :=\n"
     "  rfl\n"),
    ("\n\n## References", "\n* `Turing.pairEncode_eq`, `Turing.unaryFin_eq` — the two encodings as equations, the\n"
     "  specification API (user, 2026-10-16).\n\n## References"),
])

# Simulation: the buffered composite's configurations.
edit('Simulation.lean', [
    ("/-- Embed a configuration on virtual input `y` while the physical input remains\n",
     "/-! The specification API (user, 2026-10-16): `Turing.FinTM.bufferedFirstCfg`'s fields as\n"
     "equations, without the `simp` attribute. -/\n"
     f"attribute [simps (config := {NS})] bufferedFirstCfg\n\n"
     "/-- Embed a configuration on virtual input `y` while the physical input remains\n"),
    ("/-- One second-phase step simulates one native step, with a valid new arrival\n",
     "/-! The specification API (user, 2026-10-16): `Turing.FinTM.bufferedSecondCfg`'s fields as\n"
     "equations, without the `simp` attribute. -/\n"
     f"attribute [simps (config := {NS})] bufferedSecondCfg\n\n"
     "/-- One second-phase step simulates one native step, with a valid new arrival\n"),
    note_before_refs(
        "**The specification API** (user, 2026-10-16): the fields of the buffered composite's two\n"
        "configuration shapes, `Turing.FinTM.bufferedFirstCfg_*` and `bufferedSecondCfg_*`, as\n"
        "equations."),
])

# Build/Embed: the silent transport's frame, and both transports' scalar fields.
edit('Build/Embed.lean', [
    ("  simp [embedSilentCfg, embedSlot_unselected ι cap hcap]\n\n\nend Turing\n",
     "  simp [embedSilentCfg, embedSlot_unselected ι cap hcap]\n\n"
     "/-- **The silent transport's frame** (the specification API, user 2026-10-16): a host tape\n"
     "outside the selection `ι`, other than the capture tape, holds the ambient frame `tapes j` with\n"
     "its head at `heads j`. The frame companion of `Turing.embedSilentCfg_cap`.\n\n"
     "**Proof sketch.** Off the selection the slot search finds no source tape\n"
     "(`embedSlot_unselected`), and `j ≠ cap` selects the frame branch. -/\n"
     "theorem embedSilentCfg_unselected (ι : Fin m ↪ Fin k) (cap : Fin k)\n"
     "    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)\n"
     "    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (j : Fin k) (hj : j ∉ Set.range ι)\n"
     "    (hcap : j ≠ cap) :\n"
     "    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes j = tapes j ∧\n"
     "      (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos j = heads j := by\n"
     "  simp [embedSilentCfg, embedSlot_unselected ι j hj, hcap]\n\n"
     "/-! The specification API (user, 2026-10-16): the two transports' state, input position and\n"
     "output as equations, without the `simp` attribute. -/\n"
     f"attribute [simps (config := {NS}) state inputPos output] embedSilentCfg embedEmitCfg\n\n\n"
     "end Turing\n"),
    ("\n\n## References", "\n* `Turing.embedSilentCfg_unselected`, `Turing.embedSilentCfg_state`, `_inputPos`, `_output`,\n"
     "  `Turing.embedEmitCfg_state`, `_inputPos`, `_output` — the transports' remaining fields, the\n"
     "  specification API (user, 2026-10-16).\n\n## References"),
])
print("ok")
