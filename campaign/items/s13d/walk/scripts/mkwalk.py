"""Write the walk unit's overlays of `Build/Catalog.lean` and `Build/Contract/Catalog.lean`.

Usage: python3 -I mkwalk.py <tools dir> <base Catalog> <base Contract/Catalog> <out Catalog>
       <out Contract/Catalog>

The §13d G4 hosts survey's one missing leaf (user 2026-10-15: public, gated first). Content-anchored
edits, each asserted to match exactly once:

  Catalog
  1. The lockstep walk block (`tools/walk-block.lean.txt`: `walkTM`, `skipTM_eq_walkTM` and the
     framed `walkTM_run_ofCfg`, proved) after `Turing.skipTM`, before its framed row; the framed
     skip `Turing.skipTM_run_ofCfg` is then its one-tape rightward instance (statement
     byte-identical; one trace for both).
  2. Part 3's module paragraph names the walk.
  Contract/Catalog
  3. `framedContract` (the first part of `tools/contract-block.lean.txt`) before the sweep
     section, and `sweepContract` defined through it (statement byte-identical).
  4. The seven contract instances (the rest of the block) before the file's last `end Turing`.
  5. The module docstring lists them.
"""
import os
import sys

tools, cat_in, con_in, cat_out, con_out = sys.argv[1:6]


def rep(t, a, b):
    c = t.count(a)
    assert c == 1, (a[:80], c)
    return t.replace(a, b)


# Catalog
t = open(cat_in, encoding="utf-8").read()
walk = open(os.path.join(tools, "walk-block.lean.txt"), encoding="utf-8").read()
SKIPDOC = "/-- **R8.3, skip, framed** (design §12.8a). If tape `i` holds the word `w`\n"
t = rep(t, SKIPDOC, walk + SKIPDOC)
# 1b. the skip's framed row is the walk's one-tape rightward instance (statement byte-identical)
a = t.index("theorem skipTM_run_ofCfg {Symbol : Type*}")
b = t.index("/-- **R8.3, skip back** (design §12.8a).", a)
skip = t[a:b]
p0 = skip.index("        else ((skipTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by\n")
p0 += len("        else ((skipTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by\n")
assert skip[p0:].startswith("  let F := fun r : ℕ => catalogSeekCfg i d .run r\n")
assert skip.rstrip().endswith("exact ⟨result.1, result.2.1, fun j t ht => result.2.2 t ht j⟩")
SKIP_BODY = """  obtain ⟨h1, h2, h3⟩ := walkTM_run_ofCfg i (· = i) rfl .pos w d hstate
    (fun p hp => by simpa using hw p (by omega) (by omega))
  rw [skipTM_eq_walkTM]
  refine ⟨h1.trans ?_, h2, fun j t ht => ?_⟩
  · apply Cfg.ext <;> try rfl
    funext j
    by_cases hj : j = i
    · subst hj
      simp
      ring
    · simp [hj]
  · rw [h3 j t ht]
    by_cases hj : j = i
    · subst hj
      simp [Finset.mem_Icc]
      omega
    · simp [hj]

"""
t = t.replace(skip, skip[:p0] + SKIP_BODY, 1)
t = rep(t, """**Proof sketch.** Induct on the cells of `w`: each nonblank cell is one
right step in `run`. The delimiter is one more right step into `done`. -/
theorem skipTM_run_ofCfg""", """**Proof sketch.** The skip is the one-tape rightward walk (`Turing.skipTM_eq_walkTM`), so this
is `Turing.walkTM_run_ofCfg` at `moved := (· = i)`, `dir := .pos`, with the moved head's exact
position read as its interval. -/
theorem skipTM_run_ofCfg""")
t = rep(t, """family over blank-separated fields (R8.3) with its field-layout vocabulary,
and the two-pass transducer scan `Turing.scanTM` (R8.2). The scan is the G2""",
        """family over blank-separated fields (R8.3) with its field-layout vocabulary, the
lockstep walk `Turing.walkTM` (R8.3b, §13d G4's ruler; `Turing.skipTM` is its one-tape
instance), and the two-pass transducer scan `Turing.scanTM` (R8.2). The scan is the G2""")
assert t.count("sorry") == open(cat_in, encoding="utf-8").read().count("sorry")
open(cat_out, "w", encoding="utf-8").write(t)
print(f"Catalog overlay: {len(t.splitlines())} lines; the walk block inserted")

# Contract/Catalog
u = open(con_in, encoding="utf-8").read()
block = open(os.path.join(tools, "contract-block.lean.txt"), encoding="utf-8").read()
cut = block.index("/-- **The lockstep walk as a contract**")
assert block.count("/-- **The lockstep walk as a contract**") == 1
head, instances = block[:cut], block[cut:]
SWEEP = "/-! ### One constructor for the framed sweep rows (§13d G2, shared with R3 clear)\n"
u = rep(u, SWEEP, head + SWEEP)
OLD_BODY = """    Contract M entry {some done} (List Γ) x where
  pre w d := ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p
  time w _ := 2 * w.length + 2
  post := post
  lo w d j := if touched j then d.workTapePos j - 1 else d.workTapePos j
  hi w d j := if touched j then d.workTapePos j + w.length else d.workTapePos j
  run w d hd hp := (hrun w d hd hp).1
  exit_mem w d _ _ := by
    show (post w d).state ∈ ({some done} : Set (Option S))
    rw [hpost]
    exact Set.mem_singleton _
  cut w d hd hp u hu h := (hrun w d hd hp).2.1 u hu (Set.mem_singleton_iff.mp h)
  env w d hd hp u hu j := by
    have h := (hrun w d hd hp).2.2 j u hu
    by_cases hj : touched j
    · simpa only [hj, if_true] using h
    · simp only [hj, if_false] at h ⊢
      rw [h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
"""
NEW_BODY = """    Contract M entry {some done} (List Γ) x :=
  framedContract M entry done x
    (fun w d => ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes src (d.workTapePos src + p) = FinTM.bufferTape w p)
    (fun w _ => 2 * w.length + 2) post touched
    (fun _ d j => d.workTapePos j - 1) (fun w d j => d.workTapePos j + w.length) hpost hrun
"""
u = rep(u, OLD_BODY, NEW_BODY)
u = rep(u, """**Proof sketch.** Each field is the matching clause of `hrun`; the exit is `hpost`; a fixed head
lies in its one-point interval. -/
def sweepContract""", """**Proof sketch.** `Turing.framedContract` at the two-pass shape: time `2|w| + 2`, the touched
heads within one cell of the word interval. -/
def sweepContract""")
last = u.rindex("\nend Turing\n")
u = u[:last + 1] + instances + u[last + 1:]
u = rep(u, """## Main definitions

* `Turing.clearTM_contract`: R3 clear as a contract.
""", """## Main definitions

* `Turing.clearTM_contract`: R3 clear as a contract.
* `Turing.framedContract`: the contract of any framed one-exit row; `Turing.sweepContract` is
  its two-pass instance.
* `Turing.walkTM_contract`, `Turing.skipTM_contract`, `Turing.skipBackTM_contract`,
  `Turing.seekEndTM_contract`, `Turing.seekStartTM_contract`, `Turing.scanTM_contract`: the
  lockstep walk, the seek family and the scan as contracts (§13d G4), with the seek family's
  endpoint `Turing.seekPost`.
""")
assert u.count("sorry") == open(con_in, encoding="utf-8").read().count("sorry")
open(con_out, "w", encoding="utf-8").write(u)
print(f"Contract/Catalog overlay: {len(u.splitlines())} lines; framedContract, sweepContract "
      f"re-pointed, seekPost, 6 instances")
