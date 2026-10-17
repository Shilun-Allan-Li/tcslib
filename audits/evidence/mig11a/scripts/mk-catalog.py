"""MIG-11a, Build/Catalog: the compare's stop `compareStop` with its lemmas, and the framed compare
at that exact time; `compareTM_run_ofCfg`'s proof becomes a corollary (statement unchanged).
Every edit is asserted unique. Usage: python3 -I mk-catalog.py <worktree root>"""
import sys
root = sys.argv[1]
p = f"{root}/TCSlib/Complexity/TuringMachine/Build/Catalog.lean"
s = open(p).read()
TAG = "(MIG-11a, user 2026-10-16)"


def rep(a, b):
    global s
    n = s.count(a)
    assert n == 1, (n, a[:80])
    s = s.replace(a, b)


# 1. compareStop and its lemmas, after the private stop lemma (anchor: the next declaration).
rep("""private lemma catalog_compare_trace {Symbol : Type*} [DecidableEq Symbol] {x : List Symbol}
""", f"""/-- **The compare's stop** {TAG}: the number of leading positions at which `u` and `v`
hold the same symbol, before the first position where they differ or either word ends,
`compareStop u v = |takeWhile (fun p => p.1 = p.2) (zip u v)|`. The framed compare
(`Turing.compareTM_run_stop_ofCfg`) reads exactly this many cells forward. -/
def compareStop {{Symbol : Type*}} [DecidableEq Symbol] (u v : List Symbol) : ℕ :=
  ((u.zip v).takeWhile fun p => decide (p.1 = p.2)).length

/-- The compare's stop as an equation:
`compareStop u v = ((u.zip v).takeWhile fun p => decide (p.1 = p.2)).length` {TAG}. -/
theorem compareStop_eq {{Symbol : Type*}} [DecidableEq Symbol] (u v : List Symbol) :
    compareStop u v = ((u.zip v).takeWhile fun p => decide (p.1 = p.2)).length :=
  rfl

/-- The stop on two nonempty words: one more than the tails' stop when the heads agree, `0`
otherwise, `compareStop (a :: u) (b :: v) = if a = b then compareStop u v + 1 else 0` {TAG}. -/
theorem compareStop_cons_cons {{Symbol : Type*}} [DecidableEq Symbol] (a b : Symbol)
    (u v : List Symbol) :
    compareStop (a :: u) (b :: v) = if a = b then compareStop u v + 1 else 0 := by
  unfold compareStop
  by_cases h : a = b <;> simp [List.zip_cons_cons, h]

/-- **The stop's characterization** {TAG}: below `compareStop u v` both words hold the same
symbol, and at it they do not (they differ, or one has ended).

**Proof sketch.** Induction on `u`: an empty word stops at `0`; two heads that agree add one
to the tails' stop, and two that differ stop at `0`. -/
theorem compareStop_spec {{Symbol : Type*}} [DecidableEq Symbol] (u v : List Symbol) :
    (∀ r < compareStop u v, ∃ b, u[r]? = some b ∧ v[r]? = some b) ∧
      ¬∃ b, u[compareStop u v]? = some b ∧ v[compareStop u v]? = some b := by
  induction u generalizing v with
  | nil => simp [compareStop]
  | cons a u ih =>
    cases v with
    | nil => simp [compareStop]
    | cons b v =>
      rw [compareStop_cons_cons]
      by_cases hab : a = b
      · subst hab
        obtain ⟨h1, h2⟩ := ih v
        simp only [if_true]
        refine ⟨fun r hr => ?_, ?_⟩
        · cases r with
          | zero => exact ⟨a, rfl, rfl⟩
          | succ r => simpa using h1 r (by omega)
        · simpa using h2
      · simp only [hab, if_false]
        refine ⟨fun r hr => absurd hr (Nat.not_lt_zero _), ?_⟩
        rintro ⟨c, hc1, hc2⟩
        simp at hc1 hc2
        exact hab (hc1.trans hc2.symm)

/-- **The stop is the unique such position** {TAG}: a position below which both words hold the
same symbol and at which they do not is `compareStop u v`.

**Proof sketch.** By `Turing.compareStop_spec`, a smaller position contradicts its own second
clause, and a larger one the stop's. -/
theorem compareStop_unique {{Symbol : Type*}} [DecidableEq Symbol] {{u v : List Symbol}} {{d : ℕ}}
    (h1 : ∀ r < d, ∃ b, u[r]? = some b ∧ v[r]? = some b)
    (h2 : ¬∃ b, u[d]? = some b ∧ v[d]? = some b) : d = compareStop u v := by
  obtain ⟨c1, c2⟩ := compareStop_spec u v
  rcases Nat.lt_trichotomy d (compareStop u v) with h | h | h
  · exact absurd (c1 d h) h2
  · exact h
  · exact absurd (h1 _ h) c2

/-- The stop is at most either word's length: `compareStop u v ≤ min |u| |v|` {TAG}. -/
theorem compareStop_le {{Symbol : Type*}} [DecidableEq Symbol] (u v : List Symbol) :
    compareStop u v ≤ min u.length v.length := by
  unfold compareStop
  exact (List.takeWhile_sublist _).length_le.trans (by simp)

private lemma catalog_compare_trace {{Symbol : Type*}} [DecidableEq Symbol] {{x : List Symbol}}
""")

# 2. The exact-time framed compare, before compareTM_run_ofCfg; the latter becomes its corollary.
old_head = """theorem compareTM_run_ofCfg {Symbol : Type*} [DecidableEq Symbol] {k : ℕ} {x : List Symbol}
    (fst snd : Fin k) (hne : fst ≠ snd) (u v : List Symbol) (d : Cfg k Symbol FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
      d.workTapes fst (d.workTapePos fst + p) = FinTM.bufferTape u p)
    (hv : ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      d.workTapes snd (d.workTapePos snd + p) = FinTM.bufferTape v p) :
    ∃ δ ≤ min u.length v.length,
      (compareTM k fst snd).runFrom d (2 * δ + 2) =
          { d with state := some (FlagPhase.done (decide (u = v))) } ∧
        (∀ t < 2 * δ + 2, ∀ b,
          ((compareTM k fst snd).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
        (∀ (j : Fin k) (t : ℕ), t ≤ 2 * δ + 2 →
          if j = fst ∨ j = snd then
            ((compareTM k fst snd).runFrom d t).workTapePos j ∈
              Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (δ : ℤ))
          else ((compareTM k fst snd).runFrom d t).workTapePos j = d.workTapePos j) := by
  -- D2: the shared framed trace also covers aliased tape indices.
  have _ := hne
  obtain ⟨δ, hδ, hp, hs, he⟩ := catalog_compare_stop u v
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · rw [catalog_compare_trace"""
assert s.count(old_head) == 1
DOC_START = "/-- **R8.1, compare, framed** (design §12.8a; the generic form of"
i = s.index(DOC_START); assert s.count(DOC_START) == 1
j = s.index(old_head)
old_doc = s[i:j]
assert old_doc.endswith("`2δ + 2`. -/\n"), old_doc[-40:]
old_head = old_doc + old_head
new_head = f"""/-- **R8.1, compare, framed, at its exact time** {TAG}: as `Turing.compareTM_run_ofCfg`,
with the stop named. From the working phase, with `u` and `v` delimited at the heads of `fst`
and `snd`, the compare reaches `done (decide (u = v))` at exactly
`2 · compareStop u v + 2`, with no verdict earlier and nothing written; the two heads stay
within `[pos - 1, pos + compareStop u v]` and every other head is fixed.

**Proof sketch.** The shared framed trace at the stop of `catalog_compare_stop`, which is
`Turing.compareStop u v` by `Turing.compareStop_unique`. -/
theorem compareTM_run_stop_ofCfg {{Symbol : Type*}} [DecidableEq Symbol] {{k : ℕ}}
    {{x : List Symbol}} (fst snd : Fin k) (hne : fst ≠ snd) (u v : List Symbol)
    (d : Cfg k Symbol FlagPhase x) (hstate : d.state = some FlagPhase.run)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) →
      d.workTapes fst (d.workTapePos fst + p) = FinTM.bufferTape u p)
    (hv : ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      d.workTapes snd (d.workTapePos snd + p) = FinTM.bufferTape v p) :
    (compareTM k fst snd).runFrom d (2 * compareStop u v + 2) =
        {{ d with state := some (FlagPhase.done (decide (u = v))) }} ∧
      (∀ t < 2 * compareStop u v + 2, ∀ b,
        ((compareTM k fst snd).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * compareStop u v + 2 →
        if j = fst ∨ j = snd then
          ((compareTM k fst snd).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (compareStop u v : ℤ))
        else ((compareTM k fst snd).runFrom d t).workTapePos j = d.workTapePos j) := by
  -- D2: the shared framed trace also covers aliased tape indices.
  have _ := hne
  obtain ⟨δ, hδ, hp, hs, he⟩ := catalog_compare_stop u v
  obtain rfl : δ = compareStop u v := compareStop_unique hp hs
  refine ⟨?_, ?_, ?_⟩
  · rw [catalog_compare_trace"""
s = s.replace(old_head, new_head)
# the rest of the moved body is unchanged (it refers to δ, now compareStop u v); close it with the
# corollary.
old_tail = """    split_ifs <;> simp_all [catalogCompareF, catalogCompareR, Finset.mem_Icc] <;> omega

/-! ### R8.3 — the seek family -/
"""
new_tail = """    split_ifs <;> simp_all [catalogCompareF, catalogCompareR, Finset.mem_Icc] <;> omega

""" + old_head.split("  -- D2:")[0] + """  exact ⟨compareStop u v, compareStop_le u v,
    compareTM_run_stop_ofCfg fst snd hne u v d hstate hu hv⟩

/-! ### R8.3 — the seek family -/
"""
rep(old_tail, new_tail)
open(p, "w").write(s)
print("ok")
