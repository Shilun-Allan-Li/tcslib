/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.List.Induction
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The coin-splitting machine

The explicit finite machine behind `Turing.FinTM.computesFunInTime_pairSplitAt`
(`TCSlib.Complexity.Randomized.Primitives`): on a pair `⟨u, b⟩` it outputs the pair
`⟨b.take |u|, b.drop |u|⟩`, on a malformed word it outputs `[]`, and it halts within
`5 (n + 1)` steps on every input of length `n`. This is the primitive by which a reduction
cuts its coin string at a unary length and uses the two segments as independent uniform
strings ([PS10, §2.1], implicit in every reduction of chapters 2–4; foundation decision D11
of `PassShelatChapter2-4Plan.md`: the two new primitives are built in the `Build/` style).

## Construction (DESIGN.md §2.4)

One work tape and six control modes (nine states), in the idiom of the private buffered extractor of
`TCSlib.Complexity.TuringMachine.Build.Primitives` (copied privately, never edited).

* **Phase 1, `parse`.** The buffered aligned parser: aligned two-bit blocks `00`/`11` of the
  doubled first component are undoubled onto the work tape without emitting anything; the
  aligned separator `01` ends the phase; the end of the input inside a block or the aligned
  block `10` halts the machine — with empty output, since nothing has been emitted yet and
  the output tape is append-only (a malformed word must produce exactly `[]`).
* **Phase 2, `rewind`.** The work head walks back to the origin.
* **Phase 3, `copy`/`dup`.** A copy scan of the second component `b`: while the work head
  reads a stored symbol of `u` and the input head reads a bit `c` of `b`, the machine emits
  `c` twice (`dup` remembers `c` for the second emission) and advances both heads; exactly
  `min |u| |b|` bits of `b` are doubled, i.e. the first component `b.take |u|` of the output
  pair (`List.take` saturates when `b` is shorter than `u`).
* **Phase 4, `sep`/`tail`.** When the stored `u` or the input is exhausted the machine
  emits the separator `01` and copies the rest of the input verbatim (empty when `b` is
  shorter than `u`), then halts at the right blank.

Every phase is accounted for by an explicit step ledger: the parser costs two steps per
block, the rewind `|u| + 1`, the copy scan two steps per doubled bit, the separator two,
the tail one per remaining bit plus one; the total is at most `5 (n + 1)`.

## Main results

* `Turing.FinTM.exists_pairSplitTM` — a finite machine computes
  `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (and `[]` on malformed words) within `5 (n + 1)`
  steps.

## Main definitions

None public (the machine and its configuration family are private; the result is an
existence statement over `Turing.FinTM Bool`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of p.p.t. machines used implicitly throughout.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, multi-tape machines and linear-time string
  manipulation.)
-/

namespace Turing.FinTM

/-- Finite control of the coin-splitting machine: `parse none` expects the first bit of an
aligned block and `parse (some b)` its second bit; `rewind` walks the work head back to the
origin; `copy` is the block start of the doubling scan and `dup c` its second emission of
the bit `c`; `sep` emits the second separator bit; `tail` copies the remaining input. -/
private inductive SplitControl where
  | parse (b : Option Bool)
  | rewind
  | copy
  | dup (c : Bool)
  | sep
  | tail

/-- Enumerate the control through a finite sum representation, privately. -/
private instance splitControlFintype : Fintype SplitControl :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance splitControlDecidableEq : DecidableEq SplitControl :=
  (proxy_equiv% SplitControl).symm.decidableEq

/-- The coin-splitting machine: one work tape holding the undoubled first component. The
parser (`parse`) buffers without emitting and validates the separator; `rewind` returns the
work head to the origin; `copy`/`dup` emit each input bit twice while the work head crosses
the stored first component; `sep` and `tail` emit the separator and the remaining input. -/
private def pairSplitTM : FinTM Bool where
  k := 1
  State := SplitControl
  tm :=
    { q₀ := .parse none
      tr := fun q inp work => match q with
        | .parse none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.parse (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .parse (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.parse none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some .rewind⟩
        | .rewind => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some .rewind⟩
          | none => ⟨0, fun _ => (none, .pos), none, some .copy⟩
        | .copy => match inp with
          | none => ⟨0, fun _ => (none, 0), some false, some .sep⟩
          | some c =>
            if (work 0).isSome then ⟨0, fun _ => (none, 0), some c, some (.dup c)⟩
            else ⟨0, fun _ => (none, 0), some false, some .sep⟩
        | .dup c => ⟨.pos, fun _ => (none, .pos), some c, some .copy⟩
        | .sep => ⟨0, fun _ => (none, 0), some true, some .tail⟩
        | .tail => match inp with
          | some c => ⟨.pos, fun _ => (none, 0), some c, some .tail⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- The one-buffer configurations of the coin-splitting machine: control `q`, input head
after `i` input bits, work tape holding the word `a` from the origin with its head at cell
`z`, output `out`. -/
private def splitCfg (x : List Bool) (q : Option SplitControl) (i : ℕ) (hi : i ≤ x.length)
    (a : List Bool) (z : ℤ) (out : List Bool) : Cfg 1 Bool SplitControl x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma splitCfg_read (x : List Bool) (q : Option SplitControl) (i : ℕ)
    (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (splitCfg x q i hi a z out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [splitCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [splitCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- Two indexed configurations with equal input indices are equal (the bound proofs are
irrelevant). -/
private lemma splitCfg_congr (x : List Bool) (q : Option SplitControl) {i i' : ℕ}
    (hi : i ≤ x.length) (hi' : i' ≤ x.length) (h : i = i') (a : List Bool) (z : ℤ)
    (out : List Bool) :
    splitCfg x q i hi a z out = splitCfg x q i' hi' a z out := by
  subst h
  rfl

/-- Doubling a word extended by one bit appends the doubled bit. -/
private lemma split_dbl_append (l : List Bool) (c : Bool) :
    dbl (l ++ [c]) = dbl l ++ [c, c] := by
  simp [dbl]

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma split_first (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    pairSplitTM.tm.step
      (splitCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) =
      splitCfg x (some (.parse (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change (pairSplitTM.tm.tr (.parse none) _ _).apply _ = _
  rw [splitCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [splitCfg, hx])
  · funext i; simp [pairSplitTM, Action.apply, splitCfg]

/-- Equal-bit blocks append one decoded bit to the buffer; `01` begins the rewind (the work
head steps back onto the last stored cell) and `10` halts silently. Neither transition emits
physical output.
**Proof sketch.** The first step is `split_first`; the second reads the block's second bit
`c` at the input index `|pre| + 1`. Case analysis on `b` and `c`: equal bits write `some b`
at the right blank of the buffer (`bufferTape_append`) and move the work head right, `01`
moves it left into `rewind`, `10` halts; in every case the input head advances. -/
private lemma split_block (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    pairSplitTM.tm.runFrom
      (splitCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then splitCfg x (some (.parse none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then splitCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else splitCfg x (some .rewind) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change pairSplitTM.tm.step (pairSplitTM.tm.step _) = _
  rw [split_first x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change (pairSplitTM.tm.tr (.parse (some b)) _ _).apply _ = _
  rw [splitCfg_read]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (bufferTape_append a _).symm)
    | (funext i; simp [pairSplitTM, Action.apply, splitCfg])

/-- Rewinding the validated buffer from cell `j - 1` takes `j + 1` transitions and leaves
the work head at the origin in the `copy` state.
**Proof sketch.** At the left blank, move right and enter `copy`. Otherwise read a buffer
cell, move left, and invoke the induction hypothesis. -/
private lemma split_rewind (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j, j ≤ a.length →
    pairSplitTM.tm.runFrom (splitCfg x (some .rewind) i hi a ((j : ℤ) - 1) []) (j + 1) =
      splitCfg x (some .copy) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [pairSplitTM, splitCfg, Cfg.workTapeSymbols, Nat.cast_zero, zero_sub,
      bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : pairSplitTM.tm.step
        (splitCfg x (some .rewind) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        splitCfg x (some .rewind) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [pairSplitTM, splitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The doubling scan: as long as both the stored word and the input have symbols left,
every two steps emit the current input bit twice and advance both heads.
**Proof sketch.** Induct on the number `j` of doubled bits. The `copy` step reads the
stored cell `a[j]` and the input bit `rest[j]`, emits the latter and remembers it in `dup`;
the `dup` step emits it again and moves both heads right. The output after `j` rounds is
`dbl (rest.take j)` (`List.take_succ`). -/
private lemma split_copy (x pre rest a : List Bool) (hx : x = pre ++ rest) :
    ∀ j (_hja : j ≤ a.length) (hjr : j ≤ rest.length),
    pairSplitTM.tm.runFrom (splitCfg x (some .copy) pre.length (by simp [hx]) a 0 []) (2 * j) =
      splitCfg x (some .copy) (pre.length + j) (by simp [hx]; omega) a j (dbl (rest.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _ _
    rw [Nat.mul_zero, MultiTapeTM.runFrom_zero]
    simp [splitCfg]
  | succ j ih =>
    intro hja hjr
    have hja' : j < a.length := by omega
    have hjr' : j < rest.length := by omega
    have hr : x[pre.length + j]? = some rest[j] := by
      simp [hx, hjr']
    have h1 : pairSplitTM.tm.step
        (splitCfg x (some .copy) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j))) =
        splitCfg x (some (.dup rest[j])) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j) ++ [rest[j]]) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr .copy _ _).apply _ = _
      rw [splitCfg_read, hr]
      simp only [pairSplitTM, splitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem hja', Option.isSome_some, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply]
    have h2 : pairSplitTM.tm.step
        (splitCfg x (some (.dup rest[j])) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j) ++ [rest[j]])) =
        splitCfg x (some .copy) (pre.length + (j + 1)) (by simp [hx]; omega) a
          ((j + 1 : ℕ) : ℤ) (dbl (rest.take (j + 1))) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr (.dup rest[j]) _ _).apply _ = _
      refine Cfg.ext rfl ?_ rfl ?_ ?_
      · show moveInputPos (⟨pre.length + j + 1, _⟩ : Fin (x.length + 2)) .pos = _
        rw [moveInputPos_pos_of_ne_right _ (by simp [hx]; omega)]
        simp only [splitCfg, Fin.ext_iff]
        omega
      · funext k; simp [pairSplitTM, Action.apply, splitCfg]
      · show dbl (rest.take j) ++ [rest[j]] ++ (some rest[j]).toList = dbl (rest.take (j + 1))
        rw [List.take_succ, List.getElem?_eq_getElem hjr', Option.toList_some, split_dbl_append]
        simp
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', ih (by omega) (by omega), h1, h2]

/-- When the stored word or the input is exhausted, the `copy` state emits the separator
`01` in two steps (`copy` emits `false` and `sep` emits `true`) without moving any head.
**Proof sketch.** First step: if the input is exhausted, `copy` reads the blank and emits
`false`; otherwise the stored word is exhausted, the work head reads the right blank
(`bufferTape_nat`, `isSome none = false`) and the same transition fires. Second step:
`sep` emits `true` unconditionally and enters `tail`. Both steps are stationary. -/
private lemma split_sep (x : List Bool) (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (m : ℕ)
    (out : List Bool) (h : a[m]? = none ∨ x[i]? = none) :
    pairSplitTM.tm.runFrom (splitCfg x (some .copy) i hi a m out) 2 =
      splitCfg x (some .tail) i hi a m (out ++ [false, true]) := by
  have h1 : pairSplitTM.tm.step (splitCfg x (some .copy) i hi a m out) =
      splitCfg x (some .sep) i hi a m (out ++ [false]) := by
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .copy _ _).apply _ = _
    rw [splitCfg_read]
    rcases h with h | h
    · cases hxi : x[i]? with
      | none =>
        refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
        funext k; simp [pairSplitTM, Action.apply, splitCfg]
      | some c =>
        simp only [pairSplitTM, splitCfg, Cfg.workTapeSymbols, bufferTape_nat, h,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
        funext k; simp [Action.apply]
    · rw [h]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [pairSplitTM, Action.apply, splitCfg]
  have h2 : pairSplitTM.tm.step (splitCfg x (some .sep) i hi a m (out ++ [false])) =
      splitCfg x (some .tail) i hi a m (out ++ [false, true]) := by
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .sep _ _).apply _ = _
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [pairSplitTM, Action.apply, splitCfg]
    · simp [pairSplitTM, Action.apply, splitCfg]
  change pairSplitTM.tm.step (pairSplitTM.tm.step _) = _
  rw [h1, h2]

/-- The final phase copies the remaining input verbatim and halts at the right blank.
**Proof sketch.** The input prefix grows by one at each emitting transition; the buffer
and its head remain fixed. The right-blank test supplies the final halting step. -/
private lemma split_tail (x rest a : List Bool) (z : ℤ) : ∀ pre out (hx : x = pre ++ rest),
    pairSplitTM.tm.runFrom (splitCfg x (some .tail) pre.length (by simp [hx]) a z out)
        (rest.length + 1) =
      splitCfg x none x.length (le_refl _) a z (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .tail _ _).apply _ = _
    rw [splitCfg_read]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [pairSplitTM, Action.apply, splitCfg, hx]
    · funext k; simp [pairSplitTM, Action.apply, splitCfg]
    · simp [pairSplitTM, Action.apply, splitCfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : pairSplitTM.tm.step
        (splitCfg x (some .tail) pre.length (by simp [hx]) a z out) =
        splitCfg x (some .tail) (pre ++ [b]).length (by simp [hx]) a z (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr .tail _ _).apply _ = _
      rw [splitCfg_read]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [splitCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [pairSplitTM, Action.apply, splitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once the separator has been validated, rewind, doubling scan, separator and tail cost
at most `2|a| + |rest| + 4` steps and emit exactly the output pair.
**Proof sketch.** Let `m = min |a| |rest|`. The rewind costs `|a| + 1`
(`split_rewind`), the doubling scan `2m` (`split_copy`), the separator `2` (`split_sep`;
at head `m` the stored word or the input is exhausted) and the tail `|rest| - m + 1`
(`split_tail` after re-indexing the input position past `rest.take m`). The output is
`dbl (rest.take m) ++ 01 ++ rest.drop m`, and `take`/`drop` at `m` agree with `take`/`drop`
at `|a|` because both saturate. -/
private lemma split_finish (x pre rest a : List Bool) (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 4,
      (pairSplitTM.tm.runFrom
        (splitCfg x (some .rewind) pre.length (by simp [hx]) a (a.length - 1) []) t).state =
          none ∧
      (pairSplitTM.tm.runFrom
        (splitCfg x (some .rewind) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          dbl (rest.take a.length) ++ [false, true] ++ rest.drop a.length := by
  obtain ⟨m, hm⟩ : ∃ m, m = min a.length rest.length := ⟨_, rfl⟩
  have hma : m ≤ a.length := hm ▸ Nat.min_le_left _ _
  have hmr : m ≤ rest.length := hm ▸ Nat.min_le_right _ _
  have hcases : m = a.length ∨ (m = rest.length ∧ rest.length ≤ a.length) := by
    rcases Nat.le_total a.length rest.length with h | h
    · exact Or.inl (hm ▸ Nat.min_eq_left h)
    · exact Or.inr ⟨hm ▸ Nat.min_eq_right h, h⟩
  have hsep : a[m]? = none ∨ x[pre.length + m]? = none := by
    rcases hcases with h | ⟨h, _⟩
    · left
      rw [h]
      exact List.getElem?_eq_none (le_refl _)
    · right
      rw [h, hx]
      exact List.getElem?_eq_none (by simp)
  have htake : rest.take m = rest.take a.length := by
    rcases hcases with h | ⟨h, hle⟩
    · rw [h]
    · rw [h, List.take_length, List.take_of_length_le hle]
  have hdrop : rest.drop m = rest.drop a.length := by
    rcases hcases with h | ⟨h, hle⟩
    · rw [h]
    · rw [h, List.drop_length, List.drop_of_length_le hle]
  have hlen : (pre ++ rest.take m).length = pre.length + m := by
    simp [List.length_take, Nat.min_eq_left hmr]
  have hx' : x = (pre ++ rest.take m) ++ rest.drop m := by
    rw [List.append_assoc, List.take_append_drop]
    exact hx
  refine ⟨(a.length + 1) + (2 * m + 2) + ((rest.drop m).length + 1), ?_, ?_⟩
  · simp only [List.length_drop]
    omega
  · rw [MultiTapeTM.runFrom_add _ (a.length + 1 + (2 * m + 2)) ((rest.drop m).length + 1),
      MultiTapeTM.runFrom_add _ (a.length + 1) (2 * m + 2),
      split_rewind x a _ _ a.length (le_refl _), MultiTapeTM.runFrom_add _ (2 * m) 2,
      split_copy x pre rest a hx m hma hmr, split_sep x _ _ a m _ hsep,
      splitCfg_congr x _ _ (by simp [hx]) hlen.symm,
      split_tail x (rest.drop m) a m (pre ++ rest.take m) _ hx']
    simp [splitCfg, htake, hdrop]

/-- The silent aligned parser either rejects or validates and runs the emission phases.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the already-decoded
buffer. A doubled bit costs two steps and enlarges the buffer by one; the linear potential
`3|rest| + 2|a| + 5` pays for both effects. Missing and forbidden separators halt silently
with empty output. At `01`, apply the finish ledger `split_finish`. -/
private lemma split_run (x rest : List Bool) : ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      (pairSplitTM.tm.runFrom
        (splitCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).state =
          none ∧
      (pairSplitTM.tm.runFrom
        (splitCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (u, b) => dbl (b.take (a.length + u.length)) ++ [false, true] ++
              b.drop (a.length + u.length)
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairSplitTM.tm.tr (.parse none) _ _).apply _).state = none ∧ _
    rw [splitCfg_read]
    simp [hx, pairSplitTM, Action.apply, splitCfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change (pairSplitTM.tm.step (pairSplitTM.tm.step _)).state = none ∧
      (pairSplitTM.tm.step (pairSplitTM.tm.step _)).output = _
    rw [split_first x pre [] a b hx]
    unfold MultiTapeTM.step
    change ((pairSplitTM.tm.tr (.parse (some b)) _ _).apply _).state = none ∧ _
    rw [splitCfg_read]
    cases b <;> simp [hx, pairSplitTM, Action.apply, splitCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ :=
        ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by
        simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, split_block x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases hd : pairDecode rest with
        | none => cases b <;> simpa [pairDecode, hd] using ho
        | some p =>
          obtain ⟨u, v⟩ := p
          have e : a.length + (u.length + 1) = a.length + 1 + u.length := by omega
          cases b <;> simpa [pairDecode, hd, e] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := split_finish x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, split_block x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [split_block x pre rest a true false hx]
        simp [splitCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The coin-splitting machine halts on every input within `5(|x| + 1)` steps with the
output pair `⟨b.take |u|, b.drop |u|⟩` (for `x = ⟨u, b⟩`) or `[]` (malformed `x`). The
initial buffer and decoded prefix are empty.
**Proof sketch.** Instantiate `split_run` with the empty prefix and the empty buffer; the
initial configuration is the indexed configuration at index `0` with blank work tape
(`Cfg.ext`). On a decoded pair the output `dbl (b.take |u|) ++ 01 ++ b.drop |u|` is
`pairEncode (b.take |u|) (b.drop |u|)` by `pairEncode_eq_dbl`; the ledger
`3|x| + 5 ≤ 5(|x| + 1)` is absorbed by `ComputesInTime.mono`. -/
private lemma split_computes (x : List Bool) :
    pairSplitTM.ComputesInTime x
      (match pairDecode x with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := split_run x x [] [] rfl
  have hinit : pairSplitTM.tm.initCfg x =
      splitCfg x (some (.parse none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [pairSplitTM, splitCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : pairSplitTM.ComputesInTime x
      (match pairDecode x with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    refine ⟨hs, ?_⟩
    cases hd : pairDecode x with
    | none => simpa [hd] using ho
    | some p =>
      obtain ⟨u, b⟩ := p
      simpa [hd, pairEncode_eq_dbl] using ho
  exact hh.mono (by simp only [List.length_nil] at ht; omega)

/-- **The coin-splitting machine exists:** a finite machine computes, on a pair `⟨u, b⟩`,
the pair `⟨b.take |u|, b.drop |u|⟩` — and `[]` on a malformed word — within `5 (n + 1)`
steps on inputs of length `n`. This is the machine behind
`Turing.FinTM.computesFunInTime_pairSplitAt` [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch.** The private machine `pairSplitTM` above (one work tape, six control
modes: buffered aligned parser, rewind, doubling scan, separator, tail) with the step
ledger `split_run`: `3 |x| + 5 ≤ 5 (|x| + 1)` steps from the initial configuration, output
`dbl (b.take |u|) ++ 01 ++ b.drop |u| = pairEncode (b.take |u|) (b.drop |u|)`
(`Turing.pairEncode_eq_dbl`). -/
theorem exists_pairSplitTM :
    ∃ M : FinTM Bool,
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
          | none => [])
        fun n => 5 * (n + 1) :=
  ⟨pairSplitTM, fun x => split_computes x⟩

end Turing.FinTM
