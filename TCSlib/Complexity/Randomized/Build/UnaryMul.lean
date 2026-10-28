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
# The unary-multiplication machine

The explicit finite machine behind `Turing.FinTM.computesFunInTime_unaryMul`
(`TCSlib.Complexity.Randomized.Primitives`): on a pair `⟨u, v⟩` it outputs `1^{|u| · |v|}`,
on a malformed word it outputs `[]`, and it halts within `5 (n + 1) ^ 2` steps on every
input of length `n`. This is the primitive by which every syntactic polynomial becomes
computable in unary (`Complexity.polyTimeComputable_unaryPoly`, foundation decision D9 of
`PassShelatChapter2-4Plan.md`), so that the lengths `1^{p(n)}` a reduction needs never go
through the repetition lemma ([PS10, §2.1], the closure properties of p.p.t. machines used
implicitly throughout chapters 2–4; foundation decision D11: the two new primitives are
built in the `Build/` style).

## Construction (DESIGN.md §2.4, with the roles of the two components exchanged)

One work tape and four control modes (six states), in the idiom of the coin-splitting
machine `TCSlib.Complexity.Randomized.Build.PairSplit` (whose parser is copied privately).

* **Phase 1, `parse`.** The buffered aligned parser: aligned two-bit blocks `00`/`11` of the
  doubled first component `u` are undoubled onto the work tape without emitting anything,
  so that after the aligned separator `01` the work tape holds a word of length `|u|`; the
  end of the input inside a block or the aligned block `10` halts the machine — with empty
  output, since nothing has been emitted yet and the output tape is append-only.
* **Phase 2, rounds `next`/`emit`/`back`.** The work head is first rewound to the origin
  (`back`). Then, for every symbol of the second component `v` — `next` consumes one input
  symbol, whose content is irrelevant — the machine walks across the stored word emitting
  one `true` per cell (`emit`) and rewinds the work head again (`back`); when the input is
  exhausted, `next` halts. Each round emits `1^{|u|}`, so after `|v|` rounds the output is
  `1^{|u| · |v|}`.

**Deviation from the sketch of DESIGN.md §2.4** (which stores `v` and replays it once per
token of `u`): storing `u` and replaying it once per symbol of `v` needs no input rewind,
because the second component is consumed left to right exactly once; the product is the
same, and the machine is smaller.

Every phase is accounted for by an explicit step ledger: the parser costs two steps per
block, the initial rewind `|u| + 1`, each round `2 |u| + 3`, the final halting step one.
The potential `n · |rest| + 3 |rest| + 2 |a| + 5` (where `n` is the input length, `rest` the
unread input and `a` the buffer) pays for the parser and for the rounds, and the total on
an input of length `n` is at most `n ^ 2 + 3 n + 5 ≤ 5 (n + 1) ^ 2`.

## Main results

* `Turing.FinTM.exists_unaryMulTM` — a finite machine computes `⟨u, v⟩ ↦ 1^{|u| · |v|}`
  (and `[]` on malformed words) within `5 (n + 1) ^ 2` steps.

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

/-- Finite control of the unary-multiplication machine: `parse none` expects the first bit
of an aligned block and `parse (some b)` its second bit; `back` walks the work head back to
the origin; `next` consumes one symbol of the second component (or halts at the end of the
input); `emit` walks across the stored word emitting one `true` per cell. -/
private inductive MulControl where
  | parse (b : Option Bool)
  | back
  | next
  | emit

/-- Enumerate the control through a finite sum representation, privately. -/
private instance mulControlFintype : Fintype MulControl :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance mulControlDecidableEq : DecidableEq MulControl :=
  (proxy_equiv% MulControl).symm.decidableEq

/-- The unary-multiplication machine: one work tape holding the undoubled first component.
The parser (`parse`) buffers without emitting and validates the separator; `back` returns
the work head to the origin; `next` consumes one input symbol or halts at the right blank;
`emit` emits one `true` per stored cell and hands over to `back` at the right blank of the
buffer. -/
private def unaryMulTM : FinTM Bool where
  k := 1
  State := MulControl
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
            else ⟨.pos, fun _ => (none, .neg), none, some .back⟩
        | .back => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some .back⟩
          | none => ⟨0, fun _ => (none, .pos), none, some .next⟩
        | .next => match inp with
          | some _ => ⟨.pos, fun _ => (none, 0), none, some .emit⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .emit => match work 0 with
          | some _ => ⟨0, fun _ => (none, .pos), some true, some .emit⟩
          | none => ⟨0, fun _ => (none, .neg), none, some .back⟩ }

/-- The one-buffer configurations of the unary-multiplication machine: control `q`, input
head after `i` input bits, work tape holding the word `a` from the origin with its head at
cell `z`, output `out`. -/
private def mulCfg (x : List Bool) (q : Option MulControl) (i : ℕ) (hi : i ≤ x.length)
    (a : List Bool) (z : ℤ) (out : List Bool) : Cfg 1 Bool MulControl x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma mulCfg_read (x : List Bool) (q : Option MulControl) (i : ℕ)
    (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (mulCfg x q i hi a z out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [mulCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [mulCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- Two indexed configurations with equal input indices are equal (the bound proofs are
irrelevant). -/
private lemma mulCfg_congr (x : List Bool) (q : Option MulControl) {i i' : ℕ}
    (hi : i ≤ x.length) (hi' : i' ≤ x.length) (h : i = i') (a : List Bool) (z : ℤ)
    (out : List Bool) :
    mulCfg x q i hi a z out = mulCfg x q i' hi' a z out := by
  subst h
  rfl

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma mul_first (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    unaryMulTM.tm.step
      (mulCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) =
      mulCfg x (some (.parse (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change (unaryMulTM.tm.tr (.parse none) _ _).apply _ = _
  rw [mulCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [mulCfg, hx])
  · funext i; simp [unaryMulTM, Action.apply, mulCfg]

/-- Equal-bit blocks append one decoded bit to the buffer; `01` begins the rewind (the work
head steps back onto the last stored cell) and `10` halts silently. Neither transition emits
physical output.
**Proof sketch.** The first step is `mul_first`; the second reads the block's second bit
`c` at the input index `|pre| + 1`. Case analysis on `b` and `c`: equal bits write `some b`
at the right blank of the buffer (`bufferTape_append`) and move the work head right, `01`
moves it left into `back`, `10` halts; in every case the input head advances. -/
private lemma mul_block (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    unaryMulTM.tm.runFrom
      (mulCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then mulCfg x (some (.parse none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then mulCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else mulCfg x (some .back) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change unaryMulTM.tm.step (unaryMulTM.tm.step _) = _
  rw [mul_first x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change (unaryMulTM.tm.tr (.parse (some b)) _ _).apply _ = _
  rw [mulCfg_read]
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
    | (funext i; simp [unaryMulTM, Action.apply, mulCfg])

/-- Rewinding the buffer from cell `j - 1` takes `j + 1` transitions and leaves the work
head at the origin in the `next` state; the output is untouched.
**Proof sketch.** At the left blank, move right and enter `next`. Otherwise read a buffer
cell, move left, and invoke the induction hypothesis. -/
private lemma mul_back (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    ∀ j, j ≤ a.length →
    unaryMulTM.tm.runFrom (mulCfg x (some .back) i hi a ((j : ℤ) - 1) out) (j + 1) =
      mulCfg x (some .next) i hi a 0 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [unaryMulTM, mulCfg, Cfg.workTapeSymbols, Nat.cast_zero, zero_sub,
      bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : unaryMulTM.tm.step
        (mulCfg x (some .back) i hi a (((j + 1 : ℕ) : ℤ) - 1) out) =
        mulCfg x (some .back) i hi a ((j : ℤ) - 1) out := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [unaryMulTM, mulCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
      · funext k; simp [Action.apply, sub_eq_add_neg]
      · simp [Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The emission walk: from cell `j` of the buffer with `k = |a| - j` cells ahead, `k + 1`
transitions emit `1^k` and leave the work head on the last stored cell in the `back` state.
**Proof sketch.** Induct on `k`. With no cell ahead, `emit` reads the right blank
(`bufferTape_nat` at `|a|`), moves left and enters `back`. Otherwise it reads the stored
cell `a[j]`, emits `true`, moves right, and the induction hypothesis applies to cell
`j + 1`; the outputs match by `List.replicate_succ`. -/
private lemma mul_emit (x : List Bool) (i : ℕ) (hi : i ≤ x.length) (a : List Bool) :
    ∀ k j (out : List Bool), j + k = a.length →
    unaryMulTM.tm.runFrom (mulCfg x (some .emit) i hi a (j : ℤ) out) (k + 1) =
      mulCfg x (some .back) i hi a ((a.length : ℤ) - 1) (out ++ List.replicate k true) := by
  intro k
  induction k with
  | zero =>
    intro j out hj
    obtain rfl : j = a.length := by omega
    have hnone : a[a.length]? = none := List.getElem?_eq_none le_rfl
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [unaryMulTM, mulCfg, Cfg.workTapeSymbols, bufferTape_nat, hnone]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply, sub_eq_add_neg]
    · simp [Action.apply]
  | succ k ih =>
    intro j out hj
    have hjl : j < a.length := by omega
    have hs : unaryMulTM.tm.step (mulCfg x (some .emit) i hi a (j : ℤ) out) =
        mulCfg x (some .emit) i hi a ((j + 1 : ℕ) : ℤ) (out ++ [true]) := by
      unfold MultiTapeTM.step
      simp only [unaryMulTM, mulCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem hjl]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
      · funext k; simp [Action.apply]
      · simp [Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (j + 1) (out ++ [true]) (by omega),
      List.append_assoc, List.singleton_append, ← List.replicate_succ]

/-- One round at an input symbol: `next` consumes the symbol, `emit` walks across the buffer
emitting `1^{|a|}`, `back` rewinds; `2 |a| + 3` steps in all.
**Proof sketch.** The `next` step reads `x[i]` and advances the input head
(`moveInputPos_pos_of_ne_right`); then `mul_emit` from the origin and `mul_back` from the
last stored cell, glued with `MultiTapeTM.runFrom_add`. -/
private lemma mul_round (x : List Bool) (i : ℕ) (hi : i < x.length) (a out : List Bool) :
    unaryMulTM.tm.runFrom (mulCfg x (some .next) i hi.le a 0 out) (2 * a.length + 3) =
      mulCfg x (some .next) (i + 1) hi a 0 (out ++ List.replicate a.length true) := by
  have h1 : unaryMulTM.tm.step (mulCfg x (some .next) i hi.le a 0 out) =
      mulCfg x (some .emit) (i + 1) hi a 0 out := by
    unfold MultiTapeTM.step
    change (unaryMulTM.tm.tr .next _ _).apply _ = _
    rw [mulCfg_read, List.getElem?_eq_getElem hi]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · exact moveInputPos_pos_of_ne_right _ (by show i + 1 ≠ x.length + 1; omega)
    · funext k; simp [unaryMulTM, Action.apply, mulCfg]
    · simp [unaryMulTM, Action.apply, mulCfg]
  have h0 : unaryMulTM.tm.runFrom (mulCfg x (some .next) i hi.le a 0 out) 1 =
      mulCfg x (some .emit) (i + 1) hi a 0 out := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, h1]
  have h2 := mul_emit x (i + 1) hi a a.length 0 out (by simp)
  rw [Nat.cast_zero] at h2
  rw [show 2 * a.length + 3 = 1 + (a.length + 1) + (a.length + 1) by ring,
    MultiTapeTM.runFrom_add _ (1 + (a.length + 1)) (a.length + 1),
    MultiTapeTM.runFrom_add _ 1 (a.length + 1), h0, h2,
    mul_back x a (i + 1) hi _ a.length le_rfl]

/-- The rounds: `j` rounds over the input suffix `rest` cost `j (2 |a| + 3)` steps and emit
`1^{|a| · j}`.
**Proof sketch.** Induct on `j`; each round is `mul_round` at the input index
`|pre| + j < |x|`, and the outputs are glued by `List.replicate_add` and `Nat.mul_add`. -/
private lemma mul_loop (x pre rest a out : List Bool) (hx : x = pre ++ rest) :
    ∀ j (_hj : j ≤ rest.length),
    unaryMulTM.tm.runFrom (mulCfg x (some .next) pre.length (by simp [hx]) a 0 out)
        (j * (2 * a.length + 3)) =
      mulCfg x (some .next) (pre.length + j) (by simp [hx]; omega) a 0
        (out ++ List.replicate (a.length * j) true) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [Nat.zero_mul, MultiTapeTM.runFrom_zero]
    simp [mulCfg]
  | succ j ih =>
    intro hj
    have hlt : pre.length + j < x.length := by simp [hx]; omega
    rw [Nat.add_mul, Nat.one_mul, MultiTapeTM.runFrom_add, ih (by omega), mul_round x _ hlt,
      Nat.mul_succ, List.replicate_add, List.append_assoc]
    exact mulCfg_congr x _ hlt _ (Nat.add_assoc pre.length j 1) a 0 _

/-- At the end of the input, `next` halts in one step without touching anything. -/
private lemma mul_halt (x a out : List Bool) :
    unaryMulTM.tm.runFrom (mulCfg x (some .next) x.length le_rfl a 0 out) 1 =
      mulCfg x none x.length le_rfl a 0 out := by
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  unfold MultiTapeTM.step
  change (unaryMulTM.tm.tr .next _ _).apply _ = _
  rw [mulCfg_read, List.getElem?_eq_none le_rfl]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext k; simp [unaryMulTM, Action.apply, mulCfg]
  · simp [unaryMulTM, Action.apply, mulCfg]

/-- Once the separator has been validated, the initial rewind, the rounds and the halting
step cost `|a| + 1 + |rest| (2 |a| + 3) + 1` steps and emit exactly `1^{|a| · |rest|}`.
**Proof sketch.** `mul_back` from the last stored cell, `mul_loop` with `j = |rest|`
(re-indexing the input position to `|x|` by `mulCfg_congr`), then `mul_halt`. -/
private lemma mul_finish (x pre rest a : List Bool) (hx : x = pre ++ rest) :
    ∃ t ≤ a.length + 1 + rest.length * (2 * a.length + 3) + 1,
      (unaryMulTM.tm.runFrom
        (mulCfg x (some .back) pre.length (by simp [hx]) a (a.length - 1) []) t).state =
          none ∧
      (unaryMulTM.tm.runFrom
        (mulCfg x (some .back) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          List.replicate (a.length * rest.length) true := by
  refine ⟨a.length + 1 + rest.length * (2 * a.length + 3) + 1, le_rfl, ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, mul_back x a _ _ [] a.length le_rfl,
    mul_loop x pre rest a [] hx rest.length le_rfl,
    mulCfg_congr x _ _ le_rfl (show pre.length + rest.length = x.length by simp [hx]),
    mul_halt]
  simp [mulCfg]

/-- The silent aligned parser either rejects or validates and runs the rounds.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the already-decoded
buffer `a` (with `2 |a| ≤ |pre|`). A doubled bit costs two steps and enlarges the buffer by
one; the potential `|x| · |rest| + 3 |rest| + 2 |a| + 5` pays for it. Missing and forbidden
separators halt silently with empty output. At `01`, apply the finish ledger `mul_finish`;
its quadratic term `|rest| · 2 |a|` is dominated by `|x| · |rest|` because `2 |a| ≤ |x|`. -/
private lemma mul_run (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest) (_hpre : 2 * a.length ≤ pre.length),
    ∃ t ≤ x.length * rest.length + 3 * rest.length + 2 * a.length + 5,
      (unaryMulTM.tm.runFrom
        (mulCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).state =
          none ∧
      (unaryMulTM.tm.runFrom
        (mulCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (u, v) => List.replicate ((a.length + u.length) * v.length) true
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx _
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((unaryMulTM.tm.tr (.parse none) _ _).apply _).state = none ∧ _
    rw [mulCfg_read]
    simp [hx, unaryMulTM, Action.apply, mulCfg, pairDecode]
  | singleton b =>
    intro pre a hx _
    refine ⟨2, by simp, ?_⟩
    change (unaryMulTM.tm.step (unaryMulTM.tm.step _)).state = none ∧
      (unaryMulTM.tm.step (unaryMulTM.tm.step _)).output = _
    rw [mul_first x pre [] a b hx]
    unfold MultiTapeTM.step
    change ((unaryMulTM.tm.tr (.parse (some b)) _ _).apply _).state = none ∧ _
    rw [mulCfg_read]
    cases b <;> simp [hx, unaryMulTM, Action.apply, mulCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx hpre
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ :=
        ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      refine ⟨2 + t, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, Nat.mul_add,
          Nat.mul_one] at ht ⊢
        omega
      rw [MultiTapeTM.runFrom_add, mul_block x pre rest a b b hx, if_pos rfl]
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
      · obtain ⟨t, ht, hs, ho⟩ := mul_finish x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, ?_, ?_⟩
        · have hx2 : 2 * a.length ≤ x.length := by simp [hx]; omega
          have hmul : rest.length * (2 * a.length) ≤ x.length * rest.length := by
            rw [Nat.mul_comm x.length]
            exact Nat.mul_le_mul_left _ hx2
          simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at ht ⊢
          omega
        rw [MultiTapeTM.runFrom_add, mul_block x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp only [List.length_cons]; omega, ?_⟩
        rw [mul_block x pre rest a true false hx]
        simp [mulCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The unary-multiplication machine halts on every input within `5 (|x| + 1) ^ 2` steps
with the output `1^{|u| · |v|}` (for `x = ⟨u, v⟩`) or `[]` (malformed `x`). The initial
buffer and decoded prefix are empty.
**Proof sketch.** Instantiate `mul_run` with the empty prefix and the empty buffer; the
initial configuration is the indexed configuration at index `0` with blank work tape
(`Cfg.ext`). The ledger `|x| ^ 2 + 3 |x| + 5 ≤ 5 (|x| + 1) ^ 2` is absorbed by
`ComputesInTime.mono`. -/
private lemma mul_computes (x : List Bool) :
    unaryMulTM.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => List.replicate (u.length * v.length) true
        | none => []) (5 * (x.length + 1) ^ 2) := by
  obtain ⟨t, ht, hs, ho⟩ := mul_run x x [] [] rfl (by simp)
  have hinit : unaryMulTM.tm.initCfg x =
      mulCfg x (some (.parse none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [unaryMulTM, mulCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : unaryMulTM.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => List.replicate (u.length * v.length) true
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    refine ⟨hs, ?_⟩
    cases hd : pairDecode x with
    | none => simpa [hd] using ho
    | some p =>
      obtain ⟨u, v⟩ := p
      simpa [hd] using ho
  refine hh.mono ?_
  have hsq : (x.length + 1) ^ 2 = x.length * x.length + 2 * x.length + 1 := by ring
  simp only [List.length_nil] at ht
  rw [hsq]
  omega

/-- **The unary-multiplication machine exists:** a finite machine computes, on a pair
`⟨u, v⟩`, the unary string `1^{|u| · |v|}` — and `[]` on a malformed word — within
`5 (n + 1) ^ 2` steps on inputs of length `n`. This is the machine behind
`Turing.FinTM.computesFunInTime_unaryMul` [PS10, §2.1, implicit; foundation decision D9].

**Proof sketch.** The private machine `unaryMulTM` above (one work tape, four control
modes: buffered aligned parser, rewind, consume-one-symbol, emission walk) with the step
ledger `mul_run`: at most `|x| ^ 2 + 3 |x| + 5 ≤ 5 (|x| + 1) ^ 2` steps from the initial
configuration, output `1^{|u| · |v|}` by induction on the tokens of `u` (parser) and on the
symbols of `v` (rounds). -/
theorem exists_unaryMulTM :
    ∃ M : FinTM Bool,
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, v) => List.replicate (u.length * v.length) true
          | none => [])
        fun n => 5 * (n + 1) ^ 2 :=
  ⟨unaryMulTM, fun x => mul_computes x⟩

end Turing.FinTM
