/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.SAT
import TCSlib.Complexity.ClassNP.TMSAT
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.CookLevin.Snapshot
import TCSlib.Complexity.TuringMachine.Build.Seam

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Cook-Levin theorem

[AB09, Theorem 2.10, via Lemma 2.11 and Lemma 2.14]: `SAT` and `3SAT` are
`NP`-complete. This module states the hardness results — the campaign's
summit. The mathematical heart (snapshots and locality over oblivious
machines) is stated in `TCSlib.Complexity.CookLevin.Snapshot`; the formula
layer is phase 3's; what remains here is the tableau assembly and the
polynomial-time machine that *emits* it, both carried by the `SAT_NPHard`
sketch as named fill obligations.

## Design and deviations from [AB09]

* **The tableau runs on our oblivious machines** ([AB09] footnote 5 direction,
  recorded in the plan §2): `Complexity.oblivious_of_mem_DTIME` supplies a
  quadratic, unrestricted-tape-count oblivious decider for the verifier
  language, oblivious on all inputs at every time; snapshots have constant
  size (state plus `k + 1` read symbols) and there are `k` last-visit wirings
  per step instead of [AB09]'s one.
* **The certificate enters as input variables**: the verifier's input is the
  concatenation `x ++ u` with `|u|` the audited explicit formula, so [AB09]'s
  `y`-variables (p. 49, condition 1) split into `n` variables pinned to `x`
  by **unit clauses** — Example 2.12's equality rendering degenerates because
  `x` is a constant — and `Q(n)` free certificate variables. **Seeded design
  question (d) for the phase-4 audit.**
* **Acceptance is the local family "no step emits `false`"**, replacing
  [AB09]'s condition 4 (final accepting snapshot): our deciders signal
  through the append-only output tape with output exactly `[true]`/`[false]`,
  the per-step emission is a function of the snapshot
  (`Complexity.emitted`), and a *valid* trace is a genuine run of the
  decider, which emits exactly one bit within the budget — so forbidding
  `false`-emissions forces the output `[true]`, with "at least one emission"
  supplied by the decider contract rather than by clauses. **Seeded design
  question (a) for the phase-4 audit** — the family leans on
  `Turing.FinTM.DecidesInTime`'s totality within the tableau's horizon.
* **The horizon is the budget, not a common halting time**: obliviousness
  constrains positions only (design question (c), `Snapshot.lean`), so the
  tableau has one snapshot block per time up to the decider's budget, with
  halted steps fixed by the reconstruction functions' halted branches.

## Main results

* `Complexity.NPHard.polyTimeReducible` — hardness transfers forward along
  reductions ([AB09, §2.2] with Theorem 2.8's transitivity; a **new statement
  on the audited phase-1 notions**, flagged).
* `Complexity.SAT_NPHard` — [AB09, Lemma 2.11].
* `Complexity.SAT_NPComplete` — [AB09, Theorem 2.10.1].
* `Complexity.SAT3_NPHard`, `Complexity.SAT3_NPComplete` —
  [AB09, Theorem 2.10.2, via Lemma 2.14].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 2.10, p. 45; Lemma 2.11 and
  §2.3.2-2.3.4, pp. 45-49; Lemma 2.14, p. 49; Example 2.12, p. 46.)
-/

namespace Complexity

open Turing

/-- **Hardness transfers forward along reductions**: if every `NP` language
reduces to `L` and `L ≤ₚ L'`, then every `NP` language reduces to `L'`. (A
new statement on the audited phase-1 notions, flagged per standing practice.)

**Proof sketch.** For `L'' ∈ NP`, compose `L'' ≤ₚ L` (from `NPHard L`) with
`L ≤ₚ L'` by `Complexity.PolyTimeReducible.trans`. -/
theorem NPHard.polyTimeReducible {L L' : Language Bool}
    (hL : NPHard L) (h : L ≤ₚ L') : NPHard L' := by
  intro K hK
  exact (hL K hK).trans h

/-! The E4 checkpoint below isolates the exact ordered emission algebra.
Its clause-family arguments are not yet the Cook--Levin templates, and its
native-body hypotheses remain construction obligations. -/

/-- Last round index (and initial fuel), one less than the member count in
the six-family order of [AB09, Lemma 2.11], with the audited multi-tape
adaptation. -/
private def clLastRound (n k T : ℕ) : ℕ :=
  n + (k + 3) * T + k + 1

/-- The six families in the inherited order. Work-read members are ordered
by time, then tape; an empty clause group still occupies its own round. -/
private def clGroups (n k T : ℕ)
    (pin : ℕ → Std.Sat.CNF ℕ) (initial : Std.Sat.CNF ℕ)
    (state input : ℕ → Std.Sat.CNF ℕ)
    (work : ℕ → ℕ → Std.Sat.CNF ℕ) (accept : ℕ → Std.Sat.CNF ℕ) :
    List (Std.Sat.CNF ℕ) :=
  (List.range n).map pin ++ [initial] ++
    (List.range T).map state ++ (List.range (T + 1)).map input ++
    (List.range (T + 1)).flatMap (fun t => (List.range k).map (work t)) ++
    (List.range T).map accept

/-- Counting members gives `R+1`, including at zero input/tape/horizon
parameters; this counts groups, not clauses. -/
private lemma clGroups_length (n k T : ℕ)
    (pin : ℕ → Std.Sat.CNF ℕ) (initial : Std.Sat.CNF ℕ)
    (state input : ℕ → Std.Sat.CNF ℕ)
    (work : ℕ → ℕ → Std.Sat.CNF ℕ) (accept : ℕ → Std.Sat.CNF ℕ) :
    (clGroups n k T pin initial state input work accept).length =
      clLastRound n k T + 1 := by
  simp [clGroups, clLastRound, List.length_flatMap]
  ring

/-- A clause-group fragment has every clause marker and clause terminator,
but no formula terminator. -/
private def clFragment (φ : Std.Sat.CNF ℕ) : List Bool :=
  φ.flatMap (fun C => true :: Std.Sat.CNF.serializeClause C)

/-- Fragments preserve concatenation in the exact clause order. -/
private lemma clFragment_append (φ ψ : Std.Sat.CNF ℕ) :
    clFragment (φ ++ ψ) = clFragment φ ++ clFragment ψ := by
  simp [clFragment]

/-- Only the last chunk receives the single formula terminator. An empty
last group still emits `[false]`. -/
private def clChunk (R : ℕ) (G : ℕ → Std.Sat.CNF ℕ) (i : ℕ) : List Bool :=
  clFragment (G i) ++ if i = R then [false] else []

/-- Every proper prefix of the rounds emits exactly the corresponding
clause fragment, with no premature formula terminator.
**Proof sketch.** Induct on the prefix length. The new index is strictly
below the last round, so its chunk has no formula terminator. -/
private lemma clChunks_before (R : ℕ) (G : ℕ → Std.Sat.CNF ℕ)
    (j : ℕ) (hj : j ≤ R) :
    (List.range j).flatMap (clChunk R G) =
      clFragment ((List.range j).flatMap G) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hne : j ≠ R := by omega
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      clFragment_append, ih (by omega), clChunk, if_neg hne, List.append_nil]

/-- The `R+1` ordered chunks serialize the pure concatenation of groups.
This is the output-word identity, independent of any satisfiability claim. -/
private lemma clChunks_serialize (R : ℕ) (G : ℕ → Std.Sat.CNF ℕ) :
    (List.range (R + 1)).flatMap (clChunk R G) =
      Std.Sat.CNF.serialize ((List.range (R + 1)).flatMap G) := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
    clChunks_before R G R le_rfl]
  simp [clChunk, Std.Sat.CNF.serialize, clFragment, List.append_assoc]

/-- Looking up every in-range group reconstructs the ordered list; the
empty default is never used at a legal round. -/
private lemma clGroups_index (gs : List (Std.Sat.CNF ℕ)) :
    (List.range gs.length).map (fun i => gs[i]?.getD []) = gs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [List.getElem?_eq_getElem hj]

/-- The chunk identity specializes to the actual six-family list, with
exactly its computed last round and without rearranging clauses. -/
private lemma clGroups_serialize (n k T : ℕ)
    (pin : ℕ → Std.Sat.CNF ℕ) (initial : Std.Sat.CNF ℕ)
    (state input : ℕ → Std.Sat.CNF ℕ)
    (work : ℕ → ℕ → Std.Sat.CNF ℕ) (accept : ℕ → Std.Sat.CNF ℕ) :
    let gs := clGroups n k T pin initial state input work accept
    (List.range (clLastRound n k T + 1)).flatMap
        (clChunk (clLastRound n k T) (fun i => gs[i]?.getD [])) =
      Std.Sat.CNF.serialize gs.flatten := by
  dsimp only
  rw [clChunks_serialize, ← clGroups_length n k T pin initial state input work accept]
  congr 1
  rw [List.flatMap_def, clGroups_index]

/-- Snapshot bits occupy consecutive product-code blocks after all input
variables; this is the audited packing of [AB09, Lemma 2.11]. -/
private def clPack (m B t i : ℕ) : ℕ := m + t * B + i

/-- Verifier normalization enlarges only time, leaving the verifier
language and hence the exact certificate relation unchanged.
**Proof sketch.** Raise coefficient and degree to positive values, use
time constructibility and the proved oblivious conversion, and rule out a
zero simulation multiplier by the live initial state on empty input. -/
private lemma clObliviousVerifier {V : Language Bool} (hV : V ∈ P) :
    ∃ (M : FinTM Bool) (c A d : ℕ),
      0 < c ∧ 0 < A ∧ 0 < d ∧ M.Oblivious ∧
      M.DecidesInTime V (fun n => c * (A * (n + 1) ^ d + 1) ^ 2) := by
  obtain ⟨A, d, D, hD⟩ := mem_P_iff.mp hV
  have htime : V ∈ DTIME (fun n => (A + 1) * (n + 1) ^ (d + 1)) := by
    refine ⟨1, D, fun x => ?_⟩
    simp only [Nat.one_mul]
    apply (hD x).mono
    exact Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  obtain ⟨M, c, ho, hd⟩ := oblivious_of_mem_DTIME
    (timeConstructible_poly (A + 1) d (Nat.succ_pos A)) htime
  have hc : 0 < c := by
    by_contra hn
    have hz : c = 0 := by omega
    have he := hd []
    simp only [hz, Nat.zero_mul] at he
    exact M.not_computesInTime_zero _ _ he
  exact ⟨M, c, A + 1, d + 1, hc, Nat.succ_pos _, Nat.succ_pos _, ho, hd⟩

/-- If one common budget pays for startup, fuel, and each round, the
emitter library's complete bound is polynomial whenever that budget and
the last-round function are. The tableau horizon is not substituted for
the common budget. -/
private lemma clLoop_polyBound (c : ℕ) {P R : ℕ → ℕ}
    (hP : PolyBound P) (hR : PolyBound R) :
    PolyBound (fun n => c * (P n + 1) * (R n + 2)) := by
  obtain ⟨a, d, ha⟩ := hP
  obtain ⟨b, e, hb⟩ := hR
  refine ⟨c * (a + 1) * (b + 2), d + e, fun n => ?_⟩
  have hd : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have he : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hp : P n + 1 ≤ (a + 1) * (n + 1) ^ d := by
    have := ha n
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hr : R n + 2 ≤ (b + 2) * (n + 1) ^ e := by
    have := hb n
    rw [Nat.add_mul]
    omega
  calc
    _ ≤ c * ((a + 1) * (n + 1) ^ d) *
        ((b + 2) * (n + 1) ^ e) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hp) hr
    _ = _ := by rw [Nat.pow_add]; ring

/-- Fix one Claim-2.13 table before any input or index wiring is supplied.
The table depends only on the fixed Boolean predicate. -/
private noncomputable def clTemplate (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) :
    Std.Sat.CNF ℕ := Classical.choose (exists_cnf_boolFun ℓ p)

/-- The selected table has bounded arity, clause count, width, and exactly
the chosen Boolean meaning. -/
private lemma clTemplate_spec (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) :
    (clTemplate ℓ p).numVars ≤ ℓ ∧ (clTemplate ℓ p).length ≤ 2 ^ ℓ ∧
      (clTemplate ℓ p).WidthAtMost ℓ ∧
      ∀ a : ℕ → Bool, (clTemplate ℓ p).eval a = p (fun i => a i.val) := by
  exact Classical.choose_spec (exists_cnf_boolFun ℓ p)

/-- Relabeling a fixed template changes its wiring only. Repeated wire
indices are allowed; no injectivity assumption is used. -/
private lemma clTemplate_eval (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool)
    (wire : ℕ → ℕ) (a : ℕ → Bool) :
    ((clTemplate ℓ p).relabel wire).eval a = p (fun i => a (wire i.val)) := by
  rw [Std.Sat.CNF.eval_relabel, (clTemplate_spec ℓ p).2.2.2]
  rfl

/-- A fixed binary code for a finite field, with a total decoder. The
choice is made once for the fixed machine, before any reduction input. -/
private structure CLFieldCode (α : Type) where
  width : ℕ
  enc : α → Fin width → Bool
  dec : (Fin width → Bool) → α
  left_inv : Function.LeftInverse dec enc

/-- Every nonempty finite field admits such a fixed binary code. Using
its cardinality as a safe bit width avoids any logarithm convention. -/
private noncomputable def clFieldCode (α : Type) [Fintype α] [Nonempty α] :
    CLFieldCode α := by
  classical
  have hc : Fintype.card α ≤ Fintype.card (Fin (Fintype.card α) → Bool) := by
    simpa using (Nat.le_of_lt (show Fintype.card α < 2 ^ Fintype.card α from Nat.lt_two_pow_self))
  let e : α ↪ (Fin (Fintype.card α) → Bool) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  exact ⟨Fintype.card α, e, Function.invFun e, Function.leftInverse_invFun e.injective⟩

/-- A symbol uses two bits: presence and value. The unused blank/value-one
pattern is permitted as a raw block, but the global decoder totalizes it. -/
private def clSymbolCode (s : Option Bool) (i : Fin 2) : Bool :=
  if i.val = 0 then s.isSome else s.getD false

/-- The two-bit symbol decoder is total. -/
private def clSymbolDecode (b : Fin 2 → Bool) : Option Bool :=
  if b 0 then some (b 1) else none

/-- Every encoded symbol decodes exactly, including blank and false. -/
private lemma clSymbolDecode_code (s : Option Bool) :
    clSymbolDecode (clSymbolCode s) = s := by
  cases s <;> simp [clSymbolDecode, clSymbolCode]

/-- Product snapshot encoding: state bits, then two input-symbol bits,
then two bits per work tape. The fields are literal consecutive slices. -/
private def clBlockEncode (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (s : Snapshot M) : Fin (code.width + (2 + 2 * M.k)) → Bool :=
  Fin.addCases (code.enc s.1) (Fin.addCases (clSymbolCode s.2.1)
    (fun i => clSymbolCode (s.2.2 ⟨i.val / 2, by omega⟩) ⟨i.val % 2, by omega⟩))

/-- State-bit slice of a product block. -/
private def clStateSlice (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (b : Fin (code.width + (2 + 2 * M.k)) → Bool) (i : Fin code.width) : Bool :=
  b (i.castAdd (2 + 2 * M.k))

/-- Input-symbol slice of a product block. -/
private def clInputSlice (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (b : Fin (code.width + (2 + 2 * M.k)) → Bool) (i : Fin 2) : Bool :=
  b (Fin.natAdd code.width (i.castAdd (2 * M.k)))

/-- Work-symbol slice of a product block. -/
private def clWorkSlice (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (b : Fin (code.width + (2 + 2 * M.k)) → Bool) (τ : Fin M.k) (i : Fin 2) : Bool :=
  b (Fin.natAdd code.width (Fin.natAdd 2 ⟨τ.val * 2 + i.val, by omega⟩))

/-- State slices recover exactly the encoded state bits. -/
private lemma clBlock_state (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (s : Snapshot M) :
    clStateSlice M code (clBlockEncode M code s) = code.enc s.1 := by
  funext i
  simp [clStateSlice, clBlockEncode]

/-- Input slices recover exactly the encoded input-symbol bits. -/
private lemma clBlock_input (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (s : Snapshot M) :
    clInputSlice M code (clBlockEncode M code s) = clSymbolCode s.2.1 := by
  funext i
  simp [clInputSlice, clBlockEncode]

/-- Work slices recover exactly the encoded bits on every tape. -/
private lemma clBlock_work (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (s : Snapshot M) (τ : Fin M.k) :
    clWorkSlice M code (clBlockEncode M code s) τ = clSymbolCode (s.2.2 τ) := by
  funext i
  simp only [clWorkSlice, clBlockEncode, Fin.addCases_right]
  apply congrArg₂ clSymbolCode
  · apply congrArg s.2.2
    apply Fin.ext
    simp only
    omega
  · apply Fin.ext
    simp only
    omega

/-- Equality of all field bits is equality of blocks. This is the
bitwise-pinning obligation; decoded-field equality alone is insufficient.
**Proof sketch.** Split an arbitrary index into the state and symbol
segments, then the input and work segments. Quotient/remainder by two
select the unique tape and bit in the work segment. -/
private lemma clBlock_ext (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (a b : Fin (code.width + (2 + 2 * M.k)) → Bool)
    (hs : clStateSlice M code a = clStateSlice M code b)
    (hi : clInputSlice M code a = clInputSlice M code b)
    (hw : ∀ τ, clWorkSlice M code a τ = clWorkSlice M code b τ) : a = b := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    exact congrFun hs j
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      exact congrFun hi k
    · intro k
      let τ : Fin M.k := ⟨k.val / 2, by omega⟩
      let bit : Fin 2 := ⟨k.val % 2, by omega⟩
      have he : (⟨τ.val * 2 + bit.val, by omega⟩ : Fin (2 * M.k)) = k := by
        apply Fin.ext
        dsimp [τ, bit]
        omega
      have h := congrFun (hw τ) bit
      simpa only [clWorkSlice, he] using h

/-- Encoding is injective because each individual field code is. -/
private lemma clBlock_injective (M : FinTM Bool) (code : CLFieldCode (Option M.State)) :
    Function.Injective (clBlockEncode M code) := by
  intro s t h
  have hs := congrArg (clStateSlice M code) h
  have hi := congrArg (clInputSlice M code) h
  have hw (τ : Fin M.k) := congrArg (fun b => clWorkSlice M code b τ) h
  rw [clBlock_state, clBlock_state] at hs
  rw [clBlock_input, clBlock_input] at hi
  have hs' := code.left_inv.injective hs
  have hi' := (Function.LeftInverse.injective clSymbolDecode_code) hi
  have hw' : s.2.2 = t.2.2 := by
    funext τ
    have hτ := hw τ
    dsimp only at hτ
    rw [clBlock_work, clBlock_work] at hτ
    exact (Function.LeftInverse.injective clSymbolDecode_code) hτ
  exact Prod.ext hs' (Prod.ext hi' hw')

/-- Totalized whole-block decoding: every junk pattern gives the same
fixed halted/blank snapshot, rather than independently repairing fields. -/
private noncomputable def clBlockDecode (M : FinTM Bool)
    (code : CLFieldCode (Option M.State))
    (b : Fin (code.width + (2 + 2 * M.k)) → Bool) : Snapshot M :=
  if h : ∃ s, clBlockEncode M code s = b then Classical.choose h
  else ⟨none, none, fun _ => none⟩

/-- Whole-block decoding is a left inverse on genuine encodings. -/
private lemma clBlockDecode_encode (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (s : Snapshot M) :
    clBlockDecode M code (clBlockEncode M code s) = s := by
  classical
  unfold clBlockDecode
  rw [dif_pos ⟨s, rfl⟩]
  exact clBlock_injective M code (Classical.choose_spec (show
    ∃ t, clBlockEncode M code t = clBlockEncode M code s from ⟨s, rfl⟩))

/-- Constant product-code width for the fixed machine. -/
private def clWidth (M : FinTM Bool) (code : CLFieldCode (Option M.State)) : ℕ :=
  code.width + (2 + 2 * M.k)

/-- First block of a constant-arity reconstruction window. -/
private def clSourceBits (B : ℕ) (b : Fin (2 * B + 1) → Bool) (i : Fin B) : Bool :=
  b ⟨i.val, by omega⟩

/-- Second block of the same window. -/
private def clTargetBits (B : ℕ) (b : Fin (2 * B + 1) → Bool) (i : Fin B) : Bool :=
  b ⟨B + i.val, by omega⟩

/-- Final bit of the window, for a selected interior input symbol. -/
private def clWindowBit (B : ℕ) (b : Fin (2 * B + 1) → Bool) : Bool :=
  b ⟨2 * B, by omega⟩

/-- The finite set of reconstruction templates. Boundary input and absent
previous-visit variants are separate tables, fixed before the input. -/
private inductive CLTemplateKind (k : ℕ) where
  | initial (present : Bool)
  | state
  | input (present : Bool)
  | work (τ : Fin k) (previous : Bool)
  | accept

/-- The six-family reconstruction predicates of [AB09, Lemma 2.11], with
the audited product-bit pinning and no-false-emission adaptation. All
tables use the same constant arity `2B+1`; unused window bits are harmless.
These are pure predicates, not observations of an emitting machine. -/
private noncomputable def clPredicate (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (kind : CLTemplateKind M.k)
    (b : Fin (2 * clWidth M code + 1) → Bool) : Bool := by
  classical
  let B := clWidth M code
  let source := clBlockDecode M code (clSourceBits B b)
  let target := clTargetBits B b
  exact match kind with
  | .initial present => decide (target = clBlockEncode M code
      ⟨some M.tm.q₀, if present then some (clWindowBit B b) else none, fun _ => none⟩)
  | .state => decide (clStateSlice M code target = code.enc (stepState M source))
  | .input present => decide (clInputSlice M code target =
      clSymbolCode (if present then some (clWindowBit B b) else none))
  | .work τ previous => decide (clWorkSlice M code target τ =
      clSymbolCode (if previous then writtenOrKept M source τ else none))
  | .accept => decide (emitted M source ≠ some false)

/-- Window wires: source block, target block, selected input variable.
Repeated global indices are intentional and supported by relabeling. -/
private def clWire (m B source target p j : ℕ) : ℕ :=
  if j < B then clPack m B source j
  else if j < 2 * B then clPack m B target (j - B) else p

/-- One member's fixed template, with its input-dependent index wiring. -/
private noncomputable def clGroup (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (kind : CLTemplateKind M.k)
    (m source target p : ℕ) : Std.Sat.CNF ℕ :=
  (clTemplate (2 * clWidth M code + 1) (clPredicate M code kind)).relabel
    (clWire m (clWidth M code) source target p)

/-- Boundary input positions use the blank table and safe dummy index
zero. Interior positions use exactly the shifted input-variable index. -/
private noncomputable def clInputGroup (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (m t : ℕ) : Std.Sat.CNF ℕ :=
  let p := inputPosAt M m t
  if 0 < p ∧ p ≤ m then clGroup M code (.input true) m 0 t (p - 1)
  else clGroup M code (.input false) m 0 t 0

/-- A work-read member uses exactly the greatest strictly earlier visit
specified by `prevVisit`, or the blank table on a first visit. -/
private noncomputable def clWorkGroup (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (m t : ℕ) (τ : Fin M.k) : Std.Sat.CNF ℕ :=
  match prevVisit M m t τ with
  | none => clGroup M code (.work τ false) m 0 t 0
  | some s => clGroup M code (.work τ true) m s t 0

/-- The pure six-family tableau uses the exact original certificate
polynomial. Every time through `T` occurs in the input/work families. -/
private noncomputable def clTableauGroups (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e : ℕ) (x : List Bool) (T : ℕ) :
    List (Std.Sat.CNF ℕ) :=
  let m := x.length + C * (x.length + 1) ^ e
  clGroups x.length M.k T
    (fun j => [[(j, x[j]?.getD false)]])
    (clGroup M code (.initial (decide (0 < m))) m 0 0 0)
    (fun t => clGroup M code .state m t (t + 1) 0)
    (clInputGroup M code m)
    (fun t τ => if h : τ < M.k then clWorkGroup M code m t ⟨τ, h⟩ else [])
    (fun t => clGroup M code .accept m t 0 0)

/-- The pure formula is the ordered concatenation of those groups. -/
private noncomputable def clTableau (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e : ℕ) (x : List Bool) (T : ℕ) :
    Std.Sat.CNF ℕ := (clTableauGroups M code C e x T).flatten

/-- Ordered chunks of the concrete pure tableau serialize exactly that
tableau, including the empty-template and final-terminator cases. -/
private lemma clTableau_chunks (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e : ℕ) (x : List Bool) (T : ℕ) :
    (List.range (clLastRound x.length M.k T + 1)).flatMap
        (clChunk (clLastRound x.length M.k T)
          (fun i => (clTableauGroups M code C e x T)[i]?.getD [])) =
      Std.Sat.CNF.serialize (clTableau M code C e x T) := by
  apply clGroups_serialize

/-- The pure last-visit record is strictly earlier and is the greatest
earlier match, directly from its filtered-range maximum definition. -/
private lemma clPrev_spec (M : FinTM Bool) (m t s : ℕ) (τ : Fin M.k)
    (h : prevVisit M m t τ = some s) :
    s < t ∧ workPosAt M m s τ = workPosAt M m t τ ∧
      ∀ r, r < t → workPosAt M m r τ = workPosAt M m t τ → r ≤ s := by
  have hm := List.max?_eq_some_iff.mp h
  simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hm
  exact ⟨hm.1.1, hm.1.2, fun r hr he => hm.2 r ⟨hr, he⟩⟩

/-- A bounded cursor reaches each legal round and then stalls at the
one-past-last state. The invariant is closed even after the executed prefix. -/
private lemma clCursor_orbit (R : ℕ) (pack : ℕ → List Bool)
    (stepF : List Bool → List Bool)
    (hstep : ∀ i ≤ R + 1, stepF (pack i) = pack (min (i + 1) (R + 1)))
    (i : ℕ) : stepF^[i] (pack 0) = pack (min i (R + 1)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, hstep _ (Nat.min_le_right _ _)]
    congr 1
    omega

/-- A native body satisfying the audited clean seams emits precisely the
pure clause list, and its whole-library budget is polynomial.
**Proof sketch.** The persistent word is supplied by the packed-records
producer `pack x 0`; all startup work is paid by `P`. Close the invariant
at the saturated cursor, apply the proved forwarding loop, identify every
executed cursor and its last-terminated chunk, then use the exact word
identity and the polynomial product ledger. This is a conditional assembly
lemma: it does not construct the preparation producer or native body. -/
private lemma clEmitter_of_body
    (body F : FinTM Bool) (anchor : body.State)
    (pack : List Bool → ℕ → List Bool)
    (stepF emitF : List Bool → List Bool → List Bool)
    (G : List Bool → ℕ → Std.Sat.CNF ℕ) (R P : ℕ → ℕ)
    (hP : PolyBound P) (hR : PolyBound R)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) P)
    (hstep : ∀ x i, i ≤ R x.length + 1 →
      stepF x (pack x i) = pack x (min (i + 1) (R x.length + 1)))
    (hemit : ∀ x i, i ≤ R x.length + 1 →
      emitF x (pack x i) =
        if i ≤ R x.length then clChunk (R x.length) (G x) i else [])
    (hstart : ∀ x : List Bool, ∃ t ≤ P x.length,
      (∀ j < t, (body.tm.runFrom (body.tm.initCfg x) j).state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (pack x 0)))
    (hround : ∀ x i, i ≤ R x.length + 1 →
      ∃ t, 0 < t ∧ t ≤ P x.length ∧
        (∀ j, 0 < j → j < t →
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor
            (stateWord body.k (pack x i))) j).state ≠ some anchor) ∧
        body.tm.runFrom (Cfg.ofWords (input := x) anchor
            (stateWord body.k (pack x i))) t =
          { Cfg.ofWords (input := x) anchor
              (stateWord body.k (stepF x (pack x i)))
            with output := emitF x (pack x i) }) :
    PolyTimeComputable (fun x => Std.Sat.CNF.serialize
      ((List.range (R x.length + 1)).flatMap (G x))) := by
  let Inv (x s : List Bool) : Prop := ∃ i ≤ R x.length + 1, s = pack x i
  have hi0 : ∀ x, Inv x (pack x 0) := fun x => ⟨0, by omega, rfl⟩
  have his : ∀ x s, Inv x s → Inv x (stepF x s) := by
    rintro x s ⟨i, hi, rfl⟩
    exact ⟨min (i + 1) (R x.length + 1), Nat.min_le_right _ _, hstep x i hi⟩
  have hbody : ∀ x s, Inv x s →
      ∃ t, 0 < t ∧ t ≤ P x.length ∧
        (∀ j, 0 < j → j < t →
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor
            (stateWord body.k s)) j).state ≠ some anchor) ∧
        body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
          { Cfg.ofWords (input := x) anchor (stateWord body.k (stepF x s))
            with output := emitF x s } := by
    rintro x s ⟨i, hi, rfl⟩
    exact hround x i hi
  obtain ⟨E, c, hE⟩ := FinTM.exists_emitLoopTM body F anchor Inv stepF emitF
    (fun x => pack x 0) R P hF hi0 his hstart hbody
  obtain ⟨a, d, hbound⟩ := clLoop_polyBound c hP hR
  refine ⟨E, a, d, fun x => ?_⟩
  have hword : (List.range (R x.length + 1)).flatMap
      (fun i => emitF x ((stepF x)^[i] (pack x 0))) =
      Std.Sat.CNF.serialize ((List.range (R x.length + 1)).flatMap (G x)) := by
    rw [← clChunks_serialize]
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hir : i ≤ R x.length := by have := List.mem_range.mp hi; omega
    rw [clCursor_orbit _ _ _ (hstep x), Nat.min_eq_left (by omega)]
    rw [hemit x i (by omega), if_pos hir]
  have h := hE x
  dsimp only at h
  rw [hword] at h
  exact h.mono (hbound x.length)

/-! E4-A2 continuation: native preparation components. The arithmetic
header below is not yet the complete packed trajectory/last-visit record. -/

/-- Extract the original exact-length NP witness and normalize only its
verifier time, as in [AB09, Lemma 2.11]. Neither certificate parameter is
enlarged by the oblivious conversion. -/
private lemma clNPVerifier {L : Language Bool} (hL : L ∈ NP) :
    ∃ (C e : ℕ) (V : Language Bool) (M : FinTM Bool) (c A d : ℕ),
      (∀ x, x ∈ L ↔ ∃ u : List Bool,
        u.length = C * (x.length + 1) ^ e ∧ x ++ u ∈ V) ∧
      0 < c ∧ 0 < A ∧ 0 < d ∧ M.Oblivious ∧
      M.DecidesInTime V (fun n => c * (A * (n + 1) ^ d + 1) ^ 2) := by
  obtain ⟨C, e, V, hV, hcert⟩ := hL
  obtain ⟨M, c, A, d, hc, hA, hd, ho, hM⟩ := clObliviousVerifier hV
  exact ⟨C, e, V, M, c, A, d, hcert, hc, hA, hd, ho, hM⟩

/-- Linear catalog contracts in the polynomial-time normal form. This and
the next two assembly lemmas locally repeat the public-catalog construction
used in `ClassNP/TMSAT.lean`; no foreign private declaration is referenced. -/
private lemma clNative_linear (f : List Bool → List Bool)
    (h : ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime f (fun n => a * (n + 1))) : PolyTimeComputable f := by
  obtain ⟨M, a, hM⟩ := h
  exact ⟨M, a, 1, by simpa only [Nat.pow_one] using hM⟩

/-- Payload maps retain the first field, including its exact bytes. The
linear scan and the computed payload both fit the displayed polynomial. -/
private lemma clNative_map {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun z => match pairDecode z with
      | some (a, b) => pairEncode a (g b)
      | none => []) := by
  obtain ⟨G, C, e, hG⟩ := hg
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairMapSnd hG
    (by intro m n h; exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) e))
  refine ⟨M, a * (C + 1), e + 1, fun x => (hM x).mono ?_⟩
  have hlin : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ e + 1 by omega)
  have hp := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (Nat.le_succ e))
  calc
    _ ≤ a * ((x.length + 1) ^ (e + 1) + C * (x.length + 1) ^ (e + 1)) :=
      Nat.mul_le_mul_left a (Nat.add_le_add hlin hp)
    _ = _ := by ring

/-- Two separately computed fields can be paired while preserving the
original input needed by both computations.
**Proof sketch.** Use the audited retained-request construction: compute
the first field paired with an empty payload, retain the original input,
then compute the second field from the retained input. Pair concatenation
and projection remove the administrative layers. All scans and simulations
are the native public catalog machines, with their proved runtime bounds. -/
private lemma clNative_pair {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => pairEncode (f x) (g x)) := by
  have hd := clNative_linear _ FinTM.computesFunInTime_pairDup
  have hp := clNative_linear _ FinTM.computesFunInTime_pairFst
  have hs := clNative_linear _ FinTM.computesFunInTime_pairSnd
  have hc := clNative_linear _ FinTM.computesFunInTime_pairConcat
  have hz := clNative_linear _ (FinTM.computesFunInTime_const [])
  have hH := ((clNative_map hz).comp hd).comp hf
  have hS := (clNative_map hH).comp hd
  have hT := ((clNative_map (hg.comp hp)).comp hd).comp hS
  convert hs.comp (hc.comp hT) using 1
  funext x
  simp only [Function.comp_apply, pairDecode_pairEncode, Option.map_some, Option.getD_some]
  have he (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
    simp [pairEncode, List.append_assoc]
  rw [he, he]
  simp [pairDecode_pairEncode]

/-- Concatenating computed fields uses the validated native pair scanner. -/
private lemma clNative_append {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => f x ++ g x) := by
  simpa only [Function.comp_def, pairDecode_pairEncode] using
    (clNative_linear _ FinTM.computesFunInTime_pairConcat).comp (clNative_pair hf hg)

/-- The exact certificate polynomial is computed in unary, including zero
coefficient and zero degree. Its value is never replaced by a majorant. -/
private lemma clNative_unary (C e : ℕ) :
    PolyTimeComputable (fun x => List.replicate (C * (x.length + 1) ^ e) true) := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyUnary C e
  exact ⟨M, a, e + 1, hM⟩

/-- Replace each native input bit by a fixed bit, with no work tapes.
The boundary transition halts silently, so length zero is included. -/
private def clFillTM (b : Bool) : FinTM Bool where
  k := 0
  State := Unit
  tm := {
    q₀ := ()
    tr := fun _ inp _ => match inp with
      | none => ⟨0, fun i => Fin.elim0 i, none, none⟩
      | some _ => ⟨.pos, fun i => Fin.elim0 i, some b, some ()⟩ }

/-- After each scanned bit one output bit has been written. This is the
native scan invariant, including the final silent halting transition. -/
private lemma clFill_run (b : Bool) (x : List Bool) (i : ℕ) (hi : i ≤ x.length)
    (out : List Bool) :
    (clFillTM b).tm.runFrom
      (⟨some (), ⟨i + 1, by omega⟩, fun j => Fin.elim0 j,
        fun j => Fin.elim0 j, out⟩ : Cfg 0 Bool Unit x)
      (x.length - i + 1) =
      ⟨none, ⟨x.length + 1, by omega⟩, fun j => Fin.elim0 j,
        fun j => Fin.elim0 j, out ++ List.replicate (x.length - i) b⟩ := by
  induction h : x.length - i generalizing i out with
  | zero =>
    have he : i = x.length := by omega
    subst i
    simp [MultiTapeTM.runFrom, MultiTapeTM.step, clFillTM, Cfg.inputSymbol]
    constructor <;> funext j <;> exact Fin.elim0 j
  | succ r ih =>
    have hil : i < x.length := by omega
    have hs := inputSymbolInner (cfg :=
      (⟨some (), ⟨i + 1, by omega⟩, fun j => Fin.elim0 j,
        fun j => Fin.elim0 j, out⟩ : Cfg 0 Bool Unit x)) i (by simp [Nat.add_comm]) hil
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have step : (clFillTM b).tm.step
        (⟨some (), ⟨i + 1, by omega⟩, fun j => Fin.elim0 j,
          fun j => Fin.elim0 j, out⟩ : Cfg 0 Bool Unit x) =
        ⟨some (), ⟨i + 1 + 1, by omega⟩, fun j => Fin.elim0 j,
          fun j => Fin.elim0 j, out ++ [b]⟩ := by
      simp only [MultiTapeTM.step, clFillTM, hs, Action.apply]
      refine Cfg.ext rfl ?_ (by funext j; exact Fin.elim0 j)
        (by funext j; exact Fin.elim0 j) rfl
      exact moveInputPos_pos_of_ne_right _ (by simp; omega)
    rw [step]
    simpa [List.replicate_succ, List.append_assoc] using
      ih (i + 1) (by omega) (out ++ [b]) (by omega)

/-- The all-false reference input is produced by an actual native scan,
not by replacing the simulator's physical input with the instance. -/
private lemma clNative_fill (b : Bool) :
    PolyTimeComputable (fun x => List.replicate x.length b) := by
  refine ⟨clFillTM b, 1, 1, fun x => ?_⟩
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  have h := clFill_run b x 0 (by omega) []
  have hc : (clFillTM b).tm.initCfg x =
      (⟨some (), ⟨0 + 1, by omega⟩, fun j => Fin.elim0 j,
        fun j => Fin.elim0 j, []⟩ : Cfg 0 Bool Unit x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;> exact Fin.elim0 j
  simp only [Nat.sub_zero, List.nil_append] at h
  dsimp only
  rw [Nat.one_mul, Nat.pow_one, hc, h]
  exact ⟨rfl, rfl⟩

/-- Native exact preparation arithmetic for [AB09, Lemma 2.11]. The
six fields retain the instance and the exact binary certificate length,
reference length, and horizon, followed by the all-false reference input
and a unary horizon clock. This header does not include trajectory or
last-visit records and is not claimed to be the full preparation result. -/
private def clPrepHeader (C e c A d : ℕ) (x : List Bool) : List Bool :=
  let Q := C * (x.length + 1) ^ e
  let m := x.length + Q
  let T := c * (A * (m + 1) ^ d + 1) ^ 2
  pairEncode x (pairEncode (Nat.bits Q) (pairEncode (Nat.bits m)
    (pairEncode (Nat.bits T)
      (pairEncode (List.replicate m false) (List.replicate T true)))))

/-- All arithmetic-header fields are computed together in polynomial
time by native machines with sequential access.
**Proof sketch.** Generate the exact certificate unary word and append
it to the retained instance; its length is exactly the reference length.
Generate the verifier-time inner polynomial on that word, then the outer
quadratic on the result. Binary length scans yield the three exact
binary values. Pairing retains all fields; a constant-bit scan produces
the virtual reference input. The composition calculus charges the scans,
capture, rewind, and intermediate words, rather than assuming random access.
No positivity assumption is required on any arithmetic parameter. -/
private lemma clPrepHeader_native (C e c A d : ℕ) :
    PolyTimeComputable (clPrepHeader C e c A d) := by
  have hQ := clNative_unary C e
  have hm := clNative_append polyTimeComputable_id hQ
  have ht := (clNative_unary c 2).comp ((clNative_unary A d).comp hm)
  have hb := clNative_linear _ FinTM.computesFunInTime_lengthBits
  have hqbits := hb.comp hQ
  have hmbits := hb.comp hm
  have htbits := hb.comp ht
  have hfalse := (clNative_fill false).comp hm
  have h := clNative_pair polyTimeComputable_id
    (clNative_pair hqbits (clNative_pair hmbits
      (clNative_pair htbits (clNative_pair hfalse ht))))
  simpa only [Function.comp_def, List.length_append, List.length_replicate,
    id_eq, clPrepHeader] using h

/-- A source configuration embedded over a virtual input buffer, with a
disjoint administrative bank. The source output is deliberately absent;
the physical output is the separately supplied prefix. An internal `none`
source state remains a live host state. -/
private def clRefCfg (M : FinTM Bool) {l : ℕ} {S : Type}
    (emb : Option M.State → Bool → S) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (out : List Bool) :
    Cfg (l + (1 + M.k)) Bool S x where
  state := some (emb c.state b)
  inputPos := p
  workTapes := FinTM.tapeBlocks tapes (FinTM.bufferTape y) c.workTapes
  workTapePos := FinTM.tapeBlocks heads ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := out

/-- Native reference transition, with arbitrary simultaneous operations
on the disjoint administrative bank. Source writes and moves take effect
even when its next state is `none`. Only source emission and physical
termination are suppressed; subsequent halted-source rounds idle. -/
private def clRefAction (M : FinTM Bool) {l : ℕ} {S : Type}
    (emb : Option M.State → Bool → S) (q : Option M.State) (b : Bool)
    (work : Fin (l + (1 + M.k)) → Option Bool)
    (ops : Fin l → Option (Option Bool) × SignType) :
    Action (l + (1 + M.k)) Bool S :=
  match q with
  | none =>
    ⟨0, FinTM.tapeBlocks ops (none, 0) (fun _ => (none, 0)), none, some (emb none b)⟩
  | some q =>
    let v := work (Fin.natAdd l (Fin.castAdd M.k (0 : Fin 1)))
    let a := M.tm.tr q v (fun i => work (Fin.natAdd l (Fin.natAdd 1 i)))
    let m := FinTM.virtualMove b v a.inputTape
    ⟨0, FinTM.tapeBlocks ops (none, m) a.workTapes, none,
      some (emb a.state (FinTM.virtualNextTag b m))⟩

/-- Exact one-source-step correspondence, including the complete
administrative frame. The native input and physical output are unchanged.
**Proof sketch.** The public buffer-read and clamping lemmas identify the
virtual input. Split on the source state. The live case copies its work
actions literally, before internalizing its successor state; thus both
erasure and terminal writes survive. The halted case fixes all source
components while still applying administrative actions. -/
private lemma clRef_apply (M : FinTM Bool) {l : ℕ} {S : Type}
    (emb : Option M.State → Bool → S) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin l → ℤ → Option Bool)
    (heads : Fin l → ℤ) (out : List Bool)
    (ops : Fin l → Option (Option Bool) × SignType) :
    ∃ b', FinTM.VirtualTag (M.tm.step c).inputPos b' ∧
      (clRefAction M emb c.state b (clRefCfg M emb c b p tapes heads out).workTapeSymbols
        ops).apply (clRefCfg M emb c b p tapes heads out) =
      clRefCfg M emb (M.tm.step c) b' p
        (fun i => match (ops i).1 with
          | none => tapes i
          | some w => Function.update (tapes i) (heads i) w)
        (fun i => heads i + (ops i).2) out := by
  have hv : (clRefCfg M emb c b p tapes heads out).workTapeSymbols
      (Fin.natAdd l (Fin.castAdd M.k (0 : Fin 1))) = c.inputSymbol := by
    simp [clRefCfg, Cfg.workTapeSymbols, FinTM.bufferTape_inputSymbol]
  have hr : (fun i => (clRefCfg M emb c b p tapes heads out).workTapeSymbols
      (Fin.natAdd l (Fin.natAdd 1 i))) = c.workTapeSymbols := by
    funext i
    simp [clRefCfg, Cfg.workTapeSymbols]
  cases hq : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq]
      simp only [clRefAction]
      refine Cfg.ext (by simp [clRefCfg, hq]) (moveInputPos_zero _) ?_ ?_ (by simp [clRefCfg])
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; cases ho : (ops j).1 <;> simp [Action.apply, clRefCfg, ho]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply, clRefCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply, clRefCfg]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply, clRefCfg]
  | some q =>
    let a := M.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := FinTM.virtualMove b c.inputSymbol a.inputTape
    have hm := FinTM.virtualMove_correct c b hb a.inputTape
    have hc : M.tm.step c = a.apply c := by simp only [MultiTapeTM.step, hq, a]
    refine ⟨FinTM.virtualNextTag b m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · rw [hc]
      simp only [clRefAction, hv, hr]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [clRefCfg])
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; cases ho : (ops j).1 <;> simp [Action.apply, clRefCfg, ho]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply, clRefCfg, a]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply, clRefCfg]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [clRefCfg, Action.apply, FinTM.tapeBlocks_buffer] using hm.1
          · intro j; simp [Action.apply, clRefCfg, a]

/-- Increment a little-endian binary word, extending it on overflow. -/
private def clCountInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: clCountInc bs

/-- The number of initial true bits cleared by an increment. -/
private def clCountCarry : List Bool → ℕ
  | true :: bs => clCountCarry bs + 1
  | _ => 0

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma clCountInc_bits (n : ℕ) : clCountInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [clCountInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [clCountInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma clCountInc_length (bs : List Bool) :
    (clCountInc bs).length ≤ bs.length + 1 ∧
      clCountCarry bs ≤ (clCountInc bs).length := by
  induction bs with
  | nil => simp [clCountInc, clCountCarry]
  | cons b bs ih =>
    cases b <;> simp only [clCountInc, clCountCarry, List.length_cons] <;> omega

/-- Carry action; the native counter calls it with zero input movement. -/
private def clCountBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- Silent in-place binary increment. State 1 carries, state 2 rewinds,
and state 0 is an absorbing live return. Unlike the length clCount from
which the carry/rewind proof is harvested, this module never advances the
native input, emits an answer, or starts another increment at return. -/
private def clCountTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm := {
    q₀ := 1
    tr := fun q _ work =>
      if q = 1 then clCountBump 0 (work 0)
      else if q = 2 then
        match work 0 with
        | none => ⟨0, fun _ => (none, .pos), none, some 0⟩
        | some _ => ⟨0, fun _ => (none, .neg), none, some 2⟩
      else FinTM.controlAction 0 (some q) }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def clCountTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, and return invariants. -/
private def clCountCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => clCountTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma clCountTape_read (pre bs : List Bool) :
    clCountTape (pre ++ bs) pre.length = bs.head? := by
  simp only [clCountTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma clCountTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (clCountTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      clCountTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [clCountTape_read]
  · rw [Function.update_of_ne hz]
    unfold clCountTape
    by_cases hn : z < 0
    · simp only [if_pos hn]
    · simp only [if_neg hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_cons, if_neg (by omega), List.getElem?_tail]
        congr 1
        omega

/-- One carry transition updates exactly the currently scanned cell. -/
private lemma clCount_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    clCountTM.tm.step (clCountCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        clCountCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else clCountCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (clCountTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [clCountTM, ↓reduceIte]
  change (clCountBump .zero (clCountTape (pre ++ bs) pre.length)).apply _ = _
  rw [clCountTape_read]
  unfold clCountBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact clCountTape_write pre bs _
    · funext j; simp [Action.apply, clCountCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma clCount_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    clCountTM.tm.runFrom (clCountCfg x 1 p pre.length (pre ++ bs) [])
        (clCountCarry bs + 1) =
      clCountCfg x 2 p ((pre.length : ℤ) + clCountCarry bs - 1)
        (pre ++ clCountInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [clCountCarry, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, clCount_carry_step]
    simp [clCountInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [clCountCarry, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, clCount_carry_step]
      simp [clCountInc]
    | true =>
      simp only [clCountCarry, MultiTapeTM.runFrom_succ_eq_step, clCount_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [clCountInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the absorbing return state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma clCount_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    clCountTM.tm.runFrom (clCountCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      clCountCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clCountTM, clCountCfg, Cfg.workTapeSymbols,
        clCountTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (clCountCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [clCountCfg, Cfg.workTapeSymbols, clCountTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : clCountTM.tm.step (clCountCfg x 2 p (j : ℤ) bs []) =
        clCountCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (clCountTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [clCountTM, show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, clCountCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The carry scans at most the original binary word. -/
private lemma clCountCarry_le (w : List Bool) : clCountCarry w ≤ w.length := by
  induction w with
  | nil => simp [clCountCarry]
  | cons b w ih => cases b <;> simp [clCountCarry, ih]

/-- Complete in-place increment, with exact carry-dependent duration.
The native input head remains at the arbitrary supplied position. -/
private lemma clCount_run (x : List Bool) (p : Fin (x.length + 2)) (w : List Bool) :
    clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) (2 * clCountCarry w + 2) =
      clCountCfg x 0 p 0 (clCountInc w) [] := by
  have hc := clCount_carry x p w []
  simp only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] at hc
  rw [show 2 * clCountCarry w + 2 = (clCountCarry w + 1) + (clCountCarry w + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact clCount_rewind x p (clCountInc w) (clCountCarry w) (clCountInc_length w).2

/-- Once returned, the counter module does no further work. This allows
an arbitrary upper bound to be cut to the actual first return. -/
private lemma clCount_idle {x : List Bool} (c : Cfg 1 Bool (Fin 4) x)
    (hc : c.state = some 0) : clCountTM.tm.step c = c := by
  simp only [MultiTapeTM.step, hc, clCountTM,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, if_false]
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- The returned whole configuration is fixed, not just its control. -/
private lemma clCount_idle_run {x : List Bool} (c : Cfg 1 Bool (Fin 4) x)
    (hc : c.state = some 0) (t : ℕ) : clCountTM.tm.runFrom c t = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step, clCount_idle c hc, ih]

/-- The harvested tape representation is the library's canonical buffer,
including every negative cell and both empty-word boundaries. -/
private lemma clCountTape_eq (w : List Bool) : clCountTape w = FinTM.bufferTape w := by
  funext z
  by_cases hz : z < 0 <;> simp [clCountTape, FinTM.bufferTape, hz, show 0 ≤ z ↔ ¬z < 0 by omega]

/-- A counter below `2^w` occupies at most `w` bits. Together with the
counter runtime bound, this charges one administrative increment by two
binary scans plus two transitions, with no unary-position representation. -/
private lemma clCount_width (n w : ℕ) (hn : n < 2 ^ w) : n.bits.length ≤ w := by
  induction n using Nat.binaryRec' generalizing w with
  | zero => simp
  | bit b n hb ih =>
    cases w with
    | zero =>
      have hz : Nat.bit b n = 0 := by simpa using hn
      cases b <;> simp [Nat.bit_val] at hz
      have h := hb (by omega)
      contradiction
    | succ w =>
      rw [Nat.bits_append_bit n b hb, List.length_cons]
      apply Nat.succ_le_succ
      apply ih
      cases b <;> simp [Nat.bit_val, Nat.pow_succ] at hn <;> omega

/-- One simultaneous counter action. A stopped component is stationary.
The product construction is locally adapted from the audited
`emitterBank*` construction in `Build/Primitives.lean`; the component here
is the inherited binary increment, with one tape rather than a triple. -/
private def clBankPart {l : ℕ} (q : Fin l → Option (Fin 4))
    (work : Fin l → Option Bool) (i : Fin l) : Action 1 Bool (Fin 4) :=
  match q i with
  | none => FinTM.controlAction 0 none
  | some s => clCountTM.tm.tr s none (fun _ => work i)

/-- Simultaneous in-place increments on disjoint binary-counter tapes.
The finite control contains the vector of component controls; a returned
component remains idle while another is carrying or rewinding. -/
private def clBankTM (l : ℕ) : FinTM Bool where
  k := l
  State := Fin l → Option (Fin 4)
  tm := {
    q₀ := fun _ => some 1
    tr := fun q _ work =>
      let a := clBankPart q work
      ⟨0, fun i => (a i).workTapes 0, none, some (fun i => (a i).state)⟩ }

/-- The full product configuration retains the physical input position.
Component outputs are not forwarded: every increment is silent. -/
private def clBankCfg {l : ℕ} {x : List Bool} (p : Fin (x.length + 2))
    (c : Fin l → Cfg 1 Bool (Fin 4) x) :
    Cfg (clBankTM l).k Bool (clBankTM l).State x :=
  ⟨some (fun i => (c i).state), p, fun i => (c i).workTapes 0,
    fun i => (c i).workTapePos 0, []⟩

/-- Projecting the bank action recovers the exact one-tape action. -/
private lemma clBank_part {l : ℕ} {x : List Bool} (p : Fin (x.length + 2))
    (c : Fin l → Cfg 1 Bool (Fin 4) x) (i : Fin l) :
    clBankPart (fun i => (c i).state) (clBankCfg p c).workTapeSymbols i =
      match (c i).state with
      | none => FinTM.controlAction 0 none
      | some q => clCountTM.tm.tr q (c i).inputSymbol (c i).workTapeSymbols := by
  have hw : (fun _ : Fin 1 => (clBankCfg p c).workTapeSymbols i) =
      (c i).workTapeSymbols := by
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl
  unfold clBankPart
  dsimp only
  cases (c i).state <;> simp only [hw] <;> rfl

/-- One product step applies each native counter step, preserving the
whole tape contents and independently positioned heads.
**Proof sketch.** Project the full transition to each tape and component state. A halted component is fixed; a live component uses its own counter action. The physical input stays fixed and every component output is suppressed. -/
private lemma clBank_step {l : ℕ} {x : List Bool} (p : Fin (x.length + 2))
    (c : Fin l → Cfg 1 Bool (Fin 4) x) :
    (clBankTM l).tm.step (clBankCfg p c) =
      clBankCfg p (fun i => clCountTM.tm.step (c i)) := by
  have ha : clBankPart (fun i => (c i).state) (clBankCfg p c).workTapeSymbols =
      fun i => match (c i).state with
        | none => FinTM.controlAction 0 none
        | some q => clCountTM.tm.tr q (c i).inputSymbol (c i).workTapeSymbols := by
    funext i
    exact clBank_part p c i
  unfold MultiTapeTM.step
  change ((clBankTM l).tm.tr (fun i => (c i).state) _ _).apply _ = _
  dsimp only [clBankTM]
  rw [ha]
  refine Cfg.ext ?_ (moveInputPos_zero _) ?_ ?_ rfl
  · dsimp only [Action.apply, clBankCfg]
    congr 1
    funext i
    cases hs : (c i).state <;>
      simp [MultiTapeTM.step, hs, FinTM.controlAction, Action.apply]
  · funext i
    cases hs : (c i).state <;>
      simp [clBankCfg, MultiTapeTM.step, hs, FinTM.controlAction, Action.apply]
  · funext i
    cases hs : (c i).state <;>
      simp [clBankCfg, MultiTapeTM.step, hs, FinTM.controlAction, Action.apply]

/-- All counter trajectories are exact projections of one native bank run. -/
private lemma clBank_run {l : ℕ} {x : List Bool} (p : Fin (x.length + 2))
    (c : Fin l → Cfg 1 Bool (Fin 4) x) (t : ℕ) :
    (clBankTM l).tm.runFrom (clBankCfg p c) t =
      clBankCfg p (fun i => clCountTM.tm.runFrom (c i) t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [MultiTapeTM.runFrom_succ_eq_step', ih, clBank_step]

/-- A selected counter starts in carry control; an unselected one starts
in its absorbing return control. -/
private def clBankStart (a : Bool) : Fin 4 := if a then 1 else 0

/-- Every selected canonical counter increments once within the same
width bound. An unselected counter does no work, including on empty input.
**Proof sketch.** Consume the inherited exact increment ledger and extend
its result to the common deadline by its absorbing-return theorem. -/
private lemma clBank_component (x : List Bool) (p : Fin (x.length + 2))
    (a : Bool) (n W : ℕ) (hW : n.bits.length ≤ W) :
    clCountTM.tm.runFrom (clCountCfg x (clBankStart a) p 0 n.bits []) (2 * W + 2) =
      clCountCfg x 0 p 0 (n + if a then 1 else 0).bits [] := by
  cases a with
  | false =>
    simpa [clBankStart] using clCount_idle_run
      (clCountCfg x 0 p 0 n.bits []) rfl (2 * W + 2)
  | true =>
    have hle : 2 * clCountCarry n.bits + 2 ≤ 2 * W + 2 := by
      have := clCountCarry_le n.bits
      omega
    rw [show 2 * W + 2 = (2 * clCountCarry n.bits + 2) +
      (2 * W + 2 - (2 * clCountCarry n.bits + 2)) by omega,
      MultiTapeTM.runFrom_add]
    simp only [clBankStart, ↓reduceIte, clCount_run, clCountInc_bits]
    exact clCount_idle_run _ rfl _

/-- A full selected bank increments exactly the requested coordinates,
restores every head to zero, and costs at most two scans of the widest
counter plus two steps, independent of the fixed number of counters. -/
private lemma clBank_finish {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (a : Fin l → Bool) (n : Fin l → ℕ) (W : ℕ)
    (hW : ∀ i, (n i).bits.length ≤ W) :
    (clBankTM l).tm.runFrom
      (clBankCfg p (fun i => clCountCfg x (clBankStart (a i)) p 0 (n i).bits []))
      (2 * W + 2) =
      clBankCfg p (fun i => clCountCfg x 0 p 0 (n i + if a i then 1 else 0).bits []) := by
  rw [clBank_run]
  congr 1
  funext i
  exact clBank_component x p (a i) (n i) W (hW i)

/-- The all-returned bank is absorbing on the entire configuration. -/
private lemma clBank_idle {l : ℕ} {x : List Bool}
    (c : Cfg (clBankTM l).k Bool (clBankTM l).State x)
    (hc : c.state = some (fun _ => some (0 : Fin 4))) :
    (clBankTM l).tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  refine Cfg.ext hc.symm (moveInputPos_zero _) ?_ ?_ ?_
  · funext i
    simp [clBankTM, clBankPart, clCountTM, FinTM.controlAction, Action.apply]
  · funext i
    simp [clBankTM, clBankPart, clCountTM, FinTM.controlAction, Action.apply]
  · simp [clBankTM, Action.apply]

/-- Cut the simultaneous bank at its observed first all-returned state.
This duration may be zero when no displacement needs a counter update;
the surrounding source-step/dispatch controller supplies positivity.
**Proof sketch.** Minimize the all-returned occurrence before the common
proved deadline. Absorption implies that its first occurrence already has
the exact endpoint and restored heads. -/
private lemma clBank_first {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (a : Fin l → Bool) (n : Fin l → ℕ) (W : ℕ)
    (hW : ∀ i, (n i).bits.length ≤ W) :
    ∃ t ≤ 2 * W + 2,
      (∀ j, j < t → ((clBankTM l).tm.runFrom
        (clBankCfg p (fun i => clCountCfg x (clBankStart (a i)) p 0 (n i).bits [])) j).state ≠
          some (fun _ => some (0 : Fin 4))) ∧
      (clBankTM l).tm.runFrom
        (clBankCfg p (fun i => clCountCfg x (clBankStart (a i)) p 0 (n i).bits [])) t =
        clBankCfg p (fun i => clCountCfg x 0 p 0 (n i + if a i then 1 else 0).bits []) := by
  let start := clBankCfg p (fun i => clCountCfg x (clBankStart (a i)) p 0 (n i).bits [])
  have finish := clBank_finish x p a n W hW
  have hex : ∃ t, t ≤ 2 * W + 2 ∧
      ((clBankTM l).tm.runFrom start t).state = some (fun _ => some (0 : Fin 4)) :=
    ⟨2 * W + 2, le_rfl, by rw [finish]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  refine ⟨t, ht.1, ?_, ?_⟩
  · intro j hj hs
    have := Nat.find_min' hex (show j ≤ 2 * W + 2 ∧
      ((clBankTM l).tm.runFrom start j).state = some (fun _ => some (0 : Fin 4)) from
        ⟨by omega, hs⟩)
    omega
  · have hstay := Function.iterate_fixed (clBank_idle _ ht.2) (2 * W + 2 - t)
    change (clBankTM l).tm.runFrom ((clBankTM l).tm.runFrom start t)
      (2 * W + 2 - t) = (clBankTM l).tm.runFrom start t at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans finish

/-- Actual source-head displacements. The input component is the clamped
virtual displacement, not the source's requested (possibly blocked) move.
A halted source contributes zero on every coordinate. -/
private def clMoves (M : FinTM Bool) (s : Option M.State) (b : Bool)
    (v : Option Bool) (w : Fin M.k → Option Bool) : Fin (1 + M.k) → SignType :=
  match s with
  | none => fun _ => 0
  | some q =>
    let a := M.tm.tr q v w
    Fin.addCases (fun _ : Fin 1 => FinTM.virtualMove b v a.inputTape)
      (fun i => (a.workTapes i).2)

/-- Reference positions use the buffer's shifted input coordinate and the
source's signed work coordinates. Adding one recovers the input position. -/
private def clPositions (M : FinTM Bool) {y : List Bool}
    (c : Cfg M.k Bool M.State y) : Fin (1 + M.k) → ℤ :=
  Fin.addCases (fun _ : Fin 1 => (c.inputPos.val : ℤ) - 1) c.workTapePos

/-- Every recorded displacement is exactly the change in the represented
position, including blocked input moves and the halting transition.
**Proof sketch.** The halted branch is stationary. In the live branch the
public virtual-move theorem identifies clamped input movement, while work
heads follow the source action literally, regardless of its next state. -/
private lemma clMoves_correct (M : FinTM Bool) {y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (i : Fin (1 + M.k)) :
    clPositions M (M.tm.step c) i = clPositions M c i +
      (clMoves M c.state b c.inputSymbol c.workTapeSymbols i : ℤ) := by
  cases hs : c.state with
  | none => simp [clMoves, hs, MultiTapeTM.step_of_halt hs]
  | some q =>
    have hm := (FinTM.virtualMove_correct c b hb
      (M.tm.tr q c.inputSymbol c.workTapeSymbols).inputTape).1
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [clPositions, clMoves, MultiTapeTM.step, hs, Action.apply] using hm.symm
    · intro j
      simp [clPositions, clMoves, MultiTapeTM.step, hs, Action.apply]

/-- Select the positive-move counter in the first bank and the
negative-move counter in the second bank. Zero moves select neither. -/
private def clSelect {l : ℕ} (d : Fin l → SignType) : Fin (l + l) → Bool :=
  Fin.addCases (fun i => decide (d i = .pos)) (fun i => decide (d i = .neg))

/-- Update precisely the selected movement counts. -/
private def clAdvance {l : ℕ} (d : Fin l → SignType) (n : Fin (l + l) → ℕ) :
    Fin (l + l) → ℕ := fun i => n i + if clSelect d i then 1 else 0

/-- Signed interpretation of the two canonical nonnegative movement counts. -/
private def clSigned {l : ℕ} (n : Fin (l + l) → ℕ) (i : Fin l) : ℤ :=
  (n (Fin.castAdd l i) : ℤ) - n (Fin.natAdd l i)

/-- The signed counter interpretation advances by the actual displacement. -/
private lemma clSigned_advance {l : ℕ} (d : Fin l → SignType)
    (n : Fin (l + l) → ℕ) (i : Fin l) :
    clSigned (clAdvance d n) i = clSigned n i + (d i : ℤ) := by
  cases hd : d i <;> simp [clSigned, clAdvance, clSelect, hd, -Fin.natAdd_eq_addNat] <;> omega

/-- A source step increases each stored movement count by at most one. -/
private lemma clAdvance_bound {l : ℕ} (d : Fin l → SignType)
    (n : Fin (l + l) → ℕ) (t : ℕ) (hn : ∀ i, n i ≤ t) (i : Fin (l + l)) :
    clAdvance d n i ≤ t + 1 := by
  unfold clAdvance
  split <;> have := hn i <;> omega

/-- Equality of signed positions is equality of the two cross-sums.
This criterion compares values, not the nonunique two-counter codes. -/
private lemma clSigned_eq {l : ℕ} (n m : Fin (l + l) → ℕ) (i : Fin l) :
    clSigned n i = clSigned m i ↔
      n (Fin.castAdd l i) + m (Fin.natAdd l i) =
        m (Fin.castAdd l i) + n (Fin.natAdd l i) := by
  unfold clSigned
  omega

/-- The native tracking round executes the source action once, then
runs the selected counter bank without advancing the source again.
The outer `none` phase is a live anchor, distinct from source halting. -/
private def clTrackTM (M : FinTM Bool) : FinTM Bool where
  k := ((1 + M.k) + (1 + M.k)) + (1 + M.k)
  State := Option M.State × Bool × Option (Fin ((1 + M.k) + (1 + M.k)) → Option (Fin 4))
  tm := {
    q₀ := (some M.tm.q₀, true, none)
    tr := fun q inp work =>
      match q.2.2 with
      | none =>
        let d := clMoves M q.1 q.2.1
          (work (Fin.natAdd ((1 + M.k) + (1 + M.k)) (Fin.castAdd M.k (0 : Fin 1))))
          (fun i => work (Fin.natAdd ((1 + M.k) + (1 + M.k)) (Fin.natAdd 1 i)))
        clRefAction M (fun s b => (s, b, some (fun i => some (clBankStart (clSelect d i)))))
          q.1 q.2.1 work (fun _ => (none, 0))
      | some qs =>
        if qs = fun _ => some (0 : Fin 4) then
          FinTM.controlAction 0 (some (q.1, q.2.1, none))
        else
          FinTM.leftAction (1 + M.k) (fun s => (q.1, q.2.1, some s))
            ((clBankTM ((1 + M.k) + (1 + M.k))).tm.tr qs inp
              (fun i => work (Fin.castAdd (1 + M.k) i))) }

/-- Canonical tracking seam: every movement counter is in canonical
binary form at head zero, with the full virtual reference bank retained. -/
private def clTrackCfg (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool)
    (n : Fin ((1 + M.k) + (1 + M.k)) → ℕ) :
    Cfg (clTrackTM M).k Bool (clTrackTM M).State x :=
  clRefCfg M (fun s b => (s, b, none)) c b 1
    (fun i => FinTM.bufferTape (n i).bits) (fun _ => 0) []

/-- Exactly one source action enters the selected administrative bank.
All source effects are already applied at this boundary; counters have
not yet changed, and physical output is still empty.
**Proof sketch.** Read the source symbols through the disjoint tape injections, then apply the inherited whole-configuration reference-action theorem. The selected counter controls depend on the actual clamped displacement before that action. -/
private lemma clTrack_source (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (n : Fin ((1 + M.k) + (1 + M.k)) → ℕ) :
    ∃ b', FinTM.VirtualTag (M.tm.step c).inputPos b' ∧
      (clTrackTM M).tm.step (clTrackCfg M (x := x) c b n) =
        clRefCfg M (fun s tag => (s, tag, some (fun i => some (clBankStart
          (clSelect (clMoves M c.state b c.inputSymbol c.workTapeSymbols) i)))))
          (M.tm.step c) b' (1 : Fin (x.length + 2))
          (fun i => FinTM.bufferTape (n i).bits) (fun _ => 0) [] := by
  obtain ⟨b', hb', he⟩ := clRef_apply M
    (fun s tag => (s, tag, some (fun i => some (clBankStart
      (clSelect (clMoves M c.state b c.inputSymbol c.workTapeSymbols) i)))))
    c b hb (1 : Fin (x.length + 2))
    (fun i => FinTM.bufferTape (n i).bits) (fun _ => 0) [] (fun _ => (none, 0))
  refine ⟨b', hb', ?_⟩
  have hv : (clTrackCfg M (x := x) c b n).workTapeSymbols
      (Fin.natAdd ((1 + M.k) + (1 + M.k)) (Fin.castAdd M.k (0 : Fin 1))) =
      c.inputSymbol := by
    simp [clTrackCfg, clRefCfg, Cfg.workTapeSymbols, FinTM.bufferTape_inputSymbol]
  have hw : (fun i => (clTrackCfg M (x := x) c b n).workTapeSymbols
      (Fin.natAdd ((1 + M.k) + (1 + M.k)) (Fin.natAdd 1 i))) =
      c.workTapeSymbols := by
    funext i
    simp [clTrackCfg, clRefCfg, Cfg.workTapeSymbols]
  change ((clTrackTM M).tm.tr (c.state, b, none) _ _).apply _ = _
  dsimp only [clTrackTM]
  rw [hv, hw]
  simpa only [clTrackCfg, clRefCfg, Cfg.workTapeSymbols, Action.apply, add_zero] using he

/-- A guarded left-bank phase agrees with its source through the source's
first observed exit. The guard need not agree after that exit.
**Proof sketch.** Induct on elapsed time. Before the exit the host action
is the disjoint-bank lift of the source action, so the whole-configuration
commutation lemma applies. A physically halted source is absorbing. -/
private lemma clLeft_until {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + l) Bool S')
    (emb : S → S') (exit : S)
    (htr : ∀ q inp work, q ≠ exit → host.tr (emb q) inp work =
      FinTM.leftAction l emb (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (t : ℕ) (hf : ∀ j < t, (tm.runFrom c j).state ≠ some exit) :
    ∀ j ≤ t, host.runFrom (FinTM.leftCfg emb c tapes heads) j =
      FinTM.leftCfg emb (tm.runFrom c j) tapes heads := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), MultiTapeTM.runFrom_succ_eq_step']
    let z := tm.runFrom c j
    have hne := hf j (by omega)
    change host.step (FinTM.leftCfg emb z tapes heads) =
      FinTM.leftCfg emb (tm.step z) tapes heads
    cases hs : z.state with
    | none => simp [MultiTapeTM.step, FinTM.leftCfg, hs]
    | some q =>
      have hq : q ≠ exit := by intro he; subst q; exact hne hs
      have hw : (fun i => (FinTM.leftCfg emb z tapes heads).workTapeSymbols
          (Fin.castAdd l i)) = z.workTapeSymbols := by
        funext i
        simp [FinTM.leftCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [show (FinTM.leftCfg emb z tapes heads).state = some (emb q) by
        simp only [FinTM.leftCfg, hs, Option.map_some]]
      dsimp only
      rw [htr q _ _ hq]
      change (FinTM.leftAction l emb (tm.tr q z.inputSymbol _)).apply
        (FinTM.leftCfg emb z tapes heads) = _
      rw [hw]
      simpa only [hs] using FinTM.leftCfg_apply emb (tm.tr q z.inputSymbol z.workTapeSymbols) z tapes heads

/-- The counter-bank frame is literally the reference representation,
including its virtual-input buffer, every source tape, and all heads. -/
private lemma clTrack_frame (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool)
    (qs : Fin ((1 + M.k) + (1 + M.k)) → Fin 4)
    (n : Fin ((1 + M.k) + (1 + M.k)) → ℕ) :
    FinTM.leftCfg (fun s => (c.state, b, some s))
      (clBankCfg (1 : Fin (x.length + 2))
        (fun i => clCountCfg x (qs i) 1 0 (n i).bits []))
      (Fin.addCases (fun _ : Fin 1 => FinTM.bufferTape y) c.workTapes)
      (Fin.addCases (fun _ : Fin 1 => (c.inputPos.val : ℤ) - 1) c.workTapePos) =
      clRefCfg M (fun s b => (s, b, some (fun i => some (qs i)))) c b
        (1 : Fin (x.length + 2)) (fun i => FinTM.bufferTape (n i).bits) (fun _ => 0) [] := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [FinTM.leftCfg, clBankCfg, clCountCfg, clRefCfg, clCountTape_eq]
  · intro j; simp [FinTM.leftCfg, clRefCfg, FinTM.tapeBlocks, clBankTM]

/-- After all counters have returned, exactly one silent dispatch restores
the tracking anchor without changing source time or any tape. -/
private lemma clTrack_dispatch (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool)
    (n : Fin ((1 + M.k) + (1 + M.k)) → ℕ) :
    (clTrackTM M).tm.step
      (clRefCfg M (fun s b => (s, b, some (fun _ => some (0 : Fin 4)))) c b
        (1 : Fin (x.length + 2)) (fun i => FinTM.bufferTape (n i).bits) (fun _ => 0) []) =
      clTrackCfg M (x := x) c b n := by
  simp only [MultiTapeTM.step, clRefCfg, clTrackTM, if_true]
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- A full native source-and-counter round has a strictly positive first
anchor return. It updates exactly the signed/clamped source displacements,
suppresses source output, and restores every administrative counter head.
**Proof sketch.** Execute the inherited faithful source action once, lift
the selected counter bank until its actual first all-returned state, then
perform one silent dispatch. No interior configuration is an anchor. The
source bank is framed throughout the administrative segment, so source
halting and terminal writes are handled before counters are updated. -/
private lemma clTrack_round (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (n : Fin ((1 + M.k) + (1 + M.k)) → ℕ) (W : ℕ)
    (hW : ∀ i, (n i).bits.length ≤ W) :
    ∃ τ ≤ 2 * W + 4, 0 < τ ∧
      (∀ j, 0 < j → j < τ → ∃ s tag qs,
        ((clTrackTM M).tm.runFrom (clTrackCfg M (x := x) c b n) j).state =
          some (s, tag, some qs)) ∧
      ∃ b', FinTM.VirtualTag (M.tm.step c).inputPos b' ∧
        (clTrackTM M).tm.runFrom (clTrackCfg M (x := x) c b n) τ =
          clTrackCfg M (x := x) (M.tm.step c) b'
            (clAdvance (clMoves M c.state b c.inputSymbol c.workTapeSymbols) n) := by
  let d := clMoves M c.state b c.inputSymbol c.workTapeSymbols
  obtain ⟨b', hb', hs⟩ := clTrack_source M (x := x) c b hb n
  obtain ⟨t, ht, hf, he⟩ := clBank_first x 1 (clSelect d) n W hW
  let tapes : Fin (1 + M.k) → ℤ → Option Bool := Fin.addCases (fun _ : Fin 1 => FinTM.bufferTape y) (M.tm.step c).workTapes
  let heads : Fin (1 + M.k) → ℤ := Fin.addCases (fun _ : Fin 1 => ((M.tm.step c).inputPos.val : ℤ) - 1)
    (M.tm.step c).workTapePos
  let emb := fun qs : Fin ((1 + M.k) + (1 + M.k)) → Option (Fin 4) => ((M.tm.step c).state, b', some qs)
  let start := clBankCfg (1 : Fin (x.length + 2))
    (fun i => clCountCfg x (clBankStart (clSelect d i)) 1 0 (n i).bits [])
  have lift := clLeft_until (clBankTM ((1 + M.k) + (1 + M.k))).tm
    (clTrackTM M).tm emb (fun _ => some (0 : Fin 4))
    (by intro qs inp work hq; simp only [clTrackTM, emb, if_neg hq])
    start tapes heads t hf
  have hfirst : (clTrackTM M).tm.step (clTrackCfg M (x := x) c b n) =
      FinTM.leftCfg emb start tapes heads := by
    exact hs.trans (clTrack_frame M (M.tm.step c) b'
      (fun i => clBankStart (clSelect d i)) n).symm
  have hrun (j : ℕ) (hj : j ≤ t) :
      (clTrackTM M).tm.runFrom (clTrackCfg M (x := x) c b n) (j + 1) =
        FinTM.leftCfg emb ((clBankTM ((1 + M.k) + (1 + M.k))).tm.runFrom start j)
          tapes heads := by
    rw [MultiTapeTM.runFrom_succ_eq_step, hfirst]
    exact lift j hj
  refine ⟨t + 2, by omega, by omega, ?_, b', hb', ?_⟩
  · intro j hj hlt
    have hh := hrun (j - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hh
    rw [hh]
    dsimp only [start]
    rw [clBank_run]
    exact ⟨_, _, _, rfl⟩
  · rw [show t + 2 = (t + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step', hrun t le_rfl]
    change (clTrackTM M).tm.step (FinTM.leftCfg emb
      ((clBankTM ((1 + M.k) + (1 + M.k))).tm.runFrom start t) tapes heads) = _
    rw [he]
    exact (congrArg (clTrackTM M).tm.step
      (clTrack_frame M (M.tm.step c) b' (fun _ => 0) (clAdvance d n))).trans
        (clTrack_dispatch M (M.tm.step c) b' (clAdvance d n))

/-- Two disjoint fixed tape slots, with no run-time indexing assumption. -/
private def clTwo {α : Type} (a b : α) : Fin 2 → α := fun i => if i = 0 then a else b

/-- A two-tape native record copier. It doubles each source bit, writes
one aligned `01` field separator, then restores the source head. The
record head remains at its new right blank. Physical output is silent. -/
private def clCopyTM : FinTM Bool where
  k := 2
  State := Fin 5
  tm := {
    q₀ := 0
    tr := fun q _ work =>
      if q = 0 then
        match work 0 with
        | some b => ⟨0, clTwo (none, 0) (some (some b), .pos), none, some 1⟩
        | none => ⟨0, clTwo (none, .neg) (some (some false), .pos), none, some 2⟩
      else if q = 1 then
        ⟨0, clTwo (none, .pos) (some (some ((work 0).getD false)), .pos), none, some 0⟩
      else if q = 2 then
        ⟨0, clTwo (none, 0) (some (some true), .pos), none, some 3⟩
      else if q = 3 then
        match work 0 with
        | some _ => ⟨0, clTwo (none, .neg) (none, 0), none, some 3⟩
        | none => ⟨0, clTwo (none, .pos) (none, 0), none, some 4⟩
      else FinTM.controlAction 0 (some q) }

/-- The copier's source and accumulated record, with exact heads. -/
private def clCopyCfg (x : List Bool) (q : Fin 5) (p : Fin (x.length + 2))
    (z : ℤ) (w record : List Bool) : Cfg 2 Bool (Fin 5) x :=
  ⟨some q, p, clTwo (FinTM.bufferTape w) (FinTM.bufferTape record),
    clTwo z record.length, []⟩

/-- A copier write appends exactly one bit at the record head. -/
private lemma clCopy_write (x : List Bool) (q q' : Fin 5) (p : Fin (x.length + 2))
    (z : ℤ) (w record : List Bool) (b : Bool) (d : SignType) :
    (⟨0, clTwo (none, d) (some (some b), .pos), none, some q'⟩ : Action 2 Bool (Fin 5)).apply
      (clCopyCfg x q p z w record) = clCopyCfg x q' p (z + d) w (record ++ [b]) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    fin_cases i
    · rfl
    · exact (FinTM.bufferTape_append record b).symm
  · funext i
    fin_cases i <;> simp [clTwo, clCopyCfg, Action.apply]

/-- A pair of transitions writes the doubled source bit and advances
its read head by exactly one. The source tape is read-only. -/
private lemma clCopy_pair (x : List Bool) (p : Fin (x.length + 2))
    (pre rest record : List Bool) (b : Bool) :
    clCopyTM.tm.runFrom (clCopyCfg x 0 p pre.length (pre ++ b :: rest) record) 2 =
      clCopyCfg x 0 p (pre.length + 1) (pre ++ b :: rest) (record ++ [b, b]) := by
  have hr : FinTM.bufferTape (pre ++ b :: rest) pre.length = some b := by
    rw [FinTM.bufferTape_nat, List.getElem?_append_right le_rfl]
    simp
  have h0 : clCopyTM.tm.step (clCopyCfg x 0 p pre.length (pre ++ b :: rest) record) =
      clCopyCfg x 1 p pre.length (pre ++ b :: rest) (record ++ [b]) := by
    change (clCopyTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    simp only [clCopyTM, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols,
      clTwo, Fin.cases_zero, hr]
    simpa [clCopyCfg] using clCopy_write x 0 1 p pre.length (pre ++ b :: rest) record b 0
  rw [show 2 = 1 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, h0]
  change (clCopyTM.tm.tr (1 : Fin 5) _ _).apply _ = _
  simp only [clCopyTM, show (1 : Fin 5) ≠ 0 by decide, ↓reduceIte,
    clCopyCfg, Cfg.workTapeSymbols, clTwo, Fin.cases_zero, hr, Option.getD_some]
  simpa [clCopyCfg, List.append_assoc] using
    clCopy_write x 1 0 p pre.length (pre ++ b :: rest) (record ++ [b]) b .pos

/-- The forward pass copies all remaining source bits, charging both
writes for each bit. It has not yet written the field separator.
**Proof sketch.** Induct on the remaining source suffix. Two transitions
copy its first bit; include that bit in the preserved prefix and apply
the induction hypothesis to the rest. -/
private lemma clCopy_forward (x : List Bool) (p : Fin (x.length + 2)) (w : List Bool) :
    ∀ pre record,
      clCopyTM.tm.runFrom (clCopyCfg x 0 p pre.length (pre ++ w) record) (2 * w.length) =
        clCopyCfg x 0 p (pre ++ w).length (pre ++ w)
          (record ++ w.flatMap (fun b => [b, b])) := by
  induction w with
  | nil => intro pre record; simp
  | cons b w ih =>
    intro pre record
    rw [List.length_cons, show 2 * (w.length + 1) = 2 + 2 * w.length by omega,
      MultiTapeTM.runFrom_add, clCopy_pair]
    have h := ih (pre ++ [b]) (record ++ [b, b])
    simpa [List.append_assoc, List.length_append, Nat.cast_add, Nat.cast_one] using h

/-- The two separator writes move the source head left for rewinding and
leave the record head just after the complete self-delimiting field. -/
private lemma clCopy_separator (x : List Bool) (p : Fin (x.length + 2))
    (w record : List Bool) :
    clCopyTM.tm.runFrom (clCopyCfg x 0 p w.length w record) 2 =
      clCopyCfg x 3 p (w.length - 1) w (record ++ [false, true]) := by
  have hr : FinTM.bufferTape w w.length = none := by simp
  have h0 : clCopyTM.tm.step (clCopyCfg x 0 p w.length w record) =
      clCopyCfg x 2 p (w.length - 1) w (record ++ [false]) := by
    change (clCopyTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    simp only [clCopyTM, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols,
      clTwo, Fin.cases_zero, hr]
    simpa [clCopyCfg, sub_eq_add_neg] using clCopy_write x 0 2 p w.length w record false .neg
  rw [show 2 = 1 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, h0]
  change (clCopyTM.tm.tr (2 : Fin 5) _ _).apply _ = _
  simp only [clCopyTM, show (2 : Fin 5) ≠ 0 by decide,
    show (2 : Fin 5) ≠ 1 by decide, ↓reduceIte]
  simpa [clCopyCfg, List.append_assoc] using
    clCopy_write x 2 3 p (w.length - 1) w (record ++ [false]) true 0

/-- The source rewind costs one transition per crossed bit and one to
leave the left blank. It preserves the complete accumulated record.
**Proof sketch.** Induct on the remaining source prefix length. At minus
one, a right move returns to zero; at a source bit, move left once. -/
private lemma clCopy_rewind (x : List Bool) (p : Fin (x.length + 2))
    (w record : List Bool) : ∀ j, j ≤ w.length →
      clCopyTM.tm.runFrom (clCopyCfg x 3 p ((j : ℤ) - 1) w record) (j + 1) =
        clCopyCfg x 4 p 0 w record := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i; fin_cases i <;> simp [MultiTapeTM.step, clCopyTM, clCopyCfg,
        Cfg.workTapeSymbols, clTwo, Action.apply]
    · funext i; fin_cases i <;> simp [MultiTapeTM.step, clCopyTM, clCopyCfg,
        Cfg.workTapeSymbols, clTwo, Action.apply]
  | succ j ih =>
    intro hj
    have hr : FinTM.bufferTape w (j : ℤ) = some w[j] := by
      rw [FinTM.bufferTape_nat]
      exact List.getElem?_eq_getElem (by omega)
    have hs : clCopyTM.tm.step (clCopyCfg x 3 p j w record) =
        clCopyCfg x 3 p ((j : ℤ) - 1) w record := by
      change (clCopyTM.tm.tr (3 : Fin 5) _ _).apply _ = _
      simp only [clCopyTM, show (3 : Fin 5) ≠ 0 by decide,
        show (3 : Fin 5) ≠ 1 by decide, show (3 : Fin 5) ≠ 2 by decide,
        ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols, clTwo, Fin.cases_zero, hr]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i; fin_cases i <;> simp [clTwo, clCopyCfg, Action.apply]
      · funext i; fin_cases i <;> simp [clTwo, clCopyCfg, Action.apply, sub_eq_add_neg]
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Exact full native record-copy contract. No whole-formula serializer
is involved: this is one self-delimiting binary counter field on a work
tape. The empty field still takes three positive transitions. -/
private lemma clCopy_run (x : List Bool) (p : Fin (x.length + 2))
    (w record : List Bool) :
    clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) (3 * w.length + 3) =
      clCopyCfg x 4 p 0 w (record ++ pairEncode w []) := by
  have hf := clCopy_forward x p w [] record
  simp only [List.length_nil, Nat.cast_zero, List.nil_append] at hf
  rw [show 3 * w.length + 3 = 2 * w.length + (2 + (w.length + 1)) by omega,
    MultiTapeTM.runFrom_add, hf, MultiTapeTM.runFrom_add, clCopy_separator,
    clCopy_rewind x p w _ w.length le_rfl]
  simp [pairEncode, List.append_assoc]

/-- Returned record-copy configurations remain unchanged in their entirety. -/
private lemma clCopy_idle {x : List Bool} (c : Cfg 2 Bool (Fin 5) x)
    (hc : c.state = some (4 : Fin 5)) : clCopyTM.tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  change (FinTM.controlAction 0 (some (4 : Fin 5))).apply c = c
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- The exact recorded field is available at the copier's observed first
positive return, with both the untouched source and the new record head
specified. This permits a host to dispatch without knowing field length.
**Proof sketch.** Choose the first completed-control occurrence below the exact copying bound. Since completion is absorbing on the whole configuration, its first occurrence already has the final record and restored source head. Initial and completed controls are distinct. -/
private lemma clCopy_first (x : List Bool) (p : Fin (x.length + 2))
    (w record : List Bool) :
    ∃ t ≤ 3 * w.length + 3, 0 < t ∧
      (∀ j, j < t → (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) j).state ≠ some (4 : Fin 5)) ∧
      clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t =
        clCopyCfg x 4 p 0 w (record ++ pairEncode w []) := by
  have finish := clCopy_run x p w record
  have hex : ∃ t, t ≤ 3 * w.length + 3 ∧
      (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t).state = some (4 : Fin 5) :=
    ⟨3 * w.length + 3, le_rfl, by rw [finish]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hp : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    have hs := ht.2
    change (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t).state = some (4 : Fin 5) at hs
    rw [hz, MultiTapeTM.runFrom_zero] at hs
    have hh := congrArg (fun z => z.map Fin.val) hs
    norm_num [clCopyCfg] at hh
  refine ⟨t, ht.1, hp, ?_, ?_⟩
  · intro j hj hs
    have := Nat.find_min' hex (show j ≤ 3 * w.length + 3 ∧
      (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) j).state = some (4 : Fin 5) from ⟨by omega, hs⟩)
    omega
  · have hstay := Function.iterate_fixed (clCopy_idle _ ht.2) (3 * w.length + 3 - t)
    change clCopyTM.tm.runFrom (clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t)
      (3 * w.length + 3 - t) = clCopyTM.tm.runFrom (clCopyCfg x 0 p 0 w record) t at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans finish

/-- A concrete physical layout, with an exact selector and no aliased slot. -/
private structure clPlacement (k l : ℕ) where
  index : Fin k ↪ Fin l
  select : Fin l → Option (Fin k)
  exact : ∀ i j, select j = some i ↔ index i = j

/-- Package a concrete two-sided selection law as an injective R1 layout. -/
private def clPlacement.ofInverse {k l : ℕ} (index : Fin k → Fin l)
    (select : Fin l → Option (Fin k)) (left : ∀ i, select (index i) = some i)
    (right : ∀ i j, select j = some i → index i = j) : clPlacement k l where
  index := ⟨index, by
    intro i j h
    apply Option.some.inj
    rw [← left i, ← left j, h]⟩
  select := select
  exact i j := ⟨right i j, fun h => h ▸ left i⟩

/-- Reindex a certified layout by a bijection of its source tape indices. -/
private def clPlacement.permute {k l : ℕ} (slots : clPlacement k l)
    (e : Fin k ≃ Fin k) : clPlacement k l where
  index := e.toEmbedding.trans slots.index
  select j := (slots.select j).map e.symm
  exact i j := by
    simp only [Option.map_eq_some_iff]
    constructor
    · rintro ⟨a, ha, h⟩
      have hi : e i = a := by simpa using congrArg e h.symm
      exact (slots.exact a j).mp ha ▸ congrArg slots.index hi
    · intro h
      exact ⟨e i, (slots.exact (e i) j).mpr h, e.symm_apply_apply i⟩

/-- The complete bank is already an exact layout. -/
private def clPlacement.refl (k : ℕ) : clPlacement k k where
  index := Function.Embedding.refl _
  select := some
  exact _ _ := by simp only [Option.some.injEq]; exact eq_comm

/-- An empty source selects none of an ambient bank. -/
private def clPlacement.empty (l : ℕ) : clPlacement 0 l where
  index := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  select _ := none
  exact i := Fin.elim0 i

/-- Juxtapose certified disjoint banks; the sum tags rule out cross-bank aliases.
**Proof sketch.** Split both finite indices by bank. In a matching bank use
the component certificate; in opposite banks the finite-index values differ. -/
private def clPlacement.sum {k l m n : ℕ} (a : clPlacement k l) (b : clPlacement m n) :
    clPlacement (k + m) (l + n) :=
  clPlacement.ofInverse
    (Fin.addCases (fun i => Fin.castAdd n (a.index i)) (fun i => Fin.natAdd l (b.index i)))
    (Fin.addCases (fun j => (a.select j).map (Fin.castAdd m))
      (fun j => (b.select j).map (Fin.natAdd k)))
    (by
      intro i
      refine Fin.addCases ?_ ?_ i <;> intro j
      · simp only [Fin.addCases_left, (a.exact j (a.index j)).mpr rfl, Option.map_some]
      · simp only [Fin.addCases_right, (b.exact j (b.index j)).mpr rfl, Option.map_some])
    (by
      intro i j
      refine Fin.addCases ?_ ?_ i <;> intro u <;>
        refine Fin.addCases ?_ ?_ j <;> intro v h
      all_goals simp only [Fin.addCases_left, Fin.addCases_right, Option.map_eq_some_iff] at h ⊢
      · obtain ⟨w, hw, he⟩ := h
        have he' : w = u := Fin.ext (congrArg (fun z : Fin (k + m) => z.val) he)
        subst w
        exact congrArg (Fin.castAdd n) ((a.exact u v).mp hw)
      · obtain ⟨w, _, he⟩ := h
        have hv := congrArg Fin.val he
        change k + w.val = u.val at hv
        omega
      · obtain ⟨w, _, he⟩ := h
        have hv := congrArg Fin.val he
        change w.val = k + u.val at hv
        omega
      · obtain ⟨w, hw, he⟩ := h
        have he' : w = u := Fin.ext (Nat.add_left_cancel (congrArg (fun z : Fin (k + m) => z.val) he))
        subst w
        exact congrArg (Fin.natAdd l) ((b.exact u v).mp hw))

/-- Compose layouts; a host slot selects exactly through both certificates. -/
private def clPlacement.comp {k l m : ℕ} (a : clPlacement k l) (b : clPlacement l m) :
    clPlacement k m where
  index := a.index.trans b.index
  select j := (b.select j).bind a.select
  exact i j := by
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨u, hu, hi⟩
      change b.index (a.index i) = j
      rw [(a.exact i u).mp hi]
      exact (b.exact u j).mp hu
    · intro h
      exact ⟨a.index i, (b.exact (a.index i) j).mpr h, (a.exact i (a.index i)).mpr rfl⟩

/-- A trailing selected bank, leaving all preceding tapes in the ambient frame. -/
private def clPlacement.trailing (k l : ℕ) : clPlacement l (k + l) where
  index := Fin.natAddEmb k
  select := Fin.addCases (fun _ => none) some
  exact i j := by
    refine Fin.addCases ?_ ?_ j
    · intro a
      constructor
      · intro h
        simp only [Fin.addCases_left] at h
        cases h
      · intro h
        have hv := congrArg (fun z : Fin (k + l) => z.val) h
        change k + i.val = a.val at hv
        omega
    · intro a
      simp [Fin.ext_iff, eq_comm]

/-- Protect one trailing tape while selecting the complete leading bank. -/
private def clKeepLastPlacement (k : ℕ) : clPlacement k (k + 1) where
  index := Fin.castAddEmb 1
  select := Fin.addCases some (fun _ => none)
  exact i j := by
    have h := ((clPlacement.refl k).sum (clPlacement.empty 1)).exact (Fin.castAdd 0 i) j
    dsimp only [clPlacement.sum, clPlacement.ofInverse, clPlacement.refl, clPlacement.empty,
      Function.Embedding.coeFn_mk, Function.Embedding.refl_apply] at h
    rw [Fin.addCases_left] at h
    simpa using h

attribute [local simp] clPlacement.ofInverse clPlacement.refl clPlacement.empty
  clPlacement.sum clPlacement.comp clPlacement.trailing

/-- R1's finite search is the certified selector of a concrete layout.
**Proof sketch.** The certificate characterizes every possible successful
search result. If no source is found, the selector must also be empty. -/
private lemma clPlacement_lookup {k l : ℕ} (slots : clPlacement k l) (j : Fin l) :
    (List.finRange k).find? (fun i => decide (slots.index i = j)) = slots.select j := by
  cases hfind : (List.finRange k).find? (fun i => decide (slots.index i = j)) with
  | some i =>
    have hit := List.find?_some hfind
    have hi : slots.index i = j := of_decide_eq_true hit
    exact ((slots.exact i j).mpr hi).symm
  | none =>
    cases hs : slots.select j with
    | none => rfl
    | some i =>
      have hnone := List.find?_eq_none.mp hfind i (by simp)
      exact False.elim (hnone (by simpa using (slots.exact i j).mp hs))

/-- Forward one action using the public R1 transformer and a state map. -/
private def clPlacedAction {k l : ℕ} {S H : Type}
    (slots : clPlacement k l) (emb : S → H) (q : S) (a : Action k Bool S) : Action l Bool H :=
  ((embedEmitTM slots.index ⟨q, fun _ _ _ => a⟩).tr q none (fun _ => none)).mapState emb

/-- The public R1 configuration transport with the concrete control map. -/
private def clPlacedCfg {k l : ℕ} {S H : Type} {x : List Bool}
    (slots : clPlacement k l) (emb : S → H)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c : Cfg k Bool S x) : Cfg l Bool H x :=
  (embedEmitCfg slots.index tapes heads [] c).mapState emb

/-- A certified layout reads the source action on its exact selected slots. -/
private lemma clPlacedAction_eq {k l : ℕ} {S H : Type}
    (slots : clPlacement k l) (emb : S → H) (q : S) (a : Action k Bool S) :
    clPlacedAction slots emb q a =
      ⟨a.inputTape, (fun j => match slots.select j with
        | some i => a.workTapes i | none => (none, 0)), a.output, a.state.map emb⟩ := by
  change (⟨a.inputTape, (fun j => match (List.finRange k).find?
    (fun i => decide (slots.index i = j)) with
      | some i => a.workTapes i | none => (none, 0)), a.output, a.state.map emb⟩ : Action l Bool H) = _
  simp_rw [clPlacement_lookup]

/-- The certified selector gives both selected source fields and the ambient frame.
**Proof sketch.** On a selected slot, exact correspondence identifies the
source index and the two public selected-field theorems apply. An unselected
slot lies outside the embedding's range, so the time-zero frame theorem
preserves its tape and head. The other configuration fields are unchanged. -/
private lemma clPlacedCfg_eq {k l : ℕ} {S H : Type} {x : List Bool}
    (slots : clPlacement k l) (emb : S → H)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (c : Cfg k Bool S x) :
    clPlacedCfg slots emb tapes heads c =
      ⟨c.state.map emb, c.inputPos,
        (fun j => match slots.select j with | some i => c.workTapes i | none => tapes j),
        (fun j => match slots.select j with | some i => c.workTapePos i | none => heads j),
        c.output⟩ := by
  have fields (j : Fin l) :
      (embedEmitCfg slots.index tapes heads [] c).workTapes j =
        (match slots.select j with | some i => c.workTapes i | none => tapes j) ∧
      (embedEmitCfg slots.index tapes heads [] c).workTapePos j =
        (match slots.select j with | some i => c.workTapePos i | none => heads j) := by
    cases hs : slots.select j with
    | some i =>
      rw [← (slots.exact i j).mp hs, embedEmitCfg_selected_tape, embedEmitCfg_selected_pos]
      exact ⟨rfl, rfl⟩
    | none =>
      have outside : j ∉ Set.range slots.index := by
        rintro ⟨i, hi⟩
        have he := (slots.exact i j).mpr hi
        rw [hs] at he
        cases he
      exact (embedEmitTM_frame slots.index
        ⟨(), fun _ _ _ => FinTM.controlAction 0 none⟩ tapes heads []
        (c.mapState (fun _ => ())) 0).1 j outside
  exact Cfg.ext rfl rfl (funext fun j => (fields j).1) (funext fun j => (fields j).2) rfl

attribute [local simp] clPlacedCfg_eq

/-- One placed action commutes with the R1 configuration transport.
**Proof sketch.** Instantiate R1 at time one for a constant-action source,
then apply the public compatibility of action application with state maps.
The incoming state is irrelevant to an action's application. -/
private lemma clPlaced_apply {k l : ℕ} {S H : Type} {x : List Bool}
    (slots : clPlacement k l) (emb : S → H) (q : S)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (clPlacedAction slots emb q a).apply (clPlacedCfg slots emb tapes heads c) =
      clPlacedCfg slots emb tapes heads (a.apply c) := by
  let constant : MultiTapeTM k Bool S := ⟨q, fun _ _ _ => a⟩
  have one := embedEmitTM_runFrom slots.index constant tapes heads [] {c with state := some q} 1
  change ((embedEmitTM slots.index constant).tr q c.inputSymbol _).apply
    (embedEmitCfg slots.index tapes heads [] {c with state := some q}) = _ at one
  have result := congrArg (Cfg.mapState emb) one
  rw [← Cfg.mapState_apply] at result
  exact result

/-- R1 tape transport followed by the shared guarded state transport.
**Proof sketch.** The public state theorem performs same-carrier Z5 after
renaming; R1 identifies its embedded run and transfers the source guard. -/
private lemma clPlaced_run {k l : ℕ} {S H : Type} {x : List Bool}
    (src : MultiTapeTM k Bool S) (host : MultiTapeTM l Bool H)
    (slots : clPlacement k l) (emb : S → H) (hinj : Function.Injective emb) (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work, host.tr (emb q) inp work =
      clPlacedAction slots emb q (src.tr q inp (fun i => work (slots.index i))))
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c : Cfg k Bool S x) (t : ℕ)
    (hguard : ∀ j < t, ∀ q, (src.runFrom c j).state = some q → good q) :
    host.runFrom (clPlacedCfg slots emb tapes heads c) t =
      clPlacedCfg slots emb tapes heads (src.runFrom c t) := by
  simpa only [embedEmitTM_runFrom] using
    MultiTapeTM.runFrom_mapState_of_agreeOn (embedEmitTM slots.index src) host ⟨emb, hinj⟩ good hagree
      (embedEmitCfg slots.index tapes heads [] c) t (fun j hj q hq =>
        hguard j hj q (by simpa only [embedEmitTM_runFrom] using hq))



/-- Row copying selects one counter and the record slot, with no aliases. -/
private def clRowSelect {l : ℕ} (i : Fin l) : clPlacement 2 (l + 1) :=
  clPlacement.ofInverse (clTwo (Fin.castAdd 1 i) (Fin.natAdd l (0 : Fin 1))) (Fin.addCases (fun j => if j = i then some 0 else none) (fun _ => some 1))
    (by intro j; fin_cases j <;> simp [clTwo, -Fin.natAdd_eq_addNat])
    (by
      intro a b
      fin_cases a <;> refine Fin.addCases ?_ ?_ b <;> intro j h
      all_goals try (have hj : j = 0 := Fin.eq_zero j; subst j)
      all_goals simp [clTwo, Fin.ext_iff] at h ⊢
      all_goals try split_ifs at h
      all_goals simp_all [Fin.ext_iff])



/-- Native row controller: copy every counter in fixed tape order, then
return live. There is one charged dispatch after each complete field. -/
private def clRowTM (l : ℕ) : FinTM Bool where
  k := l + 1
  State := Fin (l + 1) × Fin 5
  tm := {
    q₀ := (0, 0)
    tr := fun q inp work =>
      if hi : q.1.val < l then
        if q.2 = 4 then
          FinTM.controlAction 0 (some (⟨q.1.val + 1, by omega⟩, 0))
        else
          clPlacedAction (clRowSelect ⟨q.1.val, hi⟩) (fun s => (q.1, s)) q.2 (clCopyTM.tm.tr q.2 inp (fun j => work ((clRowSelect ⟨q.1.val, hi⟩).index j)))
      else FinTM.controlAction 0 (some q) }

/-- Full row-copy seam; all counters are retained at zero, while the
append-only administrative record head is its exact current length. -/
private def clRowCfg {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (i : Fin (l + 1)) (q : Fin 5) (w : Fin l → List Bool) (record : List Bool) :
    Cfg (clRowTM l).k Bool (clRowTM l).State x :=
  ⟨some (i, q), p,
    Fin.addCases (fun j => FinTM.bufferTape (w j)) (fun _ : Fin 1 => FinTM.bufferTape record),
    Fin.addCases (fun _ => 0) (fun _ : Fin 1 => record.length), []⟩

/-- Relocating a single field copier gives the complete row seam. All
unselected counters, not just their current cells, retain their words. -/
private lemma clRow_frame {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (i : Fin l) (q : Fin 5) (w : Fin l → List Bool) (record : List Bool) :
    clPlacedCfg (clRowSelect i) (fun s => (i.castSucc, s))
      (Fin.addCases (fun j => FinTM.bufferTape (w j))
        (fun _ : Fin 1 => (fun _ : ℤ => none))) (fun _ => 0)
      (clCopyCfg x q p 0 (w i) record) = clRowCfg x p i.castSucc q w record := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    refine Fin.addCases ?_ ?_ j
    · intro j
      by_cases hj : j = i
      · subst j; simp [clRowSelect, clCopyCfg, clTwo, clRowCfg]
      · simp [clRowSelect, clCopyCfg, clTwo, clRowCfg, hj]
    · intro j; simp [clRowSelect, clCopyCfg, clTwo, clRowCfg]
  · funext j
    refine Fin.addCases ?_ ?_ j
    · intro j
      by_cases hj : j = i <;> simp [clRowSelect, clCopyCfg, clTwo, clRowCfg, hj]
    · intro j; simp [clRowSelect, clCopyCfg, clTwo, clRowCfg]

/-- One field is stored by actual native writes and the controller then
advances to the next field. The entire counter bank and input head are
restored; the physical output remains empty.
**Proof sketch.** Relocate the two-tape copier into the selected counter and record slots until its first completion. Its full return theorem preserves every unselected tape; one silent dispatch advances the finite field index. -/
private lemma clRow_field {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (i : Fin l) (w : Fin l → List Bool) (record : List Bool) :
    ∃ t ≤ 3 * (w i).length + 4, 0 < t ∧
      (clRowTM l).tm.runFrom (clRowCfg x p i.castSucc 0 w record) t =
        clRowCfg x p i.succ 0 w (record ++ pairEncode (w i) []) := by
  obtain ⟨t, ht, hp, hf, he⟩ := clCopy_first x p (w i) record
  let tapes : Fin (l + 1) → ℤ → Option Bool := Fin.addCases (fun j => FinTM.bufferTape (w j))
    (fun _ : Fin 1 => (fun _ : ℤ => none))
  have lift := clPlaced_run clCopyTM.tm (clRowTM l).tm (clRowSelect i) (fun s => (i.castSucc, s)) (by intro a b h; cases h; rfl) (fun s => s ≠ (4 : Fin 5))
    (by intro q hq inp work; simp [clRowTM, i.isLt, hq]; rfl) tapes (fun _ => 0)
    (clCopyCfg x 0 p 0 (w i) record) t
    (by intro j hj q hq; intro heq; subst q; exact hf j hj hq)
  rw [he] at lift
  have lift' : (clRowTM l).tm.runFrom (clRowCfg x p i.castSucc 0 w record) t =
      clRowCfg x p i.castSucc 4 w (record ++ pairEncode (w i) []) :=
    (congrArg (fun z => (clRowTM l).tm.runFrom z t)
      (clRow_frame x p i 0 w record)).symm.trans
      (lift.trans (clRow_frame x p i 4 w (record ++ pairEncode (w i) [])))
  refine ⟨t + 1, by omega, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', lift']
  change ((clRowTM l).tm.tr (i.castSucc, (4 : Fin 5)) _ _).apply _ = _
  dsimp only [clRowTM]
  split
  · rw [if_pos rfl, FinTM.controlAction_apply, moveInputPos_zero]
    rfl
  · rename_i hi
    exact False.elim (hi i.isLt)

/-- Prefix of a stored row: fields occur in increasing counter-tape
order and each is independently self-delimiting. Out-of-range prefixes
saturate; actual row controllers use only indices through the field count. -/
private def clRowPrefix {l : ℕ} (w : Fin l → List Bool) : ℕ → List Bool
  | 0 => []
  | j + 1 => clRowPrefix w j ++ if h : j < l then pairEncode (w ⟨j, h⟩) [] else []

/-- All row fields are copied by one finite controller, with an explicit
sequential-write and source-rewind ledger. No indexed access to a stored
word is assumed: selecting a tape is a fixed finite-control operation.
**Proof sketch.** Induct over the fixed number of tapes. Each field uses
the previous native first-return copier and one dispatch, costing at most
three times its width plus four. Concatenate exact whole-configuration
endpoints and the accumulated self-delimiting words. -/
private lemma clRow_prefix_run {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin l → List Bool) (record : List Bool) (W : ℕ)
    (hW : ∀ i, (w i).length ≤ W) : ∀ j (hj : j ≤ l),
    ∃ t ≤ j * (3 * W + 4),
      (clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t =
        clRowCfg x p ⟨j, by omega⟩ 0 w (record ++ clRowPrefix w j) := by
  intro j
  induction j with
  | zero => intro hj; exact ⟨0, by simp, by simp [clRowPrefix]⟩
  | succ j ih =>
    intro hj
    obtain ⟨t, ht, he⟩ := ih (by omega)
    let i : Fin l := ⟨j, by omega⟩
    obtain ⟨s, hs, _, he'⟩ := clRow_field x p i w (record ++ clRowPrefix w j)
    refine ⟨t + s, ?_, ?_⟩
    · have := hW i
      calc
        t + s ≤ j * (3 * W + 4) + (3 * W + 4) := by omega
        _ = (j + 1) * (3 * W + 4) := by ring
    · rw [MultiTapeTM.runFrom_add, he]
      change (clRowTM l).tm.runFrom (clRowCfg x p i.castSucc 0 w _) s = _
      rw [he']
      simp [clRowPrefix, show j < l by omega, List.append_assoc, i]

/-- A complete row really resides on the administrative tape after a
bounded native run; every source counter is unchanged and its head is zero. -/
private lemma clRow_stored {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin l → List Bool) (record : List Bool) (W : ℕ)
    (hW : ∀ i, (w i).length ≤ W) :
    ∃ t ≤ l * (3 * W + 4),
      (clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t =
        clRowCfg x p (Fin.last l) 0 w (record ++ clRowPrefix w l) :=
  clRow_prefix_run x p w record W hW l le_rfl

/-- Completed row controllers idle on the whole stored configuration. -/
private lemma clRow_idle {l : ℕ} {x : List Bool}
    (c : Cfg (clRowTM l).k Bool (clRowTM l).State x)
    (hc : c.state = some (Fin.last l, (0 : Fin 5))) : (clRowTM l).tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  simp only [clRowTM, Fin.val_last, Nat.lt_irrefl, dite_false]
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- A row is completely stored at the actual first end-of-row return.
The fixed positive field count makes that return strictly positive.
**Proof sketch.** Minimize the completed-control occurrence below the
proved copying bound. The completed controller is absorbing, so its
first occurrence has the exact word and all the restored counter heads. -/
private lemma clRow_first {l : ℕ} (hl : 0 < l) (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin l → List Bool) (record : List Bool) (W : ℕ)
    (hW : ∀ i, (w i).length ≤ W) :
    ∃ t ≤ l * (3 * W + 4), 0 < t ∧
      (∀ j, j < t → ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) j).state ≠
        some (Fin.last l, (0 : Fin 5))) ∧
      (clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t =
        clRowCfg x p (Fin.last l) 0 w (record ++ clRowPrefix w l) := by
  obtain ⟨B, hB, he⟩ := clRow_stored x p w record W hW
  have hex : ∃ t, t ≤ B ∧ ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t).state =
      some (Fin.last l, (0 : Fin 5)) := ⟨B, le_rfl, by rw [he]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hs := ht.2
    change ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t).state =
      some (Fin.last l, (0 : Fin 5)) at hs
    rw [hz, MultiTapeTM.runFrom_zero] at hs
    have hh := congrArg (fun z => z.map (fun q => q.1.val)) hs
    simp [clRowCfg] at hh
    omega
  refine ⟨t, ht.1.trans hB, hp, ?_, ?_⟩
  · intro j hj hs
    have := Nat.find_min' hex (show j ≤ B ∧
      ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) j).state =
        some (Fin.last l, (0 : Fin 5)) from ⟨by omega, hs⟩)
    omega
  · have hstay := Function.iterate_fixed (clRow_idle _ ht.2) (B - t)
    change (clRowTM l).tm.runFrom ((clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t)
      (B - t) = (clRowTM l).tm.runFrom (clRowCfg x p 0 0 w record) t at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans he

/-- A row's stored field lengths have their exact doubled-bit-plus-separator
ledger, independently of the native copying runtime. -/
private lemma clRowPrefix_length {l : ℕ} (w : Fin l → List Bool) (W : ℕ)
    (hW : ∀ i, (w i).length ≤ W) : ∀ j,
    (clRowPrefix w j).length ≤ j * (2 * W + 2) := by
  intro j
  induction j with
  | zero => simp [clRowPrefix]
  | succ j ih =>
    simp only [clRowPrefix, List.length_append]
    split
    · rename_i h
      have hw := hW ⟨j, h⟩
      have len (z : List Bool) : (pairEncode z []).length = 2 * z.length + 2 := by
        induction z with
        | nil => simp [pairEncode]
        | cons b z ih => simp [pairEncode, List.flatMap_cons, List.append_assoc] at ⊢ ih; omega
      rw [len]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · simp only [List.length_nil]
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The binary widths fit the elapsed-time bound, using the inherited
width theorem. This is a coarse bound for native scans, not an alternative
representation: all stored movement counts remain canonical binary. -/
private lemma clElapsed_width (n t : ℕ) (hn : n ≤ t) : n.bits.length ≤ t :=
  clCount_width n t (lt_of_le_of_lt hn (Nat.lt_two_pow_self (n := t)))

/-- A deterministic valid virtual-input tag, used only in the pure record
specification. At an interior cell either tag gives the same displacement. -/
private def clTag {n : ℕ} (p : Fin (n + 2)) : Bool := decide (p.val ≠ 0)

/-- The deterministic tag identifies both boundary blanks correctly. -/
private lemma clTag_valid {n : ℕ} (p : Fin (n + 2)) : FinTM.VirtualTag p (clTag p) := by
  constructor <;> intro h <;> simp [clTag, h]

/-- Integer displacements distinguish the three native move symbols. -/
private lemma clMove_inj (a b : SignType) (h : (a : ℤ) = (b : ℤ)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- All valid tags choose the same actual source displacement. -/
private lemma clMoves_tag (M : FinTM Bool) {y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b) :
    clMoves M c.state b c.inputSymbol c.workTapeSymbols =
      clMoves M c.state (clTag c.inputPos) c.inputSymbol c.workTapeSymbols := by
  funext i
  apply clMove_inj
  have h1 := clMoves_correct M c b hb i
  have h2 := clMoves_correct M c (clTag c.inputPos) (clTag_valid _) i
  omega

/-- Canonical pure movement counts at each source time. These count actual
clamped moves, not requested outward moves, and remain frozen after halt. -/
private def clCounts (M : FinTM Bool) (y : List Bool) :
    ℕ → Fin ((1 + M.k) + (1 + M.k)) → ℕ
  | 0 => fun _ => 0
  | t + 1 =>
    let c := M.tm.runFrom (M.tm.initCfg y) t
    clAdvance (clMoves M c.state (clTag c.inputPos) c.inputSymbol c.workTapeSymbols)
      (clCounts M y t)

/-- A native round's actual tag yields exactly the specified next counters. -/
private lemma clCounts_succ (M : FinTM Bool) (y : List Bool) (t : ℕ)
    (b : Bool) (hb : FinTM.VirtualTag (M.tm.runFrom (M.tm.initCfg y) t).inputPos b) :
    clAdvance (clMoves M (M.tm.runFrom (M.tm.initCfg y) t).state b
      (M.tm.runFrom (M.tm.initCfg y) t).inputSymbol
      (M.tm.runFrom (M.tm.initCfg y) t).workTapeSymbols) (clCounts M y t) =
        clCounts M y (t + 1) := by
  rw [clMoves_tag M _ b hb]
  rfl

/-- Every movement counter is bounded by elapsed source time. -/
private lemma clCounts_bound (M : FinTM Bool) (y : List Bool) (t : ℕ) :
    ∀ i, clCounts M y t i ≤ t := by
  induction t with
  | zero => intro i; rfl
  | succ t ih => exact clAdvance_bound _ _ t ih

/-- The stored count pairs specify precisely the signed work positions and
the shifted, clamped input position at each source time. -/
private lemma clCounts_positions (M : FinTM Bool) (y : List Bool) (t : ℕ)
    (i : Fin (1 + M.k)) :
    clSigned (clCounts M y t) i = clPositions M (M.tm.runFrom (M.tm.initCfg y) t) i := by
  induction t with
  | zero =>
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [clCounts, clSigned, clPositions, MultiTapeTM.initCfg, Cfg.init,
        -Fin.natAdd_eq_addNat]
  | succ t ih =>
    change clSigned (clAdvance _ _) i = _
    rw [clSigned_advance, ih, MultiTapeTM.runFrom_succ_eq_step']
    exact (clMoves_correct M _ _ (clTag_valid _) i).symm

/-- Number of binary movement-count fields in each stored row. -/
private abbrev clRecFields (M : FinTM Bool) : ℕ := (1 + M.k) + (1 + M.k)

/-- The serialized trajectory prefix contains exactly rows `0,...,t-1`.
The complete inclusive trajectory at horizon `T` uses prefix length `T+1`. -/
private def clRecords (M : FinTM Bool) (y : List Bool) : ℕ → List Bool
  | 0 => []
  | t + 1 => clRecords M y t ++
      clRowPrefix (fun i => (clCounts M y t i).bits) (clRecFields M)

/-- Finite phases of the actual recorder: row copying, clock test,
source-step release, running counter update, and completed live return. -/
private abbrev clRecState (M : FinTM Bool) : Type :=
  (Option M.State × Bool × (clRowTM (clRecFields M)).State) ⊕
    ((Option M.State × Bool) ⊕ ((Option M.State × Bool) ⊕ ((clTrackTM M).State ⊕ Unit)))



/-- The RecTrack layout selects its bank exactly and protects the remaining slots. -/
private def clRecTrackSelect (M : FinTM Bool) :
    clPlacement (clTrackTM M).k (clRecFields M + (1 + (1 + (1 + M.k)))) :=
  (clPlacement.refl (clRecFields M)).sum
    ((clPlacement.trailing 1 (1 + M.k)).comp (clPlacement.trailing 1 (1 + (1 + M.k))))

/-- The RecRow layout selects its bank exactly and protects the remaining slots. -/
private def clRecRowSelect (M : FinTM Bool) :
    clPlacement (clRowTM (clRecFields M)).k (clRecFields M + (1 + (1 + (1 + M.k)))) :=
  (clPlacement.refl (clRecFields M)).sum
    ((clPlacement.refl 1).sum (clPlacement.empty (1 + (1 + M.k))))

/-- The unary clock has its own slot, disjoint from source and row-copy banks. -/
private def clRecClockIndex (M : FinTM Bool) :
    Fin (clRecFields M + (1 + (1 + (1 + M.k)))) :=
  Fin.natAdd (clRecFields M) (Fin.natAdd 1 (Fin.castAdd (1 + M.k) (0 : Fin 1)))

/-- Native inclusive trajectory recorder. It stores the current row before
testing the clock, so the initial and final rows are both present. Every
counter/copy transition is outside source time. -/
private def clRecTM (M : FinTM Bool) : FinTM Bool where
  k := clRecFields M + (1 + (1 + (1 + M.k)))
  State := clRecState M
  tm := {
    q₀ := .inl (some M.tm.q₀, true, (0, 0))
    tr := fun q inp work => match q with
      | .inl (s, b, r) =>
        if r = (Fin.last (clRecFields M), 0) then
          FinTM.controlAction 0 (some (.inr (.inl (s, b))))
        else clPlacedAction (clRecRowSelect M) (fun r => .inl (s, b, r)) r ((clRowTM (clRecFields M)).tm.tr r inp (fun j => work ((clRecRowSelect M).index j)))
      | .inr (.inl (s, b)) =>
        if work (clRecClockIndex M) = none then
          FinTM.controlAction 0 (some (.inr (.inr (.inr (.inr ())))))
        else ⟨0, fun i => (none, if i = clRecClockIndex M then .pos else 0),
          none, some (.inr (.inr (.inl (s, b))))⟩
      | .inr (.inr (.inl (s, b))) =>
        clPlacedAction (clRecTrackSelect M) (fun r => .inr (.inr (.inr (.inl r)))) (s, b, none) ((clTrackTM M).tm.tr (s, b, none) inp (fun j => work ((clRecTrackSelect M).index j)))
      | .inr (.inr (.inr (.inl r))) =>
        if r.2.2 = none then
          FinTM.controlAction 0 (some (.inl (r.1, r.2.1, (0, 0))))
        else clPlacedAction (clRecTrackSelect M) (fun r => .inr (.inr (.inr (.inl r)))) r ((clTrackTM M).tm.tr r inp (fun j => work ((clRecTrackSelect M).index j)))
      | .inr (.inr (.inr (.inr _))) => FinTM.controlAction 0 (some q) }

/-- Whole recorder configuration: canonical movement counters, the actual
stored record prefix, a unary clock at logical time, and the complete
virtual reference bank. Only the record and clock heads need not be zero. -/
private def clRecCfg (M : FinTM Bool) {x y : List Bool}
    (q : clRecState M) (c : Cfg M.k Bool M.State y)
    (n : Fin (clRecFields M) → ℕ) (record : List Bool) (T t : ℕ) :
    Cfg (clRecTM M).k Bool (clRecTM M).State x :=
  ⟨some q, 1,
    FinTM.tapeBlocks (fun i => FinTM.bufferTape (n i).bits) (FinTM.bufferTape record)
      (FinTM.tapeBlocks (fun _ : Fin 1 => FinTM.bufferTape (List.replicate T true))
        (FinTM.bufferTape y) c.workTapes),
    FinTM.tapeBlocks (fun _ => 0) (record.length : ℤ)
      (FinTM.tapeBlocks (fun _ : Fin 1 => (t : ℤ)) ((c.inputPos.val : ℤ) - 1) c.workTapePos), []⟩

/-- Relocated row copying agrees with the complete recorder seam. Its
inactive bank includes every source cell and head and the unchanged clock. -/
private lemma clRec_row_frame (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (n : Fin (clRecFields M) → ℕ)
    (record : List Bool) (T t : ℕ) (i : Fin (clRecFields M + 1)) (q : Fin 5) :
    clPlacedCfg (clRecRowSelect M) (fun r => (Sum.inl (c.state, b, r) : clRecState M))
      (clRecCfg M (x := x) (.inl (c.state, b, (i, q))) c n record T t).workTapes
      (clRecCfg M (x := x) (.inl (c.state, b, (i, q))) c n record T t).workTapePos
      (clRowCfg x 1 i q (fun j => (n j).bits) record) =
        clRecCfg M (x := x) (.inl (c.state, b, (i, q))) c n record T t := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro j; simp [clRecRowSelect, clRowCfg, clRecCfg, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j
        have hj : j = 0 := Fin.eq_zero j
        subst j
        simp [clRecRowSelect, clRowCfg, clRecCfg, -Fin.natAdd_eq_addNat]
      · intro j; simp [clRecRowSelect, clRowCfg, clRecCfg, -Fin.natAdd_eq_addNat]

/-- Row-frame inactive tapes do not depend on record contents or row control.
This permits consecutive fields and rows to append without changing source time. -/
private lemma clRec_row_inactive (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (n : Fin (clRecFields M) → ℕ)
    (record record' : List Bool) (T t : ℕ)
    (r r' : (clRowTM (clRecFields M)).State)
    (z : Cfg (clRowTM (clRecFields M)).k Bool (clRowTM (clRecFields M)).State x) :
    clPlacedCfg (clRecRowSelect M) (fun u => (Sum.inl (c.state, b, u) : clRecState M))
      (clRecCfg M (x := x) (.inl (c.state, b, r)) c n record T t).workTapes
      (clRecCfg M (x := x) (.inl (c.state, b, r)) c n record T t).workTapePos z =
    clPlacedCfg (clRecRowSelect M) (fun u => (Sum.inl (c.state, b, u) : clRecState M))
      (clRecCfg M (x := x) (.inl (c.state, b, r')) c n record' T t).workTapes
      (clRecCfg M (x := x) (.inl (c.state, b, r')) c n record' T t).workTapePos z := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro j; simp [clRecRowSelect]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [clRecRowSelect, clRecCfg, -Fin.natAdd_eq_addNat]

/-- Store one complete row inside the recorder and dispatch to its clock
test. All source storage and the logical clock are unchanged throughout
this administrative segment.
**Proof sketch.** Relocate the row controller into the counter and record bank, framing the unary clock and the entire represented source. Its first completion contains the extended record; one control-only transition enters the clock test. -/
private lemma clRec_copy (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (n : Fin (clRecFields M) → ℕ)
    (record : List Bool) (T t W : ℕ) (hW : ∀ i, (n i).bits.length ≤ W) :
    ∃ s ≤ clRecFields M * (3 * W + 4) + 1,
      (clRecTM M).tm.runFrom
        (clRecCfg M (x := x) (.inl (c.state, b, (0, 0))) c n record T t) s =
      clRecCfg M (x := x) (.inr (.inl (c.state, b))) c n
        (record ++ clRowPrefix (fun i => (n i).bits) (clRecFields M)) T t := by
  obtain ⟨s, hs, _, hf, he⟩ := clRow_first (by dsimp [clRecFields]; omega) x 1
    (fun i => (n i).bits) record W hW
  let start := clRecCfg M (x := x) (.inl (c.state, b, (0, 0))) c n record T t
  let record' := record ++ clRowPrefix (fun i => (n i).bits) (clRecFields M)
  have lift := clPlaced_run (clRowTM (clRecFields M)).tm (clRecTM M).tm (clRecRowSelect M) (fun r => (Sum.inl (c.state, b, r) : clRecState M)) (by intro a b h; cases h; rfl)
    (fun r => r ≠ (Fin.last (clRecFields M), (0 : Fin 5)))
    (fun _ hr _ _ => if_neg hr)
    start.workTapes start.workTapePos
    (clRowCfg x 1 0 0 (fun i => (n i).bits) record) s
    (by intro j hj q hq heq; subst q; exact hf j hj hq)
  rw [he] at lift
  have hend := (clRec_row_inactive M c b n record record' T t
    (0, 0) (Fin.last (clRecFields M), 0)
    (clRowCfg x 1 (Fin.last (clRecFields M)) 0 (fun i => (n i).bits) record')).trans
      (clRec_row_frame M c b n record' T t (Fin.last (clRecFields M)) 0)
  have run : (clRecTM M).tm.runFrom start s =
      clRecCfg M (x := x) (.inl (c.state, b, (Fin.last (clRecFields M), 0))) c n record' T t :=
    (congrArg (fun z => (clRecTM M).tm.runFrom z s)
      (clRec_row_frame M c b n record T t 0 0)).symm.trans (lift.trans hend)
  refine ⟨s + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', run]
  simp only [MultiTapeTM.step, clRecCfg, clRecTM, if_true]
  rw [FinTM.controlAction_apply, moveInputPos_zero]

/-- Left and right slots of a disjoint tape bank cannot coincide. -/
private lemma clLeft_ne_right {a b : ℕ} (i : Fin a) (j : Fin b) :
    Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have hh := congrArg Fin.val h
  have hi := i.isLt
  change i.val = a + j.val at hh
  omega

/-- The symmetric tape-slot separation used by clock dispatch. -/
private lemma clRight_ne_left {a b : ℕ} (i : Fin a) (j : Fin b) :
    Fin.natAdd a j ≠ Fin.castAdd b i := (clLeft_ne_right i j).symm

/-- A nonempty unary-clock cell authorizes one future source step. The
clock move itself changes no source head and appends no record bits.
**Proof sketch.** At a time strictly below the horizon the unary clock reads true. The transition advances only that clock, leaving all counter, record, virtual-input and source tapes fixed. -/
private lemma clRec_tick (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (n : Fin (clRecFields M) → ℕ)
    (record : List Bool) (T t : ℕ) (ht : t < T) :
    (clRecTM M).tm.step
      (clRecCfg M (x := x) (.inr (.inl (c.state, b))) c n record T t) =
      clRecCfg M (x := x) (.inr (.inr (.inl (c.state, b)))) c n record T (t + 1) := by
  have hr : (clRecCfg M (x := x) (.inr (.inl (c.state, b))) c n record T t).workTapeSymbols
      (clRecClockIndex M) = some true := by
    simp [clRecCfg, clRecClockIndex, Cfg.workTapeSymbols, ht, -Fin.natAdd_eq_addNat]
  change ((clRecTM M).tm.tr (.inr (.inl (c.state, b))) _ _).apply _ = _
  simp only [clRecTM, hr, reduceCtorEq, if_false]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i; simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right, clRight_ne_left, -Fin.natAdd_eq_addNat]
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i; simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right, clRight_ne_left, -Fin.natAdd_eq_addNat]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right, clRight_ne_left, -Fin.natAdd_eq_addNat]
      · intro i; simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right, clRight_ne_left, -Fin.natAdd_eq_addNat]

/-- After recording the horizon row, the exhausted clock dispatches
silently to a live return. No extra source transition can occur. -/
private lemma clRec_stop (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (n : Fin (clRecFields M) → ℕ)
    (record : List Bool) (T : ℕ) :
    (clRecTM M).tm.step
      (clRecCfg M (x := x) (.inr (.inl (c.state, b))) c n record T T) =
      clRecCfg M (x := x) (.inr (.inr (.inr (.inr ())))) c n record T T := by
  have hr : (clRecCfg M (x := x) (.inr (.inl (c.state, b))) c n record T T).workTapeSymbols
      (clRecClockIndex M) = none := by
    simp [clRecCfg, clRecClockIndex, Cfg.workTapeSymbols, -Fin.natAdd_eq_addNat]
  change ((clRecTM M).tm.tr (.inr (.inl (c.state, b))) _ _).apply _ = _
  simp only [clRecTM, hr, if_true]
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- Source/counter relocation preserves the complete record and unary clock. -/
private lemma clRec_track_frame (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (n : Fin (clRecFields M) → ℕ)
    (record : List Bool) (T t : ℕ) :
    clPlacedCfg (clRecTrackSelect M)
      (fun r => (Sum.inr (.inr (.inr (.inl r))) : clRecState M))
      (clRecCfg M (x := x) (.inr (.inr (.inr (.inl (c.state, b, none))))) c n record T t).workTapes
      (clRecCfg M (x := x) (.inr (.inr (.inr (.inl (c.state, b, none))))) c n record T t).workTapePos
      (clTrackCfg M (x := x) c b n) =
        clRecCfg M (x := x) (.inr (.inr (.inr (.inl (c.state, b, none))))) c n record T t := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro j; simp [clRecTrackSelect, clTrackCfg, clRefCfg, clRecCfg,
        -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j; simp [clRecTrackSelect]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j; simp [clRecTrackSelect]
        · intro j; simp [clRecTrackSelect, clTrackCfg, clRefCfg, clRecCfg, FinTM.tapeBlocks,
            -Fin.natAdd_eq_addNat]

/-- The inactive source-step frame depends only on the stored record and
clock, so source writes and movement-count updates do not affect it. -/
private lemma clRec_track_inactive (M : FinTM Bool) {x y : List Bool}
    (c c' : Cfg M.k Bool M.State y) (b b' : Bool)
    (n n' : Fin (clRecFields M) → ℕ) (record : List Bool) (T t : ℕ)
    (z : Cfg (clTrackTM M).k Bool (clTrackTM M).State x) :
    clPlacedCfg (clRecTrackSelect M)
      (fun r => (Sum.inr (.inr (.inr (.inl r))) : clRecState M))
      (clRecCfg M (x := x) (.inr (.inr (.inr (.inl (c.state, b, none))))) c n record T t).workTapes
      (clRecCfg M (x := x) (.inr (.inr (.inr (.inl (c.state, b, none))))) c n record T t).workTapePos z =
    clPlacedCfg (clRecTrackSelect M)
      (fun r => (Sum.inr (.inr (.inr (.inl r))) : clRecState M))
      (clRecCfg M (x := x) (.inr (.inr (.inr (.inl (c'.state, b', none))))) c' n' record T t).workTapes
      (clRecCfg M (x := x) (.inr (.inr (.inr (.inl (c'.state, b', none))))) c' n' record T t).workTapePos z := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro j; simp [clRecTrackSelect]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j; simp [clRecTrackSelect, clRecCfg, -Fin.natAdd_eq_addNat]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [clRecTrackSelect, clRecCfg, -Fin.natAdd_eq_addNat]

/-- Release executes the actual first source action before any exit test.
**Proof sketch.** The selected tape exports identify the source reads; the
one-action R1 consequence supplies the complete next configuration. -/
private lemma clPlaced_release {k l : ℕ} {S H : Type} {x : List Bool}
    (src : MultiTapeTM k Bool S) (host : MultiTapeTM l Bool H)
    (slots : clPlacement k l) (emb : S → H) (release : H) (q : S)
    (htr : ∀ inp work, host.tr release inp work =
      clPlacedAction slots emb q (src.tr q inp (fun i => work (slots.index i))))
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c : Cfg k Bool S x) (hc : c.state = some q) :
    host.step {clPlacedCfg slots emb tapes heads c with state := some release} =
      clPlacedCfg slots emb tapes heads (src.step c) := by
  have symbols : (fun i => (clPlacedCfg slots emb tapes heads c).workTapeSymbols
      (slots.index i)) = c.workTapeSymbols := by
    funext i
    change (embedEmitCfg slots.index tapes heads [] c).workTapeSymbols (slots.index i) = _
    simp only [Cfg.workTapeSymbols, embedEmitCfg_selected_tape, embedEmitCfg_selected_pos]
  change (host.tr release c.inputSymbol _).apply _ = _
  rw [htr]
  change (clPlacedAction slots emb q (src.tr q c.inputSymbol
    (fun i => (clPlacedCfg slots emb tapes heads c).workTapeSymbols (slots.index i)))).apply _ = _
  rw [symbols]
  simpa only [MultiTapeTM.step, hc, Cfg.mapState, Action.apply] using
    clPlaced_apply slots emb q tapes heads (src.tr q c.inputSymbol c.workTapeSymbols) c

/-- The native recorder executes one source transition and its full signed
counter update, then dispatches to the next row-copy state. Record and clock
contents and heads are framed throughout this segment.
**Proof sketch.** Execute the source action before testing for the tracker anchor, then lift the tracker through its strictly interior bank phases. Its completed return restores all counter heads and preserves the stored record and clock; charge the final dispatch into row copying. -/
private lemma clRec_advance (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (n : Fin (clRecFields M) → ℕ) (record : List Bool) (T t W : ℕ)
    (hW : ∀ i, (n i).bits.length ≤ W) :
    ∃ s ≤ 2 * W + 5, ∃ b', FinTM.VirtualTag (M.tm.step c).inputPos b' ∧
      (clRecTM M).tm.runFrom
        (clRecCfg M (x := x) (.inr (.inr (.inl (c.state, b)))) c n record T t) s =
      clRecCfg M (x := x) (.inl ((M.tm.step c).state, b', (0, 0))) (M.tm.step c)
        (clAdvance (clMoves M c.state b c.inputSymbol c.workTapeSymbols) n) record T t := by
  obtain ⟨s, hs, hp, hf, b', hb', he⟩ := clTrack_round M (x := x) c b hb n W hW
  let n' := clAdvance (clMoves M c.state b c.inputSymbol c.workTapeSymbols) n
  let frame := clRecCfg M (x := x) (.inr (.inr (.inr (.inl (c.state, b, none))))) c n record T t
  let emb := fun r => (Sum.inr (.inr (.inr (.inl r))) : clRecState M)
  let start := clTrackCfg M (x := x) c b n
  have release := clPlaced_release (clTrackTM M).tm (clRecTM M).tm
    (clRecTrackSelect M) emb
    (.inr (.inr (.inl (c.state, b)))) (c.state, b, none)
    (by intro inp work; rfl) frame.workTapes frame.workTapePos start rfl
  have rframe := clRec_track_frame M (x := x) c b n record T t
  rw [rframe] at release
  change (clRecTM M).tm.step
    (clRecCfg M (x := x) (.inr (.inr (.inl (c.state, b)))) c n record T t) = _ at release
  have lift := clPlaced_run (clTrackTM M).tm (clRecTM M).tm (clRecTrackSelect M) emb (by intro a b h; cases h; rfl)
    (fun r => r.2.2 ≠ none)
    (by intro r hr inp work; simp only [clRecTM, emb, if_neg hr])
    frame.workTapes frame.workTapePos ((clTrackTM M).tm.step start) (s - 1)
    (by
      intro j hj q hq
      have hv := hf (j + 1) (by omega) (by omega)
      rw [MultiTapeTM.runFrom_succ_eq_step] at hv
      obtain ⟨u, tag, qs, hu⟩ := hv
      have hqq : q = (u, tag, some qs) := Option.some.inj (hq.symm.trans hu)
      rw [hqq]
      simp)
  have run : (clRecTM M).tm.runFrom
      (clRecCfg M (x := x) (.inr (.inr (.inl (c.state, b)))) c n record T t) s =
      clPlacedCfg (clRecTrackSelect M) emb frame.workTapes frame.workTapePos
        (clTrackCfg M (x := x) (M.tm.step c) b' n') := by
    rw [show s = (s - 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step, release, lift]
    rw [← MultiTapeTM.runFrom_succ_eq_step, Nat.sub_add_cancel hp, he]
  have hend := (clRec_track_inactive M c (M.tm.step c) b b' n n' record T t
    (clTrackCfg M (x := x) (M.tm.step c) b' n')).trans
      (clRec_track_frame M (x := x) (M.tm.step c) b' n' record T t)
  have run' := run.trans hend
  refine ⟨s + 1, by omega, b', hb', ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', run']
  simp only [MultiTapeTM.step, clRecCfg, clRecTM, if_true]
  rw [FinTM.controlAction_apply, moveInputPos_zero]

/-- At every logical time through the horizon, one native recorder holds
all strictly earlier rows and is ready to store the current row. This
invariant concerns actual tape contents, not merely a running schedule.
**Proof sketch.** Store the current row using native copies, test and
advance the unary clock once, execute one faithful source/counter round,
and dispatch back. The previous phase contracts preserve every inactive
bank, and the deterministic displacement lemma identifies the new words.
Each cycle charges row writes, all rewinds, the clock transition, the
source transition, counter scans, and all three dispatches. -/
private lemma clRec_prefix (M : FinTM Bool) (x y : List Bool) (T : ℕ) :
    ∀ j, j ≤ T → ∃ s ≤ j * (clRecFields M * (3 * T + 4) + 2 * T + 7), ∃ b,
      FinTM.VirtualTag (M.tm.runFrom (M.tm.initCfg y) j).inputPos b ∧
      (clRecTM M).tm.runFrom
        (clRecCfg M (x := x) (.inl (some M.tm.q₀, true, (0, 0)))
          (M.tm.initCfg y) (fun _ => 0) [] T 0) s =
      clRecCfg M (x := x)
        (.inl ((M.tm.runFrom (M.tm.initCfg y) j).state, b, (0, 0)))
        (M.tm.runFrom (M.tm.initCfg y) j) (clCounts M y j) (clRecords M y j) T j := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, by simp, true, ?_, rfl⟩
    simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]
  | succ j ih =>
    intro hj
    obtain ⟨s, hs, b, hb, he⟩ := ih (by omega)
    let c := M.tm.runFrom (M.tm.initCfg y) j
    have widths (i : Fin (clRecFields M)) : (clCounts M y j i).bits.length ≤ T :=
      clElapsed_width _ T ((clCounts_bound M y j i).trans (by omega))
    obtain ⟨a, ha, hea⟩ := clRec_copy M (x := x) c b (clCounts M y j)
      (clRecords M y j) T j T widths
    have tick := clRec_tick M (x := x) c b (clCounts M y j) (clRecords M y (j + 1)) T j (by omega)
    obtain ⟨v, hv, b', hb', hev⟩ := clRec_advance M (x := x) c b hb
      (clCounts M y j) (clRecords M y (j + 1)) T (j + 1) T widths
    refine ⟨s + (a + (1 + v)), ?_, b', ?_, ?_⟩
    · calc
        s + (a + (1 + v)) ≤ j * (clRecFields M * (3 * T + 4) + 2 * T + 7) +
          (clRecFields M * (3 * T + 4) + 2 * T + 7) := by omega
        _ = (j + 1) * (clRecFields M * (3 * T + 4) + 2 * T + 7) := by ring
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb'
    · rw [MultiTapeTM.runFrom_add, he, MultiTapeTM.runFrom_add, hea]
      change (clRecTM M).tm.runFrom
        (clRecCfg M (x := x) (.inr (.inl (c.state, b))) c (clCounts M y j)
          (clRecords M y (j + 1)) T j) (1 + v) = _
      rw [Nat.add_comm 1 v, MultiTapeTM.runFrom_succ_eq_step, tick, hev,
        clCounts_succ M y j b hb, MultiTapeTM.runFrom_succ_eq_step']

/-- The actual native recorder stores every row `0,...,T`, returns with
an empty physical output, and never substitutes a running-position invariant
for stored data. Its source state is the exact horizon configuration.
The startup seam here is explicitly prepared; native input parsing and
installation of that seam remain separate obligations. -/
private lemma clRec_complete (M : FinTM Bool) (x y : List Bool) (T : ℕ) :
    ∃ s ≤ (T + 1) * (clRecFields M * (3 * T + 4) + 2 * T + 7),
      (clRecTM M).tm.runFrom
        (clRecCfg M (x := x) (.inl (some M.tm.q₀, true, (0, 0)))
          (M.tm.initCfg y) (fun _ => 0) [] T 0) s =
      clRecCfg M (x := x) (.inr (.inr (.inr (.inr ()))))
        (M.tm.runFrom (M.tm.initCfg y) T) (clCounts M y T) (clRecords M y (T + 1)) T T := by
  obtain ⟨s, hs, b, _, he⟩ := clRec_prefix M x y T T le_rfl
  obtain ⟨a, ha, hea⟩ := clRec_copy M (x := x)
    (M.tm.runFrom (M.tm.initCfg y) T) b (clCounts M y T) (clRecords M y T) T T T
    (fun i => clElapsed_width _ T (clCounts_bound M y T i))
  refine ⟨s + (a + 1), ?_, ?_⟩
  · rw [Nat.add_mul, Nat.one_mul]
    omega
  · rw [MultiTapeTM.runFrom_add, he, MultiTapeTM.runFrom_succ_eq_step', hea]
    exact clRec_stop M _ b (clCounts M y T) (clRecords M y (T + 1)) T

/-- Prepared initialization of the entire recorder, including blank
movement counters, empty record tape, unary clock at zero, and the source's
virtual input and blank work bank. This is not a claim about `initCfg`. -/
private lemma clRec_prepared (M : FinTM Bool) (x y : List Bool) (T : ℕ) :
    Cfg.ofWords (input := x) (clRecTM M).tm.q₀
      (FinTM.tapeBlocks (fun _ : Fin (clRecFields M) => []) []
        (FinTM.tapeBlocks (fun _ : Fin 1 => List.replicate T true) y (fun _ => []))) =
    clRecCfg M (x := x) (.inl (some M.tm.q₀, true, (0, 0)))
      (M.tm.initCfg y) (fun _ => 0) [] T 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i; simp [Cfg.ofWords, clRecCfg]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [Cfg.ofWords, clRecCfg]
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [Cfg.ofWords, clRecCfg]
        · intro i
          refine Fin.addCases ?_ ?_ i <;> intro i <;>
            simp [Cfg.ofWords, clRecCfg, MultiTapeTM.initCfg, Cfg.init]

/-- The complete stored-row ledger is polynomial in the source horizon.
This bounds native recording work, separately from formula output size. -/
private lemma clRec_cost_bound (M : FinTM Bool) (T : ℕ) :
    (T + 1) * (clRecFields M * (3 * T + 4) + 2 * T + 7) ≤
      (4 * clRecFields M + 7) * (T + 1) ^ 2 := by
  have h : clRecFields M * (3 * T + 4) + 2 * T + 7 ≤
      (4 * clRecFields M + 7) * (T + 1) := by
    calc
      _ ≤ clRecFields M * (4 * (T + 1)) + 7 * (T + 1) := by
        have := Nat.mul_le_mul_left (clRecFields M) (show 3 * T + 4 ≤ 4 * (T + 1) by omega)
        omega
      _ = _ := by ring
  calc
    _ ≤ (T + 1) * ((4 * clRecFields M + 7) * (T + 1)) := Nat.mul_le_mul_left _ h
    _ = _ := by ring

/-- Numeric value of a Boolean digit. -/
private def clBit (b : Bool) : ℕ := if b then 1 else 0

/-- Little-endian value of an arbitrary binary word, including padded words. -/
private def clNum (w : List Bool) : ℕ := w.foldr Nat.bit 0

/-- Canonical inherited counter words decode to their actual values. -/
private lemma clNum_bits (n : ℕ) : clNum n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [clNum]
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn]; simpa [clNum] using congrArg (Nat.bit b) ih

/-- A word's low digit and remaining high digits have the usual binary value. -/
private lemma clNum_head (w : List Bool) :
    clNum w = 2 * clNum w.tail + clBit (w.head?.getD false) := by
  cases w with
  | nil => simp [clNum, clBit]
  | cons b w => cases b <;> simp [clNum, clBit, Nat.bit_val]

/-- One finite-control binary addition column: low bit and outgoing carry. -/
private def clAddColumn (c u v : Bool) : Bool × Bool :=
  (Bool.xor u (Bool.xor v c), (u && v) || (u && c) || (v && c))

/-- The finite addition table has its exact binary arithmetic meaning. -/
private lemma clAddColumn_value (c u v : Bool) :
    clBit u + clBit v + clBit c =
      2 * clBit (clAddColumn c u v).2 + clBit (clAddColumn c u v).1 := by
  cases c <;> cases u <;> cases v <;> decide

/-- Simultaneously add two pairs of words and retain equality of all low
bits already scanned. Only three Boolean registers are needed. -/
private def clCmpUpdate (q : Bool × Bool × Bool) (work : Fin 4 → Option Bool) :
    Bool × Bool × Bool :=
  let a := clAddColumn q.1 ((work 0).getD false) ((work 1).getD false)
  let b := clAddColumn q.2.1 ((work 2).getD false) ((work 3).getD false)
  (a.2, b.2, q.2.2 && (a.1 == b.1))

/-- The arithmetic invariant compares remaining high words plus carries,
provided all earlier low digits matched. -/
private def clCmpPred (q : Bool × Bool × Bool) (w : Fin 4 → List Bool) : Prop :=
  q.2.2 = true ∧ clNum (w 0) + clNum (w 1) + clBit q.1 =
    clNum (w 2) + clNum (w 3) + clBit q.2.1

/-- One column preserves exactly the equality being tested.
**Proof sketch.** Expand each number into twice its tail plus its low bit.
The two addition tables expose their outgoing carries. Equality is then
equivalent to equal low bits and equal remaining high sums; unequal low
bits have opposite parity and cannot be repaired by any later column. -/
private lemma clCmpUpdate_spec (q : Bool × Bool × Bool) (w : Fin 4 → List Bool) :
    clCmpPred q w ↔ clCmpPred (clCmpUpdate q (fun i => (w i).head?)) (fun i => (w i).tail) := by
  have h0 := clNum_head (w 0)
  have h1 := clNum_head (w 1)
  have h2 := clNum_head (w 2)
  have h3 := clNum_head (w 3)
  let a := clAddColumn q.1 ((w 0).head?.getD false) ((w 1).head?.getD false)
  let b := clAddColumn q.2.1 ((w 2).head?.getD false) ((w 3).head?.getD false)
  have ha := clAddColumn_value q.1 ((w 0).head?.getD false) ((w 1).head?.getD false)
  have hb := clAddColumn_value q.2.1 ((w 2).head?.getD false) ((w 3).head?.getD false)
  change clBit ((w 0).head?.getD false) + clBit ((w 1).head?.getD false) + clBit q.1 =
    2 * clBit a.2 + clBit a.1 at ha
  change clBit ((w 2).head?.getD false) + clBit ((w 3).head?.getD false) + clBit q.2.1 =
    2 * clBit b.2 + clBit b.1 at hb
  have hsumA : clNum (w 0) + clNum (w 1) + clBit q.1 =
      2 * (clNum (w 0).tail + clNum (w 1).tail + clBit a.2) + clBit a.1 := by omega
  have hsumB : clNum (w 2) + clNum (w 3) + clBit q.2.1 =
      2 * (clNum (w 2).tail + clNum (w 3).tail + clBit b.2) + clBit b.1 := by omega
  have hsplit (A B : ℕ) (u v : Bool) :
      2 * A + clBit u = 2 * B + clBit v ↔ u = v ∧ A = B := by
    cases u <;> cases v <;> simp [clBit] <;> omega
  change (q.2.2 = true ∧ clNum (w 0) + clNum (w 1) + clBit q.1 =
    clNum (w 2) + clNum (w 3) + clBit q.2.1) ↔
    ((q.2.2 && (a.1 == b.1)) = true ∧
      clNum (w 0).tail + clNum (w 1).tail + clBit a.2 =
        clNum (w 2).tail + clNum (w 3).tail + clBit b.2)
  rw [hsumA, hsumB, hsplit]
  simp [Bool.and_eq_true, and_assoc]

/-- Comparator control after scanning a specified number of bit columns. -/
private def clCmpOrbit (w : Fin 4 → List Bool) : ℕ → Bool × Bool × Bool
  | 0 => (false, false, true)
  | j + 1 => clCmpUpdate (clCmpOrbit w j) (fun i => (w i)[j]?)

/-- The column invariant holds after every prefix, including past short
word ends: missing high bits are zeros, never uncharged random access. -/
private lemma clCmpOrbit_spec (w : Fin 4 → List Bool) (j : ℕ) :
    clCmpPred (clCmpOrbit w j) (fun i => (w i).drop j) ↔
      clNum (w 0) + clNum (w 1) = clNum (w 2) + clNum (w 3) := by
  induction j with
  | zero => simp [clCmpOrbit, clCmpPred, clBit]
  | succ j ih =>
    have h := clCmpUpdate_spec (clCmpOrbit w j) (fun i => (w i).drop j)
    simpa [clCmpOrbit, List.tail_drop] using h.symm.trans ih

/-- Maximum width of the four input words; used only in the runtime proof. -/
private def clCmpSize (w : Fin 4 → List Bool) : ℕ := Finset.univ.sup (fun i => (w i).length)

/-- Every comparator word lies within the common scan width. -/
private lemma clCmp_width (w : Fin 4 → List Bool) (i : Fin 4) :
    (w i).length ≤ clCmpSize w := by
  exact Finset.le_sup (f := fun i => (w i).length) (Finset.mem_univ i)

/-- All four aligned reads are blank exactly at or beyond their common
right boundary. A word attaining the maximum prevents an early return. -/
private lemma clCmp_blank (w : Fin 4 → List Bool) (j : ℕ) :
    (∀ i, (w i)[j]? = none) ↔ clCmpSize w ≤ j := by
  simp only [List.getElem?_eq_none_iff, clCmpSize, Finset.sup_le_iff, Finset.mem_univ, true_implies]

/-- At the common right boundary only the two final carry bits remain. -/
private def clCmpVerdict (q : Bool × Bool × Bool) : Bool := q.2.2 && (q.1 == q.2.1)

/-- Boolean digits have equal numeric values exactly when they agree. -/
private lemma clBit_eq (a b : Bool) : clBit a = clBit b ↔ a = b := by
  cases a <;> cases b <;> decide

/-- The final finite-control verdict compares the two complete sums. -/
private lemma clCmpVerdict_spec (w : Fin 4 → List Bool) :
    clCmpVerdict (clCmpOrbit w (clCmpSize w)) = true ↔
      clNum (w 0) + clNum (w 1) = clNum (w 2) + clNum (w 3) := by
  have h := clCmpOrbit_spec w (clCmpSize w)
  have hn : (fun i => (w i).drop (clCmpSize w)) = fun _ => [] := by
    funext i
    exact List.drop_eq_nil_of_le (clCmp_width w i)
  rw [hn] at h
  simpa [clCmpPred, clCmpVerdict, clNum, clBit_eq, Bool.and_eq_true] using h

/-- Actual native four-word comparator. It scans all words in lockstep,
compares addition columns, and rewinds all four heads to zero. No word is
modified and nothing is physically emitted. -/
private def clCmpTM : FinTM Bool where
  k := 4
  State := (Bool × Bool × Bool) ⊕ (Bool ⊕ Bool)
  tm := {
    q₀ := .inl (false, false, true)
    tr := fun q _ work => match q with
      | .inl r =>
        if ∀ i, work i = none then
          ⟨0, fun _ => (none, .neg), none, some (.inr (.inl (clCmpVerdict r)))⟩
        else ⟨0, fun _ => (none, .pos), none, some (.inl (clCmpUpdate r work))⟩
      | .inr (.inl b) =>
        if ∀ i, work i = none then
          ⟨0, fun _ => (none, .pos), none, some (.inr (.inr b))⟩
        else ⟨0, fun _ => (none, .neg), none, some (.inr (.inl b))⟩
      | .inr (.inr _) => FinTM.controlAction 0 (some q) }

/-- Full comparator configuration, including every read-only word and head. -/
private def clCmpCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : clCmpTM.State) (w : Fin 4 → List Bool) (z : ℤ) : Cfg 4 Bool clCmpTM.State x :=
  ⟨some q, p, fun i => FinTM.bufferTape (w i), fun _ => z, []⟩

/-- At a nonnegative aligned head, native reads are precisely the current
bit column of all four complete words. -/
private lemma clCmp_read (x : List Bool) (p : Fin (x.length + 2))
    (q : clCmpTM.State) (w : Fin 4 → List Bool) (j : ℕ) :
    (clCmpCfg x p q w j).workTapeSymbols = fun i => (w i)[j]? := by
  funext i
  simp [clCmpCfg, Cfg.workTapeSymbols]

/-- One forward native step computes exactly one binary comparison column. -/
private lemma clCmp_forward_step (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin 4 → List Bool) (j : ℕ) (hj : j < clCmpSize w) :
    clCmpTM.tm.step (clCmpCfg x p (.inl (clCmpOrbit w j)) w j) =
      clCmpCfg x p (.inl (clCmpOrbit w (j + 1))) w (j + 1) := by
  have hb : ¬ ∀ i, (w i)[j]? = none := by rw [clCmp_blank]; omega
  change (clCmpTM.tm.tr (.inl (clCmpOrbit w j)) _ _).apply _ = _
  simp only [clCmpTM]
  rw [clCmp_read x p _ w j, if_neg hb]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
  funext i
  simp [clCmpCfg, Action.apply]

/-- Every prefix of the forward scan is an actual aligned native run. -/
private lemma clCmp_forward (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin 4 → List Bool) : ∀ j, j ≤ clCmpSize w →
    clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j =
      clCmpCfg x p (.inl (clCmpOrbit w j)) w j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), clCmp_forward_step x p w j (by omega)]
    simp

/-- At the right boundary the comparator stores the final carry verdict
and starts rewinding, even when all four input words are empty. -/
private lemma clCmp_finish_scan (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin 4 → List Bool) :
    clCmpTM.tm.step (clCmpCfg x p (.inl (clCmpOrbit w (clCmpSize w))) w (clCmpSize w)) =
      clCmpCfg x p (.inr (.inl (clCmpVerdict (clCmpOrbit w (clCmpSize w)))))
        w ((clCmpSize w : ℤ) - 1) := by
  have hb := (clCmp_blank w (clCmpSize w)).2 le_rfl
  change (clCmpTM.tm.tr (.inl (clCmpOrbit w (clCmpSize w))) _ _).apply _ = _
  simp only [clCmpTM]
  rw [clCmp_read x p _ w (clCmpSize w), if_pos hb]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
  funext i
  simp [clCmpCfg, Action.apply, sub_eq_add_neg]

/-- Rewind the common scan to zero while preserving all words and the verdict.
**Proof sketch.** At a nonnegative position below the common width at least
one word has a bit, so all heads move left. The first jointly blank position
on this path is minus one; one right move restores all four origins. -/
private lemma clCmp_rewind (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin 4 → List Bool) (b : Bool) : ∀ j, j ≤ clCmpSize w →
    clCmpTM.tm.runFrom (clCmpCfg x p (.inr (.inl b)) w ((j : ℤ) - 1)) (j + 1) =
      clCmpCfg x p (.inr (.inr b)) w 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    have hb : ∀ i, (clCmpCfg x p (.inr (.inl b)) w (-1)).workTapeSymbols i = none := by
      intro i
      simp [clCmpCfg, Cfg.workTapeSymbols]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (clCmpTM.tm.tr (.inr (.inl b)) _ _).apply _ = _
    simp only [clCmpTM]
    have hb' : ∀ i, (clCmpCfg x p (.inr (.inl b)) w (((0 : ℕ) : ℤ) - 1)).workTapeSymbols i = none := hb
    rw [if_pos hb']
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    simp [clCmpCfg, Action.apply]
  | succ j ih =>
    intro hj
    have hb : ¬ ∀ i, (w i)[j]? = none := by rw [clCmp_blank]; omega
    have hs : clCmpTM.tm.step (clCmpCfg x p (.inr (.inl b)) w j) =
        clCmpCfg x p (.inr (.inl b)) w ((j : ℤ) - 1) := by
      change (clCmpTM.tm.tr (.inr (.inl b)) _ _).apply _ = _
      simp only [clCmpTM]
      rw [clCmp_read x p _ w j, if_neg hb]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i
      simp [clCmpCfg, Action.apply, sub_eq_add_neg]
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The native comparison costs exactly two maximum-width scans plus two
boundary transitions, and returns every word unchanged at head zero. -/
private lemma clCmp_run (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin 4 → List Bool) :
    clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0)
        (2 * clCmpSize w + 2) =
      clCmpCfg x p (.inr (.inr (clCmpVerdict (clCmpOrbit w (clCmpSize w))))) w 0 := by
  rw [show 2 * clCmpSize w + 2 = clCmpSize w + (1 + (clCmpSize w + 1)) by omega,
    MultiTapeTM.runFrom_add, clCmp_forward x p w _ le_rfl,
    Nat.add_comm 1 _, MultiTapeTM.runFrom_succ_eq_step, clCmp_finish_scan]
  exact clCmp_rewind x p w _ _ le_rfl

/-- Completed comparisons are absorbing on the entire configuration. -/
private lemma clCmp_idle {x : List Bool} (c : Cfg 4 Bool clCmpTM.State x)
    (b : Bool) (hc : c.state = some (.inr (.inr b))) : clCmpTM.tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  change (FinTM.controlAction 0 (some (.inr (.inr b)))).apply c = c
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- The native comparator returns at its first observed completion, within
its scan bound, with the correct arithmetic verdict and all four heads restored.
**Proof sketch.** Cut the exact completed run at its first completed-state
occurrence. Whole-configuration absorption preserves both the verdict and
all read-only words. The disjoint initial phase excludes zero duration. -/
private lemma clCmp_first (x : List Bool) (p : Fin (x.length + 2))
    (w : Fin 4 → List Bool) (W : ℕ) (hW : ∀ i, (w i).length ≤ W) :
    ∃ t ≤ 2 * W + 2, 0 < t ∧ ∃ b,
      (b = true ↔ clNum (w 0) + clNum (w 1) = clNum (w 2) + clNum (w 3)) ∧
      (∀ j, j < t → ∀ d, (clCmpTM.tm.runFrom
        (clCmpCfg x p (.inl (false, false, true)) w 0) j).state ≠ some (.inr (.inr d))) ∧
      clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t =
        clCmpCfg x p (.inr (.inr b)) w 0 := by
  let b := clCmpVerdict (clCmpOrbit w (clCmpSize w))
  have finish := clCmp_run x p w
  have hex : ∃ t, t ≤ 2 * clCmpSize w + 2 ∧
      (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t).state =
        some (.inr (.inr b)) := ⟨2 * clCmpSize w + 2, le_rfl, by rw [finish]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hw : clCmpSize w ≤ W := Finset.sup_le (fun i _ => hW i)
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hh := ht.2
    change (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t).state =
      some (.inr (.inr b)) at hh
    rw [hz, MultiTapeTM.runFrom_zero] at hh
    cases hh
  refine ⟨t, by omega, hp, b, clCmpVerdict_spec w, ?_, ?_⟩
  · intro j hj d hd
    have hstay := Function.iterate_fixed (clCmp_idle _ d hd) (2 * clCmpSize w + 2 - j)
    change clCmpTM.tm.runFrom
      (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j)
      (2 * clCmpSize w + 2 - j) =
        clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le (by omega)] at hstay
    have hh := congrArg Cfg.state (finish.symm.trans hstay)
    rw [hd] at hh
    have hbd : b = d := Sum.inr.inj (Sum.inr.inj (Option.some.inj hh))
    have hs : (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j).state =
        some (.inr (.inr b)) := by rw [hbd]; exact hd
    have := Nat.find_min' hex (show j ≤ 2 * clCmpSize w + 2 ∧
      (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) j).state =
        some (.inr (.inr b)) from ⟨by omega, hs⟩)
    omega
  · have hstay := Function.iterate_fixed (clCmp_idle _ b ht.2) (2 * clCmpSize w + 2 - t)
    change clCmpTM.tm.runFrom
      (clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t)
      (2 * clCmpSize w + 2 - t) =
        clCmpTM.tm.runFrom (clCmpCfg x p (.inl (false, false, true)) w 0) t at hstay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans finish

/-- Specializing stored positions to the public all-false schedule recovers
the exact input and work coordinates, including the shifted input origin. -/
private lemma clCounts_schedule (M : FinTM Bool) (m t : ℕ) :
    clSigned (clCounts M (List.replicate m false) t) (Fin.castAdd M.k (0 : Fin 1)) + 1 =
        (inputPosAt M m t : ℤ) ∧
      ∀ τ, clSigned (clCounts M (List.replicate m false) t) (Fin.natAdd 1 τ) =
        workPosAt M m t τ := by
  delta inputPosAt workPosAt
  constructor
  · have h := clCounts_positions M (List.replicate m false) t (Fin.castAdd M.k (0 : Fin 1))
    simp only [clPositions, Fin.addCases_left] at h ⊢
    omega
  · intro τ
    simpa only [clPositions, Fin.addCases_right] using
      clCounts_positions M (List.replicate m false) t (Fin.natAdd 1 τ)

/-- Packed fields use the same doubled-bit separators as the actual copier.
This list specification supports an exact decoder, with no fixed-width
assumption and with empty binary zero fields preserved. -/
private def clFields : List (List Bool) → List Bool
  | [] => []
  | w :: ws => pairEncode w (clFields ws)

/-- Appending a tail preserves the boundary of the first encoded field. -/
private lemma clPair_append (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
  simp [pairEncode, List.append_assoc]

/-- Packing a concatenation concatenates its complete field encodings. -/
private lemma clFields_append (a b : List (List Bool)) :
    clFields (a ++ b) = clFields a ++ clFields b := by
  induction a with
  | nil => simp [clFields]
  | cons a as ih => simp [clFields, ih, clPair_append]

/-- The actual row copier stores the fixed field order exactly. -/
private lemma clRowPrefix_fields {l : ℕ} (w : Fin l → List Bool) : ∀ j, j ≤ l →
    clRowPrefix w j = clFields ((List.ofFn w).take j) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [List.take_succ_eq_append_getElem (by simpa using (show j < l by omega)), clFields_append]
    simp [clRowPrefix, show j < l by omega, ih (by omega), clFields]

/-- A native sequential field reader on two work tapes. It consumes an
aligned doubled-bit field from a read-only stream, overwrites the target
word, and rewinds only the target. The contract below requires the old
target no longer than the decoded field, as holds for movement counts
read in increasing source-time order. -/
private def clReadTM : FinTM Bool where
  k := 2
  State := Option Bool ⊕ Bool
  tm := {
    q₀ := .inl none
    tr := fun q _ work => match q with
      | .inl none =>
        ⟨0, clTwo (none, .pos) (none, 0), none, some (.inl (work 0))⟩
      | .inl (some b) =>
        if work 0 = some b then
          ⟨0, clTwo (none, .pos) (some (some b), .pos), none, some (.inl none)⟩
        else ⟨0, clTwo (none, .pos) (none, .neg), none, some (.inr false)⟩
      | .inr false =>
        if work 1 = none then
          ⟨0, clTwo (none, 0) (none, .pos), none, some (.inr true)⟩
        else ⟨0, clTwo (none, 0) (none, .neg), none, some (.inr false)⟩
      | .inr true => FinTM.controlAction 0 (some q) }

/-- The complete stream-reader configuration. The stream cursor and target
cursor are independent, and physical input and output are fixed. -/
private def clReadCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : clReadTM.State) (stream word : List Bool) (s z : ℤ) : Cfg 2 Bool clReadTM.State x :=
  ⟨some q, p, clTwo (FinTM.bufferTape stream) (FinTM.bufferTape word), clTwo s z, []⟩

/-- Reading any two successive stream bits uses real adjacent head moves.
**Proof sketch.** The first transition reads the first stream bit into finite control and advances only the stream. The matching second bit triggers one target overwrite and advances both heads. The inherited tape-update identity proves the exact overwritten suffix. -/
private lemma clRead_pair (x : List Bool) (p : Fin (x.length + 2))
    (pre rest written old : List Bool) (b : Bool) :
    clReadTM.tm.runFrom
      (clReadCfg x p (.inl none) (pre ++ b :: b :: rest) (written ++ old)
        pre.length written.length) 2 =
      clReadCfg x p (.inl none) (pre ++ b :: b :: rest) (written ++ b :: old.tail)
        (pre.length + 2) (written.length + 1) := by
  have r0 : FinTM.bufferTape (pre ++ b :: b :: rest) pre.length = some b := by
    rw [FinTM.bufferTape_nat, List.getElem?_append_right le_rfl]; simp
  have r1 : FinTM.bufferTape (pre ++ b :: b :: rest) (pre.length + 1) = some b := by
    rw [show (pre.length : ℤ) + 1 = ((pre.length + 1 : ℕ) : ℤ) by omega,
      FinTM.bufferTape_nat, List.getElem?_append_right (by omega)]; simp
  have first : clReadTM.tm.step
      (clReadCfg x p (.inl none) (pre ++ b :: b :: rest) (written ++ old)
        pre.length written.length) =
      clReadCfg x p (.inl (some b)) (pre ++ b :: b :: rest) (written ++ old)
        (pre.length + 1) written.length := by
    refine Cfg.ext ?_ (moveInputPos_zero _) ?_ ?_ rfl
    · simp [MultiTapeTM.step, clReadTM, clReadCfg, Cfg.workTapeSymbols, clTwo, r0]
    · funext i; fin_cases i <;> simp [MultiTapeTM.step, clReadTM, clReadCfg, clTwo, Action.apply]
    · funext i; fin_cases i <;> simp [MultiTapeTM.step, clReadTM, clReadCfg, clTwo, Action.apply]
  rw [show 2 = 1 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, first]
  change (clReadTM.tm.tr (.inl (some b)) _ _).apply _ = _
  simp only [clReadTM, clReadCfg, Cfg.workTapeSymbols, clTwo, ↓reduceIte, r1]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    fin_cases i
    · rfl
    · simpa only [clCountTape_eq] using clCountTape_write written old b
  · funext i; fin_cases i <;> simp [Action.apply, clTwo] <;> omega

/-- A forward parse overwrites one target cell per decoded bit, preserving
the exact unread suffix. The runtime charges both stream bits individually.
**Proof sketch.** Consume the two equal bits, extend the written prefix,
and continue with the old target's tail. The `01` separator is left for
the next lemma, so an empty binary-zero field still has a distinct boundary. -/
private lemma clRead_forward (x : List Bool) (p : Fin (x.length + 2)) (w : List Bool) :
    ∀ pre tail written old,
      clReadTM.tm.runFrom
        (clReadCfg x p (.inl none) (pre ++ pairEncode w tail) (written ++ old)
          pre.length written.length) (2 * w.length) =
        clReadCfg x p (.inl none) (pre ++ pairEncode w tail)
          (written ++ w ++ old.drop w.length) (pre.length + 2 * w.length)
          (written.length + w.length) := by
  induction w with
  | nil => intro pre tail written old; simp
  | cons b w ih =>
    intro pre tail written old
    have pair : pre ++ pairEncode (b :: w) tail = pre ++ b :: b :: pairEncode w tail := by
      simp [pairEncode]
    rw [List.length_cons, show 2 * (w.length + 1) = 2 + 2 * w.length by omega,
      MultiTapeTM.runFrom_add, pair, clRead_pair]
    have he := ih (pre ++ [b, b]) tail (written ++ [b]) old.tail
    simpa [List.append_assoc, pairEncode, mul_add, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, add_assoc, add_comm, add_left_comm] using he

/-- Consuming the aligned field separator advances the stream to the next
field and starts the target rewind without writing the separator.
**Proof sketch.** Read the false bit into finite control, then observe the unequal true bit. This branch advances past the separator and moves the target head left without writing it; the whole stream and target words stay fixed. -/
private lemma clRead_separator (x : List Bool) (p : Fin (x.length + 2))
    (pre tail w : List Bool) :
    clReadTM.tm.runFrom
      (clReadCfg x p (.inl none) (pre ++ false :: true :: tail) w pre.length w.length) 2 =
      clReadCfg x p (.inr false) (pre ++ false :: true :: tail) w
        (pre.length + 2) (w.length - 1) := by
  have r0 : FinTM.bufferTape (pre ++ false :: true :: tail) pre.length = some false := by
    rw [FinTM.bufferTape_nat, List.getElem?_append_right le_rfl]; simp
  have r1 : FinTM.bufferTape (pre ++ false :: true :: tail) (pre.length + 1) = some true := by
    rw [show (pre.length : ℤ) + 1 = ((pre.length + 1 : ℕ) : ℤ) by omega,
      FinTM.bufferTape_nat, List.getElem?_append_right (by omega)]; simp
  have first : clReadTM.tm.step
      (clReadCfg x p (.inl none) (pre ++ false :: true :: tail) w pre.length w.length) =
      clReadCfg x p (.inl (some false)) (pre ++ false :: true :: tail) w
        (pre.length + 1) w.length := by
    refine Cfg.ext ?_ (moveInputPos_zero _) ?_ ?_ rfl
    · simp [MultiTapeTM.step, clReadTM, clReadCfg, Cfg.workTapeSymbols, clTwo, r0]
    · funext i; fin_cases i <;> simp [MultiTapeTM.step, clReadTM, clReadCfg, clTwo, Action.apply]
    · funext i; fin_cases i <;> simp [MultiTapeTM.step, clReadTM, clReadCfg, clTwo, Action.apply]
  rw [show 2 = 1 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, first]
  change (clReadTM.tm.tr (.inl (some false)) _ _).apply _ = _
  simp only [clReadTM, clReadCfg, Cfg.workTapeSymbols, clTwo, ↓reduceIte, r1]
  simp only [Bool.true_eq_false, Option.some.injEq, if_false]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [Action.apply, clTwo] <;> omega

/-- The reader restores its target head and preserves the stream cursor.
**Proof sketch.** Cross the decoded target bits leftward, then leave the
left blank with one right move. No stream access occurs during this rewind. -/
private lemma clRead_rewind (x : List Bool) (p : Fin (x.length + 2))
    (stream w : List Bool) (s : ℤ) : ∀ j, j ≤ w.length →
    clReadTM.tm.runFrom (clReadCfg x p (.inr false) stream w s ((j : ℤ) - 1)) (j + 1) =
      clReadCfg x p (.inr true) stream w s 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clReadTM, clReadCfg, Cfg.workTapeSymbols, clTwo,
        Action.apply, funext_iff]
  | succ j ih =>
    intro hj
    have hr : FinTM.bufferTape w (j : ℤ) = some w[j] := by
      rw [FinTM.bufferTape_nat]; exact List.getElem?_eq_getElem (by omega)
    have hs : clReadTM.tm.step (clReadCfg x p (.inr false) stream w s j) =
        clReadCfg x p (.inr false) stream w s ((j : ℤ) - 1) := by
      change (clReadTM.tm.tr (.inr false) _ _).apply _ = _
      simp only [clReadTM, clReadCfg, Cfg.workTapeSymbols, clTwo,
        show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hr, Option.some_ne_none, if_false]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> simp [Action.apply, clTwo, sub_eq_add_neg]
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The complete native parse charges every read and rewind. It consumes
exactly one field, preserves the whole stream, replaces an old target of at most the new length,
and returns that target's head to zero. The empty field takes three steps. -/
private lemma clRead_run (x : List Bool) (p : Fin (x.length + 2))
    (pre w tail old : List Bool) (ho : old.length ≤ w.length) :
    clReadTM.tm.runFrom
      (clReadCfg x p (.inl none) (pre ++ pairEncode w tail) old pre.length 0)
        (3 * w.length + 3) =
      clReadCfg x p (.inr true) (pre ++ pairEncode w tail) w
        (pre.length + 2 * w.length + 2) 0 := by
  have hf := clRead_forward x p w pre tail [] old
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add,
    List.drop_eq_nil_of_le ho, List.append_nil] at hf
  have hlen : (w.flatMap (fun b => [b, b])).length = 2 * w.length := by
    induction w with
    | nil => simp
    | cons b w ih => simp [ih]; omega
  have hs := clRead_separator x p (pre ++ w.flatMap (fun b => [b, b])) tail w
  simp only [List.length_append, hlen, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hs
  have hword : pre ++ pairEncode w tail =
      (pre ++ w.flatMap (fun b => [b, b])) ++ false :: true :: tail := by
    simp [pairEncode, List.append_assoc]
  rw [show 3 * w.length + 3 = 2 * w.length + (2 + (w.length + 1)) by omega,
    MultiTapeTM.runFrom_add, hf, MultiTapeTM.runFrom_add, hword, hs,
    clRead_rewind x p _ w _ w.length le_rfl]

/-- Stored trajectory size is bounded separately from native runtime.
Every time at most the horizon has movement counts of width at most the
horizon, and every field has exactly a doubled payload and its separator. -/
private lemma clRecords_length (M : FinTM Bool) (y : List Bool) (T : ℕ) :
    ∀ t, t ≤ T + 1 → (clRecords M y t).length ≤ t * (clRecFields M * (2 * T + 2)) := by
  intro t
  induction t with
  | zero => intro _; simp [clRecords]
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    have widths (i : Fin (clRecFields M)) : (clCounts M y t i).bits.length ≤ T :=
      clElapsed_width _ T ((clCounts_bound M y t i).trans (by omega))
    have hr := clRowPrefix_length (fun i => (clCounts M y t i).bits) T widths (clRecFields M)
    simp only [clRecords, List.length_append]
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Cut a proved bounded run to its first visit to a fresh absorbing return.
**Proof sketch.** Minimize the return-control occurrence. Absorption makes
its whole configuration identical to the known endpoint, not just its state. -/
private lemma clFirst {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start finish : Cfg k Bool S x) (ret : S) (B : ℕ)
    (hrun : tm.runFrom start B = finish) (hret : finish.state = some ret)
    (hstart : start.state ≠ some ret)
    (hidle : ∀ c : Cfg k Bool S x, c.state = some ret → tm.step c = c) :
    ∃ t ≤ B, 0 < t ∧ (∀ j < t, (tm.runFrom start j).state ≠ some ret) ∧
      tm.runFrom start t = finish := by
  have hex : ∃ t, t ≤ B ∧ (tm.runFrom start t).state = some ret :=
    ⟨B, le_rfl, by rw [hrun]; exact hret⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hh := ht.2
    change (tm.runFrom start t).state = some ret at hh
    rw [hz, MultiTapeTM.runFrom_zero] at hh
    exact hstart hh
  refine ⟨t, ht.1, hp, ?_, ?_⟩
  · intro j hj hs
    have := Nat.find_min' hex (show j ≤ B ∧ (tm.runFrom start j).state = some ret
      from ⟨by omega, hs⟩)
    omega
  · have stay := Function.iterate_fixed (hidle _ ht.2) (B - t)
    change tm.runFrom (tm.runFrom start t) (B - t) = tm.runFrom start t at stay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1, hrun] at stay
    exact stay.symm

/-- Clearing the last occupied cell leaves exactly the shorter buffer.
Locally harvested from the audited bridge's `emCall_erase_last` proof. -/
private lemma clErase_last (w : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape (w ++ [b])) w.length none = FinTM.bufferTape w := by
  rw [FinTM.bufferTape_append, Function.update_idem]
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp [FinTM.bufferTape_nat]
  · simp [Function.update_of_ne hz]

/-- Two-tape scratch reset: preserve stream and cursor, scan the target to
its right blank, erase back to its left blank, and return at target zero. -/
private def clWipeTM : FinTM Bool where
  k := 2
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q _ work =>
      if q = 0 then
        if work 1 = none then
          ⟨0, clTwo (none, 0) (none, .neg), none, some 1⟩
        else ⟨0, clTwo (none, 0) (none, .pos), none, some 0⟩
      else if q = 1 then
        if work 1 = none then
          ⟨0, clTwo (none, 0) (none, .pos), none, some 2⟩
        else ⟨0, clTwo (none, 0) (some none, .neg), none, some 1⟩
      else FinTM.controlAction 0 (some q) }

/-- Reset seam with arbitrary preserved stream contents and stream head. -/
private def clWipeCfg (x : List Bool) (p : Fin (x.length + 2)) (q : Fin 3)
    (stream word : List Bool) (s z : ℤ) : Cfg 2 Bool (Fin 3) x :=
  ⟨some q, p, clTwo (FinTM.bufferTape stream) (FinTM.bufferTape word), clTwo s z, []⟩

/-- Forward scratch scan, including the right-blank turn.
**Proof sketch.** Each occupied cell moves the target head right once.
The blank at the word's exact length changes phase and moves left. -/
private lemma clWipe_forward (x : List Bool) (p : Fin (x.length + 2))
    (stream word : List Bool) (s : ℤ) : ∀ j, j ≤ word.length →
    clWipeTM.tm.runFrom (clWipeCfg x p 0 stream word s j) (word.length - j + 1) =
      clWipeCfg x p 1 stream word s (word.length - 1) := by
  intro j hj
  induction h : word.length - j generalizing j with
  | zero =>
    have he : j = word.length := by omega
    subst j
    rw [zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clWipeTM, clWipeCfg, Cfg.workTapeSymbols, clTwo,
        Action.apply, funext_iff, sub_eq_add_neg]
  | succ r ih =>
    have hjl : j < word.length := by omega
    have hr : FinTM.bufferTape word j = some word[j] := by
      rw [FinTM.bufferTape_nat]; exact List.getElem?_eq_getElem hjl
    have step : clWipeTM.tm.step (clWipeCfg x p 0 stream word s j) =
        clWipeCfg x p 0 stream word s (j + 1) := by
      change (clWipeTM.tm.tr (0 : Fin 3) _ _).apply _ = _
      simp only [clWipeTM, clWipeCfg, Cfg.workTapeSymbols, clTwo, ↓reduceIte,
        show (1 : Fin 2) ≠ 0 by decide, hr, Option.some_ne_none, if_false]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> simp [Action.apply, clTwo]
    rw [MultiTapeTM.runFrom_succ_eq_step, step]
    exact ih (j + 1) (by omega) (by omega)

/-- The backward pass erases all occupied cells, including the first one,
and restores the target head. The stream is not read or modified.
**Proof sketch.** Remove the final bit of the remaining prefix and induct
backwards over the word. The left blank gives the final right move. -/
private lemma clWipe_backward (x : List Bool) (p : Fin (x.length + 2))
    (stream : List Bool) (s : ℤ) : ∀ word : List Bool,
    clWipeTM.tm.runFrom (clWipeCfg x p 1 stream word s (word.length - 1))
      (word.length + 1) = clWipeCfg x p 2 stream [] s 0 := by
  intro word
  induction word using List.reverseRecOn with
  | nil =>
    rw [show ([] : List Bool).length + 1 = 1 by rfl,
      MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    refine Cfg.ext ?_ (moveInputPos_zero _) ?_ ?_ rfl
    · simp [MultiTapeTM.step, clWipeTM, clWipeCfg, Cfg.workTapeSymbols, clTwo]
    · funext i; fin_cases i <;>
        simp [MultiTapeTM.step, clWipeTM, clWipeCfg, Cfg.workTapeSymbols, clTwo, Action.apply]
    · funext i; fin_cases i <;>
        simp [MultiTapeTM.step, clWipeTM, clWipeCfg, Cfg.workTapeSymbols, clTwo, Action.apply]
  | append_singleton pre b ih =>
    have hr : FinTM.bufferTape (pre ++ [b]) pre.length = some b := by
      simp [FinTM.bufferTape_nat]
    have step : clWipeTM.tm.step (clWipeCfg x p 1 stream (pre ++ [b]) s pre.length) =
        clWipeCfg x p 1 stream pre s (pre.length - 1) := by
      change (clWipeTM.tm.tr (1 : Fin 3) _ _).apply _ = _
      simp only [clWipeTM, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true,
        clWipeCfg, Cfg.workTapeSymbols, clTwo, show (1 : Fin 2) ≠ 0 by decide,
        ↓reduceIte, hr, Option.some_ne_none]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i; fin_cases i <;> simp [Action.apply, clTwo, clErase_last]
      · funext i; fin_cases i <;> simp [Action.apply, clTwo, sub_eq_add_neg]
    rw [show ((pre ++ [b]).length : ℤ) - 1 = pre.length by simp,
      List.length_append, List.length_singleton, MultiTapeTM.runFrom_succ_eq_step, step]
    exact ih

/-- Actual reset cost: one forward and one backward pass, including both
blank transitions. No bound on the next field's length is required. -/
private lemma clWipe_run (x : List Bool) (p : Fin (x.length + 2))
    (stream word : List Bool) (s : ℤ) :
    clWipeTM.tm.runFrom (clWipeCfg x p 0 stream word s 0) (2 * word.length + 2) =
      clWipeCfg x p 2 stream [] s 0 := by
  rw [show 2 * word.length + 2 = (word.length + 1) + (word.length + 1) by omega,
    MultiTapeTM.runFrom_add]
  have h := clWipe_forward x p stream word s 0 (by omega)
  simp only [Nat.sub_zero, Nat.cast_zero] at h
  rw [h, clWipe_backward]

/-- The reset return fixes the entire configuration. -/
private lemma clWipe_idle {x : List Bool} (c : Cfg 2 Bool (Fin 3) x)
    (hc : c.state = some 2) : clWipeTM.tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  change (FinTM.controlAction 0 (some (2 : Fin 3))).apply c = c
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- Positive first completion of an actual scratch reset. -/
private lemma clWipe_first (x : List Bool) (p : Fin (x.length + 2))
    (stream word : List Bool) (s : ℤ) :
    ∃ t ≤ 2 * word.length + 2, 0 < t ∧
      (∀ j < t, (clWipeTM.tm.runFrom (clWipeCfg x p 0 stream word s 0) j).state ≠ some (2 : Fin 3)) ∧
      clWipeTM.tm.runFrom (clWipeCfg x p 0 stream word s 0) t =
        clWipeCfg x p 2 stream [] s 0 :=
  clFirst clWipeTM.tm _ _ (2 : Fin 3) _ (clWipe_run x p stream word s) rfl (by simp [clWipeCfg])
    (fun c hc => clWipe_idle c hc)

/-- An unrestricted field loader actually resets its target before invoking
the banked reader. Stream positions and all reset/read transitions are charged. -/
private def clFreshTM : FinTM Bool where
  k := 2
  State := (Fin 3) ⊕ clReadTM.State
  tm := seamCompTM clWipeTM.tm 2 clReadTM.tm (.inl none)

/-- Whole-configuration unrestricted loading, with a separate cost for
clearing the old target. The new field may be empty, shorter, or unrelated.
**Proof sketch.** Stop the reset at its first return, dispatch once to the
unchanged field reader, and use its empty-target case. Both subruns have
unchanged native input and physical output; the stream moves only in the reader. -/
private lemma clFresh_run (x : List Bool) (p : Fin (x.length + 2))
    (pre w tail old : List Bool) :
    ∃ t ≤ 2 * old.length + 3 * w.length + 6,
      clFreshTM.tm.runFrom
        ((clWipeCfg x p 0 (pre ++ pairEncode w tail) old pre.length 0).mapState Sum.inl) t =
        (clReadCfg x p (.inr true) (pre ++ pairEncode w tail) w
          (pre.length + 2 * w.length + 2) 0).mapState Sum.inr := by
  obtain ⟨a, ha, _, hf, he⟩ := clWipe_first x p (pre ++ pairEncode w tail) old pre.length
  refine ⟨a + 1 + (3 * w.length + 3), by omega, ?_⟩
  exact seamCompTM_run_ofCfg clWipeTM.tm (2 : Fin 3) clReadTM.tm (.inl none)
    he rfl hf (clRead_run x p pre w tail [] (by simp))

/-- The unrestricted loader's completed state is absorbing. -/
private lemma clFresh_idle {x : List Bool} (c : Cfg 2 Bool clFreshTM.State x)
    (hc : c.state = some (.inr (.inr true))) : clFreshTM.tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  change (FinTM.controlAction 0 (some (Sum.inr (.inr true)))).apply c = c
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- First-return loader interface without the inherited overwrite-length
precondition; cleanup is explicit in the bound and in the transition table. -/
private lemma clFresh_first (x : List Bool) (p : Fin (x.length + 2))
    (pre w tail old : List Bool) :
    ∃ t ≤ 2 * old.length + 3 * w.length + 6, 0 < t ∧
      (∀ j < t, (clFreshTM.tm.runFrom
        ((clWipeCfg x p 0 (pre ++ pairEncode w tail) old pre.length 0).mapState Sum.inl) j).state ≠
          some (.inr (.inr true))) ∧
      clFreshTM.tm.runFrom
        ((clWipeCfg x p 0 (pre ++ pairEncode w tail) old pre.length 0).mapState Sum.inl) t =
        (clReadCfg x p (.inr true) (pre ++ pairEncode w tail) w
          (pre.length + 2 * w.length + 2) 0).mapState Sum.inr := by
  obtain ⟨B, hB, he⟩ := clFresh_run x p pre w tail old
  obtain ⟨t, ht, hp, hf, hr⟩ := clFirst clFreshTM.tm _ _ (.inr (.inr true)) B he rfl
    (by simp [clWipeCfg, Cfg.mapState]) (fun c hc => clFresh_idle c hc)
  exact ⟨t, ht.trans hB, hp, hf, hr⟩



/-- Loading reverses the same two physical slots used by row copying. -/
private def clLoadSelect {l : ℕ} (i : Fin l) : clPlacement 2 (l + 1) :=
  (clRowSelect i).permute (Equiv.swap 0 1)



/-- Load a fixed row in increasing field order. Every field first clears
its own target, so repeated queries need no monotonic-width assumption. -/
private def clLoadTM (l : ℕ) : FinTM Bool where
  k := l + 1
  State := Fin (l + 1) × clFreshTM.State
  tm := {
    q₀ := (0, .inl 0)
    tr := fun q inp work =>
      if hi : q.1.val < l then
        if q.2 = .inr (.inr true) then
          FinTM.controlAction 0 (some (⟨q.1.val + 1, by omega⟩, .inl 0))
        else clPlacedAction (clLoadSelect ⟨q.1.val, hi⟩) (fun s => (q.1, s)) q.2 (clFreshTM.tm.tr q.2 inp (fun j => work ((clLoadSelect ⟨q.1.val, hi⟩).index j)))
      else FinTM.controlAction 0 (some q) }

/-- Whole row-loader seam: all field heads zero, with an explicit stream cursor. -/
private def clLoadCfg {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (i : Fin (l + 1)) (q : clFreshTM.State) (w : Fin l → List Bool)
    (stream : List Bool) (s : ℤ) : Cfg (clLoadTM l).k Bool (clLoadTM l).State x :=
  ⟨some (i, q), p,
    Fin.addCases (fun j => FinTM.bufferTape (w j)) (fun _ : Fin 1 => FinTM.bufferTape stream),
    Fin.addCases (fun _ => 0) (fun _ : Fin 1 => s), []⟩

/-- The exact inactive frame for a field call, allowing its target word to
change while every other field remains untouched. -/
private lemma clLoad_frame {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (i : Fin l) (q : clFreshTM.State) (old : Fin l → List Bool)
    (stream word : List Bool) (s : ℤ) :
    clPlacedCfg (clLoadSelect i) (fun r => (i.castSucc, r))
      (fun j => (clLoadCfg x p i.castSucc q old stream s).workTapes j) (fun _ => 0)
      (⟨some q, p, clTwo (FinTM.bufferTape stream) (FinTM.bufferTape word), clTwo s 0, []⟩ :
        Cfg 2 Bool clFreshTM.State x) =
      clLoadCfg x p i.castSucc q (Function.update old i word) stream s := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro j
      by_cases hj : j = i
      · subst j; simp [clLoadSelect, clPlacement.permute, clRowSelect, clLoadCfg, clTwo]
      · simp [clLoadSelect, clPlacement.permute, clRowSelect, clLoadCfg, clTwo, hj]
    · intro j; simp [clLoadSelect, clPlacement.permute, clRowSelect, clLoadCfg, clTwo]

/-- One actual row-field load includes target reset, native parsing,
target rewind, and one finite-control dispatch to the next field.
**Proof sketch.** Relocate the unrestricted loader using its first-return
guard. The inactive fields are framed throughout. Its completed state
contains the exact new target; a control-only step advances the field index. -/
private lemma clLoad_field {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (i : Fin l) (old : Fin l → List Bool) (pre word tail : List Bool) :
    ∃ t ≤ 2 * (old i).length + 3 * word.length + 7, 0 < t ∧
      (clLoadTM l).tm.runFrom
        (clLoadCfg x p i.castSucc (.inl 0) old (pre ++ pairEncode word tail) pre.length) t =
      clLoadCfg x p i.succ (.inl 0) (Function.update old i word)
        (pre ++ pairEncode word tail) (pre.length + 2 * word.length + 2) := by
  obtain ⟨t, ht, hp, hf, he⟩ := clFresh_first x p pre word tail (old i)
  let tapes := (clLoadCfg x p i.castSucc (.inl 0) old (pre ++ pairEncode word tail)
    pre.length).workTapes
  have lift := clPlaced_run clFreshTM.tm (clLoadTM l).tm (clLoadSelect i) (fun r => (i.castSucc, r)) (by intro a b h; cases h; rfl) (fun r => r ≠ .inr (.inr true))
    (by intro r hr inp work; simp only [clLoadTM, Fin.coe_castSucc, dif_pos i.isLt, if_neg hr]; rfl) tapes (fun _ => 0)
    ((clWipeCfg x p 0 (pre ++ pairEncode word tail) (old i) pre.length 0).mapState Sum.inl) t
    (by intro j hj q hq heq; subst q; exact hf j hj hq)
  rw [he] at lift
  have start := clLoad_frame x p i (.inl 0) old (pre ++ pairEncode word tail) (old i) pre.length
  simp only [Function.update_eq_self] at start
  have finish := clLoad_frame x p i (.inr (.inr true)) old (pre ++ pairEncode word tail)
    word (pre.length + 2 * word.length + 2)
  have run : (clLoadTM l).tm.runFrom
      (clLoadCfg x p i.castSucc (.inl 0) old (pre ++ pairEncode word tail) pre.length) t =
      clLoadCfg x p i.castSucc (.inr (.inr true)) (Function.update old i word)
        (pre ++ pairEncode word tail) (pre.length + 2 * word.length + 2) :=
    (congrArg (fun z => (clLoadTM l).tm.runFrom z t) start).symm.trans (lift.trans finish)
  refine ⟨t + 1, by omega, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', run]
  change ((clLoadTM l).tm.tr (i.castSucc, .inr (.inr true)) _ _).apply _ = _
  dsimp only [clLoadTM]
  split
  · rw [if_pos rfl, FinTM.controlAction_apply, moveInputPos_zero]
    rfl
  · rename_i hn
    exact False.elim (hn i.isLt)

/-- Intermediate row bank after exactly the first `j` fields have been loaded. -/
private def clLoadWords {l : ℕ} (old new : Fin l → List Bool) (j : ℕ) : Fin l → List Bool :=
  fun i => if i.val < j then new i else old i

/-- Updating the next field extends precisely the initialized row prefix. -/
private lemma clLoadWords_step {l : ℕ} (old new : Fin l → List Bool) (i : Fin l) :
    Function.update (clLoadWords old new i.val) i (new i) =
      clLoadWords old new (i.val + 1) := by
  funext j
  by_cases h : j = i
  · subst j; simp [clLoadWords]
  · have hv : j.val ≠ i.val := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h, clLoadWords]
    by_cases hj : j.val < i.val
    · rw [if_pos hj, if_pos (by omega)]
    · rw [if_neg hj, if_neg (by omega)]

/-- Every encoded row exposes its next field at the charged sequential
cursor; the suffix is preserved literally, including an arbitrary trailer. -/
private lemma clLoad_split {l : ℕ} (w : Fin l → List Bool) (i : Fin l) (pre tail : List Bool) :
    pre ++ clFields (List.ofFn w) ++ tail =
      (pre ++ clFields ((List.ofFn w).take i.val)) ++
        pairEncode (w i) (clFields ((List.ofFn w).drop (i.val + 1)) ++ tail) := by
  have hs : (List.ofFn w).drop i.val = w i :: (List.ofFn w).drop (i.val + 1) := by
    simpa using List.drop_eq_getElem_cons (l := List.ofFn w) (i := i.val) (by simp)
  conv_lhs => rw [← List.take_append_drop i.val (List.ofFn w), clFields_append, hs]
  simp only [clFields, clPair_append, List.append_assoc]

/-- Charged prefix loading. Every field is reset even when revisiting row
zero after a much later row, and all field heads return to zero.
**Proof sketch.** Split the encoded stream at its next field. The previous
single-field theorem advances the cursor by exactly twice the payload
length plus two. Induct over the fixed field index, summing both old and
new field widths and every reset/read/dispatch cost. -/
private lemma clLoad_prefix {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (old new : Fin l → List Bool) (pre tail : List Bool) (U W : ℕ)
    (hU : ∀ i, (old i).length ≤ U) (hW : ∀ i, (new i).length ≤ W) :
    ∀ j (hj : j ≤ l), ∃ t ≤ j * (2 * U + 3 * W + 7),
      (clLoadTM l).tm.runFrom
        (clLoadCfg x p 0 (.inl 0) old (pre ++ clFields (List.ofFn new) ++ tail) pre.length) t =
      clLoadCfg x p ⟨j, by omega⟩ (.inl 0) (clLoadWords old new j)
        (pre ++ clFields (List.ofFn new) ++ tail)
        (pre.length + (clFields ((List.ofFn new).take j)).length) := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hz : clLoadWords old new 0 = old := by funext i; simp [clLoadWords]
    exact ⟨0, by simp, by simp only [hz, List.take_zero, clFields, List.length_nil,
      Nat.cast_zero, add_zero, MultiTapeTM.runFrom_zero]; rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨a, ha, he⟩ := ih (by omega)
    let i : Fin l := ⟨j, by omega⟩
    obtain ⟨b, hb, _, hr⟩ := clLoad_field x p i (clLoadWords old new j)
      (pre ++ clFields ((List.ofFn new).take j)) (new i)
      (clFields ((List.ofFn new).drop (j + 1)) ++ tail)
    have hsplit := clLoad_split new i pre tail
    rw [← hsplit] at hr
    have hw : (clLoadWords old new j i).length = (old i).length := by
      simp [clLoadWords, i]
    rw [hw] at hb
    have hprefix : clFields ((List.ofFn new).take (j + 1)) =
        clFields ((List.ofFn new).take j) ++ pairEncode (new i) [] := by
      rw [List.take_add_one, clFields_append]
      simp [clFields, i, show j < l by omega]
    have hlen : (pairEncode (new i) []).length = 2 * (new i).length + 2 := by
      simp [pairEncode, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
    refine ⟨a + b, ?_, ?_⟩
    · have := hU i
      have := hW i
      calc
        a + b ≤ j * (2 * U + 3 * W + 7) + (2 * U + 3 * W + 7) := by omega
        _ = (j + 1) * (2 * U + 3 * W + 7) := by ring
    · rw [MultiTapeTM.runFrom_add, he]
      change (clLoadTM l).tm.runFrom (clLoadCfg x p i.castSucc _ _ _ _) b = _
      have heq : Function.update (clLoadWords old new j) i (new i) =
          clLoadWords old new (j + 1) := clLoadWords_step old new i
      rw [heq] at hr
      simpa only [List.length_append, Nat.cast_add, hprefix, hlen, add_assoc] using hr

/-- Full sequential row load from arbitrary old targets. The record stream
is retained in full, the cursor is immediately after the row, and every
field head is restored. This is a native call, not indexed list access. -/
private lemma clLoad_complete {l : ℕ} (x : List Bool) (p : Fin (x.length + 2))
    (old new : Fin l → List Bool) (pre tail : List Bool) (U W : ℕ)
    (hU : ∀ i, (old i).length ≤ U) (hW : ∀ i, (new i).length ≤ W) :
    ∃ t ≤ l * (2 * U + 3 * W + 7),
      (clLoadTM l).tm.runFrom
        (clLoadCfg x p 0 (.inl 0) old (pre ++ clFields (List.ofFn new) ++ tail) pre.length) t =
      clLoadCfg x p (Fin.last l) (.inl 0) new (pre ++ clFields (List.ofFn new) ++ tail)
        (pre.length + (clFields (List.ofFn new)).length) := by
  have hw : clLoadWords old new l = new := by funext i; simp [clLoadWords, i.isLt]
  obtain ⟨t, ht, he⟩ := clLoad_prefix x p old new pre tail U W hU hW l le_rfl
  refine ⟨t, ht, ?_⟩
  rw [hw, List.take_of_length_le (show (List.ofFn new).length ≤ l by simp)] at he
  exact he

/-- The row-loader's return is absorbing, including the empty-row case. -/
private lemma clLoad_idle {l : ℕ} {x : List Bool}
    (c : Cfg (clLoadTM l).k Bool (clLoadTM l).State x)
    (hc : c.state = some (Fin.last l, .inl 0)) : (clLoadTM l).tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  simp only [clLoadTM, Fin.val_last, Nat.lt_irrefl, dite_false]
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- A nonempty fixed row has a positive first return with the whole restored
field bank and exact sequential cursor.
**Proof sketch.** Minimize the absorbing complete row return. The initial finite field index is distinct from the final one when the row is nonempty; the zero-field case is handled explicitly. -/
private lemma clLoad_first {l : ℕ} (hl : 0 < l) (x : List Bool) (p : Fin (x.length + 2))
    (old new : Fin l → List Bool) (pre tail : List Bool) (U W : ℕ)
    (hU : ∀ i, (old i).length ≤ U) (hW : ∀ i, (new i).length ≤ W) :
    ∃ t ≤ l * (2 * U + 3 * W + 7), 0 < t ∧
      (∀ j < t, ((clLoadTM l).tm.runFrom
        (clLoadCfg x p 0 (.inl 0) old (pre ++ clFields (List.ofFn new) ++ tail) pre.length) j).state ≠
          some (Fin.last l, .inl 0)) ∧
      (clLoadTM l).tm.runFrom
        (clLoadCfg x p 0 (.inl 0) old (pre ++ clFields (List.ofFn new) ++ tail) pre.length) t =
      clLoadCfg x p (Fin.last l) (.inl 0) new (pre ++ clFields (List.ofFn new) ++ tail)
        (pre.length + (clFields (List.ofFn new)).length) := by
  obtain ⟨B, hB, he⟩ := clLoad_complete x p old new pre tail U W hU hW
  have hstart : (clLoadCfg x p 0 (.inl 0) old
      (pre ++ clFields (List.ofFn new) ++ tail) pre.length).state ≠
        some (Fin.last l, .inl 0) := by
    intro h
    have hv := congrArg (fun q => q.map (fun r => r.1.val)) h
    simp [clLoadCfg] at hv
    omega
  obtain ⟨t, ht, hp, hf, hr⟩ := clFirst (clLoadTM l).tm _ _ (Fin.last l, .inl 0) B he rfl
    hstart (fun c hc => clLoad_idle c hc)
  exact ⟨t, ht.trans hB, hp, hf, hr⟩

/-- A native input copier with a silent live return. The input head rewinds
against its actual left boundary; the destination head follows it exactly. -/
private def clInputTM : FinTM Bool where
  k := 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q inp _ =>
      if q = 0 then
        match inp with
        | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
        | none => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
      else if q = 1 then
        match inp with
        | some _ => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
        | none => ⟨.pos, fun _ => (none, .pos), none, some 2⟩
      else FinTM.controlAction 0 (some q) }

/-- Native-copy configuration with its exact copied prefix and aligned heads. -/
private def clInputCfg (x : List Bool) (q : Fin 3) (p : Fin (x.length + 2))
    (w : List Bool) (z : ℤ) : Cfg 1 Bool (Fin 3) x :=
  ⟨some q, p, fun _ => FinTM.bufferTape w, fun _ => z, []⟩

/-- Copy the entire native input, charging every source read and target write.
**Proof sketch.** At index `j`, the buffer is exactly the first `j` bits.
The next input symbol is `x[j]`; the public append-cell identity supplies
the whole tape equality after writing it. -/
private lemma clInput_forward (x : List Bool) : ∀ j (hj : j ≤ x.length),
    clInputTM.tm.runFrom (clInputCfg x 0 1 [] 0) j =
      clInputCfg x 0 ⟨j + 1, by omega⟩ (x.take j) j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (clInputCfg x 0 ⟨j + 1, by omega⟩ (x.take j) j).inputSymbol =
        some x[j] := inputSymbolInner _ (by simp [clInputCfg, Nat.add_comm]) (by omega)
    have ht : (x.take j).length = j := List.length_take_of_le (by omega)
    change (clInputTM.tm.tr (0 : Fin 3) _ _).apply _ = _
    simp only [clInputTM, if_true, hin]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [clInputCfg]; omega)
    · funext i
      change Function.update (FinTM.bufferTape (x.take j)) j (some x[j]) =
        FinTM.bufferTape (x.take (j + 1))
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        FinTM.bufferTape_append, ht]
    · funext i; simp [Action.apply, clInputCfg]

/-- Rewind both aligned heads from any prefix length to their exact origins.
**Proof sketch.** The physical left boundary identifies the origin without
an unbounded control counter. Every scanned bit moves both heads left; the
boundary transition moves both right into the canonical seam. -/
private lemma clInput_backward (x w : List Bool) : ∀ j (hj : j ≤ x.length),
    clInputTM.tm.runFrom (clInputCfg x 1 ⟨j, by omega⟩ w ((j : ℤ) - 1)) (j + 1) =
      clInputCfg x 2 1 w 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clInputTM, clInputCfg, Cfg.inputSymbol, Action.apply,
        moveInputPos, funext_iff]
  | succ j ih =>
    intro hj
    have hin : (clInputCfg x 1 ⟨j + 1, by omega⟩ w (((j + 1 : ℕ) : ℤ) - 1)).inputSymbol =
        some x[j] := inputSymbolInner _ (by simp [clInputCfg, Nat.add_comm]) (by omega)
    have hs : clInputTM.tm.step
        (clInputCfg x 1 ⟨j + 1, by omega⟩ w (((j + 1 : ℕ) : ℤ) - 1)) =
        clInputCfg x 1 ⟨j, by omega⟩ w ((j : ℤ) - 1) := by
      change (clInputTM.tm.tr (1 : Fin 3) _ _).apply _ = _
      simp only [clInputTM, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true, hin]
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · apply Fin.ext
        simpa using FinTM.moveInputPos_neg_val (⟨j + 1, by omega⟩ : Fin (x.length + 2))
      · funext i; rfl
      · funext i; simp [Action.apply, clInputCfg]; omega
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Genuine native initialization of a retained input buffer, with empty
physical output and both heads restored, in `2|x|+2` transitions.
**Proof sketch.** Run the literal forward copy through the right input blank, then rewind both the native input and target heads. The endpoint specifies the entire copied buffer. -/
private lemma clInput_run (x : List Bool) :
    clInputTM.tm.runFrom (clInputTM.tm.initCfg x) (2 * x.length + 2) =
      Cfg.ofWords (input := x) (2 : Fin 3) (fun _ : Fin 1 => x) := by
  have init : clInputTM.tm.initCfg x = clInputCfg x 0 1 [] 0 := by
    apply Cfg.ext <;> simp [MultiTapeTM.initCfg, Cfg.init, clInputCfg, clInputTM, funext_iff]
  have forward := clInput_forward x x.length le_rfl
  rw [List.take_length] at forward
  have turn : clInputTM.tm.step
      (clInputCfg x 0 ⟨x.length + 1, by omega⟩ x x.length) =
      clInputCfg x 1 ⟨x.length, by omega⟩ x ((x.length : ℤ) - 1) := by
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clInputTM, clInputCfg, Cfg.inputSymbol, Action.apply,
        FinTM.moveInputPos_neg_val, funext_iff, sub_eq_add_neg]
    apply Fin.ext
    simpa using FinTM.moveInputPos_neg_val (⟨x.length + 1, by omega⟩ : Fin (x.length + 2))
  rw [init, show 2 * x.length + 2 = x.length + ((x.length + 1) + 1) by omega,
    MultiTapeTM.runFrom_add, forward, MultiTapeTM.runFrom_succ_eq_step, turn,
    clInput_backward x x x.length (by omega)]
  rfl

/-- Native-copy return is absorbing, so it can be used at its first visit. -/
private lemma clInput_idle {x : List Bool} (c : Cfg 1 Bool (Fin 3) x)
    (hc : c.state = some 2) : clInputTM.tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  change (FinTM.controlAction 0 (some (2 : Fin 3))).apply c = c
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- Strictly positive first arrival at the genuine retained-input seam. -/
private lemma clInput_first (x : List Bool) :
    ∃ t ≤ 2 * x.length + 2, 0 < t ∧
      (∀ j < t, (clInputTM.tm.runFrom (clInputTM.tm.initCfg x) j).state ≠ some (2 : Fin 3)) ∧
      clInputTM.tm.runFrom (clInputTM.tm.initCfg x) t =
        Cfg.ofWords (input := x) (2 : Fin 3) (fun _ : Fin 1 => x) :=
  clFirst clInputTM.tm _ _ (2 : Fin 3) _ (clInput_run x) rfl
    (by simp [MultiTapeTM.initCfg, Cfg.init, clInputTM]) (fun c hc => clInput_idle c hc)



/-- Input copying selects just the final stream tape. -/
private def clPrepareSelect (l : ℕ) : clPlacement 1 (l + 1) :=
  clPlacement.trailing l 1

/-- Genuine native initialization followed by the complete sequential loader. -/
private def clPrepareTM (l : ℕ) : FinTM Bool where
  k := l + 1
  State := Fin 3 ⊕ (clLoadTM l).State
  tm := {
    q₀ := .inl 0
    tr := fun q inp work => match q with
      | .inl r =>
        if r = 2 then FinTM.controlAction 0 (some (.inr (0, .inl 0)))
        else clPlacedAction (clPrepareSelect l) Sum.inl r (clInputTM.tm.tr r inp (fun i => work ((clPrepareSelect l).index i)))
      | .inr r => ((clLoadTM l).tm.tr r inp work).mapState Sum.inr }

/-- The complete preparation transducer reaches the loader's blank-target
entry from its own native `initCfg`. No initial work-tape word is assumed.
**Proof sketch.** Lift the native input copier into the final stream slot,
leaving all field targets blank. At its first completed return both heads
are canonical. One silent dispatch enters the row loader. -/
private lemma clPrepare_start (l : ℕ) (x : List Bool) :
    ∃ t ≤ 2 * x.length + 3,
      (clPrepareTM l).tm.runFrom ((clPrepareTM l).tm.initCfg x) t =
      (clLoadCfg x 1 0 (.inl 0) (fun _ : Fin l => []) x 0).mapState Sum.inr := by
  obtain ⟨t, ht, _, hf, he⟩ := clInput_first x
  have lift := clPlaced_run clInputTM.tm (clPrepareTM l).tm (clPrepareSelect l) Sum.inl (by intro a b h; cases h; rfl) (fun q => q ≠ (2 : Fin 3))
    (fun _ hq _ _ => if_neg hq)
    (fun _ _ => none) (fun _ => 0) (clInputTM.tm.initCfg x) t
    (by intro j hj q hq heq; subst q; exact hf j hj hq)
  rw [he] at lift
  have start : clPlacedCfg (clPrepareSelect l) Sum.inl
      (fun _ _ => none) (fun _ => 0) (clInputTM.tm.initCfg x) =
      (clPrepareTM l).tm.initCfg x := by
    apply Cfg.ext <;> simp [MultiTapeTM.initCfg, Cfg.init, clInputTM, clPrepareTM]
    all_goals
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [clPrepareSelect]
  have run := (congrArg (fun z => (clPrepareTM l).tm.runFrom z t) start).symm.trans lift
  have step : (clPrepareTM l).tm.step
      (clPlacedCfg (clPrepareSelect l) Sum.inl (fun _ _ => none) (fun _ => 0)
        (Cfg.ofWords (input := x) (2 : Fin 3) (fun _ : Fin 1 => x))) =
      (clLoadCfg x 1 0 (.inl 0) (fun _ : Fin l => []) x 0).mapState Sum.inr := by
    change (FinTM.controlAction 0 (some (Sum.inr (0, .inl 0) : (clPrepareTM l).State))).apply _ = _
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    all_goals
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro i <;>
        simp [clPrepareSelect, clLoadCfg, Cfg.mapState, Cfg.ofWords]
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', run, step]

/-- Exact field-bank preparation from native input, with an arbitrary
retained trailer and an explicit sequential-copy/read/reset ledger.
**Proof sketch.** The native startup copies the actual input into the
stream buffer, then the loader consumes exactly the fixed number of fields.
All parsed fields survive at head zero; the original encoded input remains
on its tape with the cursor immediately before the trailer. -/
private lemma clPrepare_complete {l : ℕ} (w : Fin l → List Bool)
    (tail : List Bool) (W : ℕ) (hW : ∀ i, (w i).length ≤ W) :
    let x := clFields (List.ofFn w) ++ tail
    ∃ t ≤ 2 * x.length + 3 + l * (3 * W + 7),
      (clPrepareTM l).tm.runFrom ((clPrepareTM l).tm.initCfg x) t =
      (clLoadCfg x 1 (Fin.last l) (.inl 0) w x (clFields (List.ofFn w)).length).mapState Sum.inr := by
  dsimp only
  let x := clFields (List.ofFn w) ++ tail
  obtain ⟨a, ha, he⟩ := clPrepare_start l x
  obtain ⟨b, hb, hbRun⟩ := clLoad_complete x 1 (fun _ : Fin l => []) w [] tail 0 W
    (by simp) hW
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add, Nat.mul_zero] at hbRun hb
  have lift := MultiTapeTM.runFrom_mapState_of_agreeOn (clLoadTM l).tm (clPrepareTM l).tm ⟨Sum.inr, Sum.inr_injective⟩ (fun _ => True)
    (by intros; rfl) (clLoadCfg x 1 0 (.inl 0) (fun _ : Fin l => []) x 0) b
    (by intros; trivial)
  dsimp only [Function.Embedding.coeFn_mk] at lift
  rw [hbRun] at lift
  refine ⟨a + b, by dsimp [x] at ha; omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, he, lift]

/-- Completed native field preparation fixes its full final configuration. -/
private lemma clPrepare_idle {l : ℕ} {x : List Bool}
    (c : Cfg (clPrepareTM l).k Bool (clPrepareTM l).State x)
    (hc : c.state = some (.inr (Fin.last l, .inl 0))) : (clPrepareTM l).tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  simp only [clPrepareTM, clLoadTM, Fin.val_last, Nat.lt_irrefl, dite_false]
  change (FinTM.controlAction 0 (some (Sum.inr (Fin.last l, .inl 0)))).apply c = c
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- The genuine preparatory seam is reached at a positive first return,
including zero fields. Native input copying and dispatch ensure positivity. -/
private lemma clPrepare_first {l : ℕ} (w : Fin l → List Bool)
    (tail : List Bool) (W : ℕ) (hW : ∀ i, (w i).length ≤ W) :
    let x := clFields (List.ofFn w) ++ tail
    ∃ t ≤ 2 * x.length + 3 + l * (3 * W + 7), 0 < t ∧
      (∀ j < t, ((clPrepareTM l).tm.runFrom ((clPrepareTM l).tm.initCfg x) j).state ≠
        some (.inr (Fin.last l, .inl 0))) ∧
      (clPrepareTM l).tm.runFrom ((clPrepareTM l).tm.initCfg x) t =
      (clLoadCfg x 1 (Fin.last l) (.inl 0) w x (clFields (List.ofFn w)).length).mapState Sum.inr := by
  dsimp only
  obtain ⟨B, hB, he⟩ := clPrepare_complete w tail W hW
  obtain ⟨t, ht, hp, hf, hr⟩ := clFirst (clPrepareTM l).tm _ _ (.inr (Fin.last l, .inl 0)) B
    he rfl (by simp [MultiTapeTM.initCfg, Cfg.init, clPrepareTM])
    (fun c hc => clPrepare_idle c hc)
  exact ⟨t, ht.trans hB, hp, hf, hr⟩

/-- A finite list of native word computations can be packed into exact
self-delimiting fields. All repeated input scans are charged by composition. -/
private lemma clNative_fields (fs : List (List Bool → List Bool))
    (hf : ∀ f ∈ fs, PolyTimeComputable f) :
    PolyTimeComputable (fun x => clFields (fs.map (fun f => f x))) := by
  induction fs with
  | nil => exact clNative_linear _ (FinTM.computesFunInTime_const [])
  | cons f fs ih =>
    exact clNative_pair (hf f (by simp)) (ih (by intro g hg; exact hf g (by simp [hg])))

/-- Follow a fixed number of encoded header tails using actual native projections. -/
private def clHeaderTail : ℕ → List Bool → List Bool
  | 0, z => z
  | j + 1, z => ((pairDecode (clHeaderTail j z)).map Prod.snd).getD []

/-- Select a fixed encoded header field; this is implemented by charged scans. -/
private def clHeaderField (j : ℕ) (z : List Bool) : List Bool :=
  ((pairDecode (clHeaderTail j z)).map Prod.fst).getD []

/-- Native computation of a fixed tail, without free indexing into the header. -/
private lemma clHeaderTail_native (j : ℕ) : PolyTimeComputable (clHeaderTail j) := by
  induction j with
  | zero => exact polyTimeComputable_id
  | succ j ih =>
    exact (clNative_linear _ FinTM.computesFunInTime_pairSnd).comp ih

/-- Native computation of a fixed header field, with all projections charged. -/
private lemma clHeaderField_native (j : ℕ) : PolyTimeComputable (clHeaderField j) :=
  (clNative_linear _ FinTM.computesFunInTime_pairFst).comp (clHeaderTail_native j)

/-- Recorder's exact prepared work words, using its established tape layout. -/
private def clRecWords (M : FinTM Bool) (y : List Bool) (T : ℕ) :
    Fin (clRecTM M).k → List Bool :=
  FinTM.tapeBlocks (fun _ : Fin (clRecFields M) => []) []
    (FinTM.tapeBlocks (fun _ : Fin 1 => List.replicate T true) y (fun _ => []))

/-- Four retained exact header fields: instance, certificate length,
reference-input length, and source horizon. -/
private def clHeaderKeep (z : List Bool) : Fin 4 → List Bool :=
  fun i => clHeaderField i.val z

/-- Place the unpacked header into the actual recorder bank and preserve
its four arithmetic/instance fields in a disjoint bank. The unary clock is
the original fifth tail, not a guessed or enlarged horizon. -/
private def clHeaderLayout (M : FinTM Bool) (z : List Bool) :
    Fin ((clRecTM M).k + 4) → List Bool :=
  Fin.addCases
    (FinTM.tapeBlocks (fun _ : Fin (clRecFields M) => []) []
      (FinTM.tapeBlocks (fun _ : Fin 1 => clHeaderTail 5 z) (clHeaderField 4 z) (fun _ => [])))
    (clHeaderKeep z)

/-- Unpacking/repacking into the literal recorder layout is itself native
polynomial-time work, including all field encodings and blank-bank fields.
**Proof sketch.** Every field is either a constant empty word or a fixed
composition of header projections. Pack the finite collection using native
pairing. The number of fields depends only on the fixed source machine. -/
private lemma clHeaderLayout_native (M : FinTM Bool) :
    PolyTimeComputable (fun z => clFields (List.ofFn (clHeaderLayout M z))) := by
  let fs := List.ofFn (fun i : Fin ((clRecTM M).k + 4) => fun z => clHeaderLayout M z i)
  have h : ∀ f ∈ fs, PolyTimeComputable f := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i; simpa [clHeaderLayout, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat] using clNative_linear _ (FinTM.computesFunInTime_const [])
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro i; simpa [clHeaderLayout, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat] using clNative_linear _ (FinTM.computesFunInTime_const [])
        · intro i
          refine Fin.addCases ?_ ?_ i
          · intro i; simpa [clHeaderLayout, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat] using clHeaderTail_native 5
          · intro i
            refine Fin.addCases ?_ ?_ i
            · intro i; simpa [clHeaderLayout, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat] using clHeaderField_native 4
            · intro i; simpa [clHeaderLayout, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat] using clNative_linear _ (FinTM.computesFunInTime_const [])
    · intro i; simpa [clHeaderLayout, clHeaderKeep, -Fin.natAdd_eq_addNat] using clHeaderField_native i.val
  simpa only [fs, List.map_ofFn] using clNative_fields fs h

/-- On the proved arithmetic header, the unpacked recorder words are
exactly its established prepared words; certificate length remains exact. -/
private lemma clHeaderLayout_exact (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool) :
    let Q := C * (x.length + 1) ^ e
    let m := x.length + Q
    let T := c * (A * (m + 1) ^ d + 1) ^ 2
    clHeaderLayout M (clPrepHeader C e c A d x) =
      Fin.addCases (clRecWords M (List.replicate m false) T)
        (fun i : Fin 4 => if i = 0 then x else if i = 1 then Q.bits else if i = 2 then m.bits else T.bits) := by
  dsimp only
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [clHeaderLayout, clRecWords, clHeaderTail, clHeaderField, clPrepHeader,
      pairDecode_pairEncode]
  · intro i
    fin_cases i <;>
      simp [clHeaderLayout, clHeaderKeep, clHeaderTail, clHeaderField, clPrepHeader,
        pairDecode_pairEncode]

/-- Native computation of the exact, retained recorder argument. This
consumes the banked header producer rather than replacing its arithmetic. -/
private lemma clRecordArgument_native (M : FinTM Bool) (C e c A d : ℕ) :
    PolyTimeComputable (fun x =>
      clFields (List.ofFn (clHeaderLayout M (clPrepHeader C e c A d x)))) :=
  (clHeaderLayout_native M).comp (clPrepHeader_native C e c A d)

/-- Recording occupies the leading bank and preserves all five trailing fields. -/
private def clRecordSelect (M : FinTM Bool) : clPlacement (clRecTM M).k (((clRecTM M).k + 4) + 1) :=
  ((clPlacement.refl (clRecTM M).k).sum (clPlacement.empty 4)).sum (clPlacement.empty 1)

/-- Native preparation followed by the unchanged inclusive recorder.
The completed recorder remains live, so later search/packing can be added. -/
private def clRecordTM (M : FinTM Bool) : FinTM Bool where
  k := ((clRecTM M).k + 4) + 1
  State := (clPrepareTM ((clRecTM M).k + 4)).State ⊕ (clRecTM M).State
  tm := {
    q₀ := .inl (clPrepareTM ((clRecTM M).k + 4)).tm.q₀
    tr := fun q inp work => match q with
      | .inl r =>
        if r = .inr (Fin.last ((clRecTM M).k + 4), .inl 0) then
          FinTM.controlAction 0 (some (.inr (clRecTM M).tm.q₀))
        else ((clPrepareTM ((clRecTM M).k + 4)).tm.tr r inp work).mapState Sum.inl
      | .inr r => clPlacedAction (clRecordSelect M) Sum.inr r ((clRecTM M).tm.tr r inp (fun i => work ((clRecordSelect M).index i))) }

/-- Whole retained configuration around a running recorder. The original
encoded native input stays at its final parsing cursor and the four exact
header fields remain at head zero. -/
private def clRecordCfg (M : FinTM Bool) (x : List Bool) (keep : Fin 4 → List Bool)
    (c : Cfg (clRecTM M).k Bool (clRecTM M).State x) :
    Cfg (clRecordTM M).k Bool (clRecordTM M).State x :=
  clPlacedCfg (clRecordSelect M) Sum.inr
    (Fin.addCases (Fin.addCases (fun _ _ => none) (fun i => FinTM.bufferTape (keep i)))
      (fun _ : Fin 1 => FinTM.bufferTape x))
    (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => x.length)) c

/-- Reframe the parsed exact words as the recorder's established prepared
seam, retaining all other words and every administrative head.
**Proof sketch.** Check the active and inactive tape slots separately.
The inherited prepared-seam identity fixes source initialization, counters,
clock and record bank; the retained header fields are disjoint. -/
private lemma clRecord_prepare_frame (M : FinTM Bool) (x y : List Bool) (T : ℕ)
    (keep : Fin 4 → List Bool) :
    { (clLoadCfg x 1 (Fin.last ((clRecTM M).k + 4)) (.inl 0)
        (Fin.addCases (clRecWords M y T) keep) x x.length).mapState
        (fun q => (Sum.inl (Sum.inr q) : (clRecordTM M).State)) with
      state := some (.inr (clRecTM M).tm.q₀) } =
      clRecordCfg M x keep
        (clRecCfg M (x := x) (.inl (some M.tm.q₀, true, (0, 0)))
          (M.tm.initCfg y) (fun _ => 0) [] T 0) := by
  rw [← clRec_prepared]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i <;> intro i <;>
        simp [clRecordCfg, clRecordSelect, clLoadCfg, Cfg.mapState,
          Cfg.ofWords, clRecWords]
    · intro i
      simp [clRecordCfg, clRecordSelect, clLoadCfg, Cfg.mapState, Cfg.ofWords]

/-- From genuine native input, initialize the complete retained reference
layout and run the banked recorder through the inclusive horizon.
**Proof sketch.** Invoke native field preparation at its first completed
return, dispatch once into the exact prepared recorder, then relocate the
banked complete recording run. The total ledger charges native input
copying, every field load/reset, dispatch, and all source/recording work. -/
private lemma clRecord_complete (M : FinTM Bool) (y : List Bool) (T : ℕ)
    (keep : Fin 4 → List Bool) (W : ℕ)
    (hW : ∀ i : Fin ((clRecTM M).k + 4), ((Fin.addCases (clRecWords M y T) keep : Fin ((clRecTM M).k + 4) → List Bool) i).length ≤ W) :
    let x := clFields (List.ofFn (Fin.addCases (clRecWords M y T) keep)) ++ []
    ∃ t ≤ 2 * x.length + 4 + ((clRecTM M).k + 4) * (3 * W + 7) +
        (4 * clRecFields M + 7) * (T + 1) ^ 2,
      (clRecordTM M).tm.runFrom ((clRecordTM M).tm.initCfg x) t =
      clRecordCfg M x keep
        (clRecCfg M (x := x) (.inr (.inr (.inr (.inr ()))))
          (M.tm.runFrom (M.tm.initCfg y) T) (clCounts M y T) (clRecords M y (T + 1)) T T) := by
  dsimp only
  let x := clFields (List.ofFn (Fin.addCases (clRecWords M y T) keep)) ++ []
  have prep := clPrepare_first (Fin.addCases (clRecWords M y T) keep) [] W hW
  obtain ⟨a, ha, _, hf, he⟩ := prep
  have lift := MultiTapeTM.runFrom_mapState_of_agreeOn (clPrepareTM ((clRecTM M).k + 4)).tm (clRecordTM M).tm ⟨Sum.inl, Sum.inl_injective⟩
    (fun q => q ≠ .inr (Fin.last ((clRecTM M).k + 4), .inl 0))
    (fun _ hq _ _ => if_neg hq)
    ((clPrepareTM ((clRecTM M).k + 4)).tm.initCfg x) a
    (by intro j hj q hq heq; subst q; exact hf j hj hq)
  dsimp only [Function.Embedding.coeFn_mk] at lift
  rw [he] at lift
  have init : (((clPrepareTM ((clRecTM M).k + 4)).tm.initCfg x).mapState Sum.inl :
      Cfg (clRecordTM M).k Bool (clRecordTM M).State x) = (clRecordTM M).tm.initCfg x := rfl
  rw [init] at lift
  have dispatch : (clRecordTM M).tm.step
      (((clLoadCfg x 1 (Fin.last ((clRecTM M).k + 4)) (.inl 0)
        (Fin.addCases (clRecWords M y T) keep) x
        (clFields (List.ofFn (Fin.addCases (clRecWords M y T) keep))).length).mapState Sum.inr).mapState Sum.inl) =
      clRecordCfg M x keep
        (clRecCfg M (x := x) (.inl (some M.tm.q₀, true, (0, 0)))
          (M.tm.initCfg y) (fun _ => 0) [] T 0) := by
    change ((clRecordTM M).tm.tr
      (.inl (.inr (Fin.last ((clRecTM M).k + 4), .inl 0))) _ _).apply _ = _
    simp only [clRecordTM, if_true]
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    simpa only [x, List.length_append, List.length_nil, Nat.add_zero] using
      clRecord_prepare_frame M x y T keep
  obtain ⟨b, hb, hrec⟩ := clRec_complete M x y T
  have liftRec := clPlaced_run (clRecTM M).tm (clRecordTM M).tm (clRecordSelect M) Sum.inr (by intro a b h; cases h; rfl) (fun _ => True)
    (by intros; rfl)
    (Fin.addCases (Fin.addCases (fun _ _ => none) (fun i => FinTM.bufferTape (keep i)))
      (fun _ : Fin 1 => FinTM.bufferTape x))
    (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => x.length))
    (clRecCfg M (x := x) (.inl (some M.tm.q₀, true, (0, 0)))
      (M.tm.initCfg y) (fun _ => 0) [] T 0) b (by intros; trivial)
  rw [hrec] at liftRec
  have arrived : (clRecordTM M).tm.runFrom ((clRecordTM M).tm.initCfg x) (a + 1) =
      clRecordCfg M x keep
        (clRecCfg M (x := x) (.inl (some M.tm.q₀, true, (0, 0)))
          (M.tm.initCfg y) (fun _ => 0) [] T 0) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', lift, dispatch]
  refine ⟨a + 1 + b, ?_, ?_⟩
  · have hcost := clRec_cost_bound M T
    omega
  · rw [MultiTapeTM.runFrom_add, arrived]
    exact liftRec

/-- Compare a stored row against two retained target count words by
cross-sums. The order is positive-source, negative-target, positive-target,
negative-source, exactly the banked comparator's arithmetic interface. -/
private def clMatchWords {l : ℕ} (pos neg : Fin l) (row : Fin l → List Bool)
    (target : Fin 2 → List Bool) : Fin 4 → List Bool :=
  fun i => if i = 0 then row pos else if i = 1 then target 1
    else if i = 2 then target 0 else row neg



/-- The matcher loads its row and stream, preserving the four query slots. -/
private def clMatchLoadSelect (l : ℕ) : clPlacement (l + 1) (l + 5) :=
  (clPlacement.refl l).sum ((clPlacement.refl 1).sum (clPlacement.empty 4))

/-- Four distinct comparison slots, with an exact source/host correspondence. -/
private def clMatchCmpSelect {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg) : clPlacement 4 (l + 5) :=
  clPlacement.ofInverse (fun i => if i = 0 then Fin.castAdd 5 pos else if i = 1 then Fin.natAdd l (2 : Fin 5)
    else if i = 2 then Fin.natAdd l (1 : Fin 5) else Fin.castAdd 5 neg) (Fin.addCases (fun i => if i = pos then some 0 else if i = neg then some 3 else none)
    (fun i => if i = 1 then some 2 else if i = 2 then some 1 else none))
    (by intro i; fin_cases i <;> simp [hne, hne.symm, -Fin.natAdd_eq_addNat])
    (by
      intro i j
      fin_cases i <;> refine Fin.addCases ?_ ?_ j <;> intro a h
      all_goals simp only [Fin.addCases_left, Fin.addCases_right] at h
      all_goals split_ifs at h <;> simp_all [-Fin.natAdd_eq_addNat])



/-- Search phases: clock test, sequential row load, native comparison,
and completed live return. Row time is carried by the real unary clock. -/
private abbrev clMatchState (l : ℕ) := Unit ⊕ ((clLoadTM l).State ⊕ (clCmpTM.State ⊕ Unit))

/-- A native all-earlier-row matcher. Each completed comparison stores one
flag in source-time order. The clock is tested before loading, so exactly
its length of rows is inspected; the row at the target time is excluded. -/
private def clMatchTM {l : ℕ} (pos neg : Fin l) : FinTM Bool where
  k := l + 5
  State := clMatchState l
  tm := {
    q₀ := .inl ()
    tr := fun q inp work => match q with
      | .inl _ =>
        if work (Fin.natAdd l (3 : Fin 5)) = none then
          FinTM.controlAction 0 (some (.inr (.inr (.inr ()))))
        else FinTM.controlAction 0 (some (.inr (.inl (0, .inl 0))))
      | .inr (.inl r) =>
        if r = (Fin.last l, .inl 0) then
          FinTM.controlAction 0 (some (.inr (.inr (.inl (.inl (false, false, true))))))
        else clPlacedAction (clMatchLoadSelect l) (fun r => .inr (.inl r)) r ((clLoadTM l).tm.tr r inp (fun i => work ((clMatchLoadSelect l).index i)))
      | .inr (.inr (.inl r)) => match r with
        | .inr (.inr b) =>
          ⟨0, Fin.addCases (fun _ => (none, 0))
            (fun i => if i = 3 then (none, .pos) else if i = 4 then (some (some b), .pos)
              else (none, 0)), none, some (.inl ())⟩
        | r => if hne : pos ≠ neg then clPlacedAction (clMatchCmpSelect pos neg hne) (fun r => .inr (.inr (.inl r))) r (clCmpTM.tm.tr r inp (fun i => work ((clMatchCmpSelect pos neg hne).index i)))
          else FinTM.controlAction 0 none
      | .inr (.inr (.inr _)) => FinTM.controlAction 0 (some q) }

/-- Complete search seam: candidate fields, immutable target count words,
unchanged record stream with explicit cursor, unary query clock, and the
actual stored match prefix. Every binary field head is zero. -/
private def clMatchCfg {l : ℕ} (pos neg : Fin l) (x : List Bool)
    (q : clMatchState l) (row : Fin l → List Bool) (target : Fin 2 → List Bool)
    (stream : List Bool) (cursor : ℤ) (N j : ℕ) (flags : List Bool) :
    Cfg (clMatchTM pos neg).k Bool (clMatchTM pos neg).State x :=
  ⟨some q, 1,
    Fin.addCases (fun i => FinTM.bufferTape (row i))
      (fun i : Fin 5 => FinTM.bufferTape
        (if i = 0 then stream else if i = 1 then target 0 else if i = 2 then target 1
          else if i = 3 then List.replicate N true else flags)),
    Fin.addCases (fun _ => 0) (fun i : Fin 5 =>
      if i = 0 then cursor else if i = 3 then j else if i = 4 then flags.length else 0), []⟩

/-- A nonempty clock dispatches to row loading without advancing source time. -/
private lemma clMatch_tick {l : ℕ} (pos neg : Fin l) (x : List Bool)
    (row : Fin l → List Bool) (target : Fin 2 → List Bool) (stream : List Bool)
    (cursor : ℤ) (N j : ℕ) (flags : List Bool) (hj : j < N) :
    (clMatchTM pos neg).tm.step
      (clMatchCfg pos neg x (.inl ()) row target stream cursor N j flags) =
      clMatchCfg pos neg x (.inr (.inl (0, .inl 0))) row target stream cursor N j flags := by
  have hr : (clMatchCfg pos neg x (.inl ()) row target stream cursor N j flags).workTapeSymbols
      (Fin.natAdd l (3 : Fin 5)) = some true := by
    simp [clMatchCfg, Cfg.workTapeSymbols, hj, -Fin.natAdd_eq_addNat]
  change ((clMatchTM pos neg).tm.tr (.inl ()) _ _).apply _ = _
  simp only [clMatchTM, hr, Option.some_ne_none, if_false]
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- Exhausting the clock stops before inspecting the next row, including
an empty time-zero query. No stream bit is read on this transition. -/
private lemma clMatch_stop {l : ℕ} (pos neg : Fin l) (x : List Bool)
    (row : Fin l → List Bool) (target : Fin 2 → List Bool) (stream : List Bool)
    (cursor : ℤ) (N : ℕ) (flags : List Bool) :
    (clMatchTM pos neg).tm.step
      (clMatchCfg pos neg x (.inl ()) row target stream cursor N N flags) =
      clMatchCfg pos neg x (.inr (.inr (.inr ()))) row target stream cursor N N flags := by
  have hr : (clMatchCfg pos neg x (.inl ()) row target stream cursor N N flags).workTapeSymbols
      (Fin.natAdd l (3 : Fin 5)) = none := by
    simp [clMatchCfg, Cfg.workTapeSymbols, -Fin.natAdd_eq_addNat]
  change ((clMatchTM pos neg).tm.tr (.inl ()) _ _).apply _ = _
  simp only [clMatchTM, hr, if_true]
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- Loader relocation frames both target words, the unary clock, and all
stored flags. It can change the complete candidate row and stream cursor. -/
private lemma clMatch_load_frame {l : ℕ} (pos neg : Fin l) (x : List Bool)
    (q : (clLoadTM l).State) (old row : Fin l → List Bool) (target : Fin 2 → List Bool)
    (stream : List Bool) (cursor oldCursor : ℤ) (N j : ℕ) (flags : List Bool) :
    clPlacedCfg (clMatchLoadSelect l) (fun r => (Sum.inr (.inl r) : clMatchState l))
      (clMatchCfg pos neg x (.inl ()) old target stream oldCursor N j flags).workTapes
      (clMatchCfg pos neg x (.inl ()) old target stream oldCursor N j flags).workTapePos
      (clLoadCfg x 1 q.1 q.2 row stream cursor) =
      clMatchCfg pos neg x (.inr (.inl q)) row target stream cursor N j flags := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;>
    simp only [funext_iff, Fin.forall_fin_add]
  all_goals simp [Fin.forall_fin_succ, clMatchLoadSelect, clMatchCfg, clLoadCfg,
    -Fin.natAdd_eq_addNat]
  all_goals norm_num [Fin.addCases]

/-- One full row is loaded into the native search, including clearing all
old field targets, and the search then dispatches to signed comparison.
**Proof sketch.** Relocate the loader at its positive first return. The
frame theorem preserves all search bookkeeping; charge one more transition
for the dispatch to the fixed four-word comparator. -/
private lemma clMatch_load {l : ℕ} (hl : 0 < l) (pos neg : Fin l) (x : List Bool)
    (old row : Fin l → List Bool) (target : Fin 2 → List Bool)
    (pre tail : List Bool) (N j W : ℕ) (flags : List Bool)
    (hOld : ∀ i, (old i).length ≤ W) (hRow : ∀ i, (row i).length ≤ W) :
    ∃ t ≤ l * (5 * W + 7) + 1,
      (clMatchTM pos neg).tm.runFrom
        (clMatchCfg pos neg x (.inr (.inl (0, .inl 0))) old target
          (pre ++ clFields (List.ofFn row) ++ tail) pre.length N j flags) t =
      clMatchCfg pos neg x (.inr (.inr (.inl (.inl (false, false, true))))) row target
        (pre ++ clFields (List.ofFn row) ++ tail)
        (pre.length + (clFields (List.ofFn row)).length) N j flags := by
  let stream := pre ++ clFields (List.ofFn row) ++ tail
  let start := clMatchCfg pos neg x (.inr (.inl (0, .inl 0))) old target stream pre.length N j flags
  obtain ⟨t, ht, _, hf, he⟩ := clLoad_first hl x 1 old row pre tail W W hOld hRow
  have lift := clPlaced_run (clLoadTM l).tm (clMatchTM pos neg).tm (clMatchLoadSelect l) (fun r => (Sum.inr (.inl r) : clMatchState l)) (by intro a b h; cases h; rfl)
    (fun r => r ≠ (Fin.last l, .inl 0))
    (fun _ hr _ _ => if_neg hr)
    start.workTapes start.workTapePos
    (clLoadCfg x 1 0 (.inl 0) old stream pre.length) t
    (by intro a ha q hq heq; subst q; exact hf a ha hq)
  rw [he] at lift
  have fstFrame := clMatch_load_frame pos neg x (0, .inl 0) old old target stream
    pre.length pre.length N j flags
  have sndFrame := clMatch_load_frame pos neg x (Fin.last l, .inl 0) old row target stream
    (pre.length + (clFields (List.ofFn row)).length) pre.length N j flags
  have run := (congrArg (fun z => (clMatchTM pos neg).tm.runFrom z t) fstFrame).symm.trans
    (lift.trans sndFrame)
  rw [show 2 * W + 3 * W + 7 = 5 * W + 7 by omega] at ht
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', run]
  change ((clMatchTM pos neg).tm.tr (.inr (.inl (Fin.last l, .inl 0))) _ _).apply _ = _
  simp only [clMatchTM, if_true]
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- Comparator relocation preserves the entire search configuration,
including other row fields, stream cursor, clock and accumulated flags.
**Proof sketch.** Four selected slots supply the two cross-sums. Distinct
positive/negative positions ensure the selection is injective. The remaining
row and administrative slots are restored literally from the frame. -/
private lemma clMatch_cmp_frame {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg) (x : List Bool)
    (q : clCmpTM.State) (row : Fin l → List Bool) (target : Fin 2 → List Bool)
    (stream : List Bool) (cursor : ℤ) (N j : ℕ) (flags : List Bool) :
    clPlacedCfg (clMatchCmpSelect pos neg hne) (fun r => (Sum.inr (.inr (.inl r)) : clMatchState l))
      (clMatchCfg pos neg x (.inl ()) row target stream cursor N j flags).workTapes
      (clMatchCfg pos neg x (.inl ()) row target stream cursor N j flags).workTapePos
      (clCmpCfg x 1 q (clMatchWords pos neg row target) 0) =
      clMatchCfg pos neg x (.inr (.inr (.inl q))) row target stream cursor N j flags := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i
      by_cases hp : i = pos
      · subst i; simp [clMatchCmpSelect, clMatchCfg, clCmpCfg, clMatchWords]
      · by_cases hn : i = neg
        · subst i; simp [clMatchCmpSelect, clMatchCfg, clCmpCfg, clMatchWords, hne.symm]
        · simp [clMatchCmpSelect, clMatchCfg, clCmpCfg, hp, hn]
    · intro i; fin_cases i <;>
        simp [clMatchCmpSelect, clMatchCfg, clCmpCfg, clMatchWords]

/-- Commit a comparison flag by one real tape write, and advance exactly
one source-time clock token. This is silent physical-output bookkeeping. -/
private lemma clMatch_commit {l : ℕ} (pos neg : Fin l) (x : List Bool) (b : Bool)
    (row : Fin l → List Bool) (target : Fin 2 → List Bool) (stream : List Bool)
    (cursor : ℤ) (N j : ℕ) (flags : List Bool) :
    (clMatchTM pos neg).tm.step
      (clMatchCfg pos neg x (.inr (.inr (.inl (.inr (.inr b))))) row target stream cursor N j flags) =
      clMatchCfg pos neg x (.inl ()) row target stream cursor N (j + 1) (flags ++ [b]) := by
  change ((clMatchTM pos neg).tm.tr (.inr (.inr (.inl (.inr (.inr b))))) _ _).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i; simp [clMatchTM, clMatchCfg, Action.apply]
    · intro i; fin_cases i <;>
        simp [clMatchTM, clMatchCfg, Action.apply, FinTM.bufferTape_append,
          Nat.cast_add, -Fin.natAdd_eq_addNat]

/-- Signed comparison followed by its actual stored flag and clock update.
**Proof sketch.** Use the banked comparator's first completion of either
verdict, preserve all four words and restore their heads, then execute the
single commit transition. Cross-sum equality, not raw words, determines the flag. -/
private lemma clMatch_compare {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg) (x : List Bool)
    (row : Fin l → List Bool) (target : Fin 2 → List Bool) (stream : List Bool)
    (cursor : ℤ) (N j W : ℕ) (flags : List Bool)
    (hRow : ∀ i, (row i).length ≤ W) (hTarget : ∀ i, (target i).length ≤ W) :
    ∃ t ≤ 2 * W + 3, ∃ b,
      (b = true ↔ clNum (row pos) + clNum (target 1) = clNum (target 0) + clNum (row neg)) ∧
      (clMatchTM pos neg).tm.runFrom
        (clMatchCfg pos neg x (.inr (.inr (.inl (.inl (false, false, true))))) row target
          stream cursor N j flags) t =
      clMatchCfg pos neg x (.inl ()) row target stream cursor N (j + 1) (flags ++ [b]) := by
  let start := clMatchCfg pos neg x (.inl ()) row target stream cursor N j flags
  have widths : ∀ i, (clMatchWords pos neg row target i).length ≤ W := by
    intro i; fin_cases i <;> simp only [clMatchWords, ↓reduceIte] <;>
      first | exact hRow _ | exact hTarget _
  obtain ⟨t, ht, _, b, hb, hf, he⟩ := clCmp_first x 1 (clMatchWords pos neg row target) W widths
  have lift := clPlaced_run clCmpTM.tm (clMatchTM pos neg).tm (clMatchCmpSelect pos neg hne) (fun r => (Sum.inr (.inr (.inl r)) : clMatchState l)) (by intro a b h; cases h; rfl)
    (fun r => ∀ b, r ≠ .inr (.inr b))
    (by
      intro r hr inp work
      cases r with
      | inl r => simp only [clMatchTM, dif_pos hne]; rfl
      | inr r => cases r with
        | inl r => simp only [clMatchTM, dif_pos hne]; rfl
        | inr b => exact False.elim (hr b rfl))
    start.workTapes start.workTapePos
    (clCmpCfg x 1 (.inl (false, false, true)) (clMatchWords pos neg row target) 0) t
    (by intro a ha q hq d heq; subst q; exact hf a ha d hq)
  rw [he] at lift
  have fstFrame := clMatch_cmp_frame pos neg hne x (.inl (false, false, true)) row target
    stream cursor N j flags
  have sndFrame := clMatch_cmp_frame pos neg hne x (.inr (.inr b)) row target stream cursor N j flags
  have run := (congrArg (fun z => (clMatchTM pos neg).tm.runFrom z t) fstFrame).symm.trans
    (lift.trans sndFrame)
  refine ⟨t + 1, by omega, b, ?_, ?_⟩
  · simpa [clMatchWords] using hb
  · rw [MultiTapeTM.runFrom_succ_eq_step', run, clMatch_commit]

/-- Generic ordered rows, using exactly the banked self-delimiting field format. -/
private def clRows {l : ℕ} (row : ℕ → Fin l → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => clRows row n ++ clFields (List.ofFn (row n))

/-- Splitting the sequential row stream preserves its literal suffix. -/
private lemma clRows_add {l : ℕ} (row : ℕ → Fin l → List Bool) (n m : ℕ) :
    clRows row (n + m) = clRows row n ++ clRows (fun i => row (n + i)) m := by
  induction m with
  | zero => simp [clRows]
  | succ m ih => simp [clRows, ih, List.append_assoc, Nat.add_assoc]

/-- A next-row factorization follows from sequence position; obtaining the
row still requires the native loader. No random-access primitive is asserted. -/
private lemma clRows_split {l : ℕ} (row : ℕ → Fin l → List Bool) (N j : ℕ)
    (hj : j < N) (tail : List Bool) :
    ∃ rest, clRows row N ++ tail = clRows row j ++ clFields (List.ofFn (row j)) ++ rest := by
  refine ⟨clRows (fun i => row (j + 1 + i)) (N - (j + 1)) ++ tail, ?_⟩
  rw [show N = (j + 1) + (N - (j + 1)) by omega, clRows_add, clRows]
  simp only [List.append_assoc, Nat.add_sub_cancel_left]

/-- This generic row word is exactly the already-proved stored trajectory. -/
private lemma clRows_records (M : FinTM Bool) (y : List Bool) (n : ℕ) :
    clRows (fun t i => (clCounts M y t i).bits) n = clRecords M y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clRows, clRecords, ih, clRowPrefix_fields _ _ le_rfl,
      List.take_of_length_le (by simp)]

/-- The Boolean written by each signed-position comparison. -/
private def clMatchFlag {l : ℕ} (pos neg : Fin l) (row : Fin l → List Bool)
    (target : Fin 2 → List Bool) : Bool :=
  decide (clNum (row pos) + clNum (target 1) = clNum (target 0) + clNum (row neg))

/-- One complete search iteration: test one live clock token, load exactly
one row, compare cross-sums, store the flag, and advance the real clock.
**Proof sketch.** Compose the three complete-configuration component
contracts and identify the Boolean by its proved equality test. The bound
includes every reset, stream read, comparison, dispatch and flag write. -/
private lemma clMatch_round {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg) (x : List Bool)
    (old row : Fin l → List Bool) (target : Fin 2 → List Bool)
    (pre tail : List Bool) (N j W : ℕ) (flags : List Bool) (hj : j < N)
    (hOld : ∀ i, (old i).length ≤ W) (hRow : ∀ i, (row i).length ≤ W)
    (hTarget : ∀ i, (target i).length ≤ W) :
    ∃ t ≤ l * (5 * W + 7) + 2 * W + 5,
      (clMatchTM pos neg).tm.runFrom
        (clMatchCfg pos neg x (.inl ()) old target
          (pre ++ clFields (List.ofFn row) ++ tail) pre.length N j flags) t =
      clMatchCfg pos neg x (.inl ()) row target
        (pre ++ clFields (List.ofFn row) ++ tail)
        (pre.length + (clFields (List.ofFn row)).length) N (j + 1)
        (flags ++ [clMatchFlag pos neg row target]) := by
  have hl : 0 < l := Nat.zero_lt_of_lt pos.isLt
  obtain ⟨a, ha, he⟩ := clMatch_load hl pos neg x old row target pre tail N j W flags hOld hRow
  obtain ⟨b, hb, v, hv, hr⟩ := clMatch_compare pos neg hne x row target
    (pre ++ clFields (List.ofFn row) ++ tail)
    (pre.length + (clFields (List.ofFn row)).length) N j W flags hRow hTarget
  have hv' : v = clMatchFlag pos neg row target := by
    unfold clMatchFlag
    cases v <;> simp_all
  rw [hv'] at hr
  refine ⟨1 + (a + b), by omega, ?_⟩
  rw [Nat.add_comm 1 (a + b), MultiTapeTM.runFrom_succ_eq_step,
    clMatch_tick pos neg x _ _ _ _ N j flags hj, MultiTapeTM.runFrom_add, he, hr]

/-- Candidate-bank contents before the next sequential row load. -/
private def clPriorRow {l : ℕ} (row : ℕ → Fin l → List Bool) (j : ℕ) : Fin l → List Bool :=
  if j = 0 then fun _ => [] else row (j - 1)

/-- The entire native strict-prefix scan, with one stored flag for each
and only each visited source time.
**Proof sketch.** Induct over the real unary-clock position. Factor the
unchanged stream at the next row and apply the charged iteration theorem.
The previous row is explicitly reset by the loader; the immutable target
words and all accumulated flags are framed throughout. -/
private lemma clMatch_prefix {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg) (x : List Bool)
    (row : ℕ → Fin l → List Bool) (target : Fin 2 → List Bool) (N W : ℕ) (tail : List Bool)
    (hRow : ∀ s < N, ∀ i, (row s i).length ≤ W)
    (hTarget : ∀ i, (target i).length ≤ W) :
    ∀ j, j ≤ N → ∃ t ≤ j * (l * (5 * W + 7) + 2 * W + 5),
      (clMatchTM pos neg).tm.runFrom
        (clMatchCfg pos neg x (.inl ()) (fun _ => []) target (clRows row N ++ tail) 0 N 0 []) t =
      clMatchCfg pos neg x (.inl ()) (clPriorRow row j) target (clRows row N ++ tail)
        (clRows row j).length N j ((List.range j).map (fun s => clMatchFlag pos neg (row s) target)) := by
  intro j
  induction j with
  | zero => intro hj; exact ⟨0, by simp, by simp [clRows, clPriorRow]⟩
  | succ j ih =>
    intro hj
    obtain ⟨a, ha, he⟩ := ih (by omega)
    obtain ⟨rest, hs⟩ := clRows_split row N j (by omega) tail
    have oldWidth : ∀ i, (clPriorRow row j i).length ≤ W := by
      intro i
      by_cases hz : j = 0
      · simp [clPriorRow, hz]
      · simpa only [clPriorRow, if_neg hz] using hRow (j - 1) (by omega) i
    obtain ⟨b, hb, hr⟩ := clMatch_round pos neg hne x (clPriorRow row j) (row j) target
      (clRows row j) rest N j W ((List.range j).map (fun s => clMatchFlag pos neg (row s) target))
      (by omega) oldWidth (hRow j (by omega)) hTarget
    rw [← hs] at hr
    refine ⟨a + b, ?_, ?_⟩
    · calc
        a + b ≤ j * (l * (5 * W + 7) + 2 * W + 5) +
          (l * (5 * W + 7) + 2 * W + 5) := by omega
        _ = (j + 1) * (l * (5 * W + 7) + 2 * W + 5) := by ring
    · rw [MultiTapeTM.runFrom_add, he]
      simpa [clPriorRow, clRows, List.range_succ, List.map_append, Nat.cast_add] using hr

/-- Complete bounded search over exactly the first `N` rows. The next row
and arbitrary tail are untouched. At `N=0` only the silent stop executes. -/
private lemma clMatch_complete {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg) (x : List Bool)
    (row : ℕ → Fin l → List Bool) (target : Fin 2 → List Bool) (N W : ℕ) (tail : List Bool)
    (hRow : ∀ s < N, ∀ i, (row s i).length ≤ W)
    (hTarget : ∀ i, (target i).length ≤ W) :
    ∃ t ≤ N * (l * (5 * W + 7) + 2 * W + 5) + 1,
      (clMatchTM pos neg).tm.runFrom
        (clMatchCfg pos neg x (.inl ()) (fun _ => []) target (clRows row N ++ tail) 0 N 0 []) t =
      clMatchCfg pos neg x (.inr (.inr (.inr ()))) (clPriorRow row N) target
        (clRows row N ++ tail) (clRows row N).length N N
        ((List.range N).map (fun s => clMatchFlag pos neg (row s) target)) := by
  obtain ⟨t, ht, he⟩ := clMatch_prefix pos neg hne x row target N W tail hRow hTarget N le_rfl
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', he, clMatch_stop]

/-- A query against the stored schedule uses precisely signed equality. -/
private lemma clMatchFlag_schedule (M : FinTM Bool) (m s t : ℕ) (τ : Fin M.k) :
    clMatchFlag (Fin.castAdd (1 + M.k) (Fin.natAdd 1 τ))
      (Fin.natAdd (1 + M.k) (Fin.natAdd 1 τ))
      (fun i => (clCounts M (List.replicate m false) s i).bits)
      (clTwo (clCounts M (List.replicate m false) t (Fin.castAdd (1 + M.k) (Fin.natAdd 1 τ))).bits
        (clCounts M (List.replicate m false) t (Fin.natAdd (1 + M.k) (Fin.natAdd 1 τ))).bits) =
      decide (workPosAt M m s τ = workPosAt M m t τ) := by
  unfold clMatchFlag
  simp only [clTwo, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, if_false, clNum_bits]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [← clSigned_eq, (clCounts_schedule M m s).2 τ, (clCounts_schedule M m t).2 τ]

/-- Compact unambiguous optional-time code. Empty is no visit; a present
visit stores an aligned separator and its canonical little-endian index. -/
private def clVisitCode : Option ℕ → List Bool
  | none => []
  | some s => pairEncode [] s.bits

/-- The greatest marked time in an ordered flag stream, computed by a
real reverse marker scan followed by a native binary length computation. -/
private def clLastCode (flags : List Bool) : List Bool :=
  clVisitCode ((splitAtLastTrue flags).map List.length)

/-- The last-visit code has an actual polynomial-time native producer.
**Proof sketch.** Thread the flag word through the audited last-true
stripper. Its absent result is malformed as a pair and maps to the empty
code. Otherwise compute the stripped prefix's binary length on the payload;
the result is exactly the index of the last marked row. -/
private lemma clLastCode_native : PolyTimeComputable clLastCode := by
  obtain ⟨S, a, hS⟩ := FinTM.computesFunInTime_stripLast
  have hstrip : PolyTimeComputable (fun x => match pairDecode x with
      | some (u, v) => match splitAtLastTrue v with
        | some w => pairEncode u w
        | none => []
      | none => []) := ⟨S, a, 2, hS⟩
  have hz := clNative_linear _ (FinTM.computesFunInTime_const [])
  have hb := clNative_linear _ FinTM.computesFunInTime_lengthBits
  have h := (clNative_map hb).comp (hstrip.comp (clNative_pair hz polyTimeComputable_id))
  convert h using 1
  funext flags
  simp only [Function.comp_def, pairDecode_pairEncode]
  cases hs : splitAtLastTrue flags <;>
    simp [clLastCode, clVisitCode, hs, pairDecode_pairEncode] <;> rfl

/-- The marker stripper has the exact streaming recurrence: a false flag
preserves the previous candidate and a true flag selects the whole old prefix. -/
private lemma clLastMarker_step (w : List Bool) (b : Bool) :
    splitAtLastTrue (w ++ [b]) = if b then some w else splitAtLastTrue w := by
  cases b <;> simp [splitAtLastTrue]

/-- Pure index tracker for the native ordered comparison flags. It scans
all and only indices below its bound, replacing the candidate at every match. -/
private def clLastIndex (P : ℕ → Bool) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => if P n then some n else clLastIndex P n

/-- The native marker result implements the precise last-candidate recurrence. -/
private lemma clLastIndex_marker (P : ℕ → Bool) (n : ℕ) :
    (splitAtLastTrue ((List.range n).map P)).map List.length = clLastIndex P n := by
  induction n with
  | zero => simp [clLastIndex, splitAtLastTrue]
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [clLastMarker_step, clLastIndex]
    split <;> simp_all

/-- The last candidate is the maximum filtered index, not an arbitrary
match. This also certifies the empty candidate set at time zero.
**Proof sketch.** At a new matching index, every old index is strictly
smaller, so the new index is the unique maximum. At a nonmatch the filtered
list and candidate are both unchanged. -/
private lemma clLastIndex_max (P : ℕ → Bool) (n : ℕ) :
    clLastIndex P n = ((List.range n).filter P).max? := by
  induction n with
  | zero => simp [clLastIndex]
  | succ n ih =>
    rw [clLastIndex, List.range_succ, List.filter_append]
    by_cases hp : P n = true
    · simp only [hp, if_true, List.filter_cons, List.filter_nil]
      symm
      apply List.max?_eq_some_iff.mpr
      constructor
      · simp
      · intro a ha
        simp only [List.mem_append, List.mem_filter, List.mem_range,
          List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ⟨ha, _⟩ | rfl <;> omega
    · simp only [hp, Bool.false_eq_true, if_false, List.filter_cons, List.filter_nil,
        List.append_nil]
      exact ih

/-- Code of the native strict-earlier flags is precisely the public
last-visit schedule, with canonical binary time encoding. -/
private lemma clLastCode_prev (M : FinTM Bool) (m t : ℕ) (τ : Fin M.k) :
    clLastCode ((List.range t).map (fun s => decide (workPosAt M m s τ = workPosAt M m t τ))) =
      clVisitCode (prevVisit M m t τ) := by
  unfold clLastCode
  rw [clLastIndex_marker, clLastIndex_max]
  delta prevVisit
  congr 3

/-- Replay a stored buffer to physical output, starting at its right blank.
The rewind is explicit and the final blank transition physically halts. -/
private def clReplayTM : FinTM Bool where
  k := 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q _ work =>
      if q = 0 then ⟨0, fun _ => (none, .neg), none, some 1⟩
      else if q = 1 then
        if work 0 = none then ⟨0, fun _ => (none, .pos), none, some 2⟩
        else ⟨0, fun _ => (none, .neg), none, some 1⟩
      else match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some 2⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Complete replay configuration, retaining its buffer and native input head. -/
private def clReplayCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option (Fin 3)) (w : List Bool) (z : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 3) x :=
  ⟨q, p, fun _ => FinTM.bufferTape w, fun _ => z, out⟩

/-- Replay's backward scan restores the buffer head by reading each
occupied prefix cell, including the empty-buffer case.
**Proof sketch.** Induct on the occupied prefix length. Each present bit moves left without writing; the left blank moves right exactly once to the first output cell. -/
private lemma clReplay_back (x : List Bool) (p : Fin (x.length + 2)) (w out : List Bool) :
    ∀ j, j ≤ w.length →
      clReplayTM.tm.runFrom (clReplayCfg x p (some 1) w ((j : ℤ) - 1) out) (j + 1) =
        clReplayCfg x p (some 2) w 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Cfg.workTapeSymbols, Action.apply, funext_iff]
  | succ j ih =>
    intro hj
    have hr : FinTM.bufferTape w (j : ℤ) = some w[j] := by
      rw [FinTM.bufferTape_nat]; exact List.getElem?_eq_getElem (by omega)
    have step : clReplayTM.tm.step (clReplayCfg x p (some 1) w j out) =
        clReplayCfg x p (some 1) w ((j : ℤ) - 1) out := by
      change (clReplayTM.tm.tr (1 : Fin 3) _ _).apply _ = _
      simp only [clReplayTM, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true,
        clReplayCfg, Cfg.workTapeSymbols, hr, Option.some_ne_none]
      apply Cfg.ext <;> simp [Action.apply, sub_eq_add_neg]
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = j by omega,
      MultiTapeTM.runFrom_succ_eq_step, step]
    exact ih (by omega)

/-- Forward replay emits precisely the unread suffix, then halts without
adding a spurious verdict or terminator.
**Proof sketch.** At each occupied cell append exactly its bit and advance
one cell. The actual right blank executes the final silent halt. -/
private lemma clReplay_forward (x : List Bool) (p : Fin (x.length + 2)) (w : List Bool) :
    ∀ j, j ≤ w.length → ∀ out,
      clReplayTM.tm.runFrom (clReplayCfg x p (some 2) w j out) (w.length - j + 1) =
        clReplayCfg x p none w w.length (out ++ w.drop j) := by
  intro j hj
  induction h : w.length - j generalizing j with
  | zero =>
    intro out
    have hj' : j = w.length := by omega
    subst j
    rw [zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Cfg.workTapeSymbols, Action.apply, funext_iff]
  | succ r ih =>
    intro out
    have hjl : j < w.length := by omega
    have hr : FinTM.bufferTape w (j : ℤ) = some w[j] := by
      rw [FinTM.bufferTape_nat]; exact List.getElem?_eq_getElem hjl
    have step : clReplayTM.tm.step (clReplayCfg x p (some 2) w j out) =
        clReplayCfg x p (some 2) w (j + 1) (out ++ [w[j]]) := by
      change (clReplayTM.tm.tr (2 : Fin 3) _ _).apply _ = _
      simp only [clReplayTM, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        if_false, clReplayCfg, Cfg.workTapeSymbols, hr]
      apply Cfg.ext <;> simp [Action.apply, funext_iff]
    rw [MultiTapeTM.runFrom_succ_eq_step, step]
    have finish := ih (j + 1) (by omega) (by omega) (out ++ [w[j]])
    simpa only [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hjl] using finish

/-- Complete replay from the right blank charges its initial left move,
full rewind, every emitted bit, and physical halt. -/
private lemma clReplay_run (x : List Bool) (p : Fin (x.length + 2)) (w out : List Bool) :
    clReplayTM.tm.runFrom (clReplayCfg x p (some 0) w w.length out) (2 * w.length + 3) =
      clReplayCfg x p none w w.length (out ++ w) := by
  have release : clReplayTM.tm.step (clReplayCfg x p (some 0) w w.length out) =
      clReplayCfg x p (some 1) w (w.length - 1) out := by
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Action.apply, funext_iff, sub_eq_add_neg]
  rw [show 2 * w.length + 3 = ((w.length + 1) + (w.length + 1)) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, release, MultiTapeTM.runFrom_add,
    clReplay_back x p w out w.length le_rfl]
  simpa only [Nat.sub_zero, Nat.cast_zero, List.drop_zero] using
    clReplay_forward x p w 0 (by omega) out

/-- A singleton replay acts on exactly its chosen physical tape. -/
private def clOneSelect {k : ℕ} (i : Fin k) : clPlacement 1 k :=
  clPlacement.ofInverse (fun _ => i) (fun j => if j = i then some 0 else none)
    (by intro j; have hj := Fin.eq_zero j; subst j; simp)
    (by
      intro a b h
      by_cases hb : b = i
      · exact hb.symm
      · simp [hb] at h)

/-- Turn an absorbing live completion into a physical replay of one buffer.
The source computation and its startup remain unchanged before that return. -/
private def clOutputTM (A : FinTM Bool) (ret : A.State) (i : Fin A.k) : FinTM Bool where
  k := A.k
  State := A.State ⊕ Fin 3
  tm := {
    q₀ := .inl A.tm.q₀
    tr := fun q inp work => match q with
      | .inl q => if q = ret then FinTM.controlAction 0 (some (.inr 0))
          else (A.tm.tr q inp work).mapState Sum.inl
      | .inr q => clPlacedAction (clOneSelect i) Sum.inr q (clReplayTM.tm.tr q inp (fun _ => work i)) }

/-- A completed producer buffer can be physically returned with its exact
word and an explicit replay ledger. Only the supplied source contract is used.
**Proof sketch.** Cut the source's absorbing completion to its first visit,
then dispatch once into replay. The selected full tape equals the supplied
word at its right blank; every other tape is framed. Replay emits exactly
that word and halts, and the endpoint is padded only by halted absorption. -/
private lemma clOutput_compute (A : FinTM Bool) (ret : A.State) (i : Fin A.k)
    (x w : List Bool) (a : ℕ) (d : Cfg A.k Bool A.State x)
    (hrun : A.tm.runFrom (A.tm.initCfg x) a = d) (hret : d.state = some ret)
    (hstart : A.tm.q₀ ≠ ret)
    (hidle : ∀ c : Cfg A.k Bool A.State x, c.state = some ret → A.tm.step c = c)
    (hout : d.output = []) (hword : d.workTapes i = FinTM.bufferTape w)
    (hhead : d.workTapePos i = w.length) :
    (clOutputTM A ret i).ComputesInTime x w (a + 2 * w.length + 4) := by
  obtain ⟨t, ht, _, hf, he⟩ := clFirst A.tm (A.tm.initCfg x) d ret a hrun hret
    (by intro h; apply hstart; exact Option.some.inj h) hidle
  have lift := MultiTapeTM.runFrom_mapState_of_agreeOn A.tm (clOutputTM A ret i).tm ⟨Sum.inl, Sum.inl_injective⟩ (fun q => q ≠ ret)
    (fun _ hq _ _ => if_neg hq) (A.tm.initCfg x) t
    (by intro j hj q hq heq; subst q; exact hf j hj hq)
  dsimp only [Function.Embedding.coeFn_mk] at lift
  rw [he] at lift
  have init : ((A.tm.initCfg x).mapState Sum.inl :
      Cfg A.k Bool (clOutputTM A ret i).State x) = (clOutputTM A ret i).tm.initCfg x := rfl
  rw [init] at lift
  let framed := clPlacedCfg (clOneSelect i) (Sum.inr : Fin 3 → (clOutputTM A ret i).State)
    d.workTapes d.workTapePos (clReplayCfg x d.inputPos (some 0) w w.length [])
  have dispatch : (clOutputTM A ret i).tm.step (d.mapState Sum.inl) = framed := by
    have hs : (d.mapState (Sum.inl : A.State → (clOutputTM A ret i).State)).state =
        some (.inl ret) := by simp [Cfg.mapState, hret]
    unfold MultiTapeTM.step
    rw [hs]
    simp only [clOutputTM, if_true]
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext j
      by_cases hj : j = i
      · subst j; simpa [framed, clOneSelect, clReplayCfg] using hword
      · simp [framed, clOneSelect, clReplayCfg, Cfg.mapState, hj]
    · funext j
      by_cases hj : j = i
      · subst j; simpa [framed, clOneSelect, clReplayCfg] using hhead
      · simp [framed, clOneSelect, clReplayCfg, Cfg.mapState, hj]
    · exact hout
  have replay := clPlaced_run clReplayTM.tm (clOutputTM A ret i).tm (clOneSelect i) Sum.inr (by intro a b h; cases h; rfl) (fun _ => True) (by intros; rfl) d.workTapes d.workTapePos
    (clReplayCfg x d.inputPos (some 0) w w.length []) (2 * w.length + 3) (by intros; trivial)
  rw [clReplay_run] at replay
  have hc : (clOutputTM A ret i).ComputesInTime x w (t + 1 + (2 * w.length + 3)) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    have arrived : (clOutputTM A ret i).tm.runFrom ((clOutputTM A ret i).tm.initCfg x) (t + 1) =
        framed := by rw [MultiTapeTM.runFrom_succ_eq_step', lift, dispatch]
    rw [MultiTapeTM.runFrom_add, arrived, replay]
    exact ⟨rfl, by simp [clReplayCfg]⟩
  exact hc.mono (by omega)

/-- Initialize arbitrary exact work words from self-delimiting native input,
then invoke the supplied prepared machine. The retained input has its own tape. -/
private def clPreparedTM (A : FinTM Bool) : FinTM Bool where
  k := A.k + 1
  State := (clPrepareTM A.k).State ⊕ A.State
  tm := seamCompTM (clPrepareTM A.k).tm (.inr (Fin.last A.k, .inl 0))
    (embedEmitTM (clKeepLastPlacement A.k).index A.tm) A.tm.q₀

/-- Exact surrounding frame for a prepared computation after native loading. -/
private def clPreparedCfg (A : FinTM Bool) (x : List Bool) (cursor : ℤ)
    (c : Cfg A.k Bool A.State x) : Cfg (clPreparedTM A).k Bool (clPreparedTM A).State x :=
  clPlacedCfg (clKeepLastPlacement _) Sum.inr
    (Fin.addCases (fun _ _ => none) (fun _ : Fin 1 => FinTM.bufferTape x))
    (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => cursor)) c

/-- Generic prepared computation reached from genuine native input.
**Proof sketch.** Run the native loader to its first complete return and
dispatch once. Relocate the supplied machine into the loaded bank while
preserving the original input buffer. Its actual prepared run then gives
the full endpoint; no cleanup or random access is assumed. -/
private lemma clPrepared_run (A : FinTM Bool) (w : Fin A.k → List Bool) (tail : List Bool)
    (W : ℕ) (hW : ∀ i, (w i).length ≤ W) (b : ℕ) :
    let x := clFields (List.ofFn w) ++ tail
    ∃ a ≤ 2 * x.length + 4 + A.k * (3 * W + 7),
      (clPreparedTM A).tm.runFrom ((clPreparedTM A).tm.initCfg x) (a + b) =
      clPreparedCfg A x (clFields (List.ofFn w)).length
        (A.tm.runFrom (Cfg.ofWords (input := x) A.tm.q₀ w) b) := by
  dsimp only
  let x := clFields (List.ofFn w) ++ tail
  obtain ⟨a, ha, _, hf, he⟩ := clPrepare_first w tail W hW
  have lift := MultiTapeTM.runFrom_mapState_of_agreeOn (clPrepareTM A.k).tm (clPreparedTM A).tm ⟨Sum.inl, Sum.inl_injective⟩
    (fun q => q ≠ .inr (Fin.last A.k, .inl 0))
    (fun _ hq _ _ => if_neg hq)
    ((clPrepareTM A.k).tm.initCfg x) a
    (by intro j hj q hq heq; subst q; exact hf j hj hq)
  dsimp only [Function.Embedding.coeFn_mk] at lift
  rw [he] at lift
  have init : (((clPrepareTM A.k).tm.initCfg x).mapState Sum.inl :
      Cfg (clPreparedTM A).k Bool (clPreparedTM A).State x) = (clPreparedTM A).tm.initCfg x := rfl
  rw [init] at lift
  have dispatch : (clPreparedTM A).tm.step
      (((clLoadCfg x 1 (Fin.last A.k) (.inl 0) w x (clFields (List.ofFn w)).length).mapState
        Sum.inr).mapState Sum.inl) =
      clPreparedCfg A x (clFields (List.ofFn w)).length (Cfg.ofWords (input := x) A.tm.q₀ w) := by
    change ((clPreparedTM A).tm.tr (.inl (.inr (Fin.last A.k, .inl 0))) _ _).apply _ = _
    simp only [clPreparedTM, seamCompTM, if_true]
    erw [FinTM.controlAction_apply, moveInputPos_zero]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    all_goals
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro i <;>
        simp [clPreparedCfg, clKeepLastPlacement, clLoadCfg, Cfg.mapState, Cfg.ofWords]
  have run := clPlaced_run A.tm (clPreparedTM A).tm (clKeepLastPlacement _) Sum.inr (by intro a b h; cases h; rfl) (fun _ => True) (by intros; rfl)
    (Fin.addCases (fun _ _ => none) (fun _ : Fin 1 => FinTM.bufferTape x))
    (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => ((clFields (List.ofFn w)).length : ℤ)))
    (Cfg.ofWords (input := x) A.tm.q₀ w) b (by intros; trivial)
  have arrived : (clPreparedTM A).tm.runFrom ((clPreparedTM A).tm.initCfg x) (a + 1) =
      clPreparedCfg A x (clFields (List.ofFn w)).length (Cfg.ofWords (input := x) A.tm.q₀ w) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', lift, dispatch]
  refine ⟨a + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, arrived]
  exact run

/-- An absorbing return in the prepared machine remains absorbing after
native loading, with the complete retained-input frame fixed. -/
private lemma clPrepared_idle (A : FinTM Bool) (ret : A.State)
    (htr : ∀ inp work, A.tm.tr ret inp work = FinTM.controlAction 0 (some ret))
    {x : List Bool} (c : Cfg (clPreparedTM A).k Bool (clPreparedTM A).State x)
    (hc : c.state = some (.inr ret)) : (clPreparedTM A).tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  change (clPlacedAction (clKeepLastPlacement A.k) Sum.inr ret
    (A.tm.tr ret c.inputSymbol (fun i => c.workTapeSymbols ((clKeepLastPlacement A.k).index i)))).apply c = c
  rw [htr]
  have ha : clPlacedAction (clKeepLastPlacement A.k) (Sum.inr : A.State → (clPreparedTM A).State) ret (FinTM.controlAction 0 (some ret)) =
      FinTM.controlAction 0 (some (.inr ret)) := by
    rw [clPlacedAction_eq]
    unfold FinTM.controlAction
    congr 1
    funext i
    cases (clKeepLastPlacement A.k).select i <;> rfl
  rw [ha, FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- Native query argument words: blank candidate fields, retained record
stream, two target counts, a unary strict-prefix clock, and blank flags. -/
private def clQueryWords (l : ℕ) (target : Fin 2 → List Bool) (stream : List Bool) (N : ℕ) :
    Fin (l + 5) → List Bool :=
  Fin.addCases (fun _ => []) (fun i : Fin 5 =>
    if i = 0 then stream else if i = 1 then target 0 else if i = 2 then target 1
      else if i = 3 then List.replicate N true else [])

/-- Exact native-query prepared seam, including every scratch tape/head. -/
private lemma clQuery_initial {l : ℕ} (pos neg : Fin l) (x : List Bool)
    (target : Fin 2 → List Bool) (stream : List Bool) (N : ℕ) :
    Cfg.ofWords (input := x) (clMatchTM pos neg).tm.q₀ (clQueryWords l target stream N) =
      clMatchCfg pos neg x (.inl ()) (fun _ => []) target stream 0 N 0 [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i; simp [Cfg.ofWords, clMatchCfg, clQueryWords]
    · intro i; fin_cases i <;> simp [Cfg.ofWords, clMatchCfg, clQueryWords]

/-- The all-earlier matcher has a fresh absorbing live return. -/
private lemma clMatch_return {l : ℕ} (pos neg : Fin l) (inp : Option Bool)
    (work : Fin (l + 5) → Option Bool) :
    (clMatchTM pos neg).tm.tr (.inr (.inr (.inr ()))) inp work =
      FinTM.controlAction 0 (some (.inr (.inr (.inr ())))) := rfl

/-- Complete native query transducer: prepare from actual encoded input,
scan exactly the clocked strict prefix, then physically return the flags. -/
private def clQueryFlagsTM {l : ℕ} (pos neg : Fin l) : FinTM Bool :=
  clOutputTM (clPreparedTM (clMatchTM pos neg)) (.inr (.inr (.inr (.inr ()))))
    (Fin.castAdd 1 (Fin.natAdd l (4 : Fin 5)))

/-- Native query output and total component ledger, from genuine input.
**Proof sketch.** Parse the full query argument, execute the actual native
matcher, and replay its stored flags. The total charges argument copying,
all preparation resets/reads, every query row, every cross-sum comparison,
all dispatches, flag writes, rewind, replay and halt. -/
private lemma clQueryFlags_compute {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg)
    (row : ℕ → Fin l → List Bool) (target : Fin 2 → List Bool) (N W U : ℕ) (tail : List Bool)
    (hRow : ∀ s < N, ∀ i, (row s i).length ≤ W)
    (hTarget : ∀ i, (target i).length ≤ W)
    (hWords : ∀ i, (clQueryWords l target (clRows row N ++ tail) N i).length ≤ U) :
    let arg := clFields (List.ofFn (clQueryWords l target (clRows row N ++ tail) N)) ++ []
    (clQueryFlagsTM pos neg).ComputesInTime arg
      ((List.range N).map (fun s => clMatchFlag pos neg (row s) target))
      (2 * arg.length + 9 + (l + 5) * (3 * U + 7) +
        N * (l * (5 * W + 7) + 2 * W + 7)) := by
  dsimp only
  let arg := clFields (List.ofFn (clQueryWords l target (clRows row N ++ tail) N)) ++ []
  let flags := (List.range N).map (fun s => clMatchFlag pos neg (row s) target)
  have hlen : flags.length = N := by simp [flags]
  obtain ⟨b, hb, he⟩ := clMatch_complete pos neg hne arg row target N W tail hRow hTarget
  obtain ⟨a, ha, hr⟩ := clPrepared_run (clMatchTM pos neg)
    (clQueryWords l target (clRows row N ++ tail) N) [] U hWords b
  rw [clQuery_initial, he] at hr
  let d := clPreparedCfg (clMatchTM pos neg) arg
    (clFields (List.ofFn (clQueryWords l target (clRows row N ++ tail) N))).length
    (clMatchCfg pos neg arg (.inr (.inr (.inr ()))) (clPriorRow row N) target
      (clRows row N ++ tail) (clRows row N).length N N flags)
  have hd : (clPreparedTM (clMatchTM pos neg)).tm.runFrom
      ((clPreparedTM (clMatchTM pos neg)).tm.initCfg arg) (a + b) = d := hr
  have hc := clOutput_compute (clPreparedTM (clMatchTM pos neg))
    (.inr (.inr (.inr (.inr ())))) (Fin.castAdd 1 (Fin.natAdd l (4 : Fin 5)))
    arg flags (a + b) d hd rfl (by simp [clPreparedTM, seamCompTM])
    (fun c hc => clPrepared_idle (clMatchTM pos neg) (.inr (.inr (.inr ())))
      (clMatch_return pos neg) c hc) rfl
    (by simp [d, clPreparedCfg, clKeepLastPlacement, clMatchCfg, -Fin.natAdd_eq_addNat])
    (by simp [d, clPreparedCfg, clKeepLastPlacement, clMatchCfg, -Fin.natAdd_eq_addNat])
  apply hc.mono
  rw [hlen]
  have hcN : N * (l * (5 * W + 7) + 2 * W + 7) =
      N * (l * (5 * W + 7) + 2 * W + 5) + 2 * N := by ring
  rw [hcN]
  change a ≤ 2 * arg.length + 4 + (l + 5) * (3 * U + 7) at ha
  dsimp only [arg] at ha
  exact by omega

/-- The last marked source time is returned by one native transducer with
all flag generation, reverse search and binary output work in its bound.
Only canonical query inputs are promised; later callers must establish them. -/
private lemma clQueryCode_machine {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg) :
    ∃ (Q : FinTM Bool) (c e : ℕ),
      ∀ (row : ℕ → Fin l → List Bool) (target : Fin 2 → List Bool) (N W U : ℕ) (tail : List Bool),
        (∀ s < N, ∀ i, (row s i).length ≤ W) →
        (∀ i, (target i).length ≤ W) →
        (∀ i, (clQueryWords l target (clRows row N ++ tail) N i).length ≤ U) →
        let arg := clFields (List.ofFn (clQueryWords l target (clRows row N ++ tail) N)) ++ []
        Q.ComputesInTime arg
          (clLastCode ((List.range N).map (fun s => clMatchFlag pos neg (row s) target)))
          (2 * (2 * arg.length + 9 + (l + 5) * (3 * U + 7) +
            N * (l * (5 * W + 7) + 2 * W + 7)) + c * (N + 1) ^ e + 2) := by
  obtain ⟨L, c, e, hL⟩ := clLastCode_native
  refine ⟨FinTM.bufferedCompTM (clQueryFlagsTM pos neg) L, c, e, ?_⟩
  intro row target N W U tail hRow hTarget hWords
  have hQ := clQueryFlags_compute pos neg hne row target N W U tail hRow hTarget hWords
  have h := FinTM.bufferedCompTM_computesInTime (clQueryFlagsTM pos neg) L hQ
    (hL ((List.range N).map (fun s => clMatchFlag pos neg (row s) target)))
  have hlen : ((List.range N).map (fun s => clMatchFlag pos neg (row s) target)).length ≤
      2 * (clFields (List.ofFn (clQueryWords l target (clRows row N ++ tail) N)) ++ []).length +
        9 + (l + 5) * (3 * U + 7) + N * (l * (5 * W + 7) + 2 * W + 7) := by
    rw [← ((FinTM.computesInTime_iff _ _ _ _).mp hQ).2]
    exact (clQueryFlagsTM pos neg).tm.output_length_le _ _
  apply h.mono
  simp only [List.length_map, List.length_range] at hlen ⊢
  omega

/-- Each field's complete word is contained, doubled, in the actual encoded
argument; the bound includes separators and does not assume random access. -/
private lemma clFields_width (ws : List (List Bool)) (w : List Bool) (hw : w ∈ ws) :
    w.length ≤ (clFields ws).length := by
  induction ws with
  | nil => simp at hw
  | cons u us ih =>
    simp only [List.mem_cons] at hw
    have hl : (clFields (u :: us)).length = 2 * u.length + 2 + (clFields us).length := by
      simp [clFields, pairEncode, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
    rw [hl]
    rcases hw with rfl | hw
    · omega
    · have := ih hw; omega

/-- The recorder's observed completed state is absorbing with its full
retained input/header frame unchanged.
**Proof sketch.** Unfold only the completed recorder transition and its relocation. Its action preserves every cell and head and selects the same return control. -/
private lemma clRecord_idle (M : FinTM Bool) {x : List Bool}
    (c : Cfg (clRecordTM M).k Bool (clRecordTM M).State x)
    (hc : c.state = some (.inr (.inr (.inr (.inr (.inr ())))))) :
    (clRecordTM M).tm.step c = c := by
  unfold MultiTapeTM.step
  rw [hc]
  simp only [clRecordTM, clRecTM]
  have ha : clPlacedAction (clRecordSelect M) (Sum.inr : (clRecTM M).State → (clRecordTM M).State) (.inr (.inr (.inr (.inr ())))) (FinTM.controlAction 0 (some (.inr (.inr (.inr (.inr ())))))) =
      FinTM.controlAction 0 (some (.inr (.inr (.inr (.inr (.inr ())))))) := by
    rw [clPlacedAction_eq]
    unfold FinTM.controlAction
    congr 1
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [clRecordSelect]
    · intro i; simp [clRecordSelect]
  rw [ha, FinTM.controlAction_apply, moveInputPos_zero]
  cases c
  simp_all

/-- The actual trajectory tape can be returned as the entire physical
output. This preserves effects-first reference recording and its silence. -/
private def clRecordOutputTM (M : FinTM Bool) : FinTM Bool :=
  clOutputTM (clRecordTM M) (.inr (.inr (.inr (.inr (.inr ())))))
    ((clRecordSelect M).index (Fin.natAdd (clRecFields M) (Fin.castAdd (1 + (1 + M.k)) (0 : Fin 1))))

/-- Arithmetic for recorded output, separate from its native transitions. -/
private lemma clRecord_replay_budget (n k l W T R a : ℕ)
    (ha : a ≤ 2 * n + 4 + k * (3 * W + 7) + (4 * l + 7) * (T + 1) ^ 2)
    (hr : R ≤ 2 * l * (T + 1) ^ 2) :
    a + 2 * R + 4 ≤ 2 * n + 8 + k * (3 * W + 7) + (8 * l + 7) * (T + 1) ^ 2 := by
  ring_nf at ha hr ⊢
  omega

/-- A quadratic envelope for preparation, inclusive recording and replay. -/
private lemma clRecord_size_budget (n k l T : ℕ) (hT : T ≤ n) :
    2 * n + 8 + k * (3 * n + 7) + (8 * l + 7) * (T + 1) ^ 2 ≤
      (10 + 10 * k + (8 * l + 7)) * (n + 1) ^ 2 := by
  have hs : n + 1 ≤ (n + 1) ^ 2 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ 2 by decide)
  have hlin : 2 * n + 8 ≤ 10 * (n + 1) ^ 2 := by omega
  have hfields := Nat.mul_le_mul_left k (show 3 * n + 7 ≤ 10 * (n + 1) ^ 2 by omega)
  have hrec := Nat.mul_le_mul_left (8 * l + 7)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hT 1) 2)
  ring_nf at hlin hfields hrec ⊢
  omega

/-- The same argument envelope pays for one final count instead of the
full trajectory, including its physical output and final halt. -/
private lemma clCount_size_budget (n k l T R a : ℕ) (hT : T ≤ n) (hr : R ≤ T)
    (ha : a ≤ 2 * n + 4 + k * (3 * n + 7) + (4 * l + 7) * (T + 1) ^ 2) :
    a + 0 + R + 4 ≤ (10 + 10 * k + (8 * l + 7)) * (n + 1) ^ 2 := by
  have hs : n + 1 ≤ (n + 1) ^ 2 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ 2 by decide)
  have hlin : 2 * n + 8 + R ≤ 10 * (n + 1) ^ 2 := by omega
  have hfields := Nat.mul_le_mul_left k (show 3 * n + 7 ≤ 10 * (n + 1) ^ 2 by omega)
  have hrec := Nat.mul_le_mul_left (4 * l + 7)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hT 1) 2)
  ring_nf at hlin hfields hrec ha ⊢
  omega

/-- Native recording plus physical output, with every preparation,
recording, rewind, replay and terminal transition charged.
**Proof sketch.** Use the completed native retained recorder, cut its first
absorbing return, and replay its actual record tape. The inherited record
length bound pays for both traversals of that stored inclusive trajectory. -/
private lemma clRecordOutput_compute (M : FinTM Bool) (y : List Bool) (T : ℕ)
    (keep : Fin 4 → List Bool) (W : ℕ)
    (hW : ∀ i : Fin ((clRecTM M).k + 4),
      ((Fin.addCases (clRecWords M y T) keep : Fin ((clRecTM M).k + 4) → List Bool) i).length ≤ W) :
    let x := clFields (List.ofFn (Fin.addCases (clRecWords M y T) keep)) ++ []
    (clRecordOutputTM M).ComputesInTime x (clRecords M y (T + 1))
      (2 * x.length + 8 + ((clRecTM M).k + 4) * (3 * W + 7) +
        (8 * clRecFields M + 7) * (T + 1) ^ 2) := by
  dsimp only
  let x := clFields (List.ofFn (Fin.addCases (clRecWords M y T) keep)) ++ []
  obtain ⟨a, ha, hr⟩ := clRecord_complete M y T keep W hW
  have hc := clOutput_compute (clRecordTM M) (.inr (.inr (.inr (.inr (.inr ())))))
    ((clRecordSelect M).index (Fin.natAdd (clRecFields M) (Fin.castAdd (1 + (1 + M.k)) (0 : Fin 1))))
    x (clRecords M y (T + 1)) a _ hr rfl (by simp [clRecordTM])
    (fun c hc => clRecord_idle M c hc) rfl
    (by
      dsimp only [clRecordCfg, clPlacedCfg, Cfg.mapState]
      refine (embedEmitCfg_selected_tape (clRecordSelect M).index _ _ [] _ _).trans ?_
      simp [clRecCfg, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat])
    (by
      dsimp only [clRecordCfg, clPlacedCfg, Cfg.mapState]
      refine (embedEmitCfg_selected_pos (clRecordSelect M).index _ _ [] _ _).trans ?_
      simp [clRecCfg, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat])
  apply hc.mono
  have hlen := clRecords_length M y T (T + 1) le_rfl
  have hlen' : (clRecords M y (T + 1)).length ≤ 2 * clRecFields M * (T + 1) ^ 2 := by
    calc
      _ ≤ (T + 1) * (clRecFields M * (2 * T + 2)) := hlen
      _ = _ := by ring
  exact clRecord_replay_budget x.length ((clRecTM M).k + 4) (clRecFields M) W T
    (clRecords M y (T + 1)).length a ha hlen'

/-- On its canonical argument the trajectory producer has a quadratic
bound in the actual encoded argument length, including a zero horizon.
**Proof sketch.** Each initial word and the unary horizon occur in the real encoded argument. Substitute those size bounds into the complete recording/replay ledger. -/
private lemma clRecordOutput_quadratic (M : FinTM Bool) (y : List Bool) (T : ℕ)
    (keep : Fin 4 → List Bool) :
    let x := clFields (List.ofFn (Fin.addCases (clRecWords M y T) keep)) ++ []
    (clRecordOutputTM M).ComputesInTime x (clRecords M y (T + 1))
      ((10 + 10 * ((clRecTM M).k + 4) + (8 * clRecFields M + 7)) * (x.length + 1) ^ 2) := by
  dsimp only
  let ws : Fin ((clRecTM M).k + 4) → List Bool := Fin.addCases (clRecWords M y T) keep
  let x := clFields (List.ofFn ws) ++ []
  have hW : ∀ i, (ws i).length ≤ x.length := by
    intro i
    simpa [x] using clFields_width (List.ofFn ws) (ws i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hT : T ≤ x.length := by
    have hh := hW (Fin.castAdd 4 (clRecClockIndex M))
    simpa [ws, clRecWords, clRecClockIndex, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat] using hh
  have hc := clRecordOutput_compute M y T keep x.length hW
  apply hc.mono
  change 2 * x.length + 8 + ((clRecTM M).k + 4) * (3 * x.length + 7) +
    (8 * clRecFields M + 7) * (T + 1) ^ 2 ≤ _
  exact clRecord_size_budget x.length ((clRecTM M).k + 4) (clRecFields M) T hT

/-- Polynomial composition needs correctness of the second machine only
on the actual image of the first. Its native startup still uses the public
buffered composition, and the complete intermediate word is charged.
**Proof sketch.** Bound the produced word by the first runtime. Substitute
that size into the second monomial, increase both exponents to their common
product bound, and apply the per-input buffered-composition ledger. -/
private lemma clNative_image {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (B : FinTM Bool) (b r : ℕ)
    (hB : ∀ x, B.ComputesInTime (f x) (g x) (b * ((f x).length + 1) ^ r)) :
    PolyTimeComputable g := by
  obtain ⟨A, a, d, hA⟩ := hf
  refine ⟨FinTM.bufferedCompTM A B, 2 * a + b * (a + 1) ^ r + 2, d * (r + 1), ?_⟩
  intro x
  have hc := FinTM.bufferedCompTM_computesInTime A B (hA x) (hB x)
  apply hc.mono
  have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hA x)).2
  have hlen : (f x).length ≤ a * (x.length + 1) ^ d := by
    simpa only [ho] using A.tm.output_length_le x (a * (x.length + 1) ^ d)
  have hpos : 1 ≤ (x.length + 1) ^ d := Nat.one_le_pow d _ (by omega)
  have hword : (f x).length + 1 ≤ (a + 1) * (x.length + 1) ^ d := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hpow := Nat.pow_le_pow_left hword r
  rw [Nat.mul_pow, ← Nat.pow_mul] at hpow
  have hd := Nat.pow_le_pow_right (Nat.succ_pos x.length)
    (show d ≤ d * (r + 1) by rw [Nat.mul_add, Nat.mul_one]; omega)
  have hdr := Nat.pow_le_pow_right (Nat.succ_pos x.length)
    (show d * r ≤ d * (r + 1) by rw [Nat.mul_add, Nat.mul_one]; omega)
  have hm := Nat.mul_le_mul_left ((a + 1) ^ r) hdr
  have hcost := Nat.mul_le_mul_left b (hpow.trans hm)
  have hfirst := Nat.mul_le_mul_left (2 * a) hd
  have hlast : 1 ≤ (x.length + 1) ^ (d * (r + 1)) := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 2 * (a * (x.length + 1) ^ d) + b * ((f x).length + 1) ^ r + 2 := by
      dsimp only
      omega
    _ ≤ (2 * a) * (x.length + 1) ^ (d * (r + 1)) +
        (b * (a + 1) ^ r) * (x.length + 1) ^ (d * (r + 1)) +
        2 * (x.length + 1) ^ (d * (r + 1)) := by
      exact Nat.add_le_add (Nat.add_le_add
        (by simpa only [Nat.mul_assoc] using hfirst)
        (by simpa only [Nat.mul_assoc] using hcost)) (Nat.mul_le_mul_left 2 hlast)
    _ = _ := by ring

/-- The inclusive trajectory is a native polynomial-time output of the
original instance, not merely a prepared recorder configuration.
**Proof sketch.** Consume the sealed arithmetic header and its native
layout producer, then run the bounded actual recorder/replay on that exact
image. The per-image composition theorem pays for the full header, every
load/reset, recording, capture and output replay. -/
private lemma clRecords_native (M : FinTM Bool) (C e c A d : ℕ) :
    PolyTimeComputable (fun x =>
      let m := x.length + C * (x.length + 1) ^ e
      let T := c * (A * (m + 1) ^ d + 1) ^ 2
      clRecords M (List.replicate m false) (T + 1)) := by
  apply clNative_image (clRecordArgument_native M C e c A d) (clRecordOutputTM M)
    (10 + 10 * ((clRecTM M).k + 4) + (8 * clRecFields M + 7)) 2
  intro x
  rw [clHeaderLayout_exact]
  simpa only [List.append_nil] using clRecordOutput_quadratic M
    (List.replicate (x.length + C * (x.length + 1) ^ e) false)
    (c * (A * (x.length + C * (x.length + 1) ^ e + 1) ^ d + 1) ^ 2)
    (fun i : Fin 4 => if i = 0 then x else if i = 1 then (C * (x.length + 1) ^ e).bits
      else if i = 2 then (x.length + C * (x.length + 1) ^ e).bits
      else (c * (A * (x.length + C * (x.length + 1) ^ e + 1) ^ d + 1) ^ 2).bits)

/-- Replaying from any proved prefix boundary charges just that prefix's
rewind, followed by the complete word and the physical halt. -/
private lemma clReplay_from (x : List Bool) (p : Fin (x.length + 2))
    (w out : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    clReplayTM.tm.runFrom (clReplayCfg x p (some 0) w j out) (j + w.length + 3) =
      clReplayCfg x p none w w.length (out ++ w) := by
  have release : clReplayTM.tm.step (clReplayCfg x p (some 0) w j out) =
      clReplayCfg x p (some 1) w (j - 1) out := by
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Action.apply, funext_iff, sub_eq_add_neg]
  rw [show j + w.length + 3 = ((j + 1) + (w.length + 1)) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, release, MultiTapeTM.runFrom_add,
    clReplay_back x p w out j hj]
  simpa only [Nat.sub_zero, Nat.cast_zero, List.drop_zero] using
    clReplay_forward x p w 0 (by omega) out

/-- The output wrapper also accepts a buffer already at its left edge.
**Proof sketch.** Cut the absorbing source return and relocate the replay
from the explicitly supplied prefix boundary. The whole source frame is
preserved and every rewind/output transition appears in the ledger. -/
private lemma clOutputAt_compute (A : FinTM Bool) (ret : A.State) (i : Fin A.k)
    (x w : List Bool) (a j : ℕ) (d : Cfg A.k Bool A.State x)
    (hrun : A.tm.runFrom (A.tm.initCfg x) a = d) (hret : d.state = some ret)
    (hstart : A.tm.q₀ ≠ ret)
    (hidle : ∀ c : Cfg A.k Bool A.State x, c.state = some ret → A.tm.step c = c)
    (hout : d.output = []) (hword : d.workTapes i = FinTM.bufferTape w)
    (hhead : d.workTapePos i = j) (hj : j ≤ w.length) :
    (clOutputTM A ret i).ComputesInTime x w (a + j + w.length + 4) := by
  obtain ⟨t, ht, _, hf, he⟩ := clFirst A.tm (A.tm.initCfg x) d ret a hrun hret
    (by intro h; apply hstart; exact Option.some.inj h) hidle
  have lift := MultiTapeTM.runFrom_mapState_of_agreeOn A.tm (clOutputTM A ret i).tm ⟨Sum.inl, Sum.inl_injective⟩ (fun q => q ≠ ret)
    (fun _ hq _ _ => if_neg hq) (A.tm.initCfg x) t
    (by intro j hj q hq heq; subst q; exact hf j hj hq)
  dsimp only [Function.Embedding.coeFn_mk] at lift
  rw [he] at lift
  have init : ((A.tm.initCfg x).mapState Sum.inl :
      Cfg A.k Bool (clOutputTM A ret i).State x) = (clOutputTM A ret i).tm.initCfg x := rfl
  rw [init] at lift
  let framed := clPlacedCfg (clOneSelect i) (Sum.inr : Fin 3 → (clOutputTM A ret i).State)
    d.workTapes d.workTapePos (clReplayCfg x d.inputPos (some 0) w j [])
  have dispatch : (clOutputTM A ret i).tm.step (d.mapState Sum.inl) = framed := by
    have hs : (d.mapState (Sum.inl : A.State → (clOutputTM A ret i).State)).state =
        some (.inl ret) := by simp [Cfg.mapState, hret]
    unfold MultiTapeTM.step
    rw [hs]
    simp only [clOutputTM, if_true]
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext j
      by_cases hj : j = i
      · subst j; simpa [framed, clOneSelect, clReplayCfg] using hword
      · simp [framed, clOneSelect, clReplayCfg, Cfg.mapState, hj]
    · funext j
      by_cases hj : j = i
      · subst j; simpa [framed, clOneSelect, clReplayCfg] using hhead
      · simp [framed, clOneSelect, clReplayCfg, Cfg.mapState, hj]
    · exact hout
  have replay := clPlaced_run clReplayTM.tm (clOutputTM A ret i).tm (clOneSelect i) Sum.inr (by intro a b h; cases h; rfl) (fun _ => True) (by intros; rfl) d.workTapes d.workTapePos
    (clReplayCfg x d.inputPos (some 0) w j []) (j + w.length + 3) (by intros; trivial)
  rw [clReplay_from x d.inputPos w [] j hj] at replay
  have hc : (clOutputTM A ret i).ComputesInTime x w (t + 1 + (j + w.length + 3)) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    have arrived : (clOutputTM A ret i).tm.runFrom ((clOutputTM A ret i).tm.initCfg x) (t + 1) =
        framed := by rw [MultiTapeTM.runFrom_succ_eq_step', lift, dispatch]
    rw [MultiTapeTM.runFrom_add, arrived, replay]
    exact ⟨rfl, by simp [clReplayCfg]⟩
  exact hc.mono (by omega)

/-- A selected canonical final movement count, physically returned by the
actual recorder; its restored head starts at zero. -/
private def clCountOutputTM (M : FinTM Bool) (i : Fin (clRecFields M)) : FinTM Bool :=
  clOutputTM (clRecordTM M) (.inr (.inr (.inr (.inr (.inr ())))))
    ((clRecordSelect M).index (Fin.castAdd (1 + (1 + (1 + M.k))) i))

/-- The native recorder can expose any one final binary count, with the
same quadratic argument-size bound used by the complete trajectory.
**Proof sketch.** Invoke the actual retained recorder, then replay its
selected counter from its restored left edge. The elapsed-width bound
charges the output. The encoded clock bounds the source horizon. -/
private lemma clCountOutput_quadratic (M : FinTM Bool) (i : Fin (clRecFields M))
    (y : List Bool) (T : ℕ) (keep : Fin 4 → List Bool) :
    let x := clFields (List.ofFn (Fin.addCases (clRecWords M y T) keep)) ++ []
    (clCountOutputTM M i).ComputesInTime x (clCounts M y T i).bits
      ((10 + 10 * ((clRecTM M).k + 4) + (8 * clRecFields M + 7)) * (x.length + 1) ^ 2) := by
  dsimp only
  let ws : Fin ((clRecTM M).k + 4) → List Bool := Fin.addCases (clRecWords M y T) keep
  let x := clFields (List.ofFn ws) ++ []
  have hW : ∀ j, (ws j).length ≤ x.length := by
    intro j
    simpa [x] using clFields_width (List.ofFn ws) (ws j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hT : T ≤ x.length := by
    have hh := hW (Fin.castAdd 4 (clRecClockIndex M))
    simpa [ws, clRecWords, clRecClockIndex, FinTM.tapeBlocks, -Fin.natAdd_eq_addNat] using hh
  obtain ⟨a, ha, hr⟩ := clRecord_complete M y T keep x.length hW
  have selected := ((clRecordSelect M).exact (Fin.castAdd (1 + (1 + (1 + M.k))) i) _).mpr rfl
  have hc := clOutputAt_compute (clRecordTM M) (.inr (.inr (.inr (.inr (.inr ())))))
    ((clRecordSelect M).index (Fin.castAdd (1 + (1 + (1 + M.k))) i))
    x (clCounts M y T i).bits a 0 _ hr rfl (by simp [clRecordTM])
    (fun c hc => clRecord_idle M c hc) rfl
    (by simp [clRecordCfg, selected, clRecCfg, FinTM.tapeBlocks])
    (by simp [clRecordCfg, selected, clRecCfg, FinTM.tapeBlocks]) (by omega)
  have hw := clElapsed_width _ T (clCounts_bound M y T i)
  apply hc.mono
  exact clCount_size_budget x.length ((clRecTM M).k + 4) (clRecFields M) T
    (clCounts M y T i).bits.length a hT hw ha

/-- A general native recorder argument assembled from an actual input-word
producer and an actual unary-horizon producer, with four empty retained fields.
**Proof sketch.** Split the finite tape layout into counter, record, unary clock, virtual input and source slots. Native constants or the supplied native producers compute every field, then native pairing packs them. -/
private lemma clRecordWords_native (M : FinTM Bool) (y : List Bool → List Bool)
    (T : List Bool → ℕ) (hy : PolyTimeComputable y)
    (hT : PolyTimeComputable (fun x => List.replicate (T x) true)) :
    PolyTimeComputable (fun x =>
      clFields (List.ofFn (Fin.addCases (clRecWords M (y x) (T x)) (fun _ : Fin 4 => [])))) := by
  let fs : List (List Bool → List Bool) := List.ofFn (fun i : Fin ((clRecTM M).k + 4) =>
    fun x => (Fin.addCases (clRecWords M (y x) (T x)) (fun _ : Fin 4 => []) i))
  have h : ∀ f ∈ fs, PolyTimeComputable f := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i; simpa [clRecWords, FinTM.tapeBlocks] using
          clNative_linear _ (FinTM.computesFunInTime_const [])
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro i; simpa [clRecWords, FinTM.tapeBlocks] using
            clNative_linear _ (FinTM.computesFunInTime_const [])
        · intro i
          refine Fin.addCases ?_ ?_ i
          · intro i; simpa [clRecWords, FinTM.tapeBlocks] using hT
          · intro i
            refine Fin.addCases ?_ ?_ i
            · intro i; simpa [clRecWords, FinTM.tapeBlocks] using hy
            · intro i; simpa [clRecWords, FinTM.tapeBlocks] using
                clNative_linear _ (FinTM.computesFunInTime_const [])
    · intro i; simpa using clNative_linear _ (FinTM.computesFunInTime_const [])
  simpa only [fs, List.map_ofFn] using clNative_fields fs h

/-- General trajectory production consumes the same banked recorder for
every native reference input and unary horizon; no recomputed semantics
or unbounded numeric conversion is used. -/
private lemma clTrajectory_native (M : FinTM Bool) (y : List Bool → List Bool)
    (T : List Bool → ℕ) (hy : PolyTimeComputable y)
    (hT : PolyTimeComputable (fun x => List.replicate (T x) true)) :
    PolyTimeComputable (fun x => clRecords M (y x) (T x + 1)) := by
  apply clNative_image (clRecordWords_native M y T hy hT) (clRecordOutputTM M)
    (10 + 10 * ((clRecTM M).k + 4) + (8 * clRecFields M + 7)) 2
  intro x
  simpa only [List.append_nil] using clRecordOutput_quadratic M (y x) (T x) (fun _ => [])

/-- Each final counter field is a native function of the original query
input. Keeping the time unary avoids any unsupported exponential clock. -/
private lemma clFinalCount_native (M : FinTM Bool) (i : Fin (clRecFields M))
    (y : List Bool → List Bool) (T : List Bool → ℕ) (hy : PolyTimeComputable y)
    (hT : PolyTimeComputable (fun x => List.replicate (T x) true)) :
    PolyTimeComputable (fun x => (clCounts M (y x) (T x) i).bits) := by
  apply clNative_image (clRecordWords_native M y T hy hT) (clCountOutputTM M i)
    (10 + 10 * ((clRecTM M).k + 4) + (8 * clRecFields M + 7)) 2
  intro x
  simpa only [List.append_nil] using clCountOutput_quadratic M i (y x) (T x) (fun _ => [])
/-- A uniform polynomial envelope for a complete native query. The stream,
clock and every field are bounded by the actual encoded argument length.
**Proof sketch.** Bound the strict-prefix clock by the argument length, dominate the quadratic scan term, and raise the scan and conversion exponents to one common monomial. -/
private lemma clQuery_budget (l L N c e : ℕ) (hN : N ≤ L) :
    2 * (2 * L + 9 + (l + 5) * (3 * L + 7) +
      N * (l * (5 * L + 7) + 2 * L + 7)) + c * (N + 1) ^ e + 2 ≤
      (100 * (l + 10) + c) * (L + 1) ^ (e + 2) := by
  have hm := Nat.mul_le_mul_right (l * (5 * L + 7) + 2 * L + 7) hN
  have hb : 2 * (2 * L + 9 + (l + 5) * (3 * L + 7) +
      N * (l * (5 * L + 7) + 2 * L + 7)) + 2 ≤
      (100 * (l + 10)) * (L + 1) ^ 2 := by
    ring_nf at hm ⊢
    omega
  have hs := Nat.mul_le_mul_left (100 * (l + 10))
    (Nat.pow_le_pow_right (Nat.succ_pos L) (show 2 ≤ e + 2 by omega))
  have he := Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) e
  have hp := Nat.pow_le_pow_right (Nat.succ_pos L) (show e ≤ e + 2 by omega)
  have hc := Nat.mul_le_mul_left c (he.trans hp)
  calc
    _ ≤ (100 * (l + 10)) * (L + 1) ^ 2 + c * (N + 1) ^ e := by omega
    _ ≤ (100 * (l + 10)) * (L + 1) ^ (e + 2) + c * (L + 1) ^ (e + 2) :=
      Nat.add_le_add hs hc
    _ = _ := by ring

/-- The two canonical signed target fields obtained from the final row of
an actual source run. They are never compared by raw word equality. -/
private def clSearchTarget (M : FinTM Bool) (y : List Bool) (t : ℕ)
    (pos neg : Fin (clRecFields M)) : Fin 2 → List Bool :=
  clTwo (clCounts M y t pos).bits (clCounts M y t neg).bits

/-- Complete native query argument, with the inclusive final row retained
as an unconsumed suffix beyond the strict candidate clock. -/
private def clSearchArg (M : FinTM Bool) (y : List Bool) (t : ℕ)
    (pos neg : Fin (clRecFields M)) : List Bool :=
  clFields (List.ofFn (clQueryWords (clRecFields M) (clSearchTarget M y t pos neg)
    (clRecords M y (t + 1)) t))

/-- Native query arguments are built from actual recorder outputs and
native final count outputs, plus the independently computed unary clock.
**Proof sketch.** Compute each of the finitely many exact fields with the
banked recorder or a native constant/unary producer, then pair them using
the native field packer. Its composition bounds charge every retained copy. -/
private lemma clSearchArg_native (M : FinTM Bool) (pos neg : Fin (clRecFields M))
    (y : List Bool → List Bool) (T : List Bool → ℕ) (hy : PolyTimeComputable y)
    (hT : PolyTimeComputable (fun x => List.replicate (T x) true)) :
    PolyTimeComputable (fun x => clSearchArg M (y x) (T x) pos neg) := by
  let fs : List (List Bool → List Bool) := List.ofFn (fun i : Fin (clRecFields M + 5) =>
    fun x => clQueryWords (clRecFields M) (clSearchTarget M (y x) (T x) pos neg)
      (clRecords M (y x) (T x + 1)) (T x) i)
  have h : ∀ f ∈ fs, PolyTimeComputable f := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    refine Fin.addCases ?_ ?_ i
    · intro i; simpa [clQueryWords] using clNative_linear _ (FinTM.computesFunInTime_const [])
    · intro i
      fin_cases i
      · simpa [clQueryWords] using clTrajectory_native M y T hy hT
      · simpa [clQueryWords, clSearchTarget, clTwo] using clFinalCount_native M pos y T hy hT
      · simpa [clQueryWords, clSearchTarget, clTwo] using clFinalCount_native M neg y T hy hT
      · simpa [clQueryWords] using hT
      · simpa [clQueryWords] using clNative_linear _ (FinTM.computesFunInTime_const [])
  simpa only [fs, List.map_ofFn, clSearchArg] using clNative_fields fs h

/-- The native last-visit query closes on every supplied native source and
unary time producer, with a total polynomial ledger on its original input.
**Proof sketch.** Build a canonical query by native recording and field
packing. The prefix scanner consumes exactly the first `T` rows of the
inclusive `T+1` trajectory. Counts have elapsed width at most `T`; the
argument contains its unary clock and every query word. The uniform query
bound therefore applies, and native per-image composition charges all
argument construction, comparisons, reverse search and output. -/
private lemma clSearch_native (M : FinTM Bool) (pos neg : Fin (clRecFields M))
    (hne : pos ≠ neg) (y : List Bool → List Bool) (T : List Bool → ℕ)
    (hy : PolyTimeComputable y)
    (hT : PolyTimeComputable (fun x => List.replicate (T x) true)) :
    PolyTimeComputable (fun x => clLastCode ((List.range (T x)).map (fun s =>
      clMatchFlag pos neg (fun i => (clCounts M (y x) s i).bits)
        (clSearchTarget M (y x) (T x) pos neg)))) := by
  obtain ⟨Q, c, e, hQ⟩ := clQueryCode_machine pos neg hne
  apply clNative_image (clSearchArg_native M pos neg y T hy hT) Q
    (100 * (clRecFields M + 10) + c) (e + 2)
  intro x
  let row := fun s i => (clCounts M (y x) s i).bits
  let target := clSearchTarget M (y x) (T x) pos neg
  let words := clQueryWords (clRecFields M) target (clRecords M (y x) (T x + 1)) (T x)
  let arg := clSearchArg M (y x) (T x) pos neg
  have hW : ∀ i, (words i).length ≤ arg.length := by
    intro i
    exact clFields_width (List.ofFn words) (words i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hN : T x ≤ arg.length := by
    have hh := hW (Fin.natAdd (clRecFields M) (3 : Fin 5))
    simpa [words, clQueryWords, -Fin.natAdd_eq_addNat] using hh
  have hRow : ∀ s < T x, ∀ i, (row s i).length ≤ arg.length := by
    intro s hs i
    exact (clElapsed_width _ s (clCounts_bound M (y x) s i)).trans (by omega)
  have hTarget : ∀ i, (target i).length ≤ arg.length := by
    intro i
    fin_cases i <;> simp only [target, clSearchTarget, clTwo, ↓reduceIte]
    · exact (clElapsed_width _ (T x) (clCounts_bound M (y x) (T x) pos)).trans hN
    · exact (clElapsed_width _ (T x) (clCounts_bound M (y x) (T x) neg)).trans hN
  have hstream : clRows row (T x) ++ clFields (List.ofFn (row (T x))) =
      clRecords M (y x) (T x + 1) := by
    rw [← clRows, clRows_records]
  have hw : ∀ i, (clQueryWords (clRecFields M) target
      (clRows row (T x) ++ clFields (List.ofFn (row (T x)))) (T x) i).length ≤ arg.length := by
    rw [hstream]
    exact hW
  have hc := hQ row target (T x) arg.length arg.length
    (clFields (List.ofFn (row (T x)))) hRow hTarget hw
  dsimp only at hc
  rw [hstream, List.append_nil] at hc
  exact hc.mono (clQuery_budget (clRecFields M) arg.length (T x) c e hN)

/-- A native query gives exactly the frozen public greatest-strictly-earlier
work visit, with its canonical binary time code.
**Proof sketch.** Apply the native cross-sum search to the two disjoint work-coordinate count fields. The stored schedule identity identifies every comparison, and the greatest-flag theorem identifies the result. -/
private lemma clPrev_native (M : FinTM Bool) (τ : Fin M.k)
    (m T : List Bool → ℕ)
    (hm : PolyTimeComputable (fun x => List.replicate (m x) false))
    (hT : PolyTimeComputable (fun x => List.replicate (T x) true)) :
    PolyTimeComputable (fun x => clVisitCode (prevVisit M (m x) (T x) τ)) := by
  have hne : (Fin.castAdd (1 + M.k) (Fin.natAdd 1 τ) : Fin (clRecFields M)) ≠
      Fin.natAdd (1 + M.k) (Fin.natAdd 1 τ) := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + τ.val = (1 + M.k) + (1 + τ.val) at hv
    omega
  have h := clSearch_native M (Fin.castAdd (1 + M.k) (Fin.natAdd 1 τ))
    (Fin.natAdd (1 + M.k) (Fin.natAdd 1 τ)) hne (fun x => List.replicate (m x) false) T hm hT
  convert h using 1
  funext x
  rw [← clLastCode_prev]
  congr 1
  apply List.map_congr_left
  intro s hs
  exact (clMatchFlag_schedule M (m x) s (T x) τ).symm
/-- Self-delimiting last-visit codes for every work tape in finite tape order.
The request pairs the original instance with a unary query-time word. -/
private def clVisitRow (M : FinTM Bool) (C e : ℕ) (z : List Bool) : List Bool :=
  let x := clHeaderField 0 z
  let t := (clHeaderTail 1 z).length
  let m := x.length + C * (x.length + 1) ^ e
  clFields (List.ofFn (fun τ : Fin M.k => clVisitCode (prevVisit M m t τ)))

/-- One entire time-row of last-visit codes is a total native polynomial
function of the retained-instance/unary-time request.
**Proof sketch.** Native projections retain the original instance and unary
time. Exact certificate-length preparation constructs the all-false reference
input. Each fixed tape's actual recorded search is a native computation;
finite field pairing charges the whole ordered row. -/
private lemma clVisitRow_native (M : FinTM Bool) (C e : ℕ) :
    PolyTimeComputable (clVisitRow M C e) := by
  let m := fun z => (clHeaderField 0 z).length + C * ((clHeaderField 0 z).length + 1) ^ e
  let t := fun z => (clHeaderTail 1 z).length
  have hm : PolyTimeComputable (fun z => List.replicate (m z) false) := by
    have h := (clNative_fill false).comp
      (clNative_append (clHeaderField_native 0) ((clNative_unary C e).comp (clHeaderField_native 0)))
    simpa only [Function.comp_def, List.length_append, List.length_replicate, m] using h
  have ht : PolyTimeComputable (fun z => List.replicate (t z) true) :=
    (clNative_fill true).comp (clHeaderTail_native 1)
  let fs : List (List Bool → List Bool) := List.ofFn
    (fun τ : Fin M.k => fun z => clVisitCode (prevVisit M (m z) (t z) τ))
  have hf : ∀ f ∈ fs, PolyTimeComputable f := by
    intro f hf
    obtain ⟨τ, rfl⟩ := List.mem_ofFn.mp hf
    exact clPrev_native M τ m t hm ht
  simpa only [fs, List.map_ofFn, clVisitRow, m, t] using clNative_fields fs hf

/-- On a canonical request, row order is precisely the source tape order
and each payload is the canonical greatest-strictly-earlier visit code. -/
private lemma clVisitRow_exact (M : FinTM Bool) (C e : ℕ) (x : List Bool) (t : ℕ) :
    clVisitRow M C e (pairEncode x (List.replicate t true)) =
      clFields (List.ofFn (fun τ : Fin M.k =>
        clVisitCode (prevVisit M (x.length + C * (x.length + 1) ^ e) t τ))) := by
  simp [clVisitRow, clHeaderField, clHeaderTail, pairDecode_pairEncode]

/-- A native polynomial computation has a reusable clean install call,
with all scratch cells and all heads restored after each actual request.
This is a component bridge, not the final packed-producer installation.
**Proof sketch.** Instantiate the audited clean-call bridge with the actual native polynomial transducer. Bound its complete output by its runtime and absorb argument length into a positive-degree monomial. -/
private lemma clNative_cleanCall {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ (W : FinTM Bool) (entry exit : W.State) (a d : ℕ), 0 < W.k ∧
      ∀ x arg, ∃ t ≤ a * (arg.length + 1) ^ d,
        0 < t ∧
        (∀ j, 0 < j → j < t →
          (W.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord W.k arg)) j).state ≠ some exit) ∧
        W.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord W.k arg)) t =
          Cfg.ofWords exit (stateWord W.k (f arg)) := by
  obtain ⟨E, b, e, hE⟩ := hf
  obtain ⟨W, entry, exit, c, hk, hcall⟩ := FinTM.exists_installCallTM E f _ hE
  refine ⟨W, entry, exit, c * (2 * b + 1), e + 1, hk, ?_⟩
  intro x arg
  obtain ⟨t, ht, hp, hfirst, hr⟩ := hcall x arg
  refine ⟨t, ht.trans ?_, hp, hfirst, hr⟩
  have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hE arg)).2
  have hlen : (f arg).length ≤ b * (arg.length + 1) ^ e := by
    simpa only [ho] using E.tm.output_length_le arg (b * (arg.length + 1) ^ e)
  have hpow := Nat.pow_le_pow_right (Nat.succ_pos arg.length) (Nat.le_succ e)
  have htime := Nat.mul_le_mul_left b hpow
  change b * (arg.length + 1) ^ e ≤ b * (arg.length + 1) ^ (e + 1) at htime
  have harg : arg.length + 1 ≤ (arg.length + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos arg.length)
      (show 1 ≤ e + 1 by omega)
  calc
    _ ≤ c * ((2 * b + 1) * (arg.length + 1) ^ (e + 1)) := by
      apply Nat.mul_le_mul_left
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega
    _ = _ := (Nat.mul_assoc _ _ _).symm

/-- Producer-internal state retains the instance, unary query time and
all already-completed last-visit rows. This is not the final emitter state. -/
private def clVisitState (x : List Bool) (t : ℕ) (rows : List Bool) : List Bool :=
  pairEncode x (pairEncode (List.replicate t true) rows)

/-- One producer-internal time step appends the complete current visit row
and advances its unary clock; every operation is a native word computation. -/
private def clVisitStep (M : FinTM Bool) (C e : ℕ) (z : List Bool) : List Bool :=
  pairEncode (clHeaderField 0 z)
    (pairEncode (clHeaderField 1 z ++ [true])
      (clHeaderTail 2 z ++ clVisitRow M C e
        (pairEncode (clHeaderField 0 z) (clHeaderField 1 z))))

/-- A complete last-visit-row production and append is native and polynomial,
including retained copies, every search, and the actual clock increment. -/
private lemma clVisitStep_native (M : FinTM Bool) (C e : ℕ) :
    PolyTimeComputable (clVisitStep M C e) := by
  have htime := clNative_append (clHeaderField_native 1)
    (clNative_linear _ (FinTM.computesFunInTime_const [true]))
  have hrequest := clNative_pair (clHeaderField_native 0) (clHeaderField_native 1)
  have hrow := (clVisitRow_native M C e).comp hrequest
  exact clNative_pair (clHeaderField_native 0)
    (clNative_pair htime (clNative_append (clHeaderTail_native 2) hrow))

/-- Ordered pure last-visit rows; time zero is present, and the completed
horizon table has `T+1` rows. The native whole-table loop below realizes this ordered word. -/
private def clVisitRows (M : FinTM Bool) (C e : ℕ) (x : List Bool) : ℕ → List Bool
  | 0 => []
  | t + 1 => clVisitRows M C e x t ++ clVisitRow M C e (pairEncode x (List.replicate t true))

/-- The completed native step has precisely the next retained-state word,
including an append of this time's codes in fixed work-tape order. -/
private lemma clVisitStep_state (M : FinTM Bool) (C e : ℕ) (x rows : List Bool) (t : ℕ) :
    clVisitStep M C e (clVisitState x t rows) =
      clVisitState x (t + 1) (rows ++ clVisitRow M C e (pairEncode x (List.replicate t true))) := by
  simp [clVisitStep, clVisitState, clHeaderField, clHeaderTail, pairDecode_pairEncode,
    List.replicate_add, List.replicate_one]

/-- The pure orbit agrees with the intended inclusive ordered table.
This identifies the exact word the native outer loop below iterates. -/
private lemma clVisitStep_orbit (M : FinTM Bool) (C e : ℕ) (x : List Bool) (t : ℕ) :
    (clVisitStep M C e)^[t] (clVisitState x 0 []) =
      clVisitState x t (clVisitRows M C e x t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, clVisitStep_state]
    rfl

/-- The complete producer-internal row step has a clean reusable native
call, with a positive first return and all scratch restored. It does not
assert that the variable number of such calls has already been assembled. -/
private lemma clVisitStep_cleanCall (M : FinTM Bool) (C e : ℕ) :
    ∃ (W : FinTM Bool) (entry exit : W.State) (a d : ℕ), 0 < W.k ∧
      ∀ x arg, ∃ t ≤ a * (arg.length + 1) ^ d,
        0 < t ∧
        (∀ j, 0 < j → j < t →
          (W.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord W.k arg)) j).state ≠ some exit) ∧
        W.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord W.k arg)) t =
          Cfg.ofWords exit (stateWord W.k (clVisitStep M C e arg)) :=
  clNative_cleanCall (clVisitStep_native M C e)
/-- Unary-bounded repetition of one clean native call. The fresh begin
phase executes its first transition before testing the positive return. -/
private def clRepeatTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k + 1
  State := Fin 3 ⊕ C.State
  tm := {
    q₀ := .inl 0
    tr := fun q inp work => match q with
      | .inl q =>
        if q = 0 then
          if work (Fin.natAdd C.k (0 : Fin 1)) = none then FinTM.controlAction 0 (some (.inl 2))
          else ⟨0, Fin.addCases (fun _ => (none, 0)) (fun _ : Fin 1 => (none, .pos)),
            none, some (.inl 1)⟩
        else if q = 1 then
          clPlacedAction (clKeepLastPlacement _) Sum.inr entry (C.tm.tr entry inp (fun i => work ((clKeepLastPlacement _).index i)))
        else FinTM.controlAction 0 (some (.inl 2))
      | .inr q => if q = exit then FinTM.controlAction 0 (some (.inl 0))
          else clPlacedAction (clKeepLastPlacement _) Sum.inr q (C.tm.tr q inp (fun i => work ((clKeepLastPlacement _).index i))) }

/-- Whole repetition seam: the clean argument bank and one protected unary
clock, with its actual logical cursor. Every call starts with blank scratch. -/
private def clRepeatCfg (C : FinTM Bool) (entry exit : C.State) (x : List Bool)
    (q : (clRepeatTM C entry exit).State) (s : List Bool) (N j : ℕ) :
    Cfg (clRepeatTM C entry exit).k Bool (clRepeatTM C entry exit).State x :=
  ⟨some q, 1,
    Fin.addCases (fun i => FinTM.bufferTape (stateWord C.k s i))
      (fun _ : Fin 1 => FinTM.bufferTape (List.replicate N true)),
    Fin.addCases (fun _ => 0) (fun _ : Fin 1 => (j : ℤ)), []⟩

/-- Relocation of a clean call agrees with the protected-clock seam. -/
private lemma clRepeat_frame (C : FinTM Bool) (entry exit : C.State)
    (x s : List Bool) (N j : ℕ) (q : C.State) :
    clPlacedCfg (clKeepLastPlacement _)
      (Sum.inr : C.State → (clRepeatTM C entry exit).State)
      (Fin.addCases (fun _ _ => none)
        (fun _ : Fin 1 => FinTM.bufferTape (List.replicate N true)))
      (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => (j : ℤ)))
      (Cfg.ofWords (input := x) q (stateWord C.k s)) =
        clRepeatCfg C entry exit x (.inr q) s N j := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [clRepeatCfg, Cfg.ofWords, clKeepLastPlacement]

/-- One actual clean call is usable even if its exported entry equals its
exit: the fresh begin phase executes the mandatory positive first step.
**Proof sketch.** Execute that first source action directly, then relocate
only the remaining positive-time prefix. The exported strict positive return
guard excludes interception before the endpoint. The full clean endpoint
restores every scratch cell and head and preserves the unary clock. -/
private lemma clRepeat_call (C : FinTM Bool) (entry exit : C.State)
    (x s s' : List Bool) (N j t : ℕ) (hp : 0 < t)
    (hf : ∀ r, 0 < r → r < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k s)) r).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k s)) t =
      Cfg.ofWords exit (stateWord C.k s')) :
    (clRepeatTM C entry exit).tm.runFrom (clRepeatCfg C entry exit x (.inl 1) s N j) t =
      clRepeatCfg C entry exit x (.inr exit) s' N j := by
  let src := Cfg.ofWords (input := x) entry (stateWord C.k s)
  let tapes : Fin (C.k + 1) → ℤ → Option Bool := Fin.addCases (fun _ _ => none)
    (fun _ : Fin 1 => FinTM.bufferTape (List.replicate N true))
  let heads : Fin (C.k + 1) → ℤ := Fin.addCases (fun _ => 0) (fun _ : Fin 1 => (j : ℤ))
  let frame := clPlacedCfg (x := x) (clKeepLastPlacement _)
    (Sum.inr : C.State → (clRepeatTM C entry exit).State) tapes heads
  have hframe : frame src = clRepeatCfg C entry exit x (.inr entry) s N j :=
    clRepeat_frame C entry exit x s N j entry
  have symbols : (fun i => (clRepeatCfg C entry exit x (.inl 1) s N j).workTapeSymbols
      ((clKeepLastPlacement C.k).index i)) = src.workTapeSymbols := by
    funext i
    simp [clRepeatCfg, Cfg.workTapeSymbols, clKeepLastPlacement, src, Cfg.ofWords]
  have srcstep : C.tm.step src = (C.tm.tr entry src.inputSymbol src.workTapeSymbols).apply src := rfl
  have first : (clRepeatTM C entry exit).tm.step (clRepeatCfg C entry exit x (.inl 1) s N j) =
      frame (C.tm.step src) := by
    change ((clRepeatTM C entry exit).tm.tr (.inl (1 : Fin 3)) _ _).apply _ = _
    simp only [clRepeatTM, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true, symbols]
    rw [srcstep]
    calc
      _ = (clPlacedAction (clKeepLastPlacement _) (Sum.inr : C.State → (clRepeatTM C entry exit).State) entry (C.tm.tr entry src.inputSymbol src.workTapeSymbols)).apply (frame src) := by
        rw [hframe]
        rfl
      _ = _ := clPlaced_apply _ _ entry tapes heads _ src
  have run := clPlaced_run C.tm (clRepeatTM C entry exit).tm (clKeepLastPlacement _) Sum.inr (by intro a b h; cases h; rfl) (fun q => q ≠ exit)
    (by intro q hq inp work; exact if_neg hq) tapes heads
    (C.tm.step src) (t - 1) (by
      intro r hr q hq hqe
      subst q
      apply hf (r + 1) (by omega) (by omega)
      simpa only [MultiTapeTM.runFrom_succ_eq_step] using hq)
  have endSrc : C.tm.runFrom (C.tm.step src) (t - 1) =
      Cfg.ofWords exit (stateWord C.k s') := by
    rw [← MultiTapeTM.runFrom_succ_eq_step, Nat.sub_add_cancel hp]
    exact he
  rw [endSrc] at run
  rw [show t = (t - 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step, first]
  exact run.trans (clRepeat_frame C entry exit x s' N j exit)

/-- The unary clock advances once before each positive clean call. Both
administrative dispatches are charged, including calls returning empty words.
**Proof sketch.** Read and advance the occupied unary clock cell, execute the entire positive clean call, and perform one return dispatch. Both surrounding configurations are exact. -/
private lemma clRepeat_round (C : FinTM Bool) (entry exit : C.State)
    (x s s' : List Bool) (N j t : ℕ) (hj : j < N) (hp : 0 < t)
    (hf : ∀ r, 0 < r → r < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k s)) r).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k s)) t =
      Cfg.ofWords exit (stateWord C.k s')) :
    (clRepeatTM C entry exit).tm.runFrom (clRepeatCfg C entry exit x (.inl 0) s N j) (t + 2) =
      clRepeatCfg C entry exit x (.inl 0) s' N (j + 1) := by
  have hclock : FinTM.bufferTape (List.replicate N true) (j : ℤ) = some true := by
    rw [FinTM.bufferTape_nat, List.getElem?_replicate_of_lt hj]
  have tick : (clRepeatTM C entry exit).tm.step (clRepeatCfg C entry exit x (.inl 0) s N j) =
      clRepeatCfg C entry exit x (.inl 1) s N (j + 1) := by
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, clRepeatTM, clRepeatCfg, Cfg.workTapeSymbols, Action.apply,
        hclock, funext_iff, -Fin.natAdd_eq_addNat]
    all_goals
      intro i
      refine Fin.addCases ?_ ?_ i <;> intro i <;> simp
  have back : (clRepeatTM C entry exit).tm.step
      (clRepeatCfg C entry exit x (.inr exit) s' N (j + 1)) =
      clRepeatCfg C entry exit x (.inl 0) s' N (j + 1) := by
    change ((clRepeatTM C entry exit).tm.tr (.inr exit) _ _).apply _ = _
    simp only [clRepeatTM, if_true]
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    rfl
  rw [show t + 2 = (t + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step, tick,
    MultiTapeTM.runFrom_succ_eq_step', clRepeat_call C entry exit x s s' N (j + 1) t hp hf he, back]

/-- Bounded repeated clean calls consume exactly the unary number of
iterations, then return silently with the entire final state word.
**Proof sketch.** Induct over the executed clock prefix. At each stage the
actual clean-call contract supplies a positive first return; the native round
charges it and both dispatches. The final blank clock executes one silent
completion transition. Every call starts from the full restored seam. -/
private lemma clRepeat_complete (C : FinTM Bool) (entry exit : C.State)
    (f : List Bool → List Bool) (x s : List Bool) (N B : ℕ)
    (hcall : ∀ j < N, ∃ t ≤ B, 0 < t ∧
      (∀ r, 0 < r → r < t →
        (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k (f^[j] s))) r).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k (f^[j] s))) t =
        Cfg.ofWords exit (stateWord C.k (f (f^[j] s)))) :
    ∃ t ≤ N * (B + 2) + 1,
      (clRepeatTM C entry exit).tm.runFrom (clRepeatCfg C entry exit x (.inl 0) s N 0) t =
        clRepeatCfg C entry exit x (.inl 2) (f^[N] s) N N := by
  have hpref : ∀ j ≤ N, ∃ t ≤ j * (B + 2),
      (clRepeatTM C entry exit).tm.runFrom (clRepeatCfg C entry exit x (.inl 0) s N 0) t =
        clRepeatCfg C entry exit x (.inl 0) (f^[j] s) N j := by
    intro j
    induction j with
    | zero => intro hj; exact ⟨0, by simp, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨a, ha, he⟩ := ih (by omega)
      obtain ⟨b, hb, hp, hf, hr⟩ := hcall j (by omega)
      refine ⟨a + (b + 2), ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, he, clRepeat_round C entry exit x _ _ N j b (by omega) hp hf hr,
          Function.iterate_succ_apply']
  obtain ⟨a, ha, he⟩ := hpref N le_rfl
  refine ⟨a + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', he]
  change ((clRepeatTM C entry exit).tm.tr (.inl 0) _ _).apply _ = _
  simp only [clRepeatTM, if_true, clRepeatCfg, Cfg.workTapeSymbols,
    Fin.addCases_right, FinTM.bufferTape_nat, List.getElem?_replicate, Nat.lt_irrefl, if_false]
  rw [FinTM.controlAction_apply, moveInputPos_zero]

/-- Native repetition argument: the clean call's one state word, blank
scratch, and the unary number of calls in a separate protected field. -/
private def clRepeatWords (C : FinTM Bool) (s : List Bool) (N : ℕ) :
    Fin (C.k + 1) → List Bool := Fin.addCases (stateWord C.k s) (fun _ : Fin 1 => List.replicate N true)

/-- Exact prepared repetition seam for the generic native loader. -/
private lemma clRepeat_initial (C : FinTM Bool) (entry exit : C.State)
    (x s : List Bool) (N : ℕ) :
    Cfg.ofWords (input := x) (clRepeatTM C entry exit).tm.q₀ (clRepeatWords C s N) =
      clRepeatCfg C entry exit x (.inl 0) s N 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [Cfg.ofWords, clRepeatWords, clRepeatCfg]

/-- Repetition followed by physical replay of its completed state word. -/
private def clRepeatOutputTM (C : FinTM Bool) (entry exit : C.State) (hk : 0 < C.k) : FinTM Bool :=
  clOutputTM (clPreparedTM (clRepeatTM C entry exit)) (.inr (.inl 2))
    (Fin.castAdd 1 (Fin.castAdd 1 ⟨0, hk⟩))

/-- Complete native repetition ledger, including actual input parsing,
all positive calls, every clock/return dispatch and final state-word replay.
**Proof sketch.** The native loader reaches the exact prepared clock/call
bank. Each call's argument size is bounded along the actual orbit; its clean
return supplies every scratch reset. Relocate the complete unary repetition,
then replay the actual final state tape from its restored head zero. -/
private lemma clRepeatOutput_compute (C : FinTM Bool) (entry exit : C.State) (hk : 0 < C.k)
    (f : List Bool → List Bool) (a d : ℕ)
    (hcall : ∀ x arg, ∃ t ≤ a * (arg.length + 1) ^ d, 0 < t ∧
      (∀ j, 0 < j → j < t →
        (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) j).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        Cfg.ofWords exit (stateWord C.k (f arg)))
    (s : List Bool) (N W : ℕ) (hW : ∀ j ≤ N, (f^[j] s).length ≤ W) :
    let arg := clFields (List.ofFn (clRepeatWords C s N)) ++ []
    (clRepeatOutputTM C entry exit hk).ComputesInTime arg (f^[N] s)
      (2 * arg.length + 9 + (C.k + 1) * (3 * arg.length + 7) +
        N * (a * (W + 1) ^ d + 2) + W) := by
  dsimp only
  let arg := clFields (List.ofFn (clRepeatWords C s N)) ++ []
  have hWords : ∀ i, (clRepeatWords C s N i).length ≤ arg.length := by
    intro i
    simpa [arg] using clFields_width (List.ofFn (clRepeatWords C s N))
      (clRepeatWords C s N i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  obtain ⟨b, hb, he⟩ := clRepeat_complete C entry exit f arg s N (a * (W + 1) ^ d) (by
    intro j hj
    obtain ⟨t, ht, hp, hf, hr⟩ := hcall arg (f^[j] s)
    refine ⟨t, ht.trans ?_, hp, hf, hr⟩
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hW j (by omega)) 1) d))
  obtain ⟨u, hu, hr⟩ := clPrepared_run (clRepeatTM C entry exit) (clRepeatWords C s N)
    [] arg.length hWords b
  rw [clRepeat_initial, he] at hr
  have hc := clOutputAt_compute (clPreparedTM (clRepeatTM C entry exit)) (.inr (.inl 2))
    (Fin.castAdd 1 (Fin.castAdd 1 ⟨0, hk⟩)) arg (f^[N] s) (u + b) 0 _ hr rfl
    (by simp [clPreparedTM, seamCompTM])
    (fun c hc => clPrepared_idle (clRepeatTM C entry exit) (.inl 2)
      (by intros; simp [clRepeatTM]) c hc) rfl
    (by simp [clPreparedCfg, clKeepLastPlacement, clRepeatCfg, clRepeatTM, stateWord, Fin.addCases, hk])
    (by simp [clPreparedCfg, clKeepLastPlacement, clRepeatCfg, clRepeatTM, Fin.addCases, hk]) (by omega)
  apply hc.mono
  have hlast := hW N le_rfl
  change u ≤ 2 * arg.length + 4 + (C.k + 1) * (3 * arg.length + 7) at hu
  change u + b + 0 + (f^[N] s).length + 4 ≤
    2 * arg.length + 9 + (C.k + 1) * (3 * arg.length + 7) +
      N * (a * (W + 1) ^ d + 2) + W
  omega

/-- A field list with bounded payloads has the exact doubled-bit/separator
storage envelope. This is a size lemma, not a native-access shortcut. -/
private lemma clFields_size (ws : List (List Bool)) (W : ℕ)
    (hW : ∀ w ∈ ws, w.length ≤ W) : (clFields ws).length ≤ ws.length * (2 * W + 2) := by
  induction ws with
  | nil => simp [clFields]
  | cons w ws ih =>
    have hw := hW w (by simp)
    have hi := ih (by intro u hu; exact hW u (by simp [hu]))
    have hl : (clFields (w :: ws)).length = 2 * w.length + 2 + (clFields ws).length := by
      simp [clFields, pairEncode, Nat.mul_comm, Nat.add_assoc] <;> omega
    rw [hl, List.length_cons]
    calc
      _ ≤ (2 * W + 2) + ws.length * (2 * W + 2) := by omega
      _ = _ := by ring

/-- Every stored visit code fits the elapsed-time width envelope, including
absence at time zero. A present predecessor is strictly below the query time. -/
private lemma clVisitCode_size (M : FinTM Bool) (m t : ℕ) (τ : Fin M.k) :
    (clVisitCode (prevVisit M m t τ)).length ≤ t + 2 := by
  cases h : prevVisit M m t τ with
  | none => simp [clVisitCode]
  | some s =>
    have hs := (clPrev_spec M m t s τ h).1
    have hw := clElapsed_width s t (by omega)
    simpa [clVisitCode, pairEncode] using hw

/-- One entire visit row includes a delimiter even for an absent visit. -/
private lemma clVisitRow_size (M : FinTM Bool) (C e : ℕ) (x : List Bool) (t N : ℕ) (ht : t ≤ N) :
    (clVisitRow M C e (pairEncode x (List.replicate t true))).length ≤ M.k * (2 * N + 6) := by
  rw [clVisitRow_exact]
  have h := clFields_size (List.ofFn (fun τ : Fin M.k =>
    clVisitCode (prevVisit M (x.length + C * (x.length + 1) ^ e) t τ))) (N + 2) (by
      intro w hw
      obtain ⟨τ, rfl⟩ := List.mem_ofFn.mp hw
      exact (clVisitCode_size M _ t τ).trans (by omega))
  simpa only [List.length_ofFn, show 2 * (N + 2) + 2 = 2 * N + 6 by omega] using h

/-- Ordered accumulation remains quadratic in the unary outer horizon. -/
private lemma clVisitRows_size (M : FinTM Bool) (C e : ℕ) (x : List Bool) (N : ℕ) :
    ∀ t ≤ N, (clVisitRows M C e x t).length ≤ t * (M.k * (2 * N + 6)) := by
  intro t
  induction t with
  | zero => intro ht; simp [clVisitRows]
  | succ t ih =>
    intro ht
    have hi := ih (by omega)
    have hr := clVisitRow_size M C e x t N (by omega)
    simp only [clVisitRows, List.length_append]
    calc
      _ ≤ t * (M.k * (2 * N + 6)) + M.k * (2 * N + 6) := Nat.add_le_add hi hr
      _ = _ := by ring

/-- The complete retained state at every actual outer-loop time fits one
quadratic bound in the input/clock size. -/
private lemma clVisitState_size (M : FinTM Bool) (C e : ℕ) (x : List Bool)
    (N L : ℕ) (hx : x.length ≤ L) (hN : N ≤ L) :
    ∀ j ≤ N, ((clVisitStep M C e)^[j] (clVisitState x 0 [])).length ≤
      (8 + 8 * M.k) * (L + 1) ^ 2 := by
  intro j hj
  rw [clVisitStep_orbit]
  have hrow := clVisitRows_size M C e x N j hj
  have hprod := Nat.mul_le_mul (hj.trans hN)
    (Nat.mul_le_mul_left M.k (show 2 * N + 6 ≤ 2 * L + 6 by omega))
  have hlen : (clVisitState x j (clVisitRows M C e x j)).length =
      2 * x.length + 2 * j + 4 + (clVisitRows M C e x j).length := by
    simp [clVisitState, pairEncode, Nat.mul_comm, Nat.add_assoc] <;> omega
  rw [hlen]
  have hb : 2 * L + 2 * L + 4 + L * (M.k * (2 * L + 6)) ≤
      (8 + 8 * M.k) * (L + 1) ^ 2 := by ring_nf; omega
  omega
/-- Scalar polynomial envelope for the entire native repetition. The
quadratic state-size bound and the clean-call polynomial are both charged.
**Proof sketch.** Substitute the quadratic orbit-word bound into the clean-call polynomial. Multiply by the actual unary number of calls, add preparation and replay, then dominate all terms by one monomial. -/
private lemma clRepeat_budget (L N k K a d : ℕ) (hN : N ≤ L) :
    2 * L + 9 + k * (3 * L + 7) + N * (a * (K * (L + 1) ^ 2 + 1) ^ d + 2) +
      K * (L + 1) ^ 2 ≤
      (13 + 7 * k + a * (K + 1) ^ d + K) * (L + 1) ^ (2 * d + 3) := by
  have hpos : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
  have hw : K * (L + 1) ^ 2 + 1 ≤ (K + 1) * (L + 1) ^ 2 := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have hm : N * (a * (K * (L + 1) ^ 2 + 1) ^ d + 2) ≤
      a * (K + 1) ^ d * (L + 1) ^ (2 * d + 1) + 2 * (L + 1) := by
    calc
      _ ≤ (L + 1) * (a * ((K + 1) * (L + 1) ^ 2) ^ d + 2) :=
        Nat.mul_le_mul (by omega) (Nat.add_le_add_right
          (Nat.mul_le_mul_left a (Nat.pow_le_pow_left hw d)) 2)
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, pow_succ]; ring
  have hl : 2 * L + 9 + k * (3 * L + 7) + 2 * (L + 1) ≤
      (13 + 7 * k) * (L + 1) := by ring_nf; omega
  have h1 : L + 1 ≤ (L + 1) ^ (2 * d + 3) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos L)
      (show 1 ≤ 2 * d + 3 by omega)
  have h2 : (L + 1) ^ 2 ≤ (L + 1) ^ (2 * d + 3) :=
    Nat.pow_le_pow_right (Nat.succ_pos L) (by omega)
  have hd : (L + 1) ^ (2 * d + 1) ≤ (L + 1) ^ (2 * d + 3) :=
    Nat.pow_le_pow_right (Nat.succ_pos L) (by omega)
  have hl' := Nat.mul_le_mul_left (13 + 7 * k) h1
  have hk' := Nat.mul_le_mul_left K h2
  have hd' := Nat.mul_le_mul_left (a * (K + 1) ^ d) hd
  calc
    _ ≤ (13 + 7 * k) * (L + 1) + a * (K + 1) ^ d * (L + 1) ^ (2 * d + 1) +
        K * (L + 1) ^ 2 := by omega
    _ ≤ (13 + 7 * k) * (L + 1) ^ (2 * d + 3) +
        (a * (K + 1) ^ d) * (L + 1) ^ (2 * d + 3) + K * (L + 1) ^ (2 * d + 3) :=
      Nat.add_le_add (Nat.add_le_add hl' hd') hk'
    _ = _ := by ring

/-- The exact native repetition argument is itself a native computation:
one retained state field, blank call scratch, and the actual unary clock. -/
private lemma clRepeatArgument_native (C : FinTM Bool) (s : List Bool → List Bool)
    (N : List Bool → ℕ) (hs : PolyTimeComputable s)
    (hN : PolyTimeComputable (fun x => List.replicate (N x) true)) :
    PolyTimeComputable (fun x => clFields (List.ofFn (clRepeatWords C (s x) (N x)))) := by
  let fs : List (List Bool → List Bool) := List.ofFn (fun i : Fin (C.k + 1) =>
    fun x => clRepeatWords C (s x) (N x) i)
  have hf : ∀ f ∈ fs, PolyTimeComputable f := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    refine Fin.addCases ?_ ?_ i
    · intro i
      by_cases hi : i.val = 0
      · simpa [clRepeatWords, stateWord, hi] using hs
      · simpa [clRepeatWords, stateWord, hi] using clNative_linear _ (FinTM.computesFunInTime_const [])
    · intro i; simpa [clRepeatWords] using hN
  simpa only [fs, List.map_ofFn] using clNative_fields fs hf

/-- The exact inherited horizon, expressed as a length function for the
whole producer's initial unary clock. It is still distinct from emitter fuel. -/
private def clProducerHorizon (C e c A d n : ℕ) : ℕ :=
  c * (A * (n + C * (n + 1) ^ e + 1) ^ d + 1) ^ 2

/-- The inherited header supplies the outer producer's exact unary horizon;
adding one accounts for its inclusive final row, including a zero horizon. -/
private lemma clProducerClock_native (C e c A d : ℕ) :
    PolyTimeComputable (fun x => List.replicate (clProducerHorizon C e c A d x.length + 1) true) := by
  have ht := (clHeaderTail_native 5).comp (clPrepHeader_native C e c A d)
  have h := clNative_append ht (clNative_linear _ (FinTM.computesFunInTime_const [true]))
  convert h using 1
  funext x
  simp only [Function.comp_apply, clHeaderTail, clPrepHeader, pairDecode_pairEncode,
    Option.map_some, Option.getD_some]
  simp only [clProducerHorizon, List.replicate_add, List.replicate_one]

/-- The complete ordered last-visit table is produced from native original
input with a total polynomial bound; no outer-loop seam remains assumed.
**Proof sketch.** Start with the retained instance and empty table. Obtain
an actual clean call for the whole native row step, including its search,
append and cleanup. Native field packing supplies that call's initial words
and an exact `T+1` unary clock. Run the actual repetition controller, whose
invariant bounds all intermediate state words quadratically in the encoded
argument. Its ledger pays for parsing, every call and dispatch, and final
physical output. Native projection then returns precisely the stored rows. -/
private lemma clVisitRows_native (M : FinTM Bool) (C e c A d : ℕ) :
    PolyTimeComputable (fun x => clVisitRows M C e x (clProducerHorizon C e c A d x.length + 1)) := by
  obtain ⟨W, entry, exit, a, r, hk, hcall⟩ := clVisitStep_cleanCall M C e
  let N := fun x : List Bool => clProducerHorizon C e c A d x.length + 1
  let s := fun x => clVisitState x 0 []
  have hs : PolyTimeComputable s := by
    simpa [s, clVisitState] using clNative_pair polyTimeComputable_id
      (clNative_linear _ (FinTM.computesFunInTime_const (pairEncode [] [])))
  have hN : PolyTimeComputable (fun x => List.replicate (N x) true) := clProducerClock_native C e c A d
  let K := 8 + 8 * M.k
  have hstate : PolyTimeComputable (fun x => clVisitState x (N x) (clVisitRows M C e x (N x))) := by
    apply clNative_image (clRepeatArgument_native W s N hs hN) (clRepeatOutputTM W entry exit hk)
      (13 + 7 * (W.k + 1) + a * (K + 1) ^ r + K) (2 * r + 3)
    intro x
    let arg := clFields (List.ofFn (clRepeatWords W (s x) (N x)))
    have hn : N x ≤ arg.length := by
      have hh := clFields_width (List.ofFn (clRepeatWords W (s x) (N x)))
        (clRepeatWords W (s x) (N x) (Fin.natAdd W.k (0 : Fin 1)))
        (List.mem_ofFn.mpr ⟨_, rfl⟩)
      simpa only [clRepeatWords, Fin.addCases_right, List.length_replicate] using hh
    have hx : x.length ≤ arg.length := by
      have hh := clFields_width (List.ofFn (clRepeatWords W (s x) (N x)))
        (clRepeatWords W (s x) (N x) (Fin.castAdd 1 ⟨0, hk⟩))
        (List.mem_ofFn.mpr ⟨_, rfl⟩)
      have hss : (s x).length ≤ arg.length := by
        simpa only [clRepeatWords, Fin.addCases_left, stateWord, if_pos rfl] using hh
      have hlen : x.length ≤ (s x).length := by simp [s, clVisitState, pairEncode]; omega
      exact hlen.trans hss
    have hsize := clVisitState_size M C e x (N x) arg.length hx hn
    have hc := clRepeatOutput_compute W entry exit hk (clVisitStep M C e) a r hcall
      (s x) (N x) (K * (arg.length + 1) ^ 2) hsize
    dsimp only at hc
    rw [List.append_nil, clVisitStep_orbit] at hc
    exact hc.mono (clRepeat_budget arg.length (N x) (W.k + 1) K a r hn)
  have h := (clHeaderTail_native 2).comp hstate
  simpa [Function.comp_def, clHeaderTail, clVisitState, pairDecode_pairEncode, N] using h

/-- Complete packed preparation data: the untouched exact arithmetic
header, the inclusive chronological movement-count trajectory, and the
inclusive time-ordered/work-tape-ordered canonical last-visit table. -/
private def clPackedRecords (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool) : List Bool :=
  let m := x.length + C * (x.length + 1) ^ e
  let T := clProducerHorizon C e c A d x.length
  pairEncode (clPrepHeader C e c A d x)
    (pairEncode (clRecords M (List.replicate m false) (T + 1)) (clVisitRows M C e x (T + 1)))

/-- The completed packed-record producer is a genuine native polynomial
computation of the entire packed word, including all earlier-visit records.
**Proof sketch.** Pair the actual native header, actual inclusive recorder
output and actual completed native visit-table output. The native composition
calculus charges every retained copy and capture/rewind; all underlying runs
have been proved from native input. This is the complete step-1 checkpoint,
not the later emitter installation or its common budget. -/
private lemma clPackedRecords_native (M : FinTM Bool) (C e c A d : ℕ) :
    PolyTimeComputable (clPackedRecords M C e c A d) :=
  clNative_pair (clPrepHeader_native C e c A d)
    (clNative_pair (clRecords_native M C e c A d) (clVisitRows_native M C e c A d))

/-- One native machine returns the full exact packed result within one
polynomial ledger from the original input. The complete stored answer's
length is separately bounded by that same actual runtime.
**Proof sketch.** Unpack the completed native polynomial construction and
apply its one-bit-per-transition output bound. All clocked outer iterations,
individual searches, explicit resets and clean-call cleanups lie inside this
producer; no unproved final-buffer or installation seam is a hypothesis. -/
private lemma clPackedRecords_machine (M : FinTM Bool) (C e c A d : ℕ) :
    ∃ (H : FinTM Bool) (a r : ℕ),
      H.ComputesFunInTime (clPackedRecords M C e c A d) (fun n => a * (n + 1) ^ r) ∧
      ∀ x, (clPackedRecords M C e c A d x).length ≤ a * (x.length + 1) ^ r := by
  obtain ⟨H, a, r, hH⟩ := clPackedRecords_native M C e c A d
  refine ⟨H, a, r, hH, ?_⟩
  intro x
  have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hH x)).2
  simpa only [ho] using H.tm.output_length_le x (a * (x.length + 1) ^ r)

/-! E4-A5 continuation: installation and ordered emission. The clean
module host below is locally harvested from `ClassNP/SAT.lean`, with five
phases: native copy, complete producer, cursor initialization, emission,
and cursor update. All inherited A/A2/A3/A4 declarations remain frozen. -/

/-- A padded halting run can be cut at its first halt without changing any
endpoint field. This is the local instance of the engine's minimal-halt
argument: use `Nat.find` and the absorbing-halt law. -/
private lemma clA5_call_first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, fun v hv => Nat.find_min h hv, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hu]

/-- Pad a callable module into a shared bank, keeping unused tapes stationary. -/
private def clA5PadAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
  ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
    a.output, a.state⟩

/-- All modules share tape zero; a positive source bank is padded on the right. -/
private def clA5PadTM (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K) : FinTM Bool where
  k := K
  State := M.State
  tm := { q₀ := M.tm.q₀
          tr := fun q inp work => clA5PadAction (M.tm.tr q inp
            (fun i => work ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)) }

/-- Configuration embedding for the shared bank; the padding is genuinely blank. -/
private def clA5PadCfg {k K : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos,
    fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- Padding commutes with a transition, including writes at arbitrary cells.
**Proof sketch.** Split each work index by membership in the source bank;
the inactive branch neither writes nor moves. -/
private lemma clA5Pad_apply {k K : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (clA5PadAction (K := K) a).apply (clA5PadCfg c) = clA5PadCfg (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases h : i.val < k <;> simp [clA5PadAction, clA5PadCfg, Action.apply, h]
  · funext i
    by_cases h : i.val < k <;> simp [clA5PadAction, clA5PadCfg, Action.apply, h]

/-- The padded source observes exactly its original work symbols. -/
private lemma clA5Pad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (clA5PadTM M K hk).tm.runFrom (clA5PadCfg c) t = clA5PadCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, clA5PadCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (clA5PadCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [clA5PadCfg, Cfg.workTapeSymbols, i.isLt]
    have hstate : (clA5PadCfg (K := K) c).state = some q := hs
    simp only [MultiTapeTM.step, hstate, hs]
    change (clA5PadAction (M.tm.tr q c.inputSymbol _)).apply _ = _
    rw [hw]
    exact clA5Pad_apply _ _

/-- Positive tape count makes the padded seam the same canonical state word. -/
private lemma clA5Pad_seam {k K : ℕ} {S : Type} {x : List Bool}
    (hk : 0 < k) (q : S) (w out : List Bool) :
    clA5PadCfg (K := K) ({Cfg.ofWords (input := x) q (stateWord k w) with output := out}) =
      {Cfg.ofWords (input := x) q (stateWord K w) with output := out} := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : i.val < k
    · simp [clA5PadCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [clA5PadCfg, Cfg.ofWords, stateWord, hi, hn, FinTM.bufferTape]
  · funext i
    by_cases hi : i.val < k <;> simp [clA5PadCfg, Cfg.ofWords, hi]

/-- Convert a first-positive-exit module into a halting source for `emit_run`.
The Boolean release flag ensures even an entry equal to exit executes once. -/
private def clA5StopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- Release-flag embedding preserves all physical fields of a call. -/
private def clA5StopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same
physical step as the module and raises the release flag. -/
private lemma clA5Stop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (clA5StopTM C entry exit).tm.step (clA5StopCfg b c) = clA5StopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    simp only [MultiTapeTM.step, clA5StopCfg, hs, Option.map_some]
    simp only [clA5StopTM, hq, ↓reduceIte]
    rfl

/-- Live endpoints force every earlier module state to be live. -/
private lemma clA5_live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- Stop a clean call one silent step after its certified first positive exit.
**Proof sketch.** Induct on prefixes, keeping the release flag false only at
time zero. The supplied guard prevents early stopping; a final silent halt
retains every canonical seam field and every emitted bit. -/
private lemma clA5Stop_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (clA5StopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
      {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hl := clA5_live_prefix C.tm c t (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords])
  have hp : ∀ v, v ≤ t → (clA5StopTM C entry exit).tm.runFrom (clA5StopCfg false c) v =
      clA5StopCfg (decide (v ≠ 0)) (C.tm.runFrom c v) := by
    intro v
    induction v with
    | zero => intro _; rfl
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        clA5Stop_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      rfl
  have hi : Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg) = clA5StopCfg false c := rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _)]
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hflag, show C.tm.runFrom c t = _ from he]
  simp [MultiTapeTM.step, clA5StopTM, clA5StopCfg, Cfg.ofWords, FinTM.controlAction, Action.apply]

/-- Five finite modules form the body: native input copy, full packed-record
installation and cursor installation, then recurring emission and cursor update. -/
private abbrev CLA5HostState (M : Fin 5 → FinTM Bool) := Unit ⊕ (Σ i, (M i).State)

/-- A module's return destination; cursor initialization and cursor update return to
the unique loop anchor. The other calls continue to the next finite module. -/
private def clA5HostNext (i : Fin 5) : Option (Fin 5) :=
  if i = 0 then some 1 else if i = 1 then some 2 else if i = 3 then some 4 else none

/-- A named entry state inside the finite body. -/
private def clA5HostEntry (M : Fin 5 → FinTM Bool) (i : Fin 5) : CLA5HostState M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- Resolve a finite module's return, with no additional tape operation. -/
private def clA5HostRet (M : Fin 5 → FinTM Bool) (i : Fin 5) : CLA5HostState M :=
  match clA5HostNext i with
  | some j => clA5HostEntry M j
  | none => .inl ()

/-- The actual finite controller. All modules use the same padded work bank,
so the clean-call contracts restore scratch before each next call. `emitAction`
forwards the halting transition as well as ordinary transitions. -/
private def clA5HostTM (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) : FinTM Bool where
  k := K
  State := CLA5HostState M
  tm := {
    q₀ := clA5HostEntry M 0
    tr := fun q inp work => match q with
      | .inl _ => FinTM.controlAction 0 (some (clA5HostEntry M 3))
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (clA5HostRet M i)
          ((clA5PadTM (M i) K (hk i)).tm.tr s inp work) }

/-- Forwarding a padded clean configuration produces the host's canonical
seam with precisely the supplied output prefix. Positive tape count is used
only to identify the real tape-zero word. -/
private lemma clA5Host_seam (M : Fin 5 → FinTM Bool) (K : ℕ) (i : Fin 5)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : CLA5HostState M)) (clA5HostRet M i) pre
      (clA5PadCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : CLA5HostState M))).getD (clA5HostRet M i)))
        (stateWord K w) with output := pre ++ out} := by
  have h := clA5Pad_seam (K := K) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h

/-- Run one clean module inside the body, forwarding exactly its output.
**Proof sketch.** Padding preserves the source run. The audited `emit_run`
then transfers every live prefix and the halting endpoint; live prefixes
always remain in that module's state summand, hence cannot hit the anchor. -/
private lemma clA5Host_call (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (i : Fin 5) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ((clA5HostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} v).state
        ≠ some (.inl ())) ∧
    (clA5HostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} t =
      {Cfg.ofWords (clA5HostRet M i) (stateWord K result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → CLA5HostState M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (clA5HostRet M i) pre (clA5PadCfg (K := K) c) =
      {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} := by
    simpa [emb, c, clA5HostEntry] using
      clA5Host_seam M K i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (clA5HostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} v =
        emitCfg emb (clA5HostRet M i) pre (clA5PadCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (clA5PadTM (M i) K (hk i)).tm (clA5HostTM M K hk).tm emb (clA5HostRet M i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [clA5Pad_run]
        exact hg u (by omega))]
    rw [clA5Pad_run]
  constructor
  · intro v hv
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg, clA5PadCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact clA5Host_seam M K i hp x result pre out q none

/-- Joining two guarded segments preserves the first-return guard when the
intermediate seam is also outside the anchor. -/
private lemma clA5_guard_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  intro v hv
  by_cases h : v < a
  · exact ha v h
  · have hva : a ≤ v := by omega
    rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
    exact hb (v - a) (by omega)

/-- Uniform clean-module contract: a first halt with a prescribed replacement
word and emitted chunk, over every untouched native input. -/
private def CLA5Clean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- Turn a clean-call bridge contract into the uniform first-halting form.
**Proof sketch.** The release wrapper stops one step after the positive exit;
minimal-halt cutting retains its entire clean configuration. -/
private lemma clA5Clean_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    CLA5Clean (clA5StopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := clA5Stop_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := clA5_call_first_halt (clA5StopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [clA5StopTM, Cfg.ofWords] using hend.trans hs

/-- The bridge overhead is bounded by one monomial of degree one higher.
**Proof sketch.** Output length is bounded by source time; `n+1` and both
source-time terms fit the larger power. The last unit pays for stopping. -/
private lemma clA5_bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- Every polynomial word computation has a clean first-halting install
module with a polynomial budget on the argument length. -/
private lemma clA5Clean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, CLA5Clean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  -- The bridge's result length depends on the word, so enlarge it pointwise
  -- to source time before putting it in the uniform argument-length budget.
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clA5Clean_stop C entry exit f (fun _ => [])
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      refine ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, ?_⟩
      exact he)
  refine ⟨clA5StopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (clA5_bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- The emit-mode counterpart preserves the argument and forwards the exact
computed chunk. Its polynomial budget includes cleanup and the final halt. -/
private lemma clA5Clean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, CLA5Clean M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clA5Clean_stop C entry exit id f
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨clA5StopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (clA5_bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- Specialize a clean module to one call site in the finite host. -/
private lemma clA5Host_clean (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (i : Fin 5) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : CLA5Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ((clA5HostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl ())) ∧
      (clA5HostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (clA5HostEntry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (clA5HostRet M i) (stateWord K (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ := clA5Host_call M K hk i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- The inherited native input copier becomes a first-halting startup
module without changing its stored word, heads, or silent output.
**Proof sketch.** Consume the banked positive first return, add the proved
release wrapper, then cut the absorbing endpoint at its first halt. -/
private lemma clA5Copy_clean (x : List Bool) :
    let D := clA5StopTM clInputTM (0 : Fin 3) (2 : Fin 3)
    ∃ t, 0 < t ∧ t ≤ 2 * x.length + 3 ∧
      (∀ j < t, ¬(D.tm.runFrom
        (Cfg.ofWords (input := x) D.tm.q₀ (stateWord D.k [])) j).Halted) ∧
      D.tm.runFrom (Cfg.ofWords (input := x) D.tm.q₀ (stateWord D.k [])) t =
        {Cfg.ofWords (input := x) D.tm.q₀ (stateWord D.k x) with state := none} := by
  dsimp only
  obtain ⟨t, ht, hp, hf, he⟩ := clInput_first x
  have hi : clInputTM.tm.initCfg x =
      Cfg.ofWords (input := x) (0 : Fin 3) (stateWord 1 []) := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i z
    simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord, FinTM.bufferTape]
  have hw : (fun _ : Fin 1 => x) = stateWord 1 x := by
    funext i; have hi := Fin.eq_zero i; subst i; rfl
  rw [hi, hw] at he
  have hr := clA5Stop_clean clInputTM (0 : Fin 3) (2 : Fin 3) x [] x [] t hp
    (by
      intro j hj hjt
      change (clInputTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 3) (stateWord 1 [])) j).state ≠ some (2 : Fin 3)
      rw [← hi]
      exact hf j hjt) he
  change (clA5StopTM clInputTM (0 : Fin 3) (2 : Fin 3)).tm.runFrom
    (Cfg.ofWords (input := x) (false, (0 : Fin 3)) (stateWord 1 [])) (t + 1) =
    {Cfg.ofWords (true, (2 : Fin 3)) (stateWord 1 x) with state := none, output := []} at hr
  obtain ⟨u, hu, hub, hug, hue⟩ := clA5_call_first_halt
    (clA5StopTM clInputTM (0 : Fin 3) (2 : Fin 3)).tm
    (Cfg.ofWords (input := x) (false, (0 : Fin 3)) (stateWord 1 [])) (t + 1)
    (by simp [Cfg.ofWords]) (by rw [hr])
  refine ⟨u, hu, by omega, hug, ?_⟩
  simpa only [clA5StopTM, Cfg.ofWords] using hue.trans hr

/-- The final install call consumes the completed A4 producer itself. Its
argument is the genuine retained native input; its result is the full header,
trajectory and visit table. No producer component is substituted for it. -/
private lemma clA5Packed_install (M : FinTM Bool) (C e c A d : ℕ) :
    ∃ S a r, CLA5Clean S (clPackedRecords M C e c A d) (fun _ => [])
      (fun n => a * (n + 1) ^ r) := by
  obtain ⟨H, a, r, hH, _⟩ := clPackedRecords_machine M C e c A d
  exact clA5Clean_install ⟨H, a, r, hH⟩

/-- Persistent body word: a unary emission cursor followed by the entire
unchanged packed producer answer. The original instance remains in its header. -/
private def clA5Pack (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool) (i : ℕ) : List Bool :=
  pairEncode (List.replicate i true) (clPackedRecords M C e c A d x)

/-- Initial cursor installation is the actual native fixed-pair constructor;
it changes neither the header nor either stored table. -/
private lemma clA5Cursor_install :
    ∃ S a r, CLA5Clean S (pairEncode []) (fun _ => []) (fun n => a * (n + 1) ^ r) :=
  clA5Clean_install (clNative_linear _ (FinTM.computesFunInTime_pairEncodeFixed []))

/-- Concrete body module bank. Its first three modules establish the final
packed/cursor seam; the last two are the emission and cursor-update modules. -/
private def clA5Modules (S J E I : FinTM Bool) : Fin 5 → FinTM Bool := fun i =>
  match i.val with
  | 0 => clA5StopTM clInputTM (0 : Fin 3) (2 : Fin 3)
  | 1 => S
  | 2 => J
  | 3 => E
  | _ => I

/-- One finite shared bank contains every module, with a real data tape. -/
private lemma clA5Modules_bound (S J E I : FinTM Bool) :
    ∀ i, (clA5Modules S J E I i).k ≤ 1 + S.k + J.k + E.k + I.k := by
  intro i
  fin_cases i <;> simp [clA5Modules, clA5StopTM, clInputTM] <;> omega

/-- The complete final-body startup, from native `initCfg`, is silent and
ends at its first anchor with every administrative tape blank and head zero.
The emission and update modules are arbitrary here because startup never
executes them; there is no prepared-input or producer hypothesis left open.
**Proof sketch.** First copy the actual input with the inherited native copier.
Run the clean install of the completed producer, then the fixed empty-cursor
prefix install. Forward all three first-halting runs in separate state tags;
their endpoint equalities specify every tape and head, and their guards join
to exclude the anchor throughout the startup prefix. -/
private lemma clA5Startup (M : FinTM Bool) (C e c A d : ℕ) :
    ∃ (S J : FinTM Bool) (aS dS aJ dJ aH dH : ℕ),
      (∀ x, (clPackedRecords M C e c A d x).length ≤ aH * (x.length + 1) ^ dH) ∧
      ∀ E I : FinTM Bool,
        let bank := clA5Modules S J E I
        let H := clA5HostTM bank (1 + S.k + J.k + E.k + I.k) (clA5Modules_bound S J E I)
        ∀ x : List Bool, ∃ t ≤ 2 * x.length + 3 + aS * (x.length + 1) ^ dS +
            aJ * (aH * (x.length + 1) ^ dH + 1) ^ dJ,
          (∀ j < t, (H.tm.runFrom (H.tm.initCfg x) j).state ≠ some (.inl ())) ∧
          H.tm.runFrom (H.tm.initCfg x) t =
            Cfg.ofWords (.inl ()) (stateWord H.k (clA5Pack M C e c A d x 0)) := by
  obtain ⟨S, aS, dS, hS⟩ := clA5Packed_install M C e c A d
  obtain ⟨J, aJ, dJ, hJ⟩ := clA5Cursor_install
  obtain ⟨_, aH, dH, _, hlen⟩ := clPackedRecords_machine M C e c A d
  refine ⟨S, J, aS, dS, aJ, dJ, aH, dH, hlen, ?_⟩
  intro E I
  dsimp only
  let bank := clA5Modules S J E I
  let K := 1 + S.k + J.k + E.k + I.k
  let H := clA5HostTM bank K (clA5Modules_bound S J E I)
  intro x
  obtain ⟨t0, hp0, ht0, hg0, he0⟩ := clA5Copy_clean x
  obtain ⟨g0, e0⟩ := clA5Host_call bank K (clA5Modules_bound S J E I) 0
    (by simp [bank, clA5Modules, clA5StopTM, clInputTM]) x [] x [] []
    (false, (0 : Fin 3)) t0 hg0 he0
  have hi : H.tm.initCfg x =
      Cfg.ofWords (clA5HostEntry bank 0) (stateWord K []) := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i z
    simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord, FinTM.bufferTape]
  change H.tm.runFrom (Cfg.ofWords (input := x) (clA5HostEntry bank 0) (stateWord K [])) t0 =
    Cfg.ofWords (clA5HostEntry bank 1) (stateWord K x) at e0
  obtain ⟨t1, hp1, ht1, g1, e1⟩ := clA5Host_clean bank K (clA5Modules_bound S J E I) 1
    (clPackedRecords M C e c A d) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
    (by simpa [bank, clA5Modules] using hS) x x []
  change H.tm.runFrom (Cfg.ofWords (input := x) (clA5HostEntry bank 1) (stateWord K x)) t1 =
    Cfg.ofWords (clA5HostEntry bank 2) (stateWord K (clPackedRecords M C e c A d x)) at e1
  obtain ⟨t2, hp2, ht2, g2, e2⟩ := clA5Host_clean bank K (clA5Modules_bound S J E I) 2
    (pairEncode []) (fun _ => []) (fun n => aJ * (n + 1) ^ dJ)
    (by simpa [bank, clA5Modules] using hJ) x (clPackedRecords M C e c A d x) []
  change H.tm.runFrom
    (Cfg.ofWords (input := x) (clA5HostEntry bank 2) (stateWord K (clPackedRecords M C e c A d x))) t2 =
    Cfg.ofWords (.inl ()) (stateWord K (clA5Pack M C e c A d x 0)) at e2
  have hb2 := Nat.mul_le_mul_left aJ
    (Nat.pow_le_pow_left (Nat.add_le_add_right (hlen x) 1) dJ)
  have e01 : H.tm.runFrom
      (Cfg.ofWords (input := x) (clA5HostEntry bank 0) (stateWord K [])) (t0 + t1) =
      Cfg.ofWords (clA5HostEntry bank 2) (stateWord K (clPackedRecords M C e c A d x)) := by
    rw [MultiTapeTM.runFrom_add, e0, e1]
  have g01 := clA5_guard_add H.tm (.inl ()) _ _ t0 t1 g0 e0 g1
  refine ⟨t0 + t1 + t2, by omega, ?_, ?_⟩
  · rw [hi]
    exact clA5_guard_add H.tm (.inl ()) _ _ (t0 + t1) t2 g01 e01 g2
  · rw [hi, MultiTapeTM.runFrom_add, e01, e2]
    rfl

/-- A fixed word is emitted from finite control. -/
private lemma clA5_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) := by
  exact clNative_linear _ (FinTM.computesFunInTime_const w)

/-- Polynomial-time branches on the original input, using W3's captured
single-bit decision. All three budgets fit their maximum degree.

**Proof sketch.** Use the audited conditional constructor on the three witnessing machines. Bound each
monomial by the common maximum exponent and absorb the constructor overhead into one
coefficient. -/
private lemma clA5_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) := by
  obtain ⟨P, A, a, hP⟩ := hp
  obtain ⟨F, B, b, hF⟩ := hf
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hP hF hG
  let e := max a (max b c)
  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
  have ha := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show a ≤ e by exact Nat.le_max_left _ _))
  have hb := Nat.mul_le_mul_left B
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show b ≤ e by omega))
  have hc := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show c ≤ e by omega))
  have h1 : 1 ≤ (x.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  simp only [Nat.succ_eq_add_one] at ha hb hc
  calc
    _ ≤ K * ((A + B + C + 1) * (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (by simp only [Nat.add_mul, Nat.one_mul]; omega)
    _ = _ := by ring


/-- Short-circuit conjunction preserves the order of two polynomial tests. -/
private lemma clA5_pt_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) := by
  have h := clA5_pt_cond hp hq (clA5_pt_const [false])
  convert h using 1
  funext x
  cases p x <;> rfl

/-- Pure semantics for a finite one-way word transducer with at most one
emitted bit per input bit and one optional final bit. -/
private def clA5MapWord {S : Type} (next : S → Bool → S)
    (emit : S → Bool → Option Bool) (finish : S → Option Bool) : S → List Bool → List Bool
  | q, [] => (finish q).toList
  | q, b :: r => (emit q b).toList ++ clA5MapWord next emit finish (next q b) r

/-- Finite one-way transducer for local word operations used by round-field
assembly. It uses no work tapes and always halts at the right boundary. -/
private def clA5MapTM {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) : FinTM Bool where
  k := 0
  State := S
  tm := {
    q₀ := start
    tr := fun q inp _ => match inp with
      | some b => ⟨.pos, Fin.elim0, emit q b, some (next q b)⟩
      | none => ⟨0, Fin.elim0, finish q, none⟩ }

/-- Scanner frame with an explicit already-emitted prefix. -/
private def clA5MapCfg {S : Type} (x : List Bool) (q : S) (i : ℕ)
    (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨some q, ⟨i + 1, by omega⟩, Fin.elim0, Fin.elim0, out⟩

/-- The finite transducer implements its recursive word semantics exactly.
**Proof sketch.** Induct on the unread suffix. An input bit performs one
transition and appends its optional emission; the right blank performs the
final transition, including its optional last bit. -/
private lemma clA5Map_run {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) (x rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) q out,
      ((clA5MapTM next emit finish start).tm.runFrom
        (clA5MapCfg x q pre.length (by simp [hx]) out) (rest.length + 1)).state = none ∧
      ((clA5MapTM next emit finish start).tm.runFrom
        (clA5MapCfg x q pre.length (by simp [hx]) out) (rest.length + 1)).output =
          out ++ clA5MapWord next emit finish q rest := by
  induction rest with
  | nil =>
    intro pre hx q out
    simp only [List.append_nil] at hx
    subst x
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, clA5MapTM,
      clA5MapCfg, Cfg.inputSymbol, Action.apply, clA5MapWord]
  | cons b rest ih =>
    intro pre hx q out
    have hs : (clA5MapTM next emit finish start).tm.step
        (clA5MapCfg x q pre.length (by simp [hx]) out) =
        clA5MapCfg x (next q b) (pre ++ [b]).length (by simp [hx]) (out ++ (emit q b).toList) := by
      have hin : (clA5MapCfg x q pre.length (by simp [hx]) out).inputSymbol = some b := by
        rw [FinTM.inputSymbol_at _ pre.length (by simp [hx]) rfl]
        simp [hx]
      unfold MultiTapeTM.step
      change (((clA5MapTM next emit finish start).tm.tr q _ _).apply _) = _
      rw [hin]
      refine Cfg.ext_zero_tapes rfl ?_ rfl
      simpa using moveInputPos_pos_of_ne_right
        (⟨pre.length + 1, by simp [hx] <;> omega⟩ : Fin (x.length + 2)) (by simp [hx] <;> omega)
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [clA5MapWord, List.append_assoc] using
      ih (pre ++ [b]) (by simpa [List.append_assoc] using hx) (next q b) (out ++ (emit q b).toList)

/-- Every finite mapper has the exact input-length-plus-one time bound. -/
private lemma clA5Map_poly {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) :
    PolyTimeComputable (clA5MapWord next emit finish start) := by
  refine ⟨clA5MapTM next emit finish start, 1, 1, fun x => ?_⟩
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  have hi : (clA5MapTM next emit finish start).tm.initCfg x =
      clA5MapCfg x start 0 (Nat.zero_le _) [] := Cfg.ext_zero_tapes rfl rfl rfl
  simpa only [Nat.pow_one, Nat.one_mul, hi, List.length_nil, List.nil_append] using
    clA5Map_run next emit finish start x x [] (by simp) start []

/-- Removing the first bit is a two-state finite transduction. -/
private lemma clA5_pt_tail : PolyTimeComputable List.tail := by
  let emit (q b : Bool) : Option Bool := if q then some b else none
  have h := clA5Map_poly (fun (_ : Bool) _ => true) emit (fun _ => none) false
  have hc (x : List Bool) : clA5MapWord (fun (_ : Bool) _ => true) emit (fun _ => none) true x = x := by
    induction x with
    | nil => rfl
    | cons b r ih => simp [clA5MapWord, emit, ih]
  have he (x : List Bool) : clA5MapWord (fun (_ : Bool) _ => true) emit (fun _ => none) false x = x.tail := by
    cases x <;> simp [clA5MapWord, emit, hc]
  convert h using 1
  funext x
  exact (he x).symm

/-- Extracting at most the first bit is also a two-state finite transduction. -/
private lemma clA5_pt_head : PolyTimeComputable (fun x => x.take 1) := by
  let emit (q b : Bool) : Option Bool := if q then none else some b
  have h := clA5Map_poly (fun (_ : Bool) _ => true) emit (fun _ => none) false
  have hc (x : List Bool) : clA5MapWord (fun (_ : Bool) _ => true) emit (fun _ => none) true x = [] := by
    induction x with
    | nil => rfl
    | cons b r ih => simp [clA5MapWord, emit, ih]
  have he (x : List Bool) : clA5MapWord (fun (_ : Bool) _ => true) emit (fun _ => none) false x = x.take 1 := by
    cases x <;> simp [clA5MapWord, emit, hc]
  convert h using 1
  funext x
  exact (he x).symm

/-- Equality to a fixed control word is decided by the public finite-word
comparison constructor, after any polynomial field computation. -/
private lemma clA5_pt_eq {f : List Bool → List Bool} (hf : PolyTimeComputable f) (w : List Bool) :
    PolyTimeComputable (fun x => [decide (f x = w)]) := by
  have he : PolyTimeComputable (fun x => if x = w then [true] else [false]) :=
    clNative_linear _ (FinTM.computesFunInTime_ifEq w [true] [false])
  convert he.comp hf using 1
  funext x
  by_cases h : f x = w <;> simp [Function.comp_def, h]

/-- Any native transition with a quadratic orbit-size invariant can be
iterated a native unary number of times in polynomial time.
**Proof sketch.** The inherited positive clean-call bridge supplies each
iteration. Its real unary host charges every call, dispatch, loader and replay.
The actual encoded argument bounds both the initial word and the unary clock;
the supplied orbit bound is therefore covered by the inherited loop ledger. -/
private lemma clA5Iter_native {f s : List Bool → List Bool} {N : List Bool → ℕ}
    (hf : PolyTimeComputable f) (hs : PolyTimeComputable s)
    (hN : PolyTimeComputable (fun x => List.replicate (N x) true))
    (K : ℕ) (hb : ∀ x j, j ≤ N x →
      (f^[j] (s x)).length ≤ K * ((s x).length + N x + 1) ^ 2) :
    PolyTimeComputable (fun x => f^[N x] (s x)) := by
  obtain ⟨W, entry, exit, a, d, hk, hcall⟩ := clNative_cleanCall hf
  apply clNative_image (clRepeatArgument_native W s N hs hN)
    (clRepeatOutputTM W entry exit hk)
    (13 + 7 * (W.k + 1) + a * (4 * K + 1) ^ d + 4 * K) (2 * d + 3)
  intro x
  let arg := clFields (List.ofFn (clRepeatWords W (s x) (N x)))
  have hslen : (s x).length ≤ arg.length := by
    simpa [arg, clRepeatWords, stateWord] using clFields_width
      (List.ofFn (clRepeatWords W (s x) (N x))) (s x)
      (List.mem_ofFn.mpr ⟨Fin.castAdd 1 ⟨0, hk⟩, by simp only [clRepeatWords, Fin.addCases_left, stateWord, Fin.val_mk, if_pos rfl, if_pos True.intro]⟩)
  have hnlen : N x ≤ arg.length := by
    simpa [arg, clRepeatWords, -Fin.natAdd_eq_addNat] using clFields_width
      (List.ofFn (clRepeatWords W (s x) (N x))) (List.replicate (N x) true)
      (List.mem_ofFn.mpr ⟨Fin.natAdd W.k (0 : Fin 1), by simp [clRepeatWords]⟩)
  have horbit : ∀ j ≤ N x, (f^[j] (s x)).length ≤ 4 * K * (arg.length + 1) ^ 2 := by
    intro j hj
    calc
      _ ≤ K * ((s x).length + N x + 1) ^ 2 := hb x j hj
      _ ≤ K * (2 * (arg.length + 1)) ^ 2 := Nat.mul_le_mul_left K
        (Nat.pow_le_pow_left (by omega) 2)
      _ = _ := by ring
  have h := clRepeatOutput_compute W entry exit hk f a d hcall (s x) (N x)
    (4 * K * (arg.length + 1) ^ 2) horbit
  dsimp only at h
  rw [List.append_nil] at h
  exact h.mono (clRepeat_budget arg.length (N x) (W.k + 1) (4 * K) a d hnlen)

/-- A shrinking native step satisfies the orbit-size condition uniformly,
so repeated sequential projections and tail scans need no random access. -/
private lemma clA5Iter_shrinking {f s : List Bool → List Bool} {N : List Bool → ℕ}
    (hf : PolyTimeComputable f) (hs : PolyTimeComputable s)
    (hN : PolyTimeComputable (fun x => List.replicate (N x) true))
    (hshrink : ∀ w, (f w).length ≤ w.length) :
    PolyTimeComputable (fun x => f^[N x] (s x)) := by
  apply clA5Iter_native hf hs hN 1
  intro x j hj
  clear hj
  have h : (f^[j] (s x)).length ≤ (s x).length := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hshrink _).trans ih
  have hsq : (s x).length + N x + 1 ≤ ((s x).length + N x + 1) ^ 2 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right
      (show 0 < (s x).length + N x + 1 by omega) (show 1 ≤ 2 by omega)
  simp only [one_mul]
  omega

/-- Removing a computed unary number of leading bits is an actual sequence
of native tail calls. Each call is charged even after the word becomes empty. -/
private lemma clA5Drop_native {s u : List Bool → List Bool}
    (hs : PolyTimeComputable s) (hu : PolyTimeComputable u) :
    PolyTimeComputable (fun x => (s x).drop (u x).length) := by
  have h := clA5Iter_shrinking clA5_pt_tail hs ((clNative_fill true).comp hu)
    (fun w => by simp [List.length_tail])
  convert h using 1
  funext x
  symm
  induction (u x).length with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [List.tail_drop]

/-- Both decoded field components are bounded by the complete source word,
including malformed input and an empty default. This is a storage estimate.
**Proof sketch.** Strong induction on input length handles each two-bit
parser prefix; recursive branches consume two bits before the smaller call.
This local induction avoids generating an imported public induction theorem. -/
private lemma clA5Pair_sizes (w : List Bool) :
    (clHeaderField 0 w).length ≤ w.length ∧ (clHeaderTail 1 w).length ≤ w.length := by
  have haux : ∀ n, ∀ w : List Bool, w.length = n → ∀ a b,
      pairDecode w = some (a, b) → a.length + b.length ≤ w.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn a b he
      cases w with
      | nil => simp [pairDecode] at he
      | cons c w =>
        cases w with
        | nil => cases c <;> simp [pairDecode] at he
        | cons d rest =>
          have hsmall : rest.length < n := by simp only [List.length_cons] at hn; omega
          have ihrest := ih rest.length hsmall rest rfl
          cases c <;> cases d
          · cases hd : pairDecode rest with
            | none => simp [pairDecode, hd] at he
            | some p =>
              have hp := ihrest p.1 p.2 hd
              simp only [pairDecode, hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
              rcases he with ⟨rfl, rfl⟩
              simp only [List.length_cons]
              omega
          · simp only [pairDecode, Option.some.injEq, Prod.mk.injEq] at he
            rcases he with ⟨rfl, rfl⟩
            simp only [List.length_nil, List.length_cons, zero_add]
            omega
          · simp [pairDecode] at he
          · cases hd : pairDecode rest with
            | none => simp [pairDecode, hd] at he
            | some p =>
              have hp := ihrest p.1 p.2 hd
              simp only [pairDecode, hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
              rcases he with ⟨rfl, rfl⟩
              simp only [List.length_cons]
              omega
  have h (w : List Bool) := haux w.length w rfl
  cases hd : pairDecode w with
  | none => simp [clHeaderField, clHeaderTail, hd]
  | some p =>
    have hp := h w p.1 p.2 hd
    simp only [clHeaderField, clHeaderTail, hd, Option.map_some, Option.getD_some]
    omega

/-- Variable field access is a genuine unary-counted sequence of the native
pair-tail projection, followed by the native pair-first projection. -/
private lemma clA5Field_native {s u : List Bool → List Bool}
    (hs : PolyTimeComputable s) (hu : PolyTimeComputable u) :
    PolyTimeComputable (fun x => clHeaderField (u x).length (s x)) := by
  have h := clA5Iter_shrinking (clHeaderTail_native 1) hs
    ((clNative_fill true).comp hu) (fun w => (clA5Pair_sizes w).2)
  have hi (j : ℕ) (w : List Bool) : (clHeaderTail 1)^[j] w = clHeaderTail j w := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
  convert (clHeaderField_native 0).comp h using 1
  funext x
  rw [Function.comp_apply, hi]
  rfl
/-- Fixed multiplication of a native unary value is a fixed number of
native concatenations, so its coefficient belongs to finite control. -/
private lemma clA5Times_native {f : List Bool → ℕ}
    (hf : PolyTimeComputable (fun x => List.replicate (f x) true)) (k : ℕ) :
    PolyTimeComputable (fun x => List.replicate (k * f x) true) := by
  induction k with
  | zero => simpa using clA5_pt_const []
  | succ k ih =>
    simpa only [Nat.succ_mul, List.replicate_add] using clNative_append ih hf

/-- Unary comparison is charged subtraction followed by the actual finite
empty-word test; no numeric oracle enters the transition table. -/
private lemma clA5Le_native {f g : List Bool → ℕ}
    (hf : PolyTimeComputable (fun x => List.replicate (f x) true))
    (hg : PolyTimeComputable (fun x => List.replicate (g x) true)) :
    PolyTimeComputable (fun x => [decide (f x ≤ g x)]) := by
  have h := clA5_pt_eq (clA5Drop_native hf hg) []
  simpa only [List.length_replicate, List.drop_replicate, List.replicate_eq_nil_iff,
    Nat.sub_eq_zero_iff_le] using h

/-- A fixed finite template is serialized natively whenever each of its
finitely many unary wire indices is native. The variable-index cost is
included for every literal occurrence.
**Proof sketch.** For each fixed literal concatenate its native unary index,
the extra true bit, its run terminator and fixed polarity. Finite concatenation
builds each clause with its final false and the group with each true marker.
The sole formula terminator is deliberately absent from this fragment. -/
private lemma clA5Template_native (φ : Std.Sat.CNF ℕ) (wire : List Bool → ℕ → ℕ)
    (hw : ∀ j, PolyTimeComputable (fun x => List.replicate (wire x j) true)) :
    PolyTimeComputable (fun x => clFragment (φ.relabel (wire x))) := by
  have hl (l : Std.Sat.Literal ℕ) : PolyTimeComputable
      (fun x => Std.Sat.CNF.serializeLit (wire x l.1, l.2)) := by
    simpa only [Std.Sat.CNF.serializeLit, List.replicate_add, List.replicate_one,
      List.append_assoc, List.singleton_append] using
      clNative_append (hw l.1) (clA5_pt_const [true, false, l.2])
  have hc (cs : Std.Sat.CNF.Clause ℕ) : PolyTimeComputable
      (fun x => Std.Sat.CNF.serializeClause (cs.map (fun l => (wire x l.1, l.2)))) := by
    induction cs with
    | nil => simpa [Std.Sat.CNF.serializeClause] using clA5_pt_const [false]
    | cons l cs ih =>
      simpa [Std.Sat.CNF.serializeClause, List.append_assoc] using clNative_append (hl l) ih
  induction φ with
  | nil => simpa [Std.Sat.CNF.relabel, clFragment] using clA5_pt_const []
  | cons cs φ ih =>
    have h := clNative_append (clNative_append (clA5_pt_const [true]) (hc cs)) ih
    simpa [Std.Sat.CNF.relabel, clFragment, List.append_assoc] using h

/-- A packed variable's unary address is obtained by native addition and
fixed multiplication of the unary snapshot index. -/
private lemma clA5Address_native (B j : ℕ) {m t : List Bool → ℕ}
    (hm : PolyTimeComputable (fun x => List.replicate (m x) true))
    (ht : PolyTimeComputable (fun x => List.replicate (t x) true)) :
    PolyTimeComputable (fun x => List.replicate (clPack (m x) B (t x) j) true) := by
  simpa only [clPack, Nat.mul_comm B, List.replicate_add] using
    clNative_append (clNative_append hm (clA5Times_native ht B)) (clA5_pt_const (List.replicate j true))

/-- The protected Claim-2.13 table for one kind is compiled once for the
fixed machine. Only the already named unary wiring changes with input. -/
private lemma clA5Group_native (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (kind : CLTemplateKind M.k) {m s t p : List Bool → ℕ}
    (hm : PolyTimeComputable (fun x => List.replicate (m x) true))
    (hs : PolyTimeComputable (fun x => List.replicate (s x) true))
    (ht : PolyTimeComputable (fun x => List.replicate (t x) true))
    (hp : PolyTimeComputable (fun x => List.replicate (p x) true)) :
    PolyTimeComputable (fun x => clFragment (clGroup M code kind (m x) (s x) (t x) (p x))) := by
  apply clA5Template_native
  intro j
  by_cases h1 : j < clWidth M code
  · simpa only [clWire, if_pos h1] using clA5Address_native (clWidth M code) j hm hs
  · by_cases h2 : j < 2 * clWidth M code
    · simpa only [clWire, if_neg h1, if_pos h2] using
        clA5Address_native (clWidth M code) (j - clWidth M code) hm ht
    · simpa only [clWire, if_neg h1, if_neg h2] using hp

/-- Length-derived fields of the exact stored header, selected by native
projections of the persistent packed word. -/
private def clA5StoredHeader (z : List Bool) : List Bool := clHeaderField 0 (clHeaderTail 1 z)

/-- The retained original instance is recovered from the header verbatim. -/
private def clA5Instance (z : List Bool) : List Bool := clHeaderField 0 (clA5StoredHeader z)

/-- Exact stored last-round index. Header field five is the unary horizon;
its length is a value, not an unproved binary-to-unary conversion. -/
private def clA5StoredRound (M : FinTM Bool) (z : List Bool) : ℕ :=
  clLastRound (clA5Instance z).length M.k (clHeaderTail 5 (clA5StoredHeader z)).length

/-- All stored header projections agree with the unchanged producer word. -/
private lemma clA5Stored_exact (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool) (i : ℕ) :
    clA5Instance (clA5Pack M C e c A d x i) = x ∧
    clA5StoredRound M (clA5Pack M C e c A d x i) =
      clLastRound x.length M.k (clProducerHorizon C e c A d x.length) := by
  simp only [clA5Instance, clA5StoredHeader, clA5StoredRound, clA5Pack,
    clHeaderField, clHeaderTail, clPackedRecords, clPrepHeader, pairDecode_pairEncode,
    Option.map_some, Option.getD_some, List.length_replicate, clProducerHorizon]
  trivial

/-- The exact unary last-round index is computed from the retained instance
and unary horizon. Every projection and fixed repetition has a native ledger. -/
private lemma clA5StoredRound_native (M : FinTM Bool) :
    PolyTimeComputable (fun z => List.replicate (clA5StoredRound M z) true) := by
  have hh : PolyTimeComputable clA5StoredHeader :=
    (clHeaderField_native 0).comp (clHeaderTail_native 1)
  have hx := (clNative_fill true).comp ((clHeaderField_native 0).comp hh)
  have ht := (clNative_fill true).comp ((clHeaderTail_native 5).comp hh)
  have h := clNative_append (clNative_append hx (clA5Times_native ht (M.k + 3)))
    (clA5_pt_const (List.replicate (M.k + 1) true))
  simpa only [clA5StoredRound, clLastRound, clA5Instance, ← Nat.add_assoc,
    List.replicate_add, Function.comp_def, List.append_assoc] using h

/-- Cursor update leaves the complete protected producer answer unchanged.
At and beyond the saturated cursor it is stationary. -/
private def clA5Next (M : FinTM Bool) (z : List Bool) : List Bool :=
  let u := clHeaderField 0 z
  pairEncode (if u.length ≤ clA5StoredRound M z then u ++ [true] else u)
    (clHeaderTail 1 z)

/-- Saturating cursor update is an actual native word computation. -/
private lemma clA5Next_native (M : FinTM Bool) : PolyTimeComputable (clA5Next M) := by
  have hu := clHeaderField_native 0
  have hp := clA5Le_native ((clNative_fill true).comp hu) (clA5StoredRound_native M)
  have hc := clA5_pt_cond hp
    (clNative_append hu (clA5_pt_const [true])) hu
  simpa only [clA5Next, decide_eq_true_eq] using clNative_pair hc (clHeaderTail_native 1)

/-- The real native cursor word implements exactly the inherited bounded
cursor orbit, including the positive silent round's stationary update. -/
private lemma clA5Next_pack (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool) (i : ℕ)
    (hi : i ≤ clLastRound x.length M.k (clProducerHorizon C e c A d x.length) + 1) :
    clA5Next M (clA5Pack M C e c A d x i) =
      clA5Pack M C e c A d x
        (min (i + 1) (clLastRound x.length M.k (clProducerHorizon C e c A d x.length) + 1)) := by
  have hr := (clA5Stored_exact M C e c A d x i).2
  simp only [clA5Next, hr]
  simp only [clA5Pack, clHeaderField, clHeaderTail, pairDecode_pairEncode,
    Option.map_some, Option.getD_some, List.length_replicate]
  split_ifs with h
  · rw [Nat.min_eq_left (by omega), List.replicate_add, List.replicate_one]
  · have he : i = clLastRound x.length M.k (clProducerHorizon C e c A d x.length) + 1 := by omega
    rw [Nat.min_eq_right (by omega), ← he]

/-- Exact fuel and its numerical polynomial bound come from an actual unary
producer followed by the native binary length machine. The fuel is the last
round index, so the forwarding loop executes exactly one more family member. -/
private lemma clA5Fuel (M : FinTM Bool) (C e c A d : ℕ) :
    PolyBound (fun n => clLastRound n M.k (clProducerHorizon C e c A d n)) ∧
    PolyTimeComputable (fun x => Nat.bits
      (clLastRound x.length M.k (clProducerHorizon C e c A d x.length))) := by
  have hp : PolyTimeComputable (fun x => clA5Pack M C e c A d x 0) :=
    (clNative_linear _ (FinTM.computesFunInTime_pairEncodeFixed [])).comp
      (clPackedRecords_native M C e c A d)
  have hu : PolyTimeComputable (fun x => List.replicate
      (clLastRound x.length M.k (clProducerHorizon C e c A d x.length)) true) := by
    convert (clA5StoredRound_native M).comp hp using 1
    funext x
    rw [Function.comp_apply, (clA5Stored_exact M C e c A d x 0).2]
  constructor
  · obtain ⟨F, a, r, hF⟩ := hu
    refine ⟨a, r, fun n => ?_⟩
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF (List.replicate n false))).2
    have hb := F.tm.output_length_le (List.replicate n false) (a * (n + 1) ^ r)
    simp only [List.length_replicate] at ho hb
    rw [ho] at hb
    simpa using hb
  · simpa only [Function.comp_def, List.length_replicate] using
      (clNative_linear _ FinTM.computesFunInTime_lengthBits).comp hu
/-- Two native clean modules form a positive first-return round. Emission
preserves the protected word; cursor installation preserves the emitted prefix.
This also covers an empty chunk and a stationary saturated cursor.
**Proof sketch.** Dispatch once from the fresh anchor, forward the complete
first-halting emit call, then forward the complete install call. All earlier
states remain in their tagged module summands, and the full endpoint of each
call restores every scratch tape and head. -/
private lemma clA5Round (S J E I : FinTM Bool) (emit next : List Bool → List Bool)
    (BE BI : ℕ → ℕ) (hE : CLA5Clean E id emit BE) (hI : CLA5Clean I next (fun _ => []) BI)
    (x w : List Bool) :
    let bank := clA5Modules S J E I
    let H := clA5HostTM bank (1 + S.k + J.k + E.k + I.k) (clA5Modules_bound S J E I)
    ∃ t, 0 < t ∧ t ≤ 1 + BE w.length + BI w.length ∧
      (∀ v, 0 < v → v < t → (H.tm.runFrom
        (Cfg.ofWords (input := x) (.inl ()) (stateWord H.k w)) v).state ≠ some (.inl ())) ∧
      H.tm.runFrom (Cfg.ofWords (input := x) (.inl ()) (stateWord H.k w)) t =
        {Cfg.ofWords (.inl ()) (stateWord H.k (next w)) with output := emit w} := by
  dsimp only
  let bank := clA5Modules S J E I
  let K := 1 + S.k + J.k + E.k + I.k
  let H := clA5HostTM bank K (clA5Modules_bound S J E I)
  have dispatch : H.tm.step (Cfg.ofWords (input := x) (.inl ()) (stateWord K w)) =
      Cfg.ofWords (clA5HostEntry bank 3) (stateWord K w) := by
    change (FinTM.controlAction 0 (some (clA5HostEntry bank 3))).apply _ = _
    simp [FinTM.controlAction, Action.apply, Cfg.ofWords]
    exact ⟨rfl, rfl⟩
  obtain ⟨te, hep, heb, heg, he⟩ := clA5Host_clean bank K (clA5Modules_bound S J E I) 3
    id emit BE (by simpa [bank, clA5Modules] using hE) x w []
  change H.tm.runFrom (Cfg.ofWords (input := x) (clA5HostEntry bank 3) (stateWord K w)) te =
    {Cfg.ofWords (clA5HostEntry bank 4) (stateWord K w) with output := emit w} at he
  obtain ⟨ti, hip, hib, hig, hi⟩ := clA5Host_clean bank K (clA5Modules_bound S J E I) 4
    next (fun _ => []) BI (by simpa [bank, clA5Modules] using hI) x w (emit w)
  change H.tm.runFrom
    {Cfg.ofWords (input := x) (clA5HostEntry bank 4) (stateWord K w) with output := emit w} ti =
    {Cfg.ofWords (.inl ()) (stateWord K (next w)) with output := emit w ++ []} at hi
  rw [List.append_nil] at hi
  have guard := clA5_guard_add H.tm (.inl ()) _ _ te ti heg he hig
  refine ⟨(te + ti) + 1, by omega, by omega, ?_, ?_⟩
  · intro v hv hvt
    change (H.tm.runFrom (Cfg.ofWords (input := x) (.inl ()) (stateWord K w)) v).state ≠ _
    rw [show v = (v - 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step, dispatch]
    exact guard (v - 1) (by omega)
  · change H.tm.runFrom (Cfg.ofWords (input := x) (.inl ()) (stateWord K w)) ((te + ti) + 1) = _
    rw [MultiTapeTM.runFrom_succ_eq_step, dispatch, MultiTapeTM.runFrom_add, he, hi]
    rfl

/-- Addition of numerical polynomial bounds, without any computability
claim about the bound itself. -/
private lemma clA5Poly_add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n + g n) := by
  obtain ⟨a, d, ha⟩ := hf
  obtain ⟨b, e, hb⟩ := hg
  refine ⟨a + b, d + e, fun n => ?_⟩
  have hd := Nat.mul_le_mul_left a (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + e by omega))
  have he := Nat.mul_le_mul_left b (Nat.pow_le_pow_right (Nat.succ_pos n) (show e ≤ d + e by omega))
  rw [Nat.add_mul]
  exact Nat.add_le_add ((ha n).trans hd) ((hb n).trans he)

/-- Evaluating a monomial at a bounded state-word size preserves a numerical
polynomial bound. It does not turn a size estimate into a machine clock. -/
private lemma clA5Poly_call {f : ℕ → ℕ} (hf : PolyBound f) (a d : ℕ) :
    PolyBound (fun n => a * (f n + 1) ^ d) := by
  obtain ⟨b, e, hb⟩ := hf
  refine ⟨a * (b + 1) ^ d, e * d, fun n => ?_⟩
  have h1 : 1 ≤ (n + 1) ^ e := Nat.one_le_pow e _ (by omega)
  have h : f n + 1 ≤ (b + 1) * (n + 1) ^ e := by rw [Nat.add_mul, Nat.one_mul]; have := hb n; omega
  calc
    _ ≤ a * ((b + 1) * (n + 1) ^ e) ^ d := Nat.mul_le_mul_left a (Nat.pow_le_pow_left h d)
    _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul]; ring

/-- The bounded cursor and the complete producer word together have a
polynomial storage bound in the original input length. -/
private lemma clA5Pack_bound (M : FinTM Bool) (C e c A d : ℕ) :
    ∃ W : ℕ → ℕ, PolyBound W ∧ ∀ x i,
      i ≤ clLastRound x.length M.k (clProducerHorizon C e c A d x.length) + 1 →
      (clA5Pack M C e c A d x i).length ≤ W x.length := by
  obtain ⟨_, a, r, _, hlen⟩ := clPackedRecords_machine M C e c A d
  let R := fun n => clLastRound n M.k (clProducerHorizon C e c A d n)
  have hR : PolyBound R := (clA5Fuel M C e c A d).1
  refine ⟨fun n => 2 * (R n + 1) + (a * (n + 1) ^ r + 2), ?_, ?_⟩
  · exact clA5Poly_add (by simpa only [Nat.pow_one] using clA5Poly_call hR 2 1)
      (clA5Poly_add ⟨a, r, by intro n; rfl⟩ ⟨2, 0, by intro n; simp⟩)
  · intro x i hi
    have hl := hlen x
    have he : (clA5Pack M C e c A d x i).length =
        2 * i + (clPackedRecords M C e c A d x).length + 2 := by
      simp [clA5Pack, pairEncode, List.length_flatMap, Nat.mul_comm] <;> omega
    rw [he]
    change i ≤ R x.length + 1 at hi
    dsimp only
    omega

/-- Reduction of the remaining physical emitter obligation to one explicit
native word function: an exact chunk selector on the stored packed word.
Startup, cursor updates, all clean first returns, saturated silence, exact
fuel, and a single polynomial budget are discharged by this construction.
**Proof sketch.** Install the full producer and cursor, then use clean native
emission and the proved native cursor update in the five-phase host. Bound
all word sizes along the cursor orbit, and sum the separate startup, round
and native fuel ledgers into one common polynomial. The inherited emitter
and chunk identities then identify the physical answer with the serialized
pure tableau. No satisfiability fact enters this word identity. -/
private lemma clA5Output_of_nativeChunk (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e c A d : ℕ)
    (emit : List Bool → List Bool) (hemit : PolyTimeComputable emit)
    (hexact : ∀ x i,
      i ≤ clLastRound x.length M.k (clProducerHorizon C e c A d x.length) + 1 →
      emit (clA5Pack M C e c A d x i) =
        if i ≤ clLastRound x.length M.k (clProducerHorizon C e c A d x.length) then
          clChunk (clLastRound x.length M.k (clProducerHorizon C e c A d x.length))
            (fun j => (clTableauGroups M code C e x (clProducerHorizon C e c A d x.length))[j]?.getD []) i
        else []) :
    PolyTimeComputable (fun x => Std.Sat.CNF.serialize
      (clTableau M code C e x (clProducerHorizon C e c A d x.length))) := by
  obtain ⟨S, J, aS, dS, aJ, dJ, aH, dH, hlen, hstart⟩ := clA5Startup M C e c A d
  obtain ⟨E, aE, dE, hE⟩ := clA5Clean_emit hemit
  obtain ⟨I, aI, dI, hI⟩ := clA5Clean_install (clA5Next_native M)
  obtain ⟨W, hW, hw⟩ := clA5Pack_bound M C e c A d
  obtain ⟨hR, F, aF, dF, hF⟩ := clA5Fuel M C e c A d
  let R := fun n => clLastRound n M.k (clProducerHorizon C e c A d n)
  let start := fun n => 2 * n + 3 + aS * (n + 1) ^ dS + aJ * (aH * (n + 1) ^ dH + 1) ^ dJ
  let round := fun n => 1 + aE * (W n + 1) ^ dE + aI * (W n + 1) ^ dI
  let P := fun n => start n + round n + aF * (n + 1) ^ dF
  have hsPoly : PolyBound start := clA5Poly_add
    (clA5Poly_add ⟨5, 1, by intro n; simp only [Nat.pow_one]; omega⟩
      ⟨aS, dS, by intro n; rfl⟩)
    (clA5Poly_call ⟨aH, dH, by intro n; rfl⟩ aJ dJ)
  have hrPoly : PolyBound round := clA5Poly_add
    (clA5Poly_add ⟨1, 0, by intro n; simp⟩ (clA5Poly_call hW aE dE))
    (clA5Poly_call hW aI dI)
  have hP : PolyBound P := clA5Poly_add (clA5Poly_add hsPoly hrPoly) ⟨aF, dF, by intro n; rfl⟩
  let bank := clA5Modules S J E I
  let H := clA5HostTM bank (1 + S.k + J.k + E.k + I.k) (clA5Modules_bound S J E I)
  have hfuel : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) P := by
    intro x
    exact (hF x).mono (by dsimp [P]; omega)
  have hstart' : ∀ x : List Bool, ∃ t ≤ P x.length,
      (∀ j < t, (H.tm.runFrom (H.tm.initCfg x) j).state ≠ some (.inl ())) ∧
      H.tm.runFrom (H.tm.initCfg x) t =
        Cfg.ofWords (.inl ()) (stateWord H.k (clA5Pack M C e c A d x 0)) := by
    intro x
    obtain ⟨t, ht, hg, he⟩ := hstart E I x
    refine ⟨t, ?_, hg, he⟩
    change t ≤ start x.length at ht
    dsimp only [P]
    omega
  have hround : ∀ x i, i ≤ R x.length + 1 →
      ∃ t, 0 < t ∧ t ≤ P x.length ∧
        (∀ j, 0 < j → j < t → (H.tm.runFrom
          (Cfg.ofWords (input := x) (.inl ()) (stateWord H.k (clA5Pack M C e c A d x i))) j).state ≠ some (.inl ())) ∧
        H.tm.runFrom (Cfg.ofWords (input := x) (.inl ())
          (stateWord H.k (clA5Pack M C e c A d x i))) t =
          {Cfg.ofWords (.inl ()) (stateWord H.k (clA5Next M (clA5Pack M C e c A d x i)))
            with output := emit (clA5Pack M C e c A d x i)} := by
    intro x i hi
    obtain ⟨t, hp, ht, hg, he⟩ := clA5Round S J E I emit (clA5Next M)
      (fun n => aE * (n + 1) ^ dE) (fun n => aI * (n + 1) ^ dI) hE hI x
      (clA5Pack M C e c A d x i)
    have hsize := Nat.add_le_add_right (hw x i hi) 1
    have heB := Nat.mul_le_mul_left aE (Nat.pow_le_pow_left hsize dE)
    have hiB := Nat.mul_le_mul_left aI (Nat.pow_le_pow_left hsize dI)
    refine ⟨t, hp, ?_, hg, he⟩
    change t ≤ 1 + aE * ((clA5Pack M C e c A d x i).length + 1) ^ dE +
      aI * ((clA5Pack M C e c A d x i).length + 1) ^ dI at ht
    dsimp only [P, round]
    omega
  have h := clEmitter_of_body H F (.inl ()) (clA5Pack M C e c A d)
    (fun _ => clA5Next M) (fun _ => emit)
    (fun x j => (clTableauGroups M code C e x (clProducerHorizon C e c A d x.length))[j]?.getD [])
    R P hP hR hfuel (clA5Next_pack M C e c A d) hexact hstart' hround
  convert h using 1
  funext x
  exact (clTableau_chunks M code C e x (clProducerHorizon C e c A d x.length)).symm.trans
    (clChunks_serialize _ _)
/-- Replay the comparator's finite verdict after its native field loader;
the source comparator itself and its signed arithmetic are unchanged. -/
private def clA5CompareTM : FinTM Bool where
  k := (clPreparedTM clCmpTM).k
  State := (clPreparedTM clCmpTM).State
  tm := {
    q₀ := (clPreparedTM clCmpTM).tm.q₀
    tr := fun q inp work => match q with
      | .inr (.inr (.inr b)) => ⟨0, fun _ => (none, 0), some b, none⟩
      | _ => (clPreparedTM clCmpTM).tm.tr q inp work }

/-- Loading, comparing and returning one arithmetic bit is a native linear
computation on the complete encoded four-word argument.
**Proof sketch.** Consume the banked comparator and native loader, then cut
at the first completed verdict. Absorption of either completed source verdict
rules out an earlier different verdict. The replay wrapper follows every
preceding source transition and emits exactly one bit on its halting step. -/
private lemma clA5Compare_compute (w : Fin 4 → List Bool) :
    let arg := clFields (List.ofFn w) ++ []
    clA5CompareTM.ComputesInTime arg
      [decide (clNum (w 0) + clNum (w 1) = clNum (w 2) + clNum (w 3))]
      (35 * (arg.length + 1)) := by
  classical
  dsimp only
  let arg := clFields (List.ofFn w) ++ []
  let A := clPreparedTM clCmpTM
  let b := clCmpVerdict (clCmpOrbit w (clCmpSize w))
  let ret (v : Bool) : A.State := .inr (.inr (.inr v))
  have widths (i : Fin 4) : (w i).length ≤ arg.length := by
    simpa only [arg, List.append_nil] using
      clFields_width (List.ofFn w) (w i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have size : clCmpSize w ≤ arg.length := Finset.sup_le (fun i _ => widths i)
  obtain ⟨a, ha, he⟩ := clPrepared_run clCmpTM w [] arg.length widths (2 * clCmpSize w + 2)
  change a ≤ 2 * arg.length + 4 + clCmpTM.k * (3 * arg.length + 7) at ha
  change A.tm.runFrom (A.tm.initCfg arg) (a + (2 * clCmpSize w + 2)) =
    clPreparedCfg clCmpTM arg (clFields (List.ofFn w)).length
      (clCmpTM.tm.runFrom (Cfg.ofWords (input := arg) clCmpTM.tm.q₀ w) (2 * clCmpSize w + 2)) at he
  have init : Cfg.ofWords (input := arg) clCmpTM.tm.q₀ w =
      clCmpCfg arg 1 (.inl (false, false, true)) w 0 := rfl
  rw [init, clCmp_run] at he
  let result := clPreparedCfg clCmpTM arg (clFields (List.ofFn w)).length (clCmpCfg arg 1 (.inr (.inr b)) w 0)
  have hend : A.tm.runFrom (A.tm.initCfg arg) (a + (2 * clCmpSize w + 2)) = result := he
  have idle (v : Bool) (cfg : Cfg A.k Bool A.State arg) (hc : cfg.state = some (ret v)) :
      A.tm.step cfg = cfg := clPrepared_idle clCmpTM (.inr (.inr v))
        (by intros; rfl) cfg hc
  obtain ⟨t, ht, hp, hf, hr⟩ := clFirst A.tm _ result (ret b)
    (a + (2 * clCmpSize w + 2)) hend rfl (by simp [A, clPreparedTM, seamCompTM, ret]) (idle b)
  have guard : ∀ j < t, ∀ v, (A.tm.runFrom (A.tm.initCfg arg) j).state ≠ some (ret v) := by
    intro j hj v hv
    have stay := Function.iterate_fixed (idle v _ hv) (t - j)
    change A.tm.runFrom (A.tm.runFrom (A.tm.initCfg arg) j) (t - j) =
      A.tm.runFrom (A.tm.initCfg arg) j at stay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le (by omega), hr] at stay
    have hstate := congrArg Cfg.state stay
    change some (ret b) = _ at hstate
    rw [hv] at hstate
    have hb : b = v := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Option.some.inj hstate)))
    exact hf j hj (by rw [hb]; exact hv)
  have actionid (act : Action A.k Bool A.State) : Action.mapState id act = act := by
    delta Action.mapState
    simp only [Option.map_id]
    rfl
  have run := MultiTapeTM.runFrom_mapState_of_agreeOn A.tm clA5CompareTM.tm (Function.Embedding.refl _)
    (fun q => ∀ v, q ≠ ret v) (by
      intro q hq inp work
      change clA5CompareTM.tm.tr q inp work = (A.tm.tr q inp work).mapState id
      cases q with
      | inl q => rw [actionid]; rfl
      | inr q =>
        cases q with
        | inl q => rw [actionid]; rfl
        | inr q =>
          cases q with
          | inl q => rw [actionid]; rfl
          | inr v => exact False.elim (hq v rfl))
    (A.tm.initCfg arg) t (by intro j hj q hq v heq; subst q; exact guard j hj v hq)
  have mapid (cfg : Cfg A.k Bool A.State arg) : cfg.mapState id = cfg := by
    cases cfg
    simp [Cfg.mapState]
  change clA5CompareTM.tm.runFrom ((A.tm.initCfg arg).mapState id) t =
    (A.tm.runFrom (A.tm.initCfg arg) t).mapState id at run
  rw [mapid, hr, mapid] at run
  have hi : A.tm.initCfg arg = clA5CompareTM.tm.initCfg arg := rfl
  rw [hi] at run
  have finish : clA5CompareTM.tm.step result = {result with state := none, output := [b]} := by
    change (Action.mk 0 (fun _ => (none, 0)) (some b) none).apply result = _
    simp [Action.apply, show result.output = [] from rfl]
  have hb : b = decide (clNum (w 0) + clNum (w 1) = clNum (w 2) + clNum (w 3)) := by
    apply Bool.eq_iff_iff.mpr
    simpa using clCmpVerdict_spec w
  have hc : clA5CompareTM.ComputesInTime arg [b] (t + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', run, finish]
    exact ⟨rfl, rfl⟩
  rw [hb] at hc
  apply hc.mono
  change a ≤ 2 * arg.length + 4 + 4 * (3 * arg.length + 7) at ha
  change t + 1 ≤ 35 * (arg.length + 1)
  omega

/-- Native equality of two binary natural-number words, using the actual
banked four-word arithmetic comparator with its other two words empty. -/
private lemma clA5EqNum_native {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => [decide (clNum (f x) = clNum (g x))]) := by
  let w : List Bool → Fin 4 → List Bool := fun x i =>
    if i = 0 then f x else if i = 2 then g x else []
  have hw : PolyTimeComputable (fun x => clFields (List.ofFn (w x))) := by
    have h := clNative_fields [f, (fun _ => []), g, (fun _ => [])]
      (by intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with rfl | rfl | rfl | rfl
          · exact hf
          · exact clA5_pt_const []
          · exact hg
          · exact clA5_pt_const [])
    simpa [w, List.ofFn_succ, List.ofFn_zero] using h
  apply clNative_image hw clA5CompareTM 35 1
  intro x
  simpa [w, clNum, Nat.pow_one] using clA5Compare_compute (w x)
/-- State of bounded binary decoding: retain the target binary word, a
unary candidate, and the most recent successful unary answer. -/
private def clA5DecodeState (w : List Bool) (j : ℕ) : List Bool :=
  pairEncode w (pairEncode (List.replicate j true)
    (if clNum w ≤ j then List.replicate (clNum w) true else []))

/-- One bounded-decoding step compares the next unary candidate's genuine
binary encoding with the retained target and records it only on equality. -/
private def clA5DecodeStep (z : List Bool) : List Bool :=
  let w := clHeaderField 0 z
  let u := clHeaderField 1 z ++ [true]
  pairEncode w (pairEncode u
    (if clNum w = u.length then u else clHeaderTail 2 z))

/-- Every decoding step has a native polynomial implementation. The test
uses the banked arithmetic comparator and the native binary length routine. -/
private lemma clA5DecodeStep_native : PolyTimeComputable clA5DecodeStep := by
  have hu := clNative_append (clHeaderField_native 1) (clA5_pt_const [true])
  have hn := (clNative_linear _ FinTM.computesFunInTime_lengthBits).comp hu
  have he := clA5EqNum_native (clHeaderField_native 0) hn
  simp only [Function.comp_def, clNum_bits] at he
  have hc := clA5_pt_cond he hu (clHeaderTail_native 2)
  simpa only [clA5DecodeStep, decide_eq_true_eq] using
    clNative_pair (clHeaderField_native 0) (clNative_pair hu hc)

/-- The complete word invariant for bounded decoding. No decoded value is
used as a loop clock: the supplied unary budget is the only repetition count. -/
private lemma clA5DecodeStep_state (w : List Bool) (j : ℕ) :
    clA5DecodeStep (clA5DecodeState w j) = clA5DecodeState w (j + 1) := by
  simp only [clA5DecodeStep, clA5DecodeState, clHeaderField, clHeaderTail,
    pairDecode_pairEncode, Option.map_some, Option.getD_some,
    List.length_append, List.length_replicate, List.length_singleton]
  rw [show List.replicate j true ++ [true] = List.replicate (j + 1) true by
    rw [List.replicate_add, List.replicate_one]]
  by_cases he : clNum w = j + 1
  · simp only [he, if_pos, le_refl]
  · rw [if_neg he]
    by_cases hl : clNum w ≤ j
    · rw [if_pos hl, if_pos (by omega)]
    · rw [if_neg hl, if_neg (by omega)]

/-- Initial bounded-decoding state is native and has an empty unary result
also when the binary target is zero. -/
private lemma clA5DecodeState_zero (w : List Bool) :
    clA5DecodeState w 0 = pairEncode w (pairEncode [] []) := by
  simp only [clA5DecodeState, List.replicate_zero]
  by_cases h : clNum w ≤ 0
  · have hz : clNum w = 0 := by omega
    simp [hz]
  · rw [if_neg h]

/-- The actual iteration follows the exact decoding-state word. -/
private lemma clA5Decode_orbit (w : List Bool) (j : ℕ) :
    clA5DecodeStep^[j] (clA5DecodeState w 0) = clA5DecodeState w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, clA5DecodeStep_state]

/-- Candidate and answer storage grow only with the supplied unary clock,
even for a malformed binary target denoting a huge natural number. -/
private lemma clA5Decode_size (w : List Bool) (j : ℕ) :
    (clA5DecodeState w j).length ≤ 2 * w.length + 3 * j + 4 := by
  have pairlen (a b : List Bool) : (pairEncode a b).length = 2 * a.length + b.length + 2 := by
    simp [pairEncode, List.length_flatMap, Nat.mul_comm] <;> omega
  simp only [clA5DecodeState, pairlen, List.length_replicate]
  split_ifs with h
  · simp only [List.length_replicate]; omega
  · simp only [List.length_nil]; omega

/-- Decode a binary value only up to a separately supplied native unary
bound. Out-of-range values return the empty word, so all malformed requests
still have the proved polynomial cost.
**Proof sketch.** Iterate the native candidate-comparison step under the
inherited real unary loop. Its exact word invariant proves the answer, and
its linear orbit-size bound discharges the loop's quadratic storage premise.
Project the final answer only after every call and final replay is charged. -/
private lemma clA5Decode_native {f : List Bool → List Bool} {N : List Bool → ℕ}
    (hf : PolyTimeComputable f)
    (hN : PolyTimeComputable (fun x => List.replicate (N x) true)) :
    PolyTimeComputable (fun x =>
      if clNum (f x) ≤ N x then List.replicate (clNum (f x)) true else []) := by
  have hs : PolyTimeComputable (fun x => clA5DecodeState (f x) 0) := by
    simpa only [clA5DecodeState_zero] using clNative_pair hf (clA5_pt_const (pairEncode [] []))
  have hb : ∀ x j, j ≤ N x →
      (clA5DecodeStep^[j] (clA5DecodeState (f x) 0)).length ≤
        8 * ((clA5DecodeState (f x) 0).length + N x + 1) ^ 2 := by
    intro x j hj
    rw [clA5Decode_orbit]
    have hh := clA5Decode_size (f x) j
    have hlen : (f x).length ≤ (clA5DecodeState (f x) 0).length := by
      rw [clA5DecodeState_zero]
      simp [pairEncode, List.length_flatMap, Nat.mul_comm] <;> omega
    have hsq : (clA5DecodeState (f x) 0).length + N x + 1 ≤
        ((clA5DecodeState (f x) 0).length + N x + 1) ^ 2 := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right
        (show 0 < (clA5DecodeState (f x) 0).length + N x + 1 by omega) (show 1 ≤ 2 by omega)
    omega
  have h := clA5Iter_native clA5DecodeStep_native hs hN 8 hb
  convert (clHeaderTail_native 2).comp h using 1
  funext x
  rw [Function.comp_apply, clA5Decode_orbit]
  simp only [clA5DecodeState, clHeaderTail, pairDecode_pairEncode, Option.map_some, Option.getD_some]
/-- Sequential header-tail passes compose by adding their actual field counts. -/
private lemma clA5Tail_add (a b : ℕ) (w : List Bool) :
    clHeaderTail (a + b) w = clHeaderTail b (clHeaderTail a w) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change ((pairDecode (clHeaderTail (a + b) w)).map Prod.snd).getD [] = _
    rw [ih]
    rfl

/-- Removing a whole encoded prefix leaves its literal suffix. -/
private lemma clA5Tail_fields (ws : List (List Bool)) (tail : List Bool) :
    clHeaderTail ws.length (clFields ws ++ tail) = tail := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.length_cons, Nat.add_comm ws.length 1, clA5Tail_add]
    simpa only [clFields, clPair_append, clHeaderTail, pairDecode_pairEncode,
      Option.map_some, Option.getD_some] using ih

/-- A legal field is recovered bit for bit from the encoded prefix,
regardless of the suffix after the field list. -/
private lemma clA5Field_fields (ws : List (List Bool)) (tail : List Bool) (i : ℕ) (hi : i < ws.length) :
    clHeaderField i (clFields ws ++ tail) = ws[i] := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero => simp [clHeaderField, clHeaderTail, clFields, clPair_append, pairDecode_pairEncode]
    | succ i =>
      have hj : i < ws.length := by simpa using hi
      change ((pairDecode (clHeaderTail (i + 1) (clFields (w :: ws) ++ tail))).map Prod.fst).getD [] = ws[i]
      rw [Nat.add_comm i 1, clA5Tail_add]
      simp only [clFields, clPair_append, clHeaderTail, pairDecode_pairEncode,
        Option.map_some, Option.getD_some]
      exact ih i hj

/-- The exact number of fields in a stored row prefix is its row count
multiplied by the fixed row width. -/
private lemma clA5Tail_rows {l : ℕ} (row : ℕ → Fin l → List Bool) (n : ℕ) (tail : List Bool) :
    clHeaderTail (n * l) (clRows row n ++ tail) = tail := by
  induction n generalizing tail with
  | zero => simp [clHeaderTail, clRows]
  | succ n ih =>
    rw [Nat.succ_mul, clA5Tail_add, clRows, List.append_assoc, ih]
    simpa only [List.length_ofFn] using clA5Tail_fields (List.ofFn (row n)) tail

/-- Field lookup in either protected table has its literal stored value.
The native lookup implementing this equation is `clA5Field_native`. -/
private lemma clA5Field_rows {l : ℕ} (row : ℕ → Fin l → List Bool) (N t : ℕ)
    (ht : t < N) (i : Fin l) :
    clHeaderField (t * l + i.val) (clRows row N) = row t i := by
  obtain ⟨rest, he⟩ := clRows_split row N t ht []
  simp only [List.append_nil] at he
  unfold clHeaderField
  rw [he, List.append_assoc, clA5Tail_add, clA5Tail_rows]
  have h := clA5Field_fields (List.ofFn (row t)) rest i.val (by simpa using i.isLt)
  simpa [clHeaderField] using h

/-- The completed visit-table format is the same sequential fixed-width-row
format as the native field reader consumes, including time zero. -/
private lemma clA5Visits_rows (M : FinTM Bool) (C e : ℕ) (x : List Bool) (N : ℕ) :
    clVisitRows M C e x N = clRows (fun t (τ : Fin M.k) =>
      clVisitCode (prevVisit M (x.length + C * (x.length + 1) ^ e) t τ)) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [clVisitRows, ih, clVisitRow_exact, clRows]

/-- Unary source input length retained literally by the producer. -/
private def clA5InputSize (z : List Bool) : ℕ := (clHeaderField 4 (clA5StoredHeader z)).length

/-- Unary source horizon retained literally by the producer. -/
private def clA5Horizon (z : List Bool) : ℕ := (clHeaderTail 5 (clA5StoredHeader z)).length

/-- Exact stored trajectory, reached by fixed native projections. -/
private def clA5Trajectory (z : List Bool) : List Bool := clHeaderField 1 (clHeaderTail 1 z)

/-- Exact stored inclusive visit table, reached by fixed native projections. -/
private def clA5Visits (z : List Bool) : List Bool := clHeaderTail 3 z

/-- Stored bound and table projections on every legal cursor state. -/
private lemma clA5Data_exact (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool) (i : ℕ) :
    let z := clA5Pack M C e c A d x i
    let m := x.length + C * (x.length + 1) ^ e
    let T := clProducerHorizon C e c A d x.length
    clA5InputSize z = m ∧ clA5Horizon z = T ∧
      clA5Trajectory z = clRecords M (List.replicate m false) (T + 1) ∧
      clA5Visits z = clVisitRows M C e x (T + 1) := by
  simp only [clA5InputSize, clA5Horizon, clA5Trajectory, clA5Visits, clA5StoredHeader,
    clA5Pack, clPackedRecords, clPrepHeader, clHeaderField, clHeaderTail,
    pairDecode_pairEncode, Option.map_some, Option.getD_some, List.length_replicate, clProducerHorizon]
  trivial

/-- The retained input length and horizon are native unary values. -/
private lemma clA5Sizes_native :
    PolyTimeComputable (fun z => List.replicate (clA5InputSize z) true) ∧
    PolyTimeComputable (fun z => List.replicate (clA5Horizon z) true) := by
  have hh : PolyTimeComputable clA5StoredHeader :=
    (clHeaderField_native 0).comp (clHeaderTail_native 1)
  exact ⟨(clNative_fill true).comp ((clHeaderField_native 4).comp hh),
    (clNative_fill true).comp ((clHeaderTail_native 5).comp hh)⟩

/-- Bounded numeric interpretation, total also on malformed requests. -/
private def clA5SmallNum (w : List Bool) (N : ℕ) : ℕ := if clNum w ≤ N then clNum w else 0

/-- Bounded binary interpretation has the actual unary native implementation. -/
private lemma clA5SmallNum_native {f : List Bool → List Bool} {N : List Bool → ℕ}
    (hf : PolyTimeComputable f) (hN : PolyTimeComputable (fun x => List.replicate (N x) true)) :
    PolyTimeComputable (fun x => List.replicate (clA5SmallNum (f x) (N x)) true) := by
  convert clA5Decode_native hf hN using 1
  funext x
  by_cases h : clNum (f x) ≤ N x <;> simp [clA5SmallNum, h]

/-- One movement-count word read from the actual chronological trajectory. -/
private def clA5Count (M : FinTM Bool) (i : Fin (clRecFields M)) (z : List Bool) (t : ℕ) : ℕ :=
  clA5SmallNum (clHeaderField (t * clRecFields M + i.val) (clA5Trajectory z)) (clA5Horizon z)

/-- Native sequential access and bounded decoding of a selected count.
All projections, clock construction, repeated field scans and decoding calls
are charged by the native polynomial composition and repetition lemmas. -/
private lemma clA5Count_native (M : FinTM Bool) (i : Fin (clRecFields M))
    {t : List Bool → ℕ} (ht : PolyTimeComputable (fun z => List.replicate (t z) true)) :
    PolyTimeComputable (fun z => List.replicate (clA5Count M i z (t z)) true) := by
  have hi : PolyTimeComputable (fun z => List.replicate (t z * clRecFields M + i.val) true) := by
    simpa only [Nat.mul_comm (clRecFields M), List.replicate_add] using
      clNative_append (clA5Times_native ht (clRecFields M)) (clA5_pt_const (List.replicate i.val true))
  have hfields := clA5Field_native ((clHeaderField_native 1).comp (clHeaderTail_native 1)) hi
  simp only [List.length_replicate] at hfields
  exact clA5SmallNum_native hfields clA5Sizes_native.2

/-- The bounded native count access recovers the exact banked movement
count for every included source time. The bound never truncates valid data. -/
private lemma clA5Count_exact (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool)
    (j t : ℕ) (ht : t ≤ clProducerHorizon C e c A d x.length) (i : Fin (clRecFields M)) :
    clA5Count M i (clA5Pack M C e c A d x j) t =
      clCounts M (List.replicate (x.length + C * (x.length + 1) ^ e) false) t i := by
  obtain ⟨_, hT, hr, _⟩ := clA5Data_exact M C e c A d x j
  unfold clA5Count
  rw [hT, hr, ← clRows_records, clA5Field_rows _ _ t (by omega), clA5SmallNum, clNum_bits]
  rw [if_pos ((clCounts_bound M _ t i).trans ht)]

/-- Unary native addition is literal concatenation. -/
private lemma clA5Add_native {f g : List Bool → ℕ}
    (hf : PolyTimeComputable (fun x => List.replicate (f x) true))
    (hg : PolyTimeComputable (fun x => List.replicate (g x) true)) :
    PolyTimeComputable (fun x => List.replicate (f x + g x) true) := by
  simpa only [List.replicate_add] using clNative_append hf hg

/-- Unary native subtraction is the charged repeated-tail operation. -/
private lemma clA5Sub_native {f g : List Bool → ℕ}
    (hf : PolyTimeComputable (fun x => List.replicate (f x) true))
    (hg : PolyTimeComputable (fun x => List.replicate (g x) true)) :
    PolyTimeComputable (fun x => List.replicate (f x - g x) true) := by
  simpa only [List.length_replicate, List.drop_replicate] using clA5Drop_native hf hg

/-- Shifted input position recovered from its two stored movement counts.
Addition precedes natural subtraction, so the left boundary remains zero. -/
private def clA5InputPos (M : FinTM Bool) (z : List Bool) (t : ℕ) : ℕ :=
  clA5Count M (Fin.castAdd (1 + M.k) (Fin.castAdd M.k (0 : Fin 1))) z t + 1 -
    clA5Count M (Fin.natAdd (1 + M.k) (Fin.castAdd M.k (0 : Fin 1))) z t

/-- Actual native implementation of the shifted stored input position. -/
private lemma clA5InputPos_native (M : FinTM Bool) {t : List Bool → ℕ}
    (ht : PolyTimeComputable (fun z => List.replicate (t z) true)) :
    PolyTimeComputable (fun z => List.replicate (clA5InputPos M z (t z)) true) :=
  clA5Sub_native (clA5Add_native (clA5Count_native M _ ht) (clA5_pt_const [true]))
    (clA5Count_native M _ ht)

/-- Stored signed coordinates recover the exact public input schedule. -/
private lemma clA5InputPos_exact (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool)
    (j t : ℕ) (ht : t ≤ clProducerHorizon C e c A d x.length) :
    clA5InputPos M (clA5Pack M C e c A d x j) t =
      inputPosAt M (x.length + C * (x.length + 1) ^ e) t := by
  unfold clA5InputPos
  rw [clA5Count_exact M C e c A d x j t ht, clA5Count_exact M C e c A d x j t ht]
  have h := (clCounts_schedule M (x.length + C * (x.length + 1) ^ e) t).1
  unfold clSigned at h
  omega

/-- One exact stored visit code, including its explicit presence marker. -/
private def clA5Visit (M : FinTM Bool) (τ : Fin M.k) (z : List Bool) (t : ℕ) : List Bool :=
  clHeaderField (t * M.k + τ.val) (clA5Visits z)

/-- The visit code is read by the charged sequential field reader. -/
private lemma clA5Visit_native (M : FinTM Bool) (τ : Fin M.k) {t : List Bool → ℕ}
    (ht : PolyTimeComputable (fun z => List.replicate (t z) true)) :
    PolyTimeComputable (fun z => clA5Visit M τ z (t z)) := by
  have hi := clA5Add_native (clA5Times_native ht M.k)
    (clA5_pt_const (List.replicate τ.val true))
  have h := clA5Field_native (clHeaderTail_native 3) hi
  simpa only [List.length_replicate, Nat.mul_comm M.k] using h

/-- Every inclusive visit-table row is read exactly, without rerunning the
reference machine or replacing the protected table. -/
private lemma clA5Visit_exact (M : FinTM Bool) (C e c A d : ℕ) (x : List Bool)
    (j t : ℕ) (ht : t ≤ clProducerHorizon C e c A d x.length) (τ : Fin M.k) :
    clA5Visit M τ (clA5Pack M C e c A d x j) t =
      clVisitCode (prevVisit M (x.length + C * (x.length + 1) ^ e) t τ) := by
  unfold clA5Visit
  rw [(clA5Data_exact M C e c A d x j).2.2.2, clA5Visits_rows]
  exact clA5Field_rows _ _ t (by omega) τ

/-- Native stored-coordinate input template fragment. -/
private noncomputable def clA5InputFragment (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (z : List Bool) (t : ℕ) : List Bool :=
  let p := clA5InputPos M z t
  if 0 < p ∧ p ≤ clA5InputSize z then
    clFragment (clGroup M code (CLTemplateKind.input true) (clA5InputSize z) 0 t (p - 1))
  else clFragment (clGroup M code (CLTemplateKind.input false) (clA5InputSize z) 0 t 0)

/-- Both input-template choices are finite protected tables; the native
branch predicate and the shifted variable address are charged. -/
private lemma clA5InputFragment_native (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    {t : List Bool → ℕ} (ht : PolyTimeComputable (fun z => List.replicate (t z) true)) :
    PolyTimeComputable (fun z => clA5InputFragment M code z (t z)) := by
  have hp := clA5InputPos_native M ht
  have hz := clA5_pt_const (List.replicate 0 true)
  have hb := clA5_pt_and (clA5Le_native (clA5_pt_const (List.replicate 1 true)) hp)
    (clA5Le_native hp clA5Sizes_native.1)
  have hy := clA5Group_native M code (CLTemplateKind.input true) clA5Sizes_native.1 hz ht
    (clA5Sub_native hp (clA5_pt_const (List.replicate 1 true)))
  have hn := clA5Group_native M code (CLTemplateKind.input false) clA5Sizes_native.1 hz ht hz
  simpa only [clA5InputFragment, Bool.and_eq_true, Nat.succ_le_iff, decide_eq_true_eq] using
    clA5_pt_cond hb hy hn

/-- Input fragments use the exact inherited pure group on legal states. -/
private lemma clA5InputFragment_exact (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (C e c A d : ℕ) (x : List Bool) (j t : ℕ)
    (ht : t ≤ clProducerHorizon C e c A d x.length) :
    clA5InputFragment M code (clA5Pack M C e c A d x j) t =
      clFragment (clInputGroup M code (x.length + C * (x.length + 1) ^ e) t) := by
  unfold clA5InputFragment clInputGroup
  rw [clA5InputPos_exact M C e c A d x j t ht, (clA5Data_exact M C e c A d x j).1]
  dsimp only
  split <;> rfl

/-- Native stored-visit work fragment. Empty is absence; a present time
zero has its distinct nonempty marker. The numeric decoder is horizon bounded. -/
private noncomputable def clA5WorkFragment (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (τ : Fin M.k) (z : List Bool) (t : ℕ) : List Bool :=
  let w := clA5Visit M τ z t
  if w = [] then clFragment (clGroup M code (CLTemplateKind.work τ false) (clA5InputSize z) 0 t 0)
  else clFragment (clGroup M code (CLTemplateKind.work τ true) (clA5InputSize z)
    (clA5SmallNum (clHeaderTail 1 w) (clA5Horizon z)) t 0)

/-- Native implementation of either protected work template with its
actual greatest-earlier source address read from the protected visit table. -/
private lemma clA5WorkFragment_native (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (τ : Fin M.k) {t : List Bool → ℕ}
    (ht : PolyTimeComputable (fun z => List.replicate (t z) true)) :
    PolyTimeComputable (fun z => clA5WorkFragment M code τ z (t z)) := by
  have hv := clA5Visit_native M τ ht
  have hz := clA5_pt_const (List.replicate 0 true)
  have hs := clA5SmallNum_native ((clHeaderTail_native 1).comp hv) clA5Sizes_native.2
  simpa [clA5WorkFragment, Function.comp_apply] using clA5_pt_cond (clA5_pt_eq hv [])
    (clA5Group_native M code (CLTemplateKind.work τ false) clA5Sizes_native.1 hz ht hz)
    (clA5Group_native M code (CLTemplateKind.work τ true) clA5Sizes_native.1 hs ht hz)

/-- The stored earlier source is strictly below the target, so bounded
numeric decoding preserves every legitimate visit, including source zero. -/
private lemma clA5WorkFragment_exact (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (C e c A d : ℕ) (x : List Bool) (j t : ℕ)
    (ht : t ≤ clProducerHorizon C e c A d x.length) (τ : Fin M.k) :
    clA5WorkFragment M code τ (clA5Pack M C e c A d x j) t =
      clFragment (clWorkGroup M code (x.length + C * (x.length + 1) ^ e) t τ) := by
  unfold clA5WorkFragment
  rw [clA5Visit_exact M C e c A d x j t ht τ,
    (clA5Data_exact M C e c A d x j).1, (clA5Data_exact M C e c A d x j).2.1]
  unfold clWorkGroup
  cases hv : prevVisit M (x.length + C * (x.length + 1) ^ e) t τ with
  | none => rfl
  | some s =>
    have hs : s ≤ clProducerHorizon C e c A d x.length :=
      Nat.le_trans (Nat.le_of_lt (clPrev_spec M _ t s τ hv).1) ht
    have hne : pairEncode [] s.bits ≠ [] := by simp [pairEncode]
    simp [clVisitCode, hne, clHeaderTail, pairDecode_pairEncode, clA5SmallNum, clNum_bits, hs]

/-- Division by a fixed positive constant uses only finite control: count
a full block before emitting one unary bit. -/
private lemma clA5Div_native {f : List Bool → ℕ}
    (hf : PolyTimeComputable (fun x => List.replicate (f x) true)) (k : ℕ) :
    PolyTimeComputable (fun x => List.replicate (f x / k) true) := by
  cases k with
  | zero => simpa using clA5_pt_const []
  | succ k =>
    let next (q : Fin (k + 1)) (_ : Bool) : Fin (k + 1) :=
      if h : q.val = k then 0 else ⟨q.val + 1, by omega⟩
    let emit (q : Fin (k + 1)) (_ : Bool) : Option Bool := if q.val = k then some true else none
    have he (x : List Bool) (q : Fin (k + 1)) :
        clA5MapWord next emit (fun _ => none) q x =
          List.replicate ((q.val + x.length) / (k + 1)) true := by
      induction x generalizing q with
      | nil => simp [clA5MapWord, Nat.div_eq_of_lt q.isLt]
      | cons b r ih =>
        rw [clA5MapWord, ih]
        by_cases h : q.val = k
        · have ha : q.val + (b :: r).length = (k + 1) + r.length := by simp [h]; omega
          rw [ha]
          simp [emit, next, h, Nat.add_div_left, List.replicate_succ]
        · have ha : q.val + (b :: r).length = q.val + 1 + r.length := by simp; omega
          rw [ha]
          simp [emit, next, h]
    have h := (clA5Map_poly next emit (fun _ => none) 0).comp hf
    convert h using 1
    funext x
    simp [Function.comp_apply, he]

/-- Remainder by a fixed coefficient is native unary subtraction after
the finite-control quotient scan. This includes the zero-coefficient case. -/
private lemma clA5Mod_native {f : List Bool → ℕ}
    (hf : PolyTimeComputable (fun x => List.replicate (f x) true)) (k : ℕ) :
    PolyTimeComputable (fun x => List.replicate (f x % k) true) := by
  have h := clA5Sub_native hf (clA5Times_native (clA5Div_native hf k) k)
  simpa only [Nat.mod_eq_sub_div_mul, Nat.mul_comm k] using h

/-- Finite selection compiles each fixed branch and native unary tests.
No lookup of an unbounded transition table is used. -/
private lemma clA5Select_native (fs : List (List Bool → List Bool))
    (hfs : ∀ f ∈ fs, PolyTimeComputable f) {v : List Bool → ℕ}
    (hv : PolyTimeComputable (fun z => List.replicate (v z) true)) :
    PolyTimeComputable (fun z => (fs[v z]?.getD (fun _ => [])) z) := by
  induction fs generalizing v with
  | nil => simpa using clA5_pt_const []
  | cons f fs ih =>
    have hrest := ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
      (clA5Sub_native hv (clA5_pt_const (List.replicate 1 true)))
    have h := clA5_pt_cond (clA5_pt_eq hv []) (hfs f (by simp)) hrest
    convert h using 1
    funext z
    cases hvz : v z with
    | zero => simp
    | succ n => simp

/-- The work-family list has its prescribed time-then-tape order.
This indexing fact applies also when the tape count is zero (no legal index). -/
private lemma clA5Work_get {α : Type} (k N j : ℕ) (f : ℕ → ℕ → α) (hj : j < k * N) :
    ((List.range N).flatMap (fun t => (List.range k).map (f t)))[j]? =
      some (f (j / k) (j % k)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((List.range N).flatMap (fun t => (List.range k).map (f t))).length = k * N := by
      simp [List.length_flatMap, Nat.mul_comm]
    by_cases h : j < k * N
    · rw [List.getElem?_append_left (by rw [hlen]; exact h)]
      exact ih h
    · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      have hj' : j < k * N + k := by simpa only [Nat.mul_succ] using hj
      have hr : j - k * N < k := by omega
      have hd : j / k = N := Nat.div_eq_of_lt_le
        (by simpa only [Nat.mul_comm N] using (show k * N ≤ j by omega))
        (by simpa only [Nat.mul_comm (N + 1)] using hj)
      have hm : j % k = j - k * N := by rw [Nat.mod_eq_sub_div_mul, hd, Nat.mul_comm]
      simp [List.getElem?_range hr, hd, hm]

/-- Lookup of an arbitrary family in the exact six-family order. Offsets
are successively subtracted; the work quotient and remainder merely name its
fixed time-then-tape ordering. -/
private def clA5GroupAt (n k T : ℕ)
    (pin : ℕ → Std.Sat.CNF ℕ) (initial : Std.Sat.CNF ℕ)
    (state input : ℕ → Std.Sat.CNF ℕ)
    (work : ℕ → ℕ → Std.Sat.CNF ℕ) (accept : ℕ → Std.Sat.CNF ℕ) (i : ℕ) : Std.Sat.CNF ℕ :=
  if i < n then pin i else
  let j := i - n
  if j = 0 then initial else
  let j := j - 1
  if j < T then state j else
  let j := j - T
  if j < T + 1 then input j else
  let j := j - (T + 1)
  if j < k * (T + 1) then work (j / k) (j % k) else
  let j := j - k * (T + 1)
  if j < T then accept j else []

/-- The controller selector is exactly list lookup in the frozen family
list, including every boundary and the empty default. -/
private lemma clA5GroupAt_exact (n k T : ℕ)
    (pin : ℕ → Std.Sat.CNF ℕ) (initial : Std.Sat.CNF ℕ)
    (state input : ℕ → Std.Sat.CNF ℕ)
    (work : ℕ → ℕ → Std.Sat.CNF ℕ) (accept : ℕ → Std.Sat.CNF ℕ) (i : ℕ) :
    clA5GroupAt n k T pin initial state input work accept i =
      (clGroups n k T pin initial state input work accept)[i]?.getD [] := by
  have rangeGet (f : ℕ → Std.Sat.CNF ℕ) (a j : ℕ) :
      ((List.range a).map f)[j]? = if j < a then some (f j) else none := by
    by_cases h : j < a
    · simp [h, List.getElem?_range h]
    · rw [List.getElem?_eq_none (by simp; omega), if_neg h]
  have hlen : ((List.range (T + 1)).flatMap (fun t => (List.range k).map (work t))).length = k * (T + 1) := by
    simp [List.length_flatMap, Nat.mul_comm]
  unfold clA5GroupAt clGroups
  simp only [List.append_assoc, List.getElem?_append, List.length_map, List.length_range,
    List.length_singleton, hlen]
  by_cases h0 : i < n
  · simp [h0, rangeGet, h0]
  · simp only [h0, ↓reduceIte]
    by_cases h1 : i - n = 0
    · simp [h1]
    · have hn : ¬i - n < 1 := by omega
      simp only [h1, hn, ↓reduceIte]
      by_cases h2 : i - n - 1 < T
      · simp [h2, rangeGet]
      · simp only [h2, ↓reduceIte]
        by_cases h3 : i - n - 1 - T < T + 1
        · simp [h3, rangeGet]
        · simp only [h3, ↓reduceIte]
          by_cases h4 : i - n - 1 - T - (T + 1) < k * (T + 1)
          · rw [if_pos h4, if_pos h4, clA5Work_get _ _ _ _ h4]
            rfl
          · simp only [h4, ↓reduceIte, rangeGet]
            split <;> rfl

/-- Native branching on strict unary comparison. -/
private lemma clA5IfLt_native {f g : List Bool → ℕ} {a b : List Bool → List Bool}
    (hf : PolyTimeComputable (fun z => List.replicate (f z) true))
    (hg : PolyTimeComputable (fun z => List.replicate (g z) true))
    (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) :
    PolyTimeComputable (fun z => if f z < g z then a z else b z) := by
  simpa only [Nat.add_one_le_iff, decide_eq_true_eq] using clA5_pt_cond
    (clA5Le_native (clA5Add_native hf (clA5_pt_const (List.replicate 1 true))) hg) ha hb

/-- Native branching on equality to zero. -/
private lemma clA5IfZero_native {f : List Bool → ℕ} {a b : List Bool → List Bool}
    (hf : PolyTimeComputable (fun z => List.replicate (f z) true))
    (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) :
    PolyTimeComputable (fun z => if f z = 0 then a z else b z) := by
  simpa only [List.replicate_eq_nil_iff, decide_eq_true_eq] using
    clA5_pt_cond (clA5_pt_eq hf []) ha hb

/-- A native indexed bit read, with the specified false default. -/
private lemma clA5GetBit_native {f : List Bool → List Bool} {i : List Bool → ℕ}
    (hf : PolyTimeComputable f)
    (hi : PolyTimeComputable (fun z => List.replicate (i z) true)) :
    PolyTimeComputable (fun z => [(f z)[i z]?.getD false]) := by
  have h := clA5_pt_eq (clA5_pt_head.comp (clA5Drop_native hf hi)) [true]
  have he (w : List Bool) : decide (w.take 1 = [true]) = w.head?.getD false := by
    cases w with
    | nil => rfl
    | cons b w => cases b <;> rfl
  convert h using 1
  funext z
  simp only [Function.comp_apply, List.length_replicate, he, List.head?_drop]

/-- Native serialization of one pinning unit. -/
private lemma clA5Pin_native {f : List Bool → List Bool} {i : List Bool → ℕ}
    (hf : PolyTimeComputable f)
    (hi : PolyTimeComputable (fun z => List.replicate (i z) true)) :
    PolyTimeComputable (fun z => clFragment [[(i z, (f z)[i z]?.getD false)]]) := by
  have ht := clA5Template_native [[(0, true)]] (fun z _ => i z) (fun _ => hi)
  have he := clA5Template_native [[(0, false)]] (fun z _ => i z) (fun _ => hi)
  have h := clA5_pt_cond (clA5GetBit_native hf hi) ht he
  convert h using 1
  funext z
  cases (f z)[i z]?.getD false <;> rfl

/-- Current bounded emission cursor stored before the immutable producer word. -/
private def clA5Cursor (z : List Bool) : ℕ := (clHeaderField 0 z).length

/-- Native current cursor and retained instance. -/
private lemma clA5Cursor_native :
    PolyTimeComputable (fun z => List.replicate (clA5Cursor z) true) ∧
    PolyTimeComputable clA5Instance :=
  ⟨(clNative_fill true).comp (clHeaderField_native 0),
    (clHeaderField_native 0).comp ((clHeaderField_native 0).comp (clHeaderTail_native 1))⟩

/-- Residual ordinal after the pin family, before the singleton initial family. -/
private def clA5InitialIndex (z : List Bool) : ℕ := clA5Cursor z - (clA5Instance z).length
/-- Residual ordinal for the state family. -/
private def clA5StateIndex (z : List Bool) : ℕ := clA5InitialIndex z - 1
/-- Residual ordinal for the inclusive input family. -/
private def clA5InputIndex (z : List Bool) : ℕ := clA5StateIndex z - clA5Horizon z
/-- Residual ordinal for the time-then-tape work family. -/
private def clA5WorkIndex (z : List Bool) : ℕ := clA5InputIndex z - (clA5Horizon z + 1)
/-- Residual ordinal for the final accept family. -/
private def clA5AcceptIndex (M : FinTM Bool) (z : List Bool) : ℕ :=
  clA5WorkIndex z - M.k * (clA5Horizon z + 1)

/-- All family offsets are native unary arithmetic on stored words. -/
private lemma clA5Indices_native (M : FinTM Bool) :
    PolyTimeComputable (fun z => List.replicate (clA5InitialIndex z) true) ∧
    PolyTimeComputable (fun z => List.replicate (clA5StateIndex z) true) ∧
    PolyTimeComputable (fun z => List.replicate (clA5InputIndex z) true) ∧
    PolyTimeComputable (fun z => List.replicate (clA5WorkIndex z) true) ∧
    PolyTimeComputable (fun z => List.replicate (clA5AcceptIndex M z) true) := by
  have hi := clA5Sub_native clA5Cursor_native.1 ((clNative_fill true).comp clA5Cursor_native.2)
  have hs := clA5Sub_native hi (clA5_pt_const (List.replicate 1 true))
  have hn := clA5Sub_native hs clA5Sizes_native.2
  have hw := clA5Sub_native hn (clA5Add_native clA5Sizes_native.2 (clA5_pt_const (List.replicate 1 true)))
  have ha := clA5Sub_native hw (clA5Times_native
    (clA5Add_native clA5Sizes_native.2 (clA5_pt_const (List.replicate 1 true))) M.k)
  exact ⟨hi, hs, hn, hw, ha⟩

/-- The fixed tape choice at the current work-family ordinal. -/
private noncomputable def clA5WorkChoice (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (z : List Bool) : List Bool :=
  if h : clA5WorkIndex z % M.k < M.k then
    clA5WorkFragment M code ⟨clA5WorkIndex z % M.k, h⟩ z (clA5WorkIndex z / M.k)
  else []

/-- Finite tape selection, including the empty zero-tape family, is native. -/
private lemma clA5WorkChoice_native (M : FinTM Bool) (code : CLFieldCode (Option M.State)) :
    PolyTimeComputable (clA5WorkChoice M code) := by
  let fs := List.ofFn (fun τ : Fin M.k => fun z =>
    clA5WorkFragment M code τ z (clA5WorkIndex z / M.k))
  have hi := (clA5Indices_native M).2.2.2.1
  have hf : ∀ f ∈ fs, PolyTimeComputable f := by
    intro f h
    obtain ⟨τ, rfl⟩ := List.mem_ofFn.mp h
    exact clA5WorkFragment_native M code τ (clA5Div_native hi M.k)
  convert clA5Select_native fs hf (clA5Mod_native hi M.k) using 1
  funext z
  by_cases h : clA5WorkIndex z % M.k < M.k
  · have hl : clA5WorkIndex z % M.k < fs.length := by simpa [fs] using h
    rw [List.getElem?_eq_getElem hl]
    simp [clA5WorkChoice, h, fs]
  · have hl : fs.length ≤ clA5WorkIndex z % M.k := by simpa [fs] using Nat.le_of_not_gt h
    rw [List.getElem?_eq_none hl]
    simp [clA5WorkChoice, h]

/-- Concrete ordered fragment selector over the protected tables.
Only its current group's fragment is emitted; the formula terminator belongs
to the separate last-round check. -/
private noncomputable def clA5Fragment (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (z : List Bool) : List Bool :=
  if clA5Cursor z < (clA5Instance z).length then
    clFragment [[(clA5Cursor z, (clA5Instance z)[clA5Cursor z]?.getD false)]]
  else if clA5InitialIndex z = 0 then
    clFragment (clGroup M code (CLTemplateKind.initial (decide (0 < clA5InputSize z)))
      (clA5InputSize z) 0 0 0)
  else if clA5StateIndex z < clA5Horizon z then
    clFragment (clGroup M code CLTemplateKind.state (clA5InputSize z)
      (clA5StateIndex z) (clA5StateIndex z + 1) 0)
  else if clA5InputIndex z < clA5Horizon z + 1 then
    clA5InputFragment M code z (clA5InputIndex z)
  else if clA5WorkIndex z < M.k * (clA5Horizon z + 1) then
    clA5WorkChoice M code z
  else if clA5AcceptIndex M z < clA5Horizon z then
    clFragment (clGroup M code CLTemplateKind.accept (clA5InputSize z)
      (clA5AcceptIndex M z) 0 0)
  else []

/-- The whole selector is one total native polynomial transduction.
Every numeric operation is unary bounded; stored binary counters are decoded
only within the explicit unary horizon. Templates and tape choices are fixed
finite data for this source machine. -/
private lemma clA5Fragment_native (M : FinTM Bool) (code : CLFieldCode (Option M.State)) :
    PolyTimeComputable (clA5Fragment M code) := by
  have hz := clA5_pt_const (List.replicate 0 true)
  have ho := clA5_pt_const (List.replicate 1 true)
  have hm := clA5Sizes_native.1
  have hT := clA5Sizes_native.2
  obtain ⟨hi, hs, hn, hw, ha⟩ := clA5Indices_native M
  have hinit : PolyTimeComputable (fun z => clFragment
      (clGroup M code (CLTemplateKind.initial (decide (0 < clA5InputSize z)))
        (clA5InputSize z) 0 0 0)) := by
    have h := clA5IfLt_native hz hm
      (clA5Group_native M code (CLTemplateKind.initial true) hm hz hz hz)
      (clA5Group_native M code (CLTemplateKind.initial false) hm hz hz hz)
    convert h using 1
    funext z
    by_cases hp : 0 < clA5InputSize z <;> simp [hp]
  exact clA5IfLt_native clA5Cursor_native.1 ((clNative_fill true).comp clA5Cursor_native.2)
    (clA5Pin_native clA5Cursor_native.2 clA5Cursor_native.1)
    (clA5IfZero_native hi hinit (clA5IfLt_native hs hT
      (clA5Group_native M code CLTemplateKind.state hm hs (clA5Add_native hs ho) hz)
      (clA5IfLt_native hn (clA5Add_native hT ho) (clA5InputFragment_native M code hn)
        (clA5IfLt_native hw (clA5Times_native (clA5Add_native hT ho) M.k)
          (clA5WorkChoice_native M code)
          (clA5IfLt_native ha hT (clA5Group_native M code CLTemplateKind.accept hm ha hz hz)
            (clA5_pt_const []))))))

/-- The native fragment selector agrees word for word with the current
member of the unchanged pure tableau list.
**Proof sketch.** The six guarded offsets are precisely list lookup. Legal
input and work times lie in the inclusive producer tables. A work ordinal's
quotient names its time and its remainder its tape, in the original order. -/
private lemma clA5Fragment_exact (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (C e c A d : ℕ) (x : List Bool) (j : ℕ) :
    clA5Fragment M code (clA5Pack M C e c A d x j) =
      clFragment ((clTableauGroups M code C e x (clProducerHorizon C e c A d x.length))[j]?.getD []) := by
  let z := clA5Pack M C e c A d x j
  let m := x.length + C * (x.length + 1) ^ e
  let T := clProducerHorizon C e c A d x.length
  have hc : clA5Cursor z = j := by
    simp [clA5Cursor, z, clA5Pack, clHeaderField, clHeaderTail, pairDecode_pairEncode]
  have hx : clA5Instance z = x := (clA5Stored_exact M C e c A d x j).1
  have hm : clA5InputSize z = m := (clA5Data_exact M C e c A d x j).1
  have hT : clA5Horizon z = T := (clA5Data_exact M C e c A d x j).2.1
  change clA5Fragment M code z = _
  unfold clTableauGroups
  rw [← clA5GroupAt_exact]
  change clA5Fragment M code z = clFragment (clA5GroupAt x.length M.k T
    (fun i => [[(i, x[i]?.getD false)]])
    (clGroup M code (CLTemplateKind.initial (decide (0 < m))) m 0 0 0)
    (fun t => clGroup M code CLTemplateKind.state m t (t + 1) 0)
    (clInputGroup M code m)
    (fun t τ => if h : τ < M.k then clWorkGroup M code m t ⟨τ, h⟩ else [])
    (fun t => clGroup M code CLTemplateKind.accept m t 0 0) j)
  unfold clA5Fragment clA5GroupAt
  simp only [clA5InitialIndex, clA5StateIndex, clA5InputIndex, clA5WorkIndex, clA5AcceptIndex,
    hc, hx, hm, hT]
  by_cases h0 : j < x.length
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    by_cases h1 : j - x.length = 0
    · simp [h1]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : j - x.length - 1 < T
      · simp [h2]
      · simp only [h2, ↓reduceIte]
        by_cases h3 : j - x.length - 1 - T < T + 1
        · simp only [h3, ↓reduceIte]
          exact clA5InputFragment_exact M code C e c A d x j _ (by omega)
        · simp only [h3, ↓reduceIte]
          by_cases h4 : j - x.length - 1 - T - (T + 1) < M.k * (T + 1)
          · simp only [h4, ↓reduceIte]
            have hk : 0 < M.k := by
              by_contra h
              have hz : M.k = 0 := by omega
              simp [hz] at h4
            have ht : (j - x.length - 1 - T - (T + 1)) / M.k ≤ T := by
              have hh : (j - x.length - 1 - T - (T + 1)) / M.k < T + 1 :=
                (Nat.div_lt_iff_lt_mul hk).mpr (by simpa only [Nat.mul_comm M.k] using h4)
              omega
            have hτ := Nat.mod_lt (j - x.length - 1 - T - (T + 1)) hk
            unfold clA5WorkChoice
            simp only [clA5WorkIndex, clA5InputIndex, clA5StateIndex, clA5InitialIndex,
              hc, hx, hT, hτ, ↓reduceDIte]
            exact clA5WorkFragment_exact M code C e c A d x j _ ht _
          · simp only [h4, ↓reduceIte]
            split <;> rfl

/-- Native equality of two unary values. -/
private lemma clA5Eq_native {f g : List Bool → ℕ}
    (hf : PolyTimeComputable (fun z => List.replicate (f z) true))
    (hg : PolyTimeComputable (fun z => List.replicate (g z) true)) :
    PolyTimeComputable (fun z => [decide (f z = g z)]) := by
  convert clA5_pt_and (clA5Le_native hf hg) (clA5Le_native hg hf) using 1
  funext z
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Exact chunk selector, with one final formula terminator and a silent
saturated state. Empty group fragments retain their own positive body round. -/
private noncomputable def clA5Emit (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (z : List Bool) : List Bool :=
  if clA5Cursor z ≤ clA5StoredRound M z then
    clA5Fragment M code z ++ if clA5Cursor z = clA5StoredRound M z then [false] else []
  else []

/-- The complete chunk selector is an actual native polynomial program. -/
private lemma clA5Emit_native (M : FinTM Bool) (code : CLFieldCode (Option M.State)) :
    PolyTimeComputable (clA5Emit M code) := by
  have hi := clA5Cursor_native.1
  have hr := clA5StoredRound_native M
  have ht := clA5_pt_cond (clA5Eq_native hi hr) (clA5_pt_const [false]) (clA5_pt_const [])
  simpa [clA5Emit] using clA5_pt_cond (clA5Le_native hi hr)
    (clNative_append (clA5Fragment_native M code) ht) (clA5_pt_const [])

/-- Exact legal and saturated chunk values, preserving all protected
member counts and the sole-last-terminator convention. -/
private lemma clA5Emit_exact (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (C e c A d : ℕ) (x : List Bool) (j : ℕ) :
    clA5Emit M code (clA5Pack M C e c A d x j) =
      if j ≤ clLastRound x.length M.k (clProducerHorizon C e c A d x.length) then
        clChunk (clLastRound x.length M.k (clProducerHorizon C e c A d x.length))
          (fun i => (clTableauGroups M code C e x (clProducerHorizon C e c A d x.length))[i]?.getD []) j
      else [] := by
  have hc : clA5Cursor (clA5Pack M C e c A d x j) = j := by
    simp [clA5Cursor, clA5Pack, clHeaderField, clHeaderTail, pairDecode_pairEncode]
  unfold clA5Emit
  rw [hc, (clA5Stored_exact M C e c A d x j).2, clA5Fragment_exact]
  rfl

/-- **Physical output identity, before semantics.** From genuine native
input, one finite machine emits exactly `serialize (clTableau …)` in total
polynomial time. The body installs the completed packed-record producer,
uses the exact six-family chunk selector, restores every administrative word
and head on each positive first return, and has a positive silent saturated
round. Its one common budget covers startup, fuel and every whole round.
No certificate or satisfiability assumption occurs in this theorem. -/
private lemma clA5OutputIdentity (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (C e c A d : ℕ) :
    PolyTimeComputable (fun x => Std.Sat.CNF.serialize
      (clTableau M code C e x (clProducerHorizon C e c A d x.length))) := by
  exact clA5Output_of_nativeChunk M code C e c A d (clA5Emit M code)
    (clA5Emit_native M code) (fun x i _ => clA5Emit_exact M code C e c A d x i)

/-! Pure correctness begins only after `clA5OutputIdentity`. Every block
below remains a raw bit vector until its equality with an encoded genuine
snapshot has been proved. -/

/-- The raw snapshot block selected by a total SAT assignment. -/
private def clA5Block (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (m : ℕ) (a : ℕ → Bool) (t : ℕ) : Fin (clWidth M code) → Bool :=
  fun i => a (clPack m (clWidth M code) t i.val)

/-- Exact bit-level meaning of one wired protected template. -/
private noncomputable def clA5Meaning (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (kind : CLTemplateKind M.k) (m s t p : ℕ) (a : ℕ → Bool) : Prop :=
  let source := clBlockDecode M code (clA5Block M code m a s)
  let target := clA5Block M code m a t
  match kind with
  | CLTemplateKind.initial present => target = clBlockEncode M code
      ⟨some M.tm.q₀, if present then some (a p) else none, fun _ => none⟩
  | CLTemplateKind.state => clStateSlice M code target = (CLFieldCode.enc code) (stepState M source)
  | CLTemplateKind.input present => clInputSlice M code target =
      clSymbolCode (if present then some (a p) else none)
  | CLTemplateKind.work τ previous => clWorkSlice M code target τ =
      clSymbolCode (if previous then writtenOrKept M source τ else none)
  | CLTemplateKind.accept => emitted M source ≠ some false

/-- Wiring exposes the source and target raw blocks and the selected input
bit exactly. Template satisfaction therefore means bitwise equations, never
merely equality of decoded snapshots. -/
private lemma clA5Group_eval (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (kind : CLTemplateKind M.k) (m s t p : ℕ) (a : ℕ → Bool) :
    (clGroup M code kind m s t p).eval a = true ↔ clA5Meaning M code kind m s t p a := by
  classical
  let B := clWidth M code
  let window := fun j : Fin (2 * B + 1) => a (clWire m B s t p j.val)
  have hs : clSourceBits B window = clA5Block M code m a s := by
    funext i
    simp [clSourceBits, window, clWire, clA5Block, B, i.isLt]
  have ht : clTargetBits B window = clA5Block M code m a t := by
    funext i
    have h1 : ¬B + i.val < B := by omega
    have h2 : B + i.val < 2 * B := by omega
    simp [clTargetBits, window, clWire, clA5Block, h1, h2, B]
  have hp : clWindowBit B window = a p := by
    have h1 : ¬2 * B < B := by omega
    simp [clWindowBit, window, clWire, h1]
  unfold clGroup
  rw [clTemplate_eval]
  change clPredicate M code kind window = true ↔ _
  unfold clPredicate
  change (match kind with
    | CLTemplateKind.initial present => decide (clTargetBits B window = clBlockEncode M code
        ⟨some M.tm.q₀, if present then some (clWindowBit B window) else none, fun _ => none⟩)
    | CLTemplateKind.state => decide (clStateSlice M code (clTargetBits B window) =
        (CLFieldCode.enc code) (stepState M (clBlockDecode M code (clSourceBits B window))))
    | CLTemplateKind.input present => decide (clInputSlice M code (clTargetBits B window) =
        clSymbolCode (if present then some (clWindowBit B window) else none))
    | CLTemplateKind.work τ previous => decide (clWorkSlice M code (clTargetBits B window) τ =
        clSymbolCode (if previous then writtenOrKept M (clBlockDecode M code (clSourceBits B window)) τ else none))
    | CLTemplateKind.accept => decide (emitted M (clBlockDecode M code (clSourceBits B window)) ≠ some false)) = true ↔ _
  rw [hs, ht, hp]
  cases kind <;> simp only [clA5Meaning, decide_eq_true_eq]

/-- Flattening clause groups conjoins exactly their evaluations. -/
private lemma clA5Flatten_eval (gs : List (Std.Sat.CNF ℕ)) (a : ℕ → Bool) :
    Std.Sat.CNF.eval a gs.flatten = true ↔ ∀ g ∈ gs, g.eval a = true := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [List.flatten_cons, Std.Sat.CNF.eval_append, Bool.and_eq_true, ih]

/-- The six constraints extracted from the unchanged ordered tableau.
The inclusive families keep `t ≤ T`; state and acceptance keep `t < T`. -/
private lemma clA5Tableau_eval (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (C e : ℕ) (x : List Bool) (T : ℕ) (a : ℕ → Bool) :
    let m := x.length + C * (x.length + 1) ^ e
    (clTableau M code C e x T).eval a = true ↔
      (∀ j < x.length, a j = x[j]?.getD false) ∧
      clA5Meaning M code (CLTemplateKind.initial (decide (0 < m))) m 0 0 0 a ∧
      (∀ t < T, clA5Meaning M code CLTemplateKind.state m t (t + 1) 0 a) ∧
      (∀ t ≤ T, (clInputGroup M code m t).eval a = true) ∧
      (∀ t ≤ T, ∀ τ : Fin M.k, (clWorkGroup M code m t τ).eval a = true) ∧
      (∀ t < T, clA5Meaning M code CLTemplateKind.accept m t 0 0 a) := by
  dsimp only
  simp only [clTableau, clA5Flatten_eval, clTableauGroups, clGroups,
    List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_singleton,
    forall_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    or_imp, forall_and, clA5Group_eval]
  simp only [Std.Sat.CNF.eval_cons, Std.Sat.CNF.eval_nil,
    Std.Sat.CNF.Clause.eval_cons, Std.Sat.CNF.Clause.eval_nil, Bool.or_false,
    Bool.and_true, beq_iff_eq, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨hp, hz⟩, hs⟩, hi⟩, hw⟩, ha⟩
    refine ⟨hp, hz, hs, hi, ?_, ha⟩
    intro t ht τ
    exact hw _ t ht τ.val τ.isLt (by rw [dif_pos τ.isLt])
  · rintro ⟨hp, hz, hs, hi, hw, ha⟩
    refine ⟨⟨⟨⟨⟨hp, hz⟩, hs⟩, hi⟩, ?_⟩, ha⟩
    intro g t ht τ hτ heq
    subst g
    simpa only [dif_pos hτ] using hw t ht ⟨τ, hτ⟩

/-- Boundary-aware input symbols in terms of their literal input bit. -/
private lemma clA5InputBit (y : List Bool) (p : ℕ) :
    inputBitAt y p = if 0 < p ∧ p ≤ y.length then some (y[p - 1]?.getD false) else none := by
  delta inputBitAt
  by_cases h0 : p = 0
  · simp [h0]
  · by_cases hp : p ≤ y.length
    · have hi : p - 1 < y.length := by omega
      simp [h0, hp, show 0 < p by omega, List.getElem?_eq_getElem hi]
    · have hi : y.length ≤ p - 1 := by omega
      simp [h0, hp, List.getElem?_eq_none hi]

/-- Input-family clauses specify the literal raw input-symbol slice. -/
private lemma clA5Input_meaning (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (m t : ℕ) (a : ℕ → Bool) (y : List Bool) (hy : y.length = m)
    (ha : ∀ j < m, a j = y[j]?.getD false) :
    (clInputGroup M code m t).eval a = true ↔
      clInputSlice M code (clA5Block M code m a t) =
        clSymbolCode (inputBitAt y (inputPosAt M m t)) := by
  classical
  unfold clInputGroup
  dsimp only
  rw [clA5InputBit, hy]
  by_cases hp : 0 < inputPosAt M m t ∧ inputPosAt M m t ≤ m
  · rw [if_pos hp, if_pos hp, clA5Group_eval]
    change (_ = clSymbolCode (some (a (inputPosAt M m t - 1)))) ↔ _
    rw [ha _ (by omega)]
  · rw [if_neg hp, if_neg hp, clA5Group_eval]
    rfl

/-- The initial-family raw-block equation is exactly the proved initial
snapshot, with the empty input case included. -/
private lemma clA5Initial_meaning (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (m : ℕ) (a : ℕ → Bool) (y : List Bool) (hy : y.length = m)
    (ha : ∀ j < m, a j = y[j]?.getD false) :
    clA5Meaning M code (CLTemplateKind.initial (decide (0 < m))) m 0 0 0 a ↔
      clA5Block M code m a 0 = clBlockEncode M code (snapshotAt M y 0) := by
  classical
  rw [snapshotAt_zero, clA5InputBit, hy]
  by_cases hp : 0 < m
  · have hle : 1 ≤ m := by omega
    simp [clA5Meaning, hp, hle, ha 0 hp]
  · have hm : m = 0 := by omega
    simp [clA5Meaning, hm]

/-- Work-family clauses specify literal work-symbol bits. Strictly earlier
visits retain the whole-block decoder until the time induction proves its
argument is a genuine encoded block. -/
private lemma clA5Work_meaning (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (m t : ℕ) (τ : Fin M.k) (a : ℕ → Bool) :
    (clWorkGroup M code m t τ).eval a = true ↔
      clWorkSlice M code (clA5Block M code m a t) τ = clSymbolCode
        (match prevVisit M m t τ with
        | none => none
        | some s => writtenOrKept M (clBlockDecode M code (clA5Block M code m a s)) τ) := by
  unfold clWorkGroup
  cases prevVisit M m t τ <;> rw [clA5Group_eval] <;> rfl

/-- Bitwise reconstruction of every raw block by strong induction on time.
**Proof sketch.** The initial family pins the entire initial encoding. At a
successor, the state field uses the preceding encoded block; the input field
uses the oblivious input schedule; each work field uses either blank or the
strictly earlier encoded block named by the proved greatest-visit table.
`clBlock_ext` combines equality of every field bit, excluding junk blocks. -/
private lemma clA5Reconstruct (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (hM : M.Oblivious) (m T : ℕ) (a : ℕ → Bool) (y : List Bool) (hy : y.length = m)
    (hz : clA5Block M code m a 0 = clBlockEncode M code (snapshotAt M y 0))
    (hs : ∀ t < T, clA5Meaning M code CLTemplateKind.state m t (t + 1) 0 a)
    (hi : ∀ t ≤ T, clInputSlice M code (clA5Block M code m a t) =
      clSymbolCode (inputBitAt y (inputPosAt M m t)))
    (hw : ∀ t ≤ T, ∀ τ : Fin M.k,
      clWorkSlice M code (clA5Block M code m a t) τ = clSymbolCode
        (match prevVisit M m t τ with
        | none => none
        | some s => writtenOrKept M (clBlockDecode M code (clA5Block M code m a s)) τ)) :
    ∀ t ≤ T, clA5Block M code m a t = clBlockEncode M code (snapshotAt M y t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    cases t with
    | zero => exact hz
    | succ t =>
      apply clBlock_ext M code
      · rw [clBlock_state, snapshotAt_state_succ]
        have he := hs t (by omega)
        change clStateSlice M code (clA5Block M code m a (t + 1)) =
          (CLFieldCode.enc code) (stepState M (clBlockDecode M code (clA5Block M code m a t))) at he
        rw [ih t (by omega) (by omega), clBlockDecode_encode] at he
        exact he
      · rw [clBlock_input, snapshotAt_inputSymbol hM, hy]
        exact hi _ ht
      · intro τ
        rw [clBlock_work, snapshotAt_workSymbol hM, hy, hw _ ht τ]
        cases hp : prevVisit M m (t + 1) τ with
        | none => rfl
        | some s =>
          dsimp only
          rw [ih s (clPrev_spec M m (t + 1) s τ hp).1 (by have := (clPrev_spec M m (t + 1) s τ hp).1; omega),
            clBlockDecode_encode]

/-- Read exactly the first `m` assignment bits as the verifier's input. -/
private def clA5ReadInput (m : ℕ) (a : ℕ → Bool) : List Bool := List.ofFn (fun i : Fin m => a i.val)

/-- Each recovered input bit is the assigned bit at that variable. -/
private lemma clA5ReadInput_get (m : ℕ) (a : ℕ → Bool) (j : ℕ) (hj : j < m) :
    (clA5ReadInput m a)[j]?.getD false = a j := by
  simp [clA5ReadInput, hj]

/-- Pinning recovers an exact-length certificate, without enlarging its
polynomial or silently switching to a bounded-length witness. -/
private lemma clA5Certificate (C e : ℕ) (x : List Bool) (a : ℕ → Bool)
    (hp : ∀ j < x.length, a j = x[j]?.getD false) :
    ∃ u : List Bool, u.length = C * (x.length + 1) ^ e ∧
      clA5ReadInput (x.length + C * (x.length + 1) ^ e) a = x ++ u := by
  let y := clA5ReadInput (x.length + C * (x.length + 1) ^ e) a
  have hlen : y.length = x.length + C * (x.length + 1) ^ e := by simp [y, clA5ReadInput]
  have ht : y.take x.length = x := by
    apply List.ext_getElem (by simp [hlen])
    intro j hj hk
    have hbit := (clA5ReadInput_get (x.length + C * (x.length + 1) ^ e) a j (by omega)).trans (hp j hk)
    simpa [y, List.getElem?_eq_getElem (show j < y.length by omega), List.getElem?_eq_getElem hk] using hbit
  refine ⟨y.drop x.length, by simp [hlen], ?_⟩
  change y = x ++ y.drop x.length
  calc
    y = y.take x.length ++ y.drop x.length := (List.take_append_drop _ _).symm
    _ = x ++ y.drop x.length := by rw [ht]

/-- Physical run output is precisely the chronological concatenation of
snapshot emissions, including the write on a halting transition. -/
private lemma clA5Run_output (M : FinTM Bool) (y : List Bool) (T : ℕ) :
    (M.tm.runFrom (M.tm.initCfg y) T).output =
      (List.range T).flatMap (fun t => (emitted M (snapshotAt M y t)).toList) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, ih,
      List.range_succ, List.flatMap_append, List.flatMap_singleton]
    congr 1
    delta MultiTapeTM.outputSymbol emitted snapshotAt
    cases (M.tm.runFrom (M.tm.initCfg y) T).state <;> rfl

/-- No false emission is equivalent to no false bit in the append-only
output prefix. This is an exact word statement, not a halting assumption. -/
private lemma clA5NoFalse (M : FinTM Bool) (y : List Bool) (T : ℕ) :
    false ∉ (M.tm.runFrom (M.tm.initCfg y) T).output ↔
      ∀ t < T, emitted M (snapshotAt M y t) ≠ some false := by
  rw [clA5Run_output]
  constructor
  · intro h t ht he
    apply h
    exact List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, by rw [he]; simp⟩
  · intro h hb
    obtain ⟨t, ht, hb⟩ := List.mem_flatMap.mp hb
    cases he : emitted M (snapshotAt M y t) with
    | none => simp [he] at hb
    | some b =>
      have hh : b = false := by simpa [he, eq_comm] using hb
      subst b
      exact h t (List.mem_range.mp ht) he

/-- A total decider's exact singleton output turns the local no-false
condition into membership. In particular, silent or junk traces cannot
satisfy this argument: the total decider supplies its actual verdict bit. -/
private lemma clA5Decider_accept (M : FinTM Bool) (V : Language Bool) (y : List Bool) (T : ℕ)
    (hM : M.ComputesInTime y [MultiTapeTM.indicator (V : Set (List Bool)) y] T) :
    (∀ t < T, emitted M (snapshotAt M y t) ≠ some false) ↔ y ∈ V := by
  classical
  rw [← clA5NoFalse, ((FinTM.computesInTime_iff _ _ _ _).mp hM).2]
  delta MultiTapeTM.indicator
  by_cases h : y ∈ V <;> simp [h]

/-- Every product code contains the two input-symbol bits. -/
private lemma clA5Width_pos (M : FinTM Bool) (code : CLFieldCode (Option M.State)) :
    0 < clWidth M code := by
  unfold clWidth
  omega

/-- A genuine run supplies a total SAT assignment: literal input bits,
then the raw encoding of every chronological snapshot block. -/
private def clA5TraceAssignment (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (y : List Bool) (v : ℕ) : Bool :=
  if v < y.length then y[v]?.getD false else
    clBlockEncode M code (snapshotAt M y ((v - y.length) / clWidth M code))
      ⟨(v - y.length) % clWidth M code, Nat.mod_lt _ (clA5Width_pos M code)⟩

/-- Input variables of the genuine assignment retain the literal bits. -/
private lemma clA5Trace_input (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (y : List Bool) (j : ℕ) (hj : j < y.length) :
    clA5TraceAssignment M code y j = y[j]?.getD false := by
  simp [clA5TraceAssignment, hj]

/-- Quotient and remainder recover each complete raw snapshot block. -/
private lemma clA5Trace_block (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (y : List Bool) (t : ℕ) :
    clA5Block M code y.length (clA5TraceAssignment M code y) t =
      clBlockEncode M code (snapshotAt M y t) := by
  funext i
  let B := clWidth M code
  have hn : ¬clPack y.length B t i.val < y.length := by unfold clPack; omega
  have hd : clPack y.length B t i.val - y.length = t * B + i.val := by unfold clPack; omega
  have hq : (t * B + i.val) / B = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (clA5Width_pos M code), Nat.div_eq_of_lt i.isLt]
    omega
  have hr : (t * B + i.val) % B = i.val := by
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt i.isLt
  change (if clPack y.length B t i.val < y.length then _ else
    clBlockEncode M code (snapshotAt M y ((clPack y.length B t i.val - y.length) / B))
      ⟨(clPack y.length B t i.val - y.length) % B, _⟩) = _
  rw [if_neg hn]
  simp only [hd, hq]
  apply congrArg (clBlockEncode M code (snapshotAt M y t))
  exact Fin.ext hr

/-- Soundness: a satisfying assignment determines an exact-length witness.
The raw-block strong induction rules out junk assignments before any use of
the decoder, and totality plus the no-false family forces the true verdict. -/
private lemma clA5Sound (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (hM : M.Oblivious) (V : Language Bool) (C e : ℕ) (x : List Bool) (T : ℕ)
    (hD : ∀ y : List Bool, y.length = x.length + C * (x.length + 1) ^ e →
      M.ComputesInTime y [MultiTapeTM.indicator (V : Set (List Bool)) y] T)
    (hφ : (clTableau M code C e x T).Satisfiable) :
    ∃ u : List Bool, u.length = C * (x.length + 1) ^ e ∧ x ++ u ∈ V := by
  obtain ⟨a, ha⟩ := hφ
  obtain ⟨hp, hz, hs, hi, hw, he⟩ := (clA5Tableau_eval M code C e x T a).mp ha
  let m := x.length + C * (x.length + 1) ^ e
  let y := clA5ReadInput m a
  have hy : y.length = m := by simp [y, clA5ReadInput]
  have hb : ∀ j < m, a j = y[j]?.getD false := fun j hj => (clA5ReadInput_get m a j hj).symm
  have hraw := clA5Reconstruct M code hM m T a y hy
    ((clA5Initial_meaning M code m a y hy hb).mp hz) hs
    (fun t ht => (clA5Input_meaning M code m t a y hy hb).mp (hi t ht))
    (fun t ht τ => (clA5Work_meaning M code m t τ a).mp (hw t ht τ))
  have hfalse : ∀ t < T, emitted M (snapshotAt M y t) ≠ some false := by
    intro t ht
    have hh := he t ht
    change emitted M (clBlockDecode M code (clA5Block M code m a t)) ≠ some false at hh
    rwa [hraw t (by omega), clBlockDecode_encode] at hh
  have hv : y ∈ V := (clA5Decider_accept M V y T (hD y hy)).mp hfalse
  obtain ⟨u, hu, hxy⟩ := clA5Certificate C e x a hp
  exact ⟨u, hu, hxy ▸ hv⟩

/-- Completeness: an accepted exact-length witness gives the literal input
assignment and raw encodings of its genuine snapshots. Each field equation
is one of the proved snapshot APIs; the singleton true output supplies the
no-false family. -/
private lemma clA5Complete (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (hM : M.Oblivious) (V : Language Bool) (C e : ℕ) (x : List Bool) (T : ℕ)
    (hD : ∀ y : List Bool, y.length = x.length + C * (x.length + 1) ^ e →
      M.ComputesInTime y [MultiTapeTM.indicator (V : Set (List Bool)) y] T)
    (hcert : ∃ u : List Bool, u.length = C * (x.length + 1) ^ e ∧ x ++ u ∈ V) :
    (clTableau M code C e x T).Satisfiable := by
  obtain ⟨u, hu, hv⟩ := hcert
  let m := x.length + C * (x.length + 1) ^ e
  let y := x ++ u
  let a := clA5TraceAssignment M code y
  have hy : y.length = m := by simp [y, m, hu]
  have hb : ∀ j < m, a j = y[j]?.getD false := by
    intro j hj
    exact clA5Trace_input M code y j (by omega)
  have hraw (t : ℕ) : clA5Block M code m a t = clBlockEncode M code (snapshotAt M y t) := by
    simpa only [hy] using clA5Trace_block M code y t
  refine ⟨a, (clA5Tableau_eval M code C e x T a).mpr ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hb j (by dsimp [m]; omega)]
    exact congrArg (fun w : Option Bool => w.getD false) (List.getElem?_append_left hj)
  · exact (clA5Initial_meaning M code m a y hy hb).mpr (hraw 0)
  · intro t _
    change clStateSlice M code (clA5Block M code m a (t + 1)) =
      (CLFieldCode.enc code) (stepState M (clBlockDecode M code (clA5Block M code m a t)))
    rw [hraw, hraw, clBlock_state, clBlockDecode_encode, snapshotAt_state_succ]
  · intro t _
    apply (clA5Input_meaning M code m t a y hy hb).mpr
    rw [hraw, clBlock_input, snapshotAt_inputSymbol hM, hy]
  · intro t _ τ
    apply (clA5Work_meaning M code m t τ a).mpr
    rw [hraw, clBlock_work, snapshotAt_workSymbol hM, hy]
    cases prevVisit M m t τ with
    | none => rfl
    | some s => dsimp only; rw [hraw, clBlockDecode_encode]
  · intro t ht
    change emitted M (clBlockDecode M code (clA5Block M code m a t)) ≠ some false
    rw [hraw, clBlockDecode_encode]
    exact (clA5Decider_accept M V y T (hD y hy)).mpr hv t ht

/-- The protected tableau is equisatisfiable with the original exact NP
certificate relation. The emitter identity was proved before this pure layer. -/
private lemma clA5Equisat (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (hM : M.Oblivious) (V : Language Bool) (C e c A d : ℕ)
    (hD : M.DecidesInTime V (fun n => c * (A * (n + 1) ^ d + 1) ^ 2)) (x : List Bool) :
    (clTableau M code C e x (clProducerHorizon C e c A d x.length)).Satisfiable ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ e ∧ x ++ u ∈ V := by
  have hc : ∀ y : List Bool, y.length = x.length + C * (x.length + 1) ^ e →
      M.ComputesInTime y [MultiTapeTM.indicator (V : Set (List Bool)) y]
        (clProducerHorizon C e c A d x.length) := by
    intro y hy
    simpa only [hy, clProducerHorizon] using hD y
  exact ⟨clA5Sound M code hM V C e x _ hc, clA5Complete M code hM V C e x _ hc⟩

/-- The native exact serialization is a Karp reduction for each audited NP
verifier. Neither the certificate parameters nor any public statement change. -/
private lemma clA5Reduction {L : Language Bool} (hL : L ∈ NP) : L ≤ₚ SAT := by
  obtain ⟨C, e, V, M, c, A, d, hcert, _, _, _, hM, hD⟩ := clNPVerifier hL
  let code := clFieldCode (Option M.State)
  refine ⟨fun x => Std.Sat.CNF.serialize (clTableau M code C e x (clProducerHorizon C e c A d x.length)),
    clA5OutputIdentity M code C e c A d, ?_⟩
  intro x
  change x ∈ L ↔ (Std.Sat.CNF.decode (Std.Sat.CNF.serialize
    (clTableau M code C e x (clProducerHorizon C e c A d x.length)))).Satisfiable
  rw [Std.Sat.CNF.decode_serialize, clA5Equisat M code hM V C e c A d hD, hcert x]

/-- **Lemma 2.11 (Cook-Levin hardness)** [AB09]: `SAT` is `NP`-hard.

**Proof sketch.** Fix `L ∈ NP` with certificate length `Q n = C₀(n+1)^(c₀)`
and verifier language `V ∈ P`.

**(1) Normalization.** `Complexity.mem_P_iff` gives a decider for `V` within
`A(m+1)^d`; enlarge to `A ≥ 1, d ≥ 1` (`Turing.FinTM.ComputesInTime.mono`),
so `Complexity.timeConstructible_poly A (d-1)` makes the bound
time-constructible, and `Complexity.oblivious_of_mem_DTIME` yields an
oblivious `M` and constant `c` with `M.DecidesInTime V T*`, where
`T* m = c(A(m+1)^d + 1)^2` — an explicit polynomial. On inputs of length
`m = n + Q n` (the verifier reads `x ++ u`), write `T = T* m` for the
tableau horizon; `M`'s schedule and last-visit data are
`Complexity.inputPosAt`/`workPosAt`/`prevVisit` at length `m`.

**(2) Variables of `φ_x`** ([AB09] p. 49, adapted): input variables
`y_0, …, y_{m-1}` — the first `n` pinned to `x`'s bits, the last `Q n` free
(the certificate; design question (d)) — and snapshot-block variables
`z_{t,0}, …, z_{t,B-1}` for `0 ≤ t ≤ T`, where `B` is the bit size of a fixed
injective **product** encoding of `Complexity.Snapshot M` — a fixed code for
the optional state followed by fixed codes for the input symbol and each
work symbol, so the block's fields are literal slices of the block and the
bitwise pinning of family (ii)-(v) is per-field (round-1 audit, note 5) —
with a totalized decoder (`dec (enc s) = s`; junk patterns decode to a fixed
snapshot). `B` is a constant of `M`. Index packing `y_j ↦ j`,
`z_{t,i} ↦ m + tB + i` — explicit arithmetic, disjoint and injective by
quotient/remainder by `B`, unary serialization polynomial since all indices
are `< m + (T+1)B`.

**(3) Clause families**, each of constant size per member except where noted,
each obtained from a Boolean function on constantly many block bits via
`Complexity.exists_cnf_boolFun` (Claim 2.13) composed with the index packing
(a relabeling — `Std.Sat.CNF.relabel` is the carrier's tool):
(i) *pinning*: `n` unit clauses forcing `y_j = x_j` for `j < n`;
(ii) *initial block*: clauses forcing `z_0` to encode
`⟨some q₀, input read, blanks⟩` per `Complexity.snapshotAt_zero`, with the
input-read component wired to `y`-variables at position `inputPosAt m 0 = 1`
(boundary blank cases folded in as constants);
(iii) *state succession*: for each `t < T`, clauses forcing `z_{t+1}`'s state
field to `Complexity.stepState` of `z_t`'s decoded block
(`Complexity.snapshotAt_state_succ`);
(iv) *input-read wiring*: for each `t ≤ T`, clauses forcing `z_t`'s
input-symbol field to the `y`-variable at `inputPosAt m t` (or the constant
blank at boundary positions) — [AB09]'s `y_inputpos(i)`
(`Complexity.snapshotAt_inputSymbol`);
(v) *work-read wiring*: for each `t ≤ T` and each of the `k` tapes `τ`,
clauses forcing `z_t`'s `τ`-read field to
`Complexity.writtenOrKept` of the block at `prevVisit m t τ`, or to the
constant blank when `prevVisit = none`
(`Complexity.snapshotAt_workSymbol`; the `k` wirings per step generalize
[AB09]'s single `z_prev(i)`);
(vi) *acceptance*: for each `t < T`, clauses forbidding
`Complexity.emitted` of `z_t`'s decoded block from being `some false`
(design question (a); [AB09]'s condition 4 replaced — see the deviations
list). Block decoding is totalized (junk bit patterns decode to a fixed
snapshot — the `codeFallback` convention), and the forcing clauses pin each
`z_t` **bitwise** to the encoding of the reconstructed snapshot, so no junk
assignment survives family (ii)-(v).

**(4) Correctness**: `φ_x` satisfiable iff `x ∈ L`. (⇐) For `x ∈ L` take the
witness `u`, assign `y := x ++ u` and `z_t :=` the encoding of
`Complexity.snapshotAt M (x ++ u) t`: families (i)-(v) hold by the four
snapshot theorems, and (vi) holds because the genuine run's emissions
concatenate to `M`'s output `[true]` (`Turing.MultiTapeTM.step_output`
chained; `x ++ u ∈ V` since `u` witnesses membership). (⇒) A satisfying
assignment reads off `u` from the free `y`-variables; by induction on `t`,
families (ii)-(v) force every `z_t` to equal the encoding of the genuine
snapshot of the run on `x ++ u` — at each step the four snapshot theorems
say the genuine snapshot satisfies the same reconstruction equations, and
the bitwise pinning makes the solution unique. The run halts within `T`
(`M.DecidesInTime`, totality), its output is `[true]` or `[false]`
(the indicator contract), the emissions are the `Complexity.emitted` values
of the genuine snapshots, and family (vi) rules out `[false]`: so
`x ++ u ∈ V`, hence `x ∈ L`. Both directions quantify over **all** `u` of
the exact audited length — no bounded-length slippage.

**(5) The emitting machine** — `f x := Std.Sat.CNF.serialize φ_x`, with
`Complexity.PolyTimeComputable f` by the staged obligations below, every
stage under the **output-silence contract** (round-1 audit, finding 1): the
preparatory machines' answers are captured on work tapes and their
emissions discarded — `Complexity.timeConstructible_poly`'s machines answer
on the real output tape, and the reference simulation of `M` emits its
verdict bit, so unwrapped forwarding would prefix the serialization and
collapse the emitted word to the fallback (the audit's concrete false
positive: `[false] ++ serialize φ_x` fails exact consumption and decodes to
`[] ∈ SAT`); likewise a forwarded source *halt* would strand the output at
`[false] = serialize []`. **Invariant: the physical output is empty before
serialization, and equals the emitted serialization prefix thereafter.**
Stages (the audit's contract table, adopted verbatim):
(s1) *exact arithmetic* — retain `x`; compute the exact `Q n`, `m`, and `T`
(the phase-3 exact-value discipline), capturing binary subroutine answers on
work tapes and returning control with empty physical output;
(s2) *reference simulation* — present the **virtual** input
`List.replicate m false` (the definitional reference input of
`Complexity.inputPosAt`/`workPosAt`), virtual head starting at `1` and
clamped to `0..m+1`, on disjoint work tapes: the physical input is still
`x`, so native-input embeddings alone do not suffice;
(s3) *simulation output and halt* — discard the source's output field, keep
an **internal** halted flag rather than halting the controller, and after
source halting record the frozen positions until the clock reaches `T`;
(s4) *trajectory* — record times `0..T` inclusive, work counters matching
the signed source positions and input counters the clamped reference
positions (`O(log T)` bits each); administrative controller steps do not
count as simulated time;
(s5) *last visits* — for each target time and tape, compare all earlier
recorded positions and keep the greatest match, or `none` (`O(k·T²)`
comparisons of `O(log T)`-bit integers, with sequential-scan access costs —
polynomial feasibility, no random-access assumption);
(s6) *serialization* — emit the clause families in the fixed order of
(2)-(3) with packed indices in unary (run-length emission driven by binary
counters), every marker and the final terminator included, and halt only
after completion. The constant per-family clause tables are hardwired
finite-control data of the fixed `M` (Claim 2.13 applied once, off-line, to
`M`'s finitely many reconstruction functions); the `Simulation` lockstep
gadgets and the buffered-capture precedents are usable *components*, but the
bare embeddings forward output and halts and are **not** substitutes for
these contracts. Output length — the fill's ledger is the exact identity
`|serialize φ_x| = 1 + 2·#clauses + Σ_{(v,b) occurrence} (v + 3)`; the
pinning family alone costs `n(n-1)/2 + 5n` bits (its unary indices grow),
absorbed by the dominant terms since `T ≥ (m+1)²` — in all an explicit
polynomial in `n`, and time polynomial likewise.

**(6) Conclusion.** `x ∈ L ↔ φ_x` satisfiable
`↔ f x ∈ SAT` (`Std.Sat.CNF.decode_serialize`), so `L ≤ₚ SAT` via
`Complexity.PolyTimeReducible`; quantify over `L ∈ NP` for
`Complexity.NPHard`. -/
theorem SAT_NPHard : NPHard SAT := by
  intro L hL
  exact clA5Reduction hL

/-- **Theorem 2.10.1 (Cook-Levin)** [AB09]: `SAT` is `NP`-complete.

**Proof sketch.** `Complexity.SAT_mem_NP` and `Complexity.SAT_NPHard`,
assembled by the definition of `Complexity.NPComplete`. -/
theorem SAT_NPComplete : NPComplete SAT := by
  exact ⟨SAT_mem_NP, SAT_NPHard⟩

/-- **`3SAT` is `NP`-hard** [AB09, Theorem 2.10.2, hardness half]:
Cook-Levin followed by clause splitting.

**Proof sketch.** `Complexity.SAT_NPHard` transferred along
`Complexity.SAT_reducible_SAT3` (Lemma 2.14) by
`Complexity.NPHard.polyTimeReducible`. -/
theorem SAT3_NPHard : NPHard SAT3 := by
  exact SAT_NPHard.polyTimeReducible SAT_reducible_SAT3

/-- **Theorem 2.10.2** [AB09]: `3SAT` is `NP`-complete.

**Proof sketch.** `Complexity.SAT3_mem_NP` and `Complexity.SAT3_NPHard`. -/
theorem SAT3_NPComplete : NPComplete SAT3 := by
  exact ⟨SAT3_mem_NP, SAT3_NPHard⟩

end Complexity
