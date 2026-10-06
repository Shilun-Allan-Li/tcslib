/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.SAT
import TCSlib.Complexity.ClassNP.TMSAT
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.CookLevin.Snapshot

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

/-- Unary literal indices have their exact, nonconstant cost. -/
private lemma clSerializeLit_length (l : Std.Sat.Literal ℕ) :
    (Std.Sat.CNF.serializeLit l).length = l.1 + 3 := by
  simp [Std.Sat.CNF.serializeLit, Nat.add_assoc]

/-- One clause costs its literal encodings plus its clause terminator. -/
private lemma clSerializeClause_length (C : Std.Sat.CNF.Clause ℕ) :
    (Std.Sat.CNF.serializeClause C).length =
      1 + (C.map (fun l => l.1 + 3)).sum := by
  simp [Std.Sat.CNF.serializeClause, List.length_flatMap,
    clSerializeLit_length, Nat.add_comm]

/-- Exact inherited ledger: one formula terminator, two bits per clause,
and `v+3` bits per literal occurrence. -/
private lemma clSerialize_length (φ : Std.Sat.CNF ℕ) :
    (Std.Sat.CNF.serialize φ).length = 1 + 2 * φ.length +
      (φ.map (fun C => (C.map (fun l => l.1 + 3)).sum)).sum := by
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    have hs : (Std.Sat.CNF.serialize (C :: φ)).length =
        1 + (Std.Sat.CNF.serializeClause C).length +
          (Std.Sat.CNF.serialize φ).length := by
      simp only [Std.Sat.CNF.serialize, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil]
      omega
    rw [hs, clSerializeClause_length, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- The literal-occurrence part of the ledger is bounded by the actual
index ceiling, rather than by a constant per clause. -/
private lemma clClause_cost_le (C : Std.Sat.CNF.Clause ℕ) (N : ℕ)
    (h : ∀ l ∈ C, l.1 < N) :
    (C.map (fun l => l.1 + 3)).sum ≤ (N + 2) * C.length := by
  induction C with
  | nil => simp
  | cons l C ih =>
    have hl := h l (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Bound the full unary serializer by its clause and literal counts. -/
private lemma clSerialize_length_le (φ : Std.Sat.CNF ℕ) (N : ℕ)
    (h : ∀ C ∈ φ, ∀ l ∈ C, l.1 < N) :
    (Std.Sat.CNF.serialize φ).length ≤
      1 + 2 * φ.length + (N + 2) * (φ.map List.length).sum := by
  rw [clSerialize_length]
  suffices (φ.map (fun C => (C.map (fun l => l.1 + 3)).sum)).sum ≤
      (N + 2) * (φ.map List.length).sum by omega
  induction φ with
  | nil => simp
  | cons C φ ih =>
    have hc := clClause_cost_le C N (h C (by simp))
    have ht := ih (fun D hD => h D (by simp [hD]))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- Snapshot bits occupy consecutive product-code blocks after all input
variables; this is the audited packing of [AB09, Lemma 2.11]. -/
private def clPack (m B t i : ℕ) : ℕ := m + t * B + i

/-- No packed snapshot variable overlaps an input variable. -/
private lemma clPack_disjoint (m B t i j : ℕ) (hj : j < m) :
    j < clPack m B t i := by
  unfold clPack
  omega

/-- Quotient and remainder recover the time and the bit within a block. -/
private lemma clPack_injective (m B t u i j : ℕ) (hi : i < B) (hj : j < B)
    (h : clPack m B t i = clPack m B u j) : t = u ∧ i = j := by
  have he : t * B + i = u * B + j := by unfold clPack at h; omega
  have hq := congrArg (fun a => a / B) he
  have hr := congrArg (fun a => a % B) he
  simp only [Nat.add_comm (t * B) i, Nat.add_comm (u * B) j,
    Nat.add_mul_div_right _ _ (by omega : 0 < B),
    Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj, Nat.zero_add] at hq
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hr
  exact ⟨hq, hr⟩

/-- The exact index ceiling includes time `T`, not just times below it. -/
private lemma clPack_lt (m B T t i : ℕ) (ht : t ≤ T) (hi : i < B) :
    clPack m B t i < m + (T + 1) * B := by
  have hm := Nat.mul_le_mul_right B ht
  unfold clPack
  rw [Nat.add_mul, Nat.one_mul]
  omega

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

/-- The normalized tableau horizon dominates the square of input length
plus one, including length zero. -/
private lemma clHorizon_lower (c A d m : ℕ) (hc : 0 < c) (hA : 0 < A)
    (hd : 0 < d) : (m + 1) ^ 2 ≤ c * (A * (m + 1) ^ d + 1) ^ 2 := by
  have hp : m + 1 ≤ (m + 1) ^ d := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos m) (show 1 ≤ d by omega)
  have ha : (m + 1) ^ d ≤ A * (m + 1) ^ d := by
    simpa using Nat.mul_le_mul_right ((m + 1) ^ d) (show 1 ≤ A by omega)
  calc
    (m + 1) ^ 2 ≤ (A * (m + 1) ^ d + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    _ ≤ c * (A * (m + 1) ^ d + 1) ^ 2 := by
      exact (Nat.one_mul _).symm.le.trans
        (Nat.mul_le_mul_right _ (show 1 ≤ c by omega))

/-- An actual clean native call installs the exact certificate-length
word for all coefficients and degrees, including zero. The native input
is untouched and the physical output is empty at return.
**Proof sketch.** Feed the catalog's exact polynomial evaluator to the
install bridge. Bound its complete binary answer by its own runtime,
then absorb argument length into the same positive-degree polynomial.
This supplies the certificate-arithmetic component, not the producer of
the complete preparation records required by stages s1--s5. -/
private lemma clCertificateCall (C e : ℕ) :
    ∃ (W : FinTM Bool) (entry exit : W.State) (a : ℕ), 0 < W.k ∧
      ∀ (x arg : List Bool), ∃ t ≤ a * (arg.length + 1) ^ (e + 1),
        0 < t ∧
        (∀ j, 0 < j → j < t →
          (W.tm.runFrom (Cfg.ofWords (input := x) entry
            (stateWord W.k arg)) j).state ≠ some exit) ∧
        W.tm.runFrom (Cfg.ofWords (input := x) entry
            (stateWord W.k arg)) t =
          Cfg.ofWords exit (stateWord W.k
            (Nat.bits (C * (arg.length + 1) ^ e))) := by
  obtain ⟨E, b, hE⟩ := FinTM.computesFunInTime_polyBits C e
  obtain ⟨W, entry, exit, c, hk, hcall⟩ := FinTM.exists_installCallTM E _ _ hE
  refine ⟨W, entry, exit, c * (2 * b + 1), hk, ?_⟩
  intro x arg
  obtain ⟨t, ht, hp, hf, hr⟩ := hcall x arg
  refine ⟨t, ht.trans ?_, hp, hf, hr⟩
  have hout := (FinTM.computesInTime_iff _ _ _ _).mp (hE arg)
  have hlen := E.tm.output_length_le arg (b * (arg.length + 1) ^ (e + 1))
  rw [hout.2] at hlen
  have harg : arg.length + 1 ≤ (arg.length + 1) ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos arg.length)
      (show 1 ≤ e + 1 by omega)
  calc
    c * (b * (arg.length + 1) ^ (e + 1) + arg.length +
        (Nat.bits (C * (arg.length + 1) ^ e)).length + 1)
        ≤ c * ((2 * b + 1) * (arg.length + 1) ^ (e + 1)) := by
      apply Nat.mul_le_mul_left
      dsimp only at hlen
      rw [show (2 * b + 1) * (arg.length + 1) ^ (e + 1) =
        b * (arg.length + 1) ^ (e + 1) + b * (arg.length + 1) ^ (e + 1) +
          (arg.length + 1) ^ (e + 1) by ring]
      omega
    _ = _ := (Nat.mul_assoc _ _ _).symm

/-- The verifier input length uses the original certificate polynomial
exactly; only its upper bound is enlarged. -/
private lemma clInputLength_bound (C e n : ℕ) :
    n + C * (n + 1) ^ e + 1 ≤ (C + 1) * (n + 1) ^ max 1 e := by
  have hbase : n + 1 ≤ (n + 1) ^ max 1 e := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left 1 e)
  have hpow : (n + 1) ^ e ≤ (n + 1) ^ max 1 e :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right 1 e)
  have hmul := Nat.mul_le_mul_left C hpow
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The exact tableau horizon has an explicit polynomial majorant in
the original instance length. No certificate is padded in this bound.
**Proof sketch.** Substitute the preceding length bound, raise it to
the verifier degree, absorb the added one using positivity of the common
power, square, and collect powers. -/
private lemma clHorizon_upper (C e c A d n : ℕ) :
    c * (A * (n + C * (n + 1) ^ e + 1) ^ d + 1) ^ 2 ≤
      c * (A * (C + 1) ^ d + 1) ^ 2 *
        (n + 1) ^ (2 * d * max 1 e) := by
  have hpow := Nat.pow_le_pow_left (clInputLength_bound C e n) d
  rw [Nat.mul_pow, ← Nat.pow_mul] at hpow
  have hmul := Nat.mul_le_mul_left A hpow
  have hone : 1 ≤ (n + 1) ^ (max 1 e * d) :=
    Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hinner : A * (n + C * (n + 1) ^ e + 1) ^ d + 1 ≤
      (A * (C + 1) ^ d + 1) * (n + 1) ^ (max 1 e * d) := by
    calc
      _ ≤ A * ((C + 1) ^ d * (n + 1) ^ (max 1 e * d)) +
          (n + 1) ^ (max 1 e * d) := Nat.add_le_add hmul hone
      _ = _ := by ring
  calc
    _ ≤ c * (((A * (C + 1) ^ d + 1) *
        (n + 1) ^ (max 1 e * d)) ^ 2) :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left hinner 2)
    _ = _ := by
      rw [Nat.mul_pow, ← Nat.pow_mul,
        show max 1 e * d * 2 = 2 * d * max 1 e by ring, Nat.mul_assoc]
      simp only [Nat.mul_assoc]

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

/-- The pinning family contributes one unit clause per original input
bit, with its own global input-variable index. -/
private def clPins (x : List Bool) : Std.Sat.CNF ℕ :=
  (List.range x.length).map (fun j => [(j, x[j]?.getD false)])

/-- Pinning alone already has quadratic unary-serialization cost. This
is its fragment cost; the sole formula terminator is accounted for later. -/
private lemma clPins_length (x : List Bool) :
    (clFragment (clPins x)).length =
      x.length * (x.length - 1) / 2 + 5 * x.length := by
  simp [clFragment, clPins, List.length_flatMap, Std.Sat.CNF.serializeClause,
    clSerializeLit_length, List.map_map, Function.comp_def, List.sum_map_add,
    List.range_eq_range', List.sum_range']
  omega

/-- The number of literal occurrences is bounded by width times clause
count, including empty clauses and the empty formula. -/
private lemma clLiteralCount_le (φ : Std.Sat.CNF ℕ) (w : ℕ)
    (hw : φ.WidthAtMost w) : (φ.map List.length).sum ≤ w * φ.length := by
  induction φ with
  | nil => simp
  | cons C φ ih =>
    have hc := hw C (by simp)
    have ht := ih (fun D hD => hw D (by simp [hD]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Constant template counts and widths give a unary-output bound that
still charges the full, input-dependent index ceiling. -/
private lemma clSerialize_uniform (φ : Std.Sat.CNF ℕ) (H w N : ℕ)
    (hc : φ.length ≤ H) (hw : φ.WidthAtMost w)
    (hv : ∀ C ∈ φ, ∀ l ∈ C, l.1 < N) :
    (Std.Sat.CNF.serialize φ).length ≤ 1 + H * (2 + (N + 2) * w) := by
  have hl := (clLiteralCount_le φ w hw).trans (Nat.mul_le_mul_left w hc)
  calc
    _ ≤ 1 + 2 * φ.length + (N + 2) * (φ.map List.length).sum :=
      clSerialize_length_le φ N hv
    _ ≤ 1 + 2 * H + (N + 2) * (w * H) :=
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hc) 1)
        (Nat.mul_le_mul_left (N + 2) hl)
    _ = _ := by ring

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

/-- A mentioned literal's index is strictly below the formula's variable
ceiling. This derives the needed local bound from the public definition. -/
private lemma clLiteral_lt_numVars (φ : Std.Sat.CNF ℕ) (C : Std.Sat.CNF.Clause ℕ)
    (l : Std.Sat.Literal ℕ) (hC : C ∈ φ) (hl : l ∈ C) : l.1 < φ.numVars := by
  apply Nat.lt_of_succ_le
  exact List.le_max_of_le
    (List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨l, hl, rfl⟩⟩) le_rfl

/-- A wired template retains its fixed size and width, and every actual
literal uses a permitted wire index. The wire function outside the
template's arity is irrelevant. -/
private lemma clTemplate_wiring (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool)
    (wire : ℕ → ℕ) (N : ℕ) (hwire : ∀ j < ℓ, wire j < N) :
    ((clTemplate ℓ p).relabel wire).length ≤ 2 ^ ℓ ∧
      ((clTemplate ℓ p).relabel wire).WidthAtMost ℓ ∧
      ∀ C ∈ (clTemplate ℓ p).relabel wire, ∀ l ∈ C, l.1 < N := by
  obtain ⟨hv, hc, hw, -⟩ := clTemplate_spec ℓ p
  refine ⟨by simpa [Std.Sat.CNF.relabel] using hc, ?_, ?_⟩
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    simpa [Std.Sat.CNF.Clause.relabel] using hw D hD
  · intro C hC l hl
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    obtain ⟨v, hvl, rfl⟩ := List.mem_map.mp hl
    exact hwire v.1 ((clLiteral_lt_numVars _ D v hD hvl).trans_le hv)

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

/-- The concrete pure formula has the audited `R+1` group count. -/
private lemma clTableauGroups_length (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e : ℕ) (x : List Bool) (T : ℕ) :
    (clTableauGroups M code C e x T).length = clLastRound x.length M.k T + 1 := by
  apply clGroups_length

/-- Ordered chunks of the concrete pure tableau serialize exactly that
tableau, including the empty-template and final-terminator cases. -/
private lemma clTableau_chunks (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e : ℕ) (x : List Bool) (T : ℕ) :
    (List.range (clLastRound x.length M.k T + 1)).flatMap
        (clChunk (clLastRound x.length M.k T)
          (fun i => (clTableauGroups M code C e x T)[i]?.getD [])) =
      Std.Sat.CNF.serialize (clTableau M code C e x T) := by
  apply clGroups_serialize

/-- Clause count, width, and literal-index bounds for a pure group. -/
private def CLBounds (K w N : ℕ) (φ : Std.Sat.CNF ℕ) : Prop :=
  φ.length ≤ K ∧ φ.WidthAtMost w ∧ ∀ C ∈ φ, ∀ l ∈ C, l.1 < N

/-- All valid template wires stay below the inclusive-horizon ceiling. -/
private lemma clGroup_bounds (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (kind : CLTemplateKind M.k) (m T s t p : ℕ)
    (hs : s ≤ T) (ht : t ≤ T) (hp : p < m + (T + 1) * clWidth M code) :
    CLBounds (2 ^ (2 * clWidth M code + 1)) (2 * clWidth M code + 1)
      (m + (T + 1) * clWidth M code) (clGroup M code kind m s t p) := by
  apply clTemplate_wiring
  intro j hj
  unfold clWire
  split
  · next h => exact clPack_lt m _ T s j hs h
  · split
    · next h₁ h₂ => exact clPack_lt m _ T t (j - clWidth M code) ht (by omega)
    · exact hp

/-- Positive code width makes the dummy index zero safe even at `m=T=0`. -/
private lemma clCeiling_pos (M : FinTM Bool) (code : CLFieldCode (Option M.State))
    (m T : ℕ) : 0 < m + (T + 1) * clWidth M code := by
  have hB : 0 < clWidth M code := by unfold clWidth; omega
  have hp : 0 < (T + 1) * clWidth M code := Nat.mul_pos (Nat.succ_pos T) hB
  omega

/-- Input-read wiring is bounded in both interior and boundary cases. -/
private lemma clInputGroup_bounds (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (m T t : ℕ) (ht : t ≤ T) :
    CLBounds (2 ^ (2 * clWidth M code + 1)) (2 * clWidth M code + 1)
      (m + (T + 1) * clWidth M code) (clInputGroup M code m t) := by
  unfold clInputGroup
  dsimp only
  split
  · next h => exact clGroup_bounds M code _ m T 0 t _ (Nat.zero_le _) ht (by omega)
  · exact clGroup_bounds M code _ m T 0 t 0 (Nat.zero_le _) ht
      (clCeiling_pos M code m T)

/-- The pure last-visit record is strictly earlier and is the greatest
earlier match, directly from its filtered-range maximum definition. -/
private lemma clPrev_spec (M : FinTM Bool) (m t s : ℕ) (τ : Fin M.k)
    (h : prevVisit M m t τ = some s) :
    s < t ∧ workPosAt M m s τ = workPosAt M m t τ ∧
      ∀ r, r < t → workPosAt M m r τ = workPosAt M m t τ → r ≤ s := by
  have hm := List.max?_eq_some_iff.mp h
  simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hm
  exact ⟨hm.1.1, hm.1.2, fun r hr he => hm.2 r ⟨hr, he⟩⟩

/-- Work-read wiring stays in the horizon, including first visits and
the final snapshot at time `T`. -/
private lemma clWorkGroup_bounds (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (m T t : ℕ) (τ : Fin M.k) (ht : t ≤ T) :
    CLBounds (2 ^ (2 * clWidth M code + 1)) (2 * clWidth M code + 1)
      (m + (T + 1) * clWidth M code) (clWorkGroup M code m t τ) := by
  unfold clWorkGroup
  cases h : prevVisit M m t τ with
  | none =>
    exact clGroup_bounds M code _ m T 0 t 0 (Nat.zero_le _) ht
      (clCeiling_pos M code m T)
  | some s =>
    have hs := (clPrev_spec M m t s τ h).1
    exact clGroup_bounds M code _ m T s t 0 (by omega) ht (clCeiling_pos M code m T)

/-- A pinning group fits the same positive-arity template envelope. -/
private lemma clPin_bounds (ℓ N j : ℕ) (b : Bool) (hℓ : 0 < ℓ) (hj : j < N) :
    CLBounds (2 ^ ℓ) ℓ N [[(j, b)]] := by
  refine ⟨by simpa using Nat.one_le_two_pow (n := ℓ), ?_, ?_⟩
  · simpa [Std.Sat.CNF.WidthAtMost] using hℓ
  · intro D hD l hl
    have hD' := List.mem_singleton.mp hD
    subst D
    have hl' := List.mem_singleton.mp hl
    subst l
    exact hj

/-- Every group of the concrete formula has one fixed template envelope.
The only growing quantities are the number of groups and wire indices.
**Proof sketch.** Split membership into the six ordered families. Pinning
uses original input indices; transition targets are at most `T`; input
and work groups use the proved boundary/previous-visit cases. -/
private lemma clTableauGroups_bounds (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e : ℕ) (x : List Bool) (T : ℕ) :
    ∀ g ∈ clTableauGroups M code C e x T,
      CLBounds (2 ^ (2 * clWidth M code + 1)) (2 * clWidth M code + 1)
        (x.length + C * (x.length + 1) ^ e + (T + 1) * clWidth M code) g := by
  let m := x.length + C * (x.length + 1) ^ e
  have hz := clCeiling_pos M code m T
  intro g hg
  change g ∈ clGroups x.length M.k T _ _ _ _ _ _ at hg
  simp only [clGroups, List.mem_append, List.mem_map, List.mem_singleton,
    List.mem_flatMap, List.mem_range, or_assoc] at hg
  rcases hg with hpin | hinit | hstate | hinput | hwork | haccept
  · obtain ⟨j, hj, rfl⟩ := hpin
    exact clPin_bounds _ _ j _ (by omega) (by omega)
  · subst g
    exact clGroup_bounds M code _ m T 0 0 0 (Nat.zero_le _) (Nat.zero_le _) hz
  · obtain ⟨t, ht, rfl⟩ := hstate
    exact clGroup_bounds M code _ m T t (t + 1) 0 (by omega) (by omega) hz
  · obtain ⟨t, ht, rfl⟩ := hinput
    exact clInputGroup_bounds M code m T t (by omega)
  · obtain ⟨t, ht, τ, hτ, heq⟩ := hwork
    rw [dif_pos hτ] at heq
    subst g
    exact clWorkGroup_bounds M code m T t ⟨τ, hτ⟩ (by omega)
  · obtain ⟨t, ht, rfl⟩ := haccept
    exact clGroup_bounds M code _ m T t 0 0 (by omega) (Nat.zero_le _) hz

/-- Concatenation adds clause counts and preserves widths and index
ceilings; no clause can be lost or reordered in this accounting. -/
private lemma clFlatten_bounds (gs : List (Std.Sat.CNF ℕ)) (K w N : ℕ)
    (h : ∀ g ∈ gs, CLBounds K w N g) :
    CLBounds (gs.length * K) w N gs.flatten := by
  induction gs with
  | nil => simp [CLBounds, Std.Sat.CNF.WidthAtMost]
  | cons g gs ih =>
    obtain ⟨hc, hw, hv⟩ := h g (by simp)
    obtain ⟨hct, hwt, hvt⟩ := ih (fun a ha => h a (by simp [ha]))
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatten_cons, List.length_append, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega
    · intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact hw D hD
      · exact hwt D hD
    · intro D hD l hl
      rcases List.mem_append.mp hD with hD | hD
      · exact hv D hD l hl
      · exact hvt D hD l hl

/-- Explicit output-length bound for the actual pure tableau. Both its
unary indices and its `R+1` family members are charged. -/
private lemma clTableau_length (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e : ℕ) (x : List Bool) (T : ℕ) :
    (Std.Sat.CNF.serialize (clTableau M code C e x T)).length ≤
      1 + ((clLastRound x.length M.k T + 1) * 2 ^ (2 * clWidth M code + 1)) *
        (2 + (x.length + C * (x.length + 1) ^ e +
          (T + 1) * clWidth M code + 2) * (2 * clWidth M code + 1)) := by
  obtain ⟨hc, hw, hv⟩ := clFlatten_bounds _ _ _ _ (clTableauGroups_bounds M code C e x T)
  rw [clTableauGroups_length] at hc
  exact clSerialize_uniform _ _ _ _ hc hw hv

/-- The audited output-size estimate is quadratic in the tableau horizon,
with a fully explicit constant depending only on the fixed machine/code.
It is not a runtime bound for the yet-unconstructed preparation machine.
**Proof sketch.** There are at most `(k+4)(T+1)` groups; the index ceiling
plus two is at most `(B+3)(T+1)`. Substitute these into the exact template
ledger and absorb the single terminator using `(T+1)^2 ≥ 1`. -/
private lemma clTableau_quadratic (M : FinTM Bool)
    (code : CLFieldCode (Option M.State)) (C e : ℕ) (x : List Bool) (T : ℕ)
    (hm : x.length + C * (x.length + 1) ^ e ≤ T) :
    (Std.Sat.CNF.serialize (clTableau M code C e x T)).length ≤
      (1 + (M.k + 4) * 2 ^ (2 * clWidth M code + 1) *
        (2 + (clWidth M code + 3) * (2 * clWidth M code + 1))) * (T + 1) ^ 2 := by
  let B := clWidth M code
  let K := 2 ^ (2 * B + 1)
  let w := 2 * B + 1
  have hn : x.length ≤ T := by omega
  have hr : clLastRound x.length M.k T + 1 ≤ (M.k + 4) * (T + 1) := by
    unfold clLastRound
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have hv : x.length + C * (x.length + 1) ^ e + (T + 1) * B + 2 ≤
      (B + 3) * (T + 1) := by
    rw [Nat.add_mul B 3 (T + 1), Nat.mul_comm B (T + 1)]
    omega
  have hw : 2 + (x.length + C * (x.length + 1) ^ e + (T + 1) * B + 2) * w ≤
      (2 + (B + 3) * w) * (T + 1) := by
    calc
      _ ≤ 2 + ((B + 3) * (T + 1)) * w :=
        Nat.add_le_add_left (Nat.mul_le_mul_right w hv) 2
      _ ≤ 2 * (T + 1) + ((B + 3) * (T + 1)) * w := by omega
      _ = _ := by ring
  have hsq : 1 ≤ (T + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos T)
  calc
    _ ≤ 1 + ((clLastRound x.length M.k T + 1) * K) *
        (2 + (x.length + C * (x.length + 1) ^ e + (T + 1) * B + 2) * w) :=
      clTableau_length M code C e x T
    _ ≤ 1 + ((M.k + 4) * (T + 1) * K) * ((2 + (B + 3) * w) * (T + 1)) :=
      Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_right K hr) hw) 1
    _ = 1 + ((M.k + 4) * K * (2 + (B + 3) * w)) * (T + 1) ^ 2 := by ring
    _ ≤ _ := by
      change 1 + ((M.k + 4) * K * (2 + (B + 3) * w)) * (T + 1) ^ 2 ≤
        (1 + (M.k + 4) * K * (2 + (B + 3) * w)) * (T + 1) ^ 2
      rw [Nat.add_mul 1 _ _, Nat.one_mul]
      exact Nat.add_le_add_right hsq _

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

/-- A ready native arithmetic producer, together with a polynomial bound
on its actual complete answer. The latter follows from one-bit-per-step
output, so all six retained fields are charged to the same runtime. -/
private lemma clPrepHeader_machine (C e c A d : ℕ) :
    ∃ (H : FinTM Bool) (a r : ℕ),
      H.ComputesFunInTime (clPrepHeader C e c A d) (fun n => a * (n + 1) ^ r) ∧
      ∀ x, (clPrepHeader C e c A d x).length ≤ a * (x.length + 1) ^ r := by
  obtain ⟨H, a, r, hH⟩ := clPrepHeader_native C e c A d
  refine ⟨H, a, r, hH, fun x => ?_⟩
  have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hH x)).2
  simpa only [ho] using H.tm.output_length_le x (a * (x.length + 1) ^ r)

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

/-- The silent virtual-reference stepper is a finite native machine.
It deliberately never physically halts: its surrounding bounded controller
is responsible for stopping at the horizon, including after an early source halt. -/
private def clRefTM (M : FinTM Bool) (l : ℕ) : FinTM Bool where
  k := l + (1 + M.k)
  State := Option M.State × Bool
  tm := {
    q₀ := (some M.tm.q₀, true)
    tr := fun q _ work => clRefAction M Prod.mk q.1 q.2 work (fun _ => (none, 0)) }

/-- The stepper preserves every represented source component at every
source time, while keeping its physical output and administrative bank fixed. -/
private lemma clRef_run (M : FinTM Bool) (l : ℕ) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin l → ℤ → Option Bool)
    (heads : Fin l → ℤ) (out : List Bool) (t : ℕ) :
    ∃ b', FinTM.VirtualTag (M.tm.runFrom c t).inputPos b' ∧
      (clRefTM M l).tm.runFrom (clRefCfg M Prod.mk c b p tapes heads out) t =
        clRefCfg M Prod.mk (M.tm.runFrom c t) b' p tapes heads out := by
  induction t with
  | zero => exact ⟨b, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b', hb', he⟩ := ih
    obtain ⟨b'', hb'', he'⟩ := clRef_apply M Prod.mk (M.tm.runFrom c t) b'
      hb' p tapes heads out (fun _ => (none, 0))
    refine ⟨b'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, MultiTapeTM.runFrom_succ_eq_step']
      simpa [MultiTapeTM.step, clRefTM, clRefCfg] using he'

/-- The prepared virtual-input seam has the genuine source initial state,
blank source tapes, zero work heads, and virtual input head one. The native
input can be arbitrary, independent of the virtual input and its length. -/
private lemma clRef_initial (M : FinTM Bool) (l : ℕ) (x y : List Bool)
    (words : Fin l → List Bool) :
    Cfg.ofWords (input := x) (clRefTM M l).tm.q₀
      (FinTM.tapeBlocks words y (fun _ => [])) =
      clRefCfg M Prod.mk (M.tm.initCfg y) true 1
        (fun i => FinTM.bufferTape (words i)) (fun _ => 0) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [Cfg.ofWords, clRefCfg]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [Cfg.ofWords, clRefCfg, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [Cfg.ofWords, clRefCfg]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [Cfg.ofWords, clRefCfg, MultiTapeTM.initCfg, Cfg.init]

/-- Native simulation realizes exactly the inherited reference schedule,
at every time including zero and all frozen times after source halting.
This is a running representation, not yet a serialized trajectory record. -/
private lemma clRef_schedule (M : FinTM Bool) (l m : ℕ) (x : List Bool)
    (words : Fin l → List Bool) (t : ℕ) :
    let start := Cfg.ofWords (input := x) (clRefTM M l).tm.q₀
      (FinTM.tapeBlocks words (List.replicate m false) (fun _ => []))
    let result := (clRefTM M l).tm.runFrom start t
    result.output = [] ∧ result.state ≠ none ∧ result.inputPos = 1 ∧
      result.workTapePos (Fin.natAdd l (Fin.castAdd M.k (0 : Fin 1))) =
        (inputPosAt M m t : ℤ) - 1 ∧
      (∀ i, result.workTapePos (Fin.natAdd l (Fin.natAdd 1 i)) = workPosAt M m t i) := by
  dsimp only
  rw [clRef_initial]
  obtain ⟨b, _, hr⟩ := clRef_run M l (M.tm.initCfg (List.replicate m false)) true
    (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) (1 : Fin (x.length + 2))
    (fun i => FinTM.bufferTape (words i)) (fun _ => 0) [] t
  rw [hr]
  delta inputPosAt workPosAt
  simp [clRefCfg]

/-- The bounded reference runner consumes one unary clock cell per source
step. Clock exhaustion dispatches to a live return state; source halting
does not dispatch. The initial configuration in its contract is prepared,
not claimed to arise from native initialization without header installation. -/
private def clRefClockTM (M : FinTM Bool) : FinTM Bool where
  k := 1 + (1 + M.k)
  State := (Option M.State × Bool) ⊕ Unit
  tm := {
    q₀ := .inl (some M.tm.q₀, true)
    tr := fun q _ work => match q with
      | .inr _ => FinTM.controlAction 0 (some (.inr ()))
      | .inl (s, b) =>
        if work (Fin.castAdd (1 + M.k) (0 : Fin 1)) = none then
          FinTM.controlAction 0 (some (.inr ()))
        else
          clRefAction M (fun q b => .inl (q, b)) s b work (fun _ => (none, .pos)) }

/-- Running configuration of the clocked reference component. Its clock
head records source time, separately from any future administrative cost. -/
private def clRefClockCfg (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (T t : ℕ) :
    Cfg (clRefClockTM M).k Bool (clRefClockTM M).State x :=
  clRefCfg M (fun q b => .inl (q, b)) c b 1
    (fun _ : Fin 1 => FinTM.bufferTape (List.replicate T true)) (fun _ => t) []

/-- A nonempty clock advances the represented configuration once and the
clock once. The complete post-transition source configuration is retained. -/
private lemma clRefClock_step (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (T t : ℕ) (ht : t < T) :
    ∃ b', FinTM.VirtualTag (M.tm.step c).inputPos b' ∧
      (clRefClockTM M).tm.step (clRefClockCfg M (x := x) c b T t) =
        clRefClockCfg M (M.tm.step c) b' T (t + 1) := by
  have hr : (clRefClockCfg M (x := x) c b T t).workTapeSymbols
      (Fin.castAdd (1 + M.k) (0 : Fin 1)) = some true := by
    simp [clRefClockCfg, clRefCfg, Cfg.workTapeSymbols, ht]
  obtain ⟨b', hb', he⟩ := clRef_apply M (fun q b => Sum.inl (q, b)) c b hb
    (1 : Fin (x.length + 2))
    (fun _ : Fin 1 => FinTM.bufferTape (List.replicate T true)) (fun _ => (t : ℤ)) []
    (fun _ => (none, .pos))
  refine ⟨b', hb', ?_⟩
  have hs : (clRefClockCfg M (x := x) c b T t).state = some (.inl (c.state, b)) := rfl
  simp only [MultiTapeTM.step, hs, clRefClockTM, hr, reduceCtorEq, if_false]
  simpa [clRefClockCfg, Nat.cast_add, Nat.cast_one] using he

/-- The inclusive source-time invariant holds at every time `0 ≤ t ≤ T`.
It is independent of any source halting-time or verdict assumption. -/
private lemma clRefClock_run (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (T t : ℕ) (ht : t ≤ T) :
    ∃ b', FinTM.VirtualTag (M.tm.runFrom c t).inputPos b' ∧
      (clRefClockTM M).tm.runFrom (clRefClockCfg M (x := x) c b T 0) t =
        clRefClockCfg M (M.tm.runFrom c t) b' T t := by
  induction t with
  | zero => exact ⟨b, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b', hb', hr⟩ := ih (by omega)
    obtain ⟨b'', hb'', hs⟩ := clRefClock_step M (x := x)
      (M.tm.runFrom c t) b' hb' T t (by omega)
    refine ⟨b'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
    · rw [MultiTapeTM.runFrom_succ_eq_step', hr, hs,
        MultiTapeTM.runFrom_succ_eq_step']

/-- The exhausted-clock dispatch takes one positive administrative step
and changes only control. In particular it does not advance source time. -/
private lemma clRefClock_return (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (T : ℕ) :
    (clRefClockTM M).tm.step (clRefClockCfg M (x := x) c b T T) =
      { clRefClockCfg M (x := x) c b T T with state := some (.inr ()) } := by
  have hr : (clRefClockCfg M (x := x) c b T T).workTapeSymbols
      (Fin.castAdd (1 + M.k) (0 : Fin 1)) = none := by
    simp [clRefClockCfg, clRefCfg, Cfg.workTapeSymbols]
  have hs : (clRefClockCfg M (x := x) c b T T).state = some (.inl (c.state, b)) := rfl
  simp only [MultiTapeTM.step, hs, clRefClockTM, hr, if_true]
  simpa only [moveInputPos_zero] using
    FinTM.controlAction_apply (clRefClockCfg M (x := x) c b T T) 0 (some (.inr ()))

/-- The clocked runner's entire boundary contract: exact `T+1` duration,
strict first return, complete final configuration, and an empty physical
output. This is a component return, not yet a clean packed-record seam.
**Proof sketch.** The inclusive invariant gives every prefix through `T`,
whose state is in the simulation summand. At `T` the clock is blank;
one silent control action enters the disjoint return summand. The record
on the right includes the source's effects at its final simulated step. -/
private lemma clRefClock_first (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (T : ℕ) :
    (∀ j, j < T + 1 →
      ((clRefClockTM M).tm.runFrom (clRefClockCfg M (x := x) c b T 0) j).state ≠
        some (.inr ())) ∧
    ∃ b', FinTM.VirtualTag (M.tm.runFrom c T).inputPos b' ∧
      (clRefClockTM M).tm.runFrom (clRefClockCfg M (x := x) c b T 0) (T + 1) =
        { clRefClockCfg M (x := x) (M.tm.runFrom c T) b' T T with state := some (.inr ()) } := by
  constructor
  · intro j hj
    obtain ⟨b', _, hr⟩ := clRefClock_run M (x := x) c b hb T j (by omega)
    rw [hr]
    simp [clRefClockCfg, clRefCfg]
  · obtain ⟨b', hb', hr⟩ := clRefClock_run M (x := x) c b hb T T le_rfl
    refine ⟨b', hb', ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hr, clRefClock_return]

/-- Genuine source initialization at the prepared clock/buffer seam.
This statement includes all source tapes and both administrative heads. -/
private lemma clRefClock_initial (M : FinTM Bool) (x y : List Bool) (T : ℕ) :
    Cfg.ofWords (input := x) (clRefClockTM M).tm.q₀
      (FinTM.tapeBlocks (fun _ : Fin 1 => List.replicate T true) y (fun _ => [])) =
      clRefClockCfg M (x := x) (M.tm.initCfg y) true T 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [Cfg.ofWords, clRefClockCfg, clRefCfg]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [Cfg.ofWords, clRefClockCfg, clRefCfg, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [Cfg.ofWords, clRefClockCfg, clRefCfg]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [Cfg.ofWords, clRefClockCfg, clRefCfg, MultiTapeTM.initCfg, Cfg.init]

/-! Native head-clCount component for the record producer. The carry
and rewind proofs below are harvested locally from
`ClassP/TimeConstructible.lean` at the required base, with a silent
absorbing return in place of that machine's input-scanning state. All
names are new privates; no private constant from another module is cited. -/

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

/-- The complete increment reaches its result at a strictly positive
first return, within two scans of the input counter plus two steps.
**Proof sketch.** Minimize the first return-state occurrence before the
proved completion time. Since that state is absorbing on the entire
configuration, its first occurrence already has the proved final word
and restored head. Initial carry control excludes duration zero. -/
private lemma clCount_first (x : List Bool) (p : Fin (x.length + 2)) (w : List Bool) :
    ∃ t ≤ 2 * w.length + 2, 0 < t ∧
      (∀ j, j < t → (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) j).state ≠ some (0 : Fin 4)) ∧
      clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) t =
        clCountCfg x 0 p 0 (clCountInc w) [] := by
  let B := 2 * clCountCarry w + 2
  have hfinish := clCount_run x p w
  have hex : ∃ t, t ≤ B ∧ (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) t).state = some (0 : Fin 4) :=
    ⟨B, le_rfl, by rw [hfinish]; rfl⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  have hp : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    have hs := ht.2
    change (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) t).state = some (0 : Fin 4) at hs
    rw [hz, MultiTapeTM.runFrom_zero] at hs
    norm_num [clCountCfg] at hs
  refine ⟨t, ht.1.trans (by dsimp [B]; have := clCountCarry_le w; omega), hp, ?_, ?_⟩
  · intro j hj hs
    have hmin := Nat.find_min' hex (show j ≤ B ∧
      (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) j).state = some (0 : Fin 4) from ⟨by omega, hs⟩)
    omega
  · have hstay := clCount_idle_run
      (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) t) ht.2 (B - t)
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
    exact hstay.symm.trans hfinish

/-- The harvested tape representation is the library's canonical buffer,
including every negative cell and both empty-word boundaries. -/
private lemma clCountTape_eq (w : List Bool) : clCountTape w = FinTM.bufferTape w := by
  funext z
  by_cases hz : z < 0 <;> simp [clCountTape, FinTM.bufferTape, hz, show 0 ≤ z ↔ ¬z < 0 by omega]

/-- The in-place binary counter has a complete clean seam contract.
It can update positive/negative movement counts without changing native
input, physical output, or any counter head at return. -/
private lemma clCount_seam (x : List Bool) (n : ℕ) :
    ∃ t ≤ 2 * n.bits.length + 2, 0 < t ∧
      (∀ j, j < t → (clCountTM.tm.runFrom
        (Cfg.ofWords (input := x) (1 : Fin 4) (stateWord 1 n.bits)) j).state ≠ some (0 : Fin 4)) ∧
      clCountTM.tm.runFrom (Cfg.ofWords (input := x) (1 : Fin 4) (stateWord 1 n.bits)) t =
        Cfg.ofWords (0 : Fin 4) (stateWord 1 (n + 1).bits) := by
  have he (q : Fin 4) (w : List Bool) :
      Cfg.ofWords (input := x) q (stateWord 1 w) = clCountCfg x q 1 0 w [] := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    simp [Cfg.ofWords, stateWord, clCountCfg, clCountTape_eq]
  obtain ⟨t, ht, hp, hf, hr⟩ := clCount_first x 1 n.bits
  refine ⟨t, ht, hp, ?_, ?_⟩
  · simpa only [he] using hf
  · simpa only [he, clCountInc_bits] using hr

/-- An administrative transition is framed away from the reference
buffer and source bank. It may rewrite and move administrative tapes,
but leaves every represented source component and the physical output
unchanged. This is the no-source-clock-advance boundary for recording. -/
private lemma clRef_admin (M : FinTM Bool) {l : ℕ} {S : Type}
    (emb next : Option M.State → Bool → S) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (out : List Bool)
    (ops : Fin l → Option (Option Bool) × SignType) :
    (⟨0, FinTM.tapeBlocks ops (none, 0) (fun _ => (none, 0)),
      none, some (next c.state b)⟩ : Action (l + (1 + M.k)) Bool S).apply
        (clRefCfg M emb c b p tapes heads out) =
      clRefCfg M next c b p
        (fun i => match (ops i).1 with
          | none => tapes i
          | some w => Function.update (tapes i) (heads i) w)
        (fun i => heads i + (ops i).2) out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [clRefCfg])
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

/-- Run an administrative binary-counter increment while retaining the
entire virtual reference configuration in a disjoint bank. The finite
control stores the source state and boundary tag throughout the call. -/
private def clRefCountTM (M : FinTM Bool) : FinTM Bool where
  k := 1 + (1 + M.k)
  State := Option M.State × Bool × Fin 4
  tm := {
    q₀ := (some M.tm.q₀, true, 1)
    tr := fun q inp work =>
      FinTM.leftAction (1 + M.k) (fun s => (q.1, q.2.1, s))
        (clCountTM.tm.tr q.2.2 inp (fun i => work (Fin.castAdd (1 + M.k) i))) }

/-- The generic left-bank embedding is exactly the reference frame with
one binary administrative counter, not merely equal on selected fields. -/
private lemma clRefCount_frame (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (q : Fin 4) (w : List Bool) :
    FinTM.leftCfg (fun s => (c.state, b, s)) (clCountCfg x q 1 0 w [])
      (Fin.addCases (fun _ : Fin 1 => FinTM.bufferTape y) c.workTapes)
      (Fin.addCases (fun _ : Fin 1 => (c.inputPos.val : ℤ) - 1) c.workTapePos) =
      clRefCfg M (fun s b => (s, b, q)) c b (1 : Fin (x.length + 2))
        (fun _ : Fin 1 => FinTM.bufferTape w) (fun _ => 0) [] := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [FinTM.leftCfg, clCountCfg, clRefCfg, clCountTape_eq]
  · intro j; simp [FinTM.leftCfg, clRefCfg, FinTM.tapeBlocks]

/-- A complete native counter update consumes physical time without
advancing the represented source clock or disturbing any source tape or
head. The counter returns canonical binary successor, with strict first
return and an explicit sequential-scan bound.
**Proof sketch.** Lift the proved in-place counter into the left bank.
The right bank contains the virtual input and every source tape and head;
the public disjoint-bank run theorem preserves that whole bank. The
injective counter-state projection transfers the first-return property. -/
private lemma clRefCount_first (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (b : Bool) (n : ℕ) :
    ∃ t ≤ 2 * n.bits.length + 2, 0 < t ∧
      (∀ j, j < t →
        ((clRefCountTM M).tm.runFrom
          (clRefCfg M (fun s b => (s, b, (1 : Fin 4))) c b (1 : Fin (x.length + 2))
            (fun _ : Fin 1 => FinTM.bufferTape n.bits) (fun _ => 0) []) j).state ≠
          some (c.state, b, (0 : Fin 4))) ∧
      (clRefCountTM M).tm.runFrom
        (clRefCfg M (fun s b => (s, b, (1 : Fin 4))) c b (1 : Fin (x.length + 2))
          (fun _ : Fin 1 => FinTM.bufferTape n.bits) (fun _ => 0) []) t =
        clRefCfg M (fun s b => (s, b, (0 : Fin 4))) c b (1 : Fin (x.length + 2))
          (fun _ : Fin 1 => FinTM.bufferTape (n + 1).bits) (fun _ => 0) [] := by
  obtain ⟨t, ht, hp, hf, hr⟩ := clCount_first x 1 n.bits
  have lift (j : ℕ) := FinTM.leftCfg_run clCountTM.tm (clRefCountTM M).tm
    (fun s => (c.state, b, s)) (fun _ _ _ => rfl) (clCountCfg x 1 1 0 n.bits [])
    (Fin.addCases (fun _ : Fin 1 => FinTM.bufferTape y) c.workTapes)
    (Fin.addCases (fun _ : Fin 1 => (c.inputPos.val : ℤ) - 1) c.workTapePos) j
  refine ⟨t, ht, hp, ?_, ?_⟩
  · intro j hj hs
    have hequiv := congrArg Cfg.state (lift j)
    have hs' : (FinTM.leftCfg (fun s => (c.state, b, s))
        (clCountTM.tm.runFrom (clCountCfg x 1 1 0 n.bits []) j)
        (Fin.addCases (fun _ : Fin 1 => FinTM.bufferTape y) c.workTapes)
        (Fin.addCases (fun _ : Fin 1 => (c.inputPos.val : ℤ) - 1) c.workTapePos)).state =
          some (c.state, b, (0 : Fin 4)) := by
      apply hequiv.symm.trans
      simpa [FinTM.leftCfg, clCountCfg, clRefCfg, FinTM.tapeBlocks, clCountTape_eq] using hs
    apply hf j hj
    have he := congrArg (fun s => s.map (fun z => z.2.2)) hs'
    simpa only [FinTM.leftCfg, Option.map_map, Function.comp_def, Option.map_id',
      Option.map_some] using he
  · have h := lift t
    rw [hr, clCountInc_bits] at h
    simpa [FinTM.leftCfg, clCountCfg, clRefCfg, FinTM.tapeBlocks, clCountTape_eq] using h

/-- A counter below `2^w` occupies at most `w` bits. Together with
`clRefCount_first`, this charges one administrative increment by two
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

/-- The reference component's `T+1` physical-step cost is polynomial in
the original instance length. This is only its component budget; record
scans, searches, cleanup, and emission still need their separate common `P`. -/
private lemma clRefClock_bound (C e c A d n : ℕ) :
    c * (A * (n + C * (n + 1) ^ e + 1) ^ d + 1) ^ 2 + 1 ≤
      (c * (A * (C + 1) ^ d + 1) ^ 2 + 1) *
        (n + 1) ^ (2 * d * max 1 e) := by
  have h := clHorizon_upper C e c A d n
  have hp : 1 ≤ (n + 1) ^ (2 * d * max 1 e) := Nat.one_le_pow _ _ (Nat.succ_pos n)
  rw [Nat.add_mul, Nat.one_mul]
  omega

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
  sorry

/-- **Theorem 2.10.1 (Cook-Levin)** [AB09]: `SAT` is `NP`-complete.

**Proof sketch.** `Complexity.SAT_mem_NP` and `Complexity.SAT_NPHard`,
assembled by the definition of `Complexity.NPComplete`. -/
theorem SAT_NPComplete : NPComplete SAT := by
  sorry

/-- **`3SAT` is `NP`-hard** [AB09, Theorem 2.10.2, hardness half]:
Cook-Levin followed by clause splitting.

**Proof sketch.** `Complexity.SAT_NPHard` transferred along
`Complexity.SAT_reducible_SAT3` (Lemma 2.14) by
`Complexity.NPHard.polyTimeReducible`. -/
theorem SAT3_NPHard : NPHard SAT3 := by
  sorry

/-- **Theorem 2.10.2** [AB09]: `3SAT` is `NP`-complete.

**Proof sketch.** `Complexity.SAT3_mem_NP` and `Complexity.SAT3_NPHard`. -/
theorem SAT3_NPComplete : NPComplete SAT3 := by
  sorry

end Complexity
