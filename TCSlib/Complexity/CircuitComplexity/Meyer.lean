/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerSigma
import TCSlib.Complexity.CircuitComplexity.MeyerSigmaEXP
import TCSlib.Complexity.PolyHierarchy.Collapse
import TCSlib.Complexity.TimeHierarchy.Separation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem

[AB09, Thm 6.20] (Meyer): **if `EXP ⊆ P/poly` then `EXP = Σ₂ᵖ`**, and its consequence
[AB09, p. 115]: **if `P = NP` then `EXP ⊄ P/poly`**. The inclusion `Σ₂ᵖ ⊆ EXP` is
unconditional (`Complexity.SigmaP_two_subset_EXP`, `MeyerSigmaEXP.lean`); the content of
the theorem is `EXP ⊆ Σ₂ᵖ`.

## The proof

Let `L ∈ EXP` be decided by `M` within `c₀ · 2^{n^c}` steps. The *tableau language*
`Tab M` (`MeyerTab.lean`) — "the bit selected by `sel` of the configuration of `M` on `x`
after `t` steps, at offset `±a` from a head" — is in `EXP`, decided by the machine
`tabTM M` (`MeyerMachine*.lean`). Under `EXP ⊆ P/poly` it has polynomial-size circuits.
Then

`x ∈ L ⟺ ∃ U ∀ (t, a, j, p) : (t, a, j, p) is not a counterexample for U`,

where `U` pads the description of a circuit guessed to compute the tableau at the query
length of `x`, and the counterexamples (`MeyerVerifier.lean`) are the failures of the
local checks — initial row, step rule, final row — evaluated with the circuit evaluator
`CVAL`. If `x ∈ L`, the true circuit passes all checks (`complete_numeric`); if a guessed
circuit passes all checks, it computes the true tableau row by row, so the true run
accepts (`sound_numeric`). The inner language is in `coNP`, so `L ∈ Σ₂ᵖ`.

## Divergences from [AB09]

* **Head-relative tableau instead of oblivious snapshots.** The book makes `M` oblivious
  and has the verifier compute, for each snapshot index, the indices of the previous
  visits of each head ("these indices can be represented in polynomial time"). That
  computation is exponentially long for the obliviousness construction available here
  (`Complexity.oblivious_of_mem_DTIME`, whose schedule is only existential). Instead the
  guessed tableau records, for every time `t`, each tape's contents *relative to its
  head*; one step changes such a row only locally (cell `d` becomes the old cell `d + m`,
  or the written symbol), so the checks need only increments, unary input indices and
  `CVAL` queries. Work-tape offsets are sound inside a light cone; input offsets range
  over `[-(n+1), n+1]` with an explicit boundary rule.
* **Width.** Times and offsets are words of the explicit width `W = (c₀+3)(n+1)^{c+1}`,
  so `2^W - 1` bounds the running time; the final check is at time `2^W - 1`.
* **`Σ₂ᵖ ⊆ EXP`** (used tacitly by the book) is proved in `MeyerSigmaEXP.lean` through a
  the brute-force enumerator of `ClassNP/EXP.lean` with an arbitrary-time verifier
  (`Complexity.exists_proj_decider`).
* **The time hierarchy** enters through `Complexity.P_ne_EXP`, proved in
  `TimeHierarchy/Separation.lean` with the library's quadratic universal-machine overhead.

## Main definitions

None.

## Main results

* `Complexity.Meyer.width_ok` — the width suffices; `Complexity.Meyer.mem_iff_final` —
  acceptance in the final row; `Complexity.Meyer.desc_len_le` — the guessed description
  has polynomial length.

* `Complexity.EXP_subset_SigmaP_two_of_EXP_subset_PPoly` — the inclusion `EXP ⊆ Σ₂ᵖ`.
* `Complexity.EXP_eq_SigmaP_two_of_EXP_subset_PPoly` — [AB09, Thm 6.20].
* `Complexity.not_EXP_subset_PPoly_of_P_eq_NP` — [AB09, p. 115, corollary of Thm 6.20].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1; §5.2, Theorem 5.4; §6.4,
  Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing BoolCircuit Complexity.TimeHierarchy Complexity.PolyHierarchy

/-! ### The width -/

/-- `(n + 1)^{c+1} ≥ n^c + n`. -/
theorem pow_succ_ge (n c : ℕ) : n ^ c + n ≤ (n + 1) ^ (c + 1) := by
  have h1 : n ^ c ≤ (n + 1) ^ c := Nat.pow_le_pow_left (by omega) c
  have h2 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  nlinarith

/-- **The width suffices**: with `W = (c₀ + 3)(n + 1)^{c+1}`, the last time `2^W - 1`
bounds the running time `c₀ 2^{n^c}`, and input offsets `≤ n + 2` fit in `W` bits.

**Proof sketch.** Since `(n+1)^{c+1} ≥ n^c + n`, `W ≥ c₀ + n^c + n + 2`, so `2^W ≥ 2^{c₀}
2^{n^c} 2^{n+2}`; bound `2^{c₀} ≥ c₀ + 1` and `2^{n+2} > n + 2`. -/
theorem width_ok (c₀ c n : ℕ) :
    n + 2 < 2 ^ wd (c₀ + 3) (c + 1) n ∧ c₀ * 2 ^ n ^ c ≤ 2 ^ wd (c₀ + 3) (c + 1) n - 1 := by
  have hX := pow_succ_ge n c
  have hX1 : 1 ≤ (n + 1) ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
  have hW : c₀ + n ^ c + (n + 2) ≤ wd (c₀ + 3) (c + 1) n := by
    unfold wd; nlinarith
  have h2 : 2 ^ (c₀ + n ^ c + (n + 2)) ≤ 2 ^ wd (c₀ + 3) (c + 1) n :=
    Nat.pow_le_pow_right (by omega) hW
  rw [pow_add, pow_add] at h2
  have ha : c₀ + 1 ≤ 2 ^ c₀ := Nat.lt_two_pow_self
  have hb : n + 2 < 2 ^ (n + 2) := Nat.lt_two_pow_self
  have hc : 1 ≤ 2 ^ n ^ c := Nat.one_le_two_pow
  have hp : 0 < 2 ^ c₀ * 2 ^ n ^ c := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  constructor
  · calc n + 2 < 2 ^ (n + 2) := hb
      _ ≤ 2 ^ c₀ * 2 ^ n ^ c * 2 ^ (n + 2) := Nat.le_mul_of_pos_left _ hp
      _ ≤ _ := h2
  · have e1 : (c₀ + 1) * 2 ^ n ^ c * (n + 2) ≤ 2 ^ c₀ * 2 ^ n ^ c * 2 ^ (n + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul ha le_rfl) hb.le
    have e2 : c₀ * 2 ^ n ^ c + 1 ≤ (c₀ + 1) * 2 ^ n ^ c := by
      rw [Nat.add_mul, one_mul]; omega
    have e3 : (c₀ + 1) * 2 ^ n ^ c ≤ (c₀ + 1) * 2 ^ n ^ c * (n + 2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- **Acceptance in the final row**: if `M` decides `L` within `c₀ 2^{n^c}` steps, then
`x ∈ L` iff the run is halted with output summary `one true` at time `2^W - 1`. -/
theorem mem_iff_final {L : Language Bool} {M : FinTM Bool} {c₀ c : ℕ}
    (hM : M.DecidesInTime L fun n => c₀ * 2 ^ n ^ c) (x : List Bool) :
    x ∈ L ↔ SS (M.tm.runFrom (M.tm.initCfg x) (2 ^ wd (c₀ + 3) (c + 1) x.length - 1)) =
      (none, OutReg.one true) := by
  have h := ((hM x).mono (width_ok c₀ c x.length).2)
  rw [Turing.FinTM.computesInTime_iff] at h
  obtain ⟨h1, h2⟩ := h
  simp only [SS, h1, h2, OutReg.ofList, Prod.mk.injEq, true_and]
  simp only [MultiTapeTM.indicator]
  by_cases hx : x ∈ L <;> simp [hx]

/-! ### The guessed description -/

/-- **The guessed description has polynomial length** [AB09, Thm 6.20 proof: "a
`q(n)`-sized circuit `C`"]: the description of a size-`a(n+1)^k` fan-in-two family's
circuit for the query length `nbits + 4W + 4 + n`, plus one marker bit, fits in
`(12 a² K^{2k} + 1)(n + 1)^{2(cw+1)k}` bits, `K = nbits + 4 Cw + 6`.

**Proof sketch.** The query length plus one is at most `K (n + 1)^{cw+1}`; the size bound
and `length_encode_le_of_isFaninTwo` (`|⌜C⌝| ≤ 12 S²`) give the bound. -/
theorem desc_len_le {a k : ℕ} (Cw cw nb : ℕ) {F : DAGCircuitFamily} (hF : F.HasFaninTwo)
    (hS : ∀ n, (F.circuit n).size ≤ a * (n + 1) ^ k) (n : ℕ) :
    (F.circuit (nb + 2 * wd Cw cw n + 2 * wd Cw cw n + 4 + n)).encode.length + 1 ≤
      (12 * a ^ 2 * (nb + 4 * Cw + 6) ^ (2 * k) + 1) * (n + 1) ^ (2 * (cw + 1) * k) := by
  set P := (n + 1) ^ (cw + 1) with hP
  set K := nb + 4 * Cw + 6 with hK
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hn1 : n + 1 ≤ P := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hWP : wd Cw cw n ≤ Cw * P :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hq : nb + 2 * wd Cw cw n + 2 * wd Cw cw n + 4 + n + 1 ≤ K * P := by
    have : K * P = nb * P + 4 * (Cw * P) + 6 * P := by rw [hK]; ring
    rw [this]
    have : nb ≤ nb * P := Nat.le_mul_of_pos_right _ hP1
    omega
  have hsize : (F.circuit (nb + 2 * wd Cw cw n + 2 * wd Cw cw n + 4 + n)).size ≤
      a * K ^ k * P ^ k := by
    calc _ ≤ a * (nb + 2 * wd Cw cw n + 2 * wd Cw cw n + 4 + n + 1) ^ k := hS _
      _ ≤ a * (K * P) ^ k := Nat.mul_le_mul_left a (Nat.pow_le_pow_left hq k)
      _ = _ := by rw [mul_pow, mul_assoc]
  have henc := DAGCircuit.length_encode_le_of_isFaninTwo _
    (hF (nb + 2 * wd Cw cw n + 2 * wd Cw cw n + 4 + n))
  have hPk : P ^ (2 * k) = (n + 1) ^ (2 * (cw + 1) * k) := by
    rw [hP, ← pow_mul]; ring_nf
  have hone : 1 ≤ (n + 1) ^ (2 * (cw + 1) * k) := Nat.one_le_pow _ _ (by omega)
  have hsq := Nat.pow_le_pow_left hsize 2
  calc _ ≤ 12 * (a * K ^ k * P ^ k) ^ 2 + 1 := by omega
    _ = 12 * a ^ 2 * K ^ (2 * k) * (n + 1) ^ (2 * (cw + 1) * k) + 1 := by
        rw [← hPk]; ring
    _ ≤ _ := by nlinarith

/-- The in-range instance of numbers `(t, a, j)` satisfies the range atom.

**Proof sketch.** The words `enumWord W t`, `enumWord W a` have width `W`; the padded code `bits j
++ 0^{W - |bits j|}` has length `W` because `|bits j| = size j ≤ W` for `j < 2^W`. -/
theorem lenAll_inst (M : FinTM Bool) (Cw cw : ℕ) (x U : List Bool) {t a j : ℕ}
    (hj : j ≤ x.length + 1) (hjW : j < 2 ^ wd Cw cw x.length) :
    evalAtom Cw cw M .lenAll (vin x U (enumWord (wd Cw cw x.length) t) (enumWord (wd Cw cw x.length) a)
      (List.replicate j true)
      (List.replicate (wd Cw cw x.length - (Nat.bits j).length) false)) = true := by
  have hb : (Nat.bits j).length ≤ wd Cw cw x.length := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr hjW
  simp only [evalAtom, vt_vin, va_vin, vj_vin, vx_vin, bjw, vp_vin, length_enumWord,
    List.length_replicate, List.length_append, decide_eq_true_eq]
  refine ⟨trivial, trivial, hj, by omega⟩

end Complexity.Meyer

namespace Complexity

open Turing BoolCircuit Meyer Complexity.TimeHierarchy Complexity.PolyHierarchy
  Complexity.KarpLipton

/-- **Meyer's theorem, the main inclusion** [AB09, Thm 6.20, proof]: if `EXP ⊆ P/poly`
then every `EXP` language is in `Σ₂ᵖ`.

Here `P/poly` is `BoolCircuit.PPoly` (polynomial-size fan-in-two families of the book's
circuit model, [AB09, Def 6.5]) and `Σ₂ᵖ` is `Complexity.SigmaP 2` ([AB09, Def 5.3]).
Divergence (see the module docstring): the guessed tableau is head-relative rather than
the book's oblivious snapshots.

**Proof sketch.** Let `M` decide `L` within `c₀ 2^{n^c}`; its tableau language is in
`EXP` (`Tab_mem_EXP`), hence decided by a polynomial-size fan-in-two family `F`. Then
`x ∈ L ⟺ ∃ U (|U| = B(|x|+1)^b), ⟨x, U⟩ ∈ innerLang`, a `Σ₂ᵖ` formula since
`innerLang ∈ coNP`: (⇒) pad the description of `F`'s circuit for the query length of `x`
(`desc_len_le`); on every in-range instance the atoms are the numeric valuation of
`F`'s truthful answers (`atoms_vin`, `ansD_family`), which pass every check
(`complete_numeric`) because `M` accepts by time `2^W - 1` (`mem_iff_final`); (⇐) the
in-range instances give the hypothesis of `sound_numeric`, so the true run accepts. -/
theorem EXP_subset_SigmaP_two_of_EXP_subset_PPoly (h : EXP ⊆ BoolCircuit.PPoly) :
    EXP ⊆ SigmaP 2 := by
  intro L hL
  obtain ⟨c, c₀, M, hM⟩ := Set.mem_iUnion.mp hL
  obtain ⟨a, k, F, hF, hS, hFL⟩ := h (Tab_mem_EXP M)
  refine mem_SigmaP_two_iff.mpr ⟨12 * a ^ 2 * (nbits M + 4 * (c₀ + 3) + 6) ^ (2 * k) + 1,
    2 * (c + 1 + 1) * k, innerLang (c₀ + 3) (c + 1) M, innerLang_mem_coNP _ _ M, fun x => ?_⟩
  have hn := (width_ok c₀ c x.length).1
  have hfin := mem_iff_final hM x
  constructor
  · -- completeness: the true circuit passes every check
    intro hx
    have hacc := hfin.mp hx
    set W := wd (c₀ + 3) (c + 1) x.length with hW
    set d := (F.circuit (nbits M + 2 * W + 2 * W + 4 + x.length)).encode with hd
    have hlen := desc_len_le (c₀ + 3) (c + 1) (nbits M) hF hS x.length
    rw [← hW, ← hd] at hlen
    refine ⟨List.replicate ((12 * a ^ 2 * (nbits M + 4 * (c₀ + 3) + 6) ^ (2 * k) + 1) *
        (x.length + 1) ^ (2 * (c + 1 + 1) * k) - d.length - 1) true ++ false :: d, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    · intro v hv
      set U := List.replicate ((12 * a ^ 2 * (nbits M + 4 * (c₀ + 3) + 6) ^ (2 * k) + 1) *
        (x.length + 1) ^ (2 * (c + 1 + 1) * k) - d.length - 1) true ++ false :: d with hU
      have hDU : dropMarker U = d := by rw [hU, dropMarker_marker]
      set z := pairEncode (pairEncode x U) v with hz
      have hcong : (fun α => evalAtom (c₀ + 3) (c + 1) M α z) =
          fun α => evalAtom (c₀ + 3) (c + 1) M α (vin x U (vt z) (va z) (vj z) (vp z)) := by
        funext α
        apply evalAtom_congr <;> simp [vx, vD, vt, va, vj, vp, z, vin]
      change badF M (fun α => evalAtom (c₀ + 3) (c + 1) M α z) = true at hv
      rw [hcong] at hv
      simp only [badF, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hv
      obtain ⟨hlenA, hnot⟩ := hv
      have hat := atoms_vin (M := M) (c₀ + 3) (c + 1) x U (vt z) (va z) (vj z) (vp z) hn hlenA
      rw [hat] at hnot
      apply hnot
      have hrange := hlenA
      simp only [evalAtom, vt_vin, va_vin, vj_vin, vx_vin, decide_eq_true_eq] at hrange
      obtain ⟨h1, h2, h3, -⟩ := hrange
      have hT : ∀ sel t a, t < 2 ^ W → a < 2 ^ W →
          AnsOf M W x (dropMarker U) sel t a =
            tabAns M sel (M.tm.runFrom (M.tm.initCfg x) t) a := by
        intro sel t a ht ha
        rw [hDU, hd]
        exact ansD_family hF hFL W x sel t a ht ha
      have hgood := complete_numeric (M := M) (Ans := AnsOf M W x (dropMarker U)) (W := W)
        (x := x) hT (xb := xbOf x) (fun j hj => xbOf_eq x j hj) hn hacc
      exact hgood _ _ _ (by have := ctrVal_lt (vt z); rwa [h1] at this)
        (by have := ctrVal_lt (va z); rwa [h2] at this) h3
  · -- soundness: a description passing every check certifies acceptance
    rintro ⟨U, -, hU⟩
    apply hfin.mpr
    set W := wd (c₀ + 3) (c + 1) x.length with hW
    refine sound_numeric (Ans := AnsOf M W x (dropMarker U)) (xb := xbOf x) ?_
      (fun j hj => xbOf_eq x j hj)
    intro t a j ht ha hj
    have hjW : j < 2 ^ W := by omega
    have hz := hU (pairEncode (pairEncode (enumWord W t) (enumWord W a))
      (pairEncode (List.replicate j true) (List.replicate (W - (Nat.bits j).length) false)))
    have hlenA := lenAll_inst M (c₀ + 3) (c + 1) x U (t := t) (a := a) hj hjW
    have hat := atoms_vin (M := M) (c₀ + 3) (c + 1) x U _ _ _ _ hn hlenA
    simp only [← hW] at hat
    simp only [List.length_replicate, ctrVal_enumWord W t ht, ctrVal_enumWord W a ha] at hat
    change ¬ (badF M (fun α => evalAtom (c₀ + 3) (c + 1) M α (vin x U _ _ _ _)) = true) at hz
    rw [hat] at hz
    simp only [badF, NumVal, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not,
      not_not] at hz
    exact hz

/-- **Meyer's theorem** [AB09, Thm 6.20]: if `EXP ⊆ P/poly` then `EXP = Σ₂ᵖ`.

**Proof sketch.** `EXP ⊆ Σ₂ᵖ` is `EXP_subset_SigmaP_two_of_EXP_subset_PPoly`; the converse
`Σ₂ᵖ ⊆ EXP` holds unconditionally (`SigmaP_two_subset_EXP`). -/
theorem EXP_eq_SigmaP_two_of_EXP_subset_PPoly (h : EXP ⊆ BoolCircuit.PPoly) :
    EXP = SigmaP 2 :=
  Set.Subset.antisymm (EXP_subset_SigmaP_two_of_EXP_subset_PPoly h) SigmaP_two_subset_EXP

/-- **`P = NP` implies `EXP ⊄ P/poly`** [AB09, p. 115, after Thm 6.20]: "if `P = NP`, then
`P = Σ₂ᵖ` (Thm 5.4), and so if `EXP ⊆ P/poly` we'd get `P = EXP`, contradicting the Time
Hierarchy Theorem (Thm 3.1)."

**Proof sketch.** Under `EXP ⊆ P/poly`, Meyer's theorem gives `EXP ⊆ Σ₂ᵖ ⊆ PH`, and
`P = NP` collapses `PH = P` (`Complexity.PH_eq_P_of_P_eq_NP`), so `EXP ⊆ P ⊆ EXP`,
contradicting `Complexity.P_ne_EXP`. -/
theorem not_EXP_subset_PPoly_of_P_eq_NP (h : P = NP) : ¬ EXP ⊆ BoolCircuit.PPoly := by
  intro hE
  have h1 : EXP ⊆ P := by
    rw [← PH_eq_P_of_P_eq_NP h]
    exact (EXP_subset_SigmaP_two_of_EXP_subset_PPoly hE).trans (SigmaP_subset_PH 2)
  exact P_ne_EXP (Set.Subset.antisymm P_subset_EXP h1)

end Complexity
