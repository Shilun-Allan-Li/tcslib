/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Complexity.BranchingPrograms.Eval
import TCSlib.Complexity.BranchingPrograms.Barrington

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Homomorphic evaluation of permutation branching programs and formulas (GSW)

## Main definitions

* `select`: the homomorphic selector `select P C U V = (G − C) ⊡ U + C ⊡ V`, fresh selector
  on the left.
* `homEvalPBP`: a branching program run homomorphically, the shared host
  `BranchingProgram.evalWith` (registry row H18) instantiated with `select P`.
* `homEvalFormula`: a fan-in-2 formula through Barrington's program (output `sigma1`), read at
  coordinate `sigma1 0`.

## Main results

* `Encrypts.select` (G1): one selector step costs an additive `2·N·β`.
* `encrypts_homEvalPBP` (G2): a permutation program of length `L` gives noise `L·2·N·β`.
* `encrypts_homEvalFormula` (G3): a formula of depth `d` gives noise `4^d·2·N·β`.

All three are proved here; the definitions are total and computable.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §3.3 (Eq. (4), Eval with Eq. (5)–(6)), Thm 3.5, Lemma 3.6 with its
  proof.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: Eq. (4.1), Lemma 4.1.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, §6.1.3 (bootstrapping).
* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1) (1989), 150–164: Thm 1.

**Deviations.** The selector carries the fresh ciphertext on the left of both products
(`(G − C) ⊡ U`, `C ⊡ V`), mirroring [BV14, Eq. (5)–(6)], which multiplies the state on the
left; with the library's `⊡` (`GSW.mul`, right operand decomposed) this order makes the noise
of a step additive in the state's noise. Noise bounds are worst case, not probabilistic
([BV14, Lemma 3.6] holds with overwhelming probability). The formula's output is coordinate
`σ 0` of the state started at `0` (Barrington's C16 reading), not [BV14]'s coordinate `1`:
a five-cycle moves `0`, so coordinate `0` would encode the complement.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit

/-- **The homomorphic selector** `select P C U V = (G − C) ⊡ U + C ⊡ V`: if `C` encrypts the
bit `b`, the result encrypts `(1 − b)·u + b·v`, selecting `U`'s message when `b = 0` and `V`'s
when `b = 1` [BV14, §3.3, Eq. (5)–(6), p014-b002, mirrored; AP14, Eq. (4.1), p011-b001].
The fresh selector ciphertext is on the left of both products (Gate 41's convention). -/
def select (P : Parameters) (C U V : Ciphertext P) : Ciphertext P :=
  mul P (gadget P - C) U + mul P C V

/-- `select P C U V` is `mul P (gadget P - C) U + mul P C V`. -/
theorem select_eq (P : Parameters) (C U V : Ciphertext P) :
    select P C U V = mul P (gadget P - C) U + mul P C V := rfl

/-- **Homomorphic evaluation of a branching program**: the host
`BranchingProgram.evalWith` (H18) with values and selectors in `Ciphertext P` and selector
`select P`, `homEvalPBP P B cts V = B.evalWith (select P) cts V`; instruction `ι` selects with
the input ciphertext `cts ι.var` [BV14, §3.3, Eval, p014-b002; AP14, Eq. (4.1), p011-b001].
For a permutation program each step is the pull form `V'_i = select (cts var) (V (σ₀⁻¹ i))
(V (σ₁⁻¹ i))` (`Instr.stepWith_of_isPermutation`). Computable. -/
def homEvalPBP (P : Parameters) {w k : ℕ} (B : BranchingProgram w k)
    (cts : Fin k → Ciphertext P) (V : Fin w → Ciphertext P) : Fin w → Ciphertext P :=
  B.evalWith (select P) cts V

/-- `homEvalPBP P B cts V` is `B.evalWith (select P) cts V`. -/
theorem homEvalPBP_eq (P : Parameters) {w k : ℕ} (B : BranchingProgram w k)
    (cts : Fin k → Ciphertext P) (V : Fin w → Ciphertext P) :
    homEvalPBP P B cts V = B.evalWith (select P) cts V := rfl

/-- **Homomorphic evaluation of a formula** [BV14, §3.3, Eval, p014-b002, with Thm 3.5,
p014-b001; Pei16, §6.1.3, p070-b001]: convert the formula `c` on `k ≥ 1` inputs to
Barrington's width-5 permutation program with output five-cycle `sigma1`, run it
homomorphically from the state `Pi.single 0 G` (an encryption of the one-hot state `0` with
zero noise), and read coordinate `sigma1 0`:
`homEvalFormula P c cts = homEvalPBP P (barrington c sigma1) cts (Pi.single 0 (gadget P))
(sigma1 0)`. Deviation: [BV14] outputs the state's coordinate `1`; here the accepting
coordinate is `σ 0` (`barrington_yield_zero`, r3 §H3.7). Computable (P6-Q13). -/
def homEvalFormula (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) : Ciphertext P :=
  homEvalPBP P (BranchingProgram.barrington c BranchingProgram.sigma1) cts
    (Pi.single 0 (gadget P)) (BranchingProgram.sigma1 0)

/-- `homEvalFormula P c cts` is `homEvalPBP P (barrington c sigma1) cts (Pi.single 0 (gadget P))`
at coordinate `sigma1 0`. -/
theorem homEvalFormula_eq (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) :
    homEvalFormula P c cts =
      homEvalPBP P (BranchingProgram.barrington c BranchingProgram.sigma1) cts
        (Pi.single 0 (gadget P)) (BranchingProgram.sigma1 0) := rfl

/-! ### Targets G1–G3 -/

/-- **G1. The selector step.** If `C` encrypts a bit `b ∈ {0, 1}` with noise at most `β` and
`U`, `V` encrypt `u`, `v` with noise at most `βV`, all under the key vector `t`, then
`select P C U V` encrypts `(1 − b)·u + b·v` with noise at most `βV + 2·(N·β)`, `N = P.columns`:
`Encrypts P t ((1 - b) * u + b * v) (βV + 2 * (P.columns * β)) (select P C U V)`
[BV14, §3.3, Eq. (5)–(6), p014-b002; Lemma 3.6 proof, p015-b002, mirrored; AP14, Eq. (4.1),
p011-b001; Lemma 4.1, p012-b001]. Deviation: worst case, and the selector sits on the left.

**Proof sketch.** `encrypts_gadget` and `Encrypts.sub` give `G − C` encrypting `1 − b` with
noise `0 + β`; `select_eq` exposes the two products `(G − C) ⊡ U` and `C ⊡ V`. Case on
`b ∈ {0, 1}`. The product whose left operand encrypts the bit `1` is `Encrypts.mul_bit`, with
noise `N·β + βV`; the other left operand encrypts `0`, and `Encrypts.mul` gives noise
`N·β + |0|·βV = N·β`. `Encrypts.add` sums the two, the message is `(1 − b)·u + b·v`, and the
noise `2·(N·β) + βV` is at most `βV + 2·(N·β)` (`Encrypts.mono`). -/
theorem Encrypts.select (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}
    {b u v : ℤ} {β βV : ℕ} {C U V : Ciphertext P} (hC : Encrypts P t b β C)
    (hU : Encrypts P t u βV U) (hV : Encrypts P t v βV V) (hb : b = 0 ∨ b = 1) :
    Encrypts P t ((1 - b) * u + b * v) (βV + 2 * (P.columns * β)) (select P C U V) := by
  rw [select_eq]
  -- `G − C` encrypts `1 − b` with noise `0 + β`
  have hGC := Encrypts.sub P (encrypts_gadget P) hC
  rcases hb with rfl | rfl
  · -- `b = 0`: the left product carries the bit `1` (`Encrypts.mul_bit`), the right one the
    -- message `0`, whose state noise vanishes (`Encrypts.mul`, `|0|·βV = 0`)
    have hL := Encrypts.mul_bit P (b := true) (by simpa using hGC) hU
    have hR := Encrypts.mul P hC hV
    rw [show ((1 : ℤ) - 0) * u + 0 * v = ((true.toNat : ℕ) : ℤ) * u + 0 * v by simp]
    exact Encrypts.mono P (Encrypts.add P hL hR) (by simp; omega)
  · -- `b = 1`: the left product carries the message `0` (`Encrypts.mul`), the right one the
    -- bit `1` (`Encrypts.mul_bit`)
    have hL := Encrypts.mul P hGC hU
    have hR := Encrypts.mul_bit P (b := true) (by simpa using hC) hV
    rw [show ((1 : ℤ) - 1) * u + 1 * v = (1 - 1) * u + ((true.toNat : ℕ) : ℤ) * v by simp]
    exact Encrypts.mono P (Encrypts.add P hL hR) (by simp; omega)

/-- The selector step with a Boolean selector and natural-number messages: if `C` encrypts
`b.toNat` with noise at most `β` and `U`, `V` encrypt `u`, `v` with noise at most `βV`, then
`select P C U V` encrypts `if b then v else u` with noise at most `βV + 2·(N·β)`:
`Encrypts P t (if b then v else u : ℕ) (βV + 2 * (P.columns * β)) (select P C U V)`.
Glue: `Encrypts.select` (G1) at `b.toNat`, read through `Bool.toNat`. -/
private theorem encrypts_select_ite (P : Parameters)
    {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus} {b : Bool} {u v : ℕ} {β βV : ℕ}
    {C U V : Ciphertext P} (hC : Encrypts P t (b.toNat : ℤ) β C) (hU : Encrypts P t (u : ℤ) βV U)
    (hV : Encrypts P t (v : ℤ) βV V) :
    Encrypts P t ((if b then v else u : ℕ) : ℤ) (βV + 2 * (P.columns * β)) (select P C U V) := by
  have h := Encrypts.select P hC hU hV (by cases b <;> simp)
  cases b <;> simpa using h

/-- **G2. Homomorphic permutation-program evaluation.** For a permutation program `B` of
width `w` on `k` inputs, input ciphertexts `cts j` encrypting the bits `x j` with noise at most
`β` under `t`, and the start state `Pi.single s₀ G`, coordinate `i` of the evaluated state
encrypts the indicator of `B.yield x s₀ = i` with noise at most `B.length·(2·(N·β))`:
`Encrypts P t (decide (B.yield x s₀ = i)).toNat (B.length * (2 * (P.columns * β)))
(homEvalPBP P B cts (Pi.single s₀ (gadget P)) i)`
[BV14, Lemma 3.6, p015-b001, with its proof, p015-b002; AP14, Lemma 4.1, p012-b001].
Deviation: worst case (BV14: with overwhelming probability), for every permutation program.

**Proof sketch.** Apply the host lemma `BranchingProgram.evalWith_rel` (C7) to the
homomorphic run and to the Boolean run `evalWith (fun b u v => if b then v else u) x
(Pi.single s₀ 1)` (whose result is `Pi.single (B.yield x s₀) 1` by `evalWith_single`, C8),
with the relation at step `τ`: every coordinate `i` of the ciphertext state encrypts the
natural number at coordinate `i` of the Boolean state, with noise at most `τ·(2·(N·β))`. At
step `0`: `Pi.single` coordinates are `G` (`encrypts_gadget`) and `0` (`encrypts_zero`). Step:
the instruction is a permutation (`isPermutation_iff`), so both steps are pull forms
(`Instr.stepWith_of_isPermutation`, C6); coordinate `i` is `select (cts var) U V` with `U`, `V`
the predecessors' ciphertexts, and `Encrypts.select` (G1) with `βV = τ·(2·(N·β))` gives
`(τ + 1)·(2·(N·β))`; the messages agree because `(1 − b)·u + b·v` at `b = (x var).toNat` is the
Boolean branch `if x var then v else u` (the private glue `encrypts_select_ite`). At
`τ = B.length` read `evalWith_single` and `Pi.single_eq_same`, `Pi.single_eq_of_ne`. Uses the
`homEvalPBP_eq` reader. -/
theorem encrypts_homEvalPBP (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}
    {w k : ℕ} (B : BranchingProgram w k) (hB : B.IsPermutation) (x : Fin k → Bool)
    (cts : Fin k → Ciphertext P) (β : ℕ)
    (hin : ∀ j, Encrypts P t ((x j).toNat : ℤ) β (cts j)) (s₀ i : Fin w) :
    Encrypts P t ((decide (B.yield x s₀ = i)).toNat : ℤ) (B.length * (2 * (P.columns * β)))
      (homEvalPBP P B cts (Pi.single s₀ (gadget P)) i) := by
  -- the relation at step `τ`: coordinate `i` of the ciphertext state encrypts coordinate `i` of
  -- the Boolean state with noise at most `τ·(2·(N·β))`
  let R : ℕ → (Fin w → Ciphertext P) → (Fin w → ℕ) → Prop := fun τ U U' =>
    ∀ i, Encrypts P t ((U' i : ℕ) : ℤ) (τ * (2 * (P.columns * β))) (U i)
  -- step `0`: the start states `Pi.single s₀ G` and `Pi.single s₀ 1`
  have h0 : R 0 (Pi.single s₀ (gadget P)) (Pi.single s₀ 1) := by
    intro j
    rw [zero_mul]
    by_cases hj : j = s₀
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same, Nat.cast_one]
      exact encrypts_gadget P
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, Nat.cast_zero]
      exact encrypts_zero P
  -- one instruction: both runs take the pull form, and the selector step adds `2·(N·β)`
  have hstep : ∀ τ (hτ : τ < B.length) (U : Fin w → Ciphertext P) (U' : Fin w → ℕ), R τ U U' →
      R (τ + 1) ((B.instrs[τ]'(hτ.trans_eq B.length_eq)).stepWith (select P) cts U)
        ((B.instrs[τ]'(hτ.trans_eq B.length_eq)).stepWith
          (fun b (u v : ℕ) => if b then v else u) x U') := by
    intro τ hτ U U' hR j
    have hι : (B.instrs[τ]'(hτ.trans_eq B.length_eq)).IsPermutation :=
      (BranchingProgram.Instr.isPermutation_iff _).2
        ((BranchingProgram.isPermutation_iff B).1 hB _ (List.getElem_mem _))
    rw [BranchingProgram.Instr.stepWith_of_isPermutation _ _ hι,
      BranchingProgram.Instr.stepWith_of_isPermutation _ _ hι]
    exact Encrypts.mono P (encrypts_select_ite P (hin _) (hR _) (hR _))
      (le_of_eq (by ring))
  have hrel := BranchingProgram.evalWith_rel (select P) (fun b (u v : ℕ) => if b then v else u)
    cts x B R _ _ h0 hstep
  -- read coordinate `i` of the Boolean result `Pi.single (B.yield x s₀) 1` (`evalWith_single`)
  have hi := hrel i
  rw [BranchingProgram.evalWith_single] at hi
  rw [homEvalPBP_eq]
  have hm : (((Pi.single (B.yield x s₀) 1 : Fin w → ℕ) i : ℕ) : ℤ) =
      ((decide (B.yield x s₀ = i)).toNat : ℤ) := by
    by_cases hy : B.yield x s₀ = i
    · rw [hy, Pi.single_eq_same, decide_eq_true rfl]
      rfl
    · rw [Pi.single_eq_of_ne (Ne.symm hy), decide_eq_false hy]
      rfl
  rw [← hm]
  exact hi

/-- **G3. Homomorphic formula evaluation.** For a formula `c` of fan-in at most two on
`k ≥ 1` inputs and input ciphertexts `cts j` encrypting the bits `x j` with noise at most `β`
under `t`, `homEvalFormula P c cts` encrypts `c.eval x` with noise at most
`4^(c.depth)·(2·(N·β))`:
`Encrypts P t (c.eval x).toNat (4 ^ c.depth * (2 * (P.columns * β))) (homEvalFormula P c cts)`
[BV14, Thm 3.5, p014-b001, with Lemma 3.6, p015-b001; Pei16, §6.1.3, p070-b001; Bar89, Thm 1,
p003-b002]. Deviation: the output coordinate is `σ 0` (BV14: coordinate `1`), worst case.

**Proof sketch.** `homEvalFormula_eq`, then G2 (`encrypts_homEvalPBP`) for the program
`barrington c sigma1`, which is a permutation program (`isPermutation_barrington`, C15), at
`s₀ = 0` and `i = sigma1 0`. Its message is `decide (yield x 0 = sigma1 0)`; by
`barrington_yield_zero` (C16, with `isFiveCycle_sigma1`) the yield at `0` is `sigma1 0` if
`c.eval x` and `0` otherwise, and `sigma1 0 ≠ 0` (`sigma1_eq` and kernel `decide` on
`Fin 5`), so the message is `(c.eval x).toNat`. The noise
`length·(2·(N·β))` is at most `4^(c.depth)·(2·(N·β))` by `barrington_length_le` (C14) and
`Encrypts.mono`. -/
theorem encrypts_homEvalFormula (P : Parameters)
    {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus} {k : ℕ} [NeZero k]
    (c : TreeCircuit k) (hc : c.maxFanin ≤ 2) (x : Fin k → Bool) (cts : Fin k → Ciphertext P)
    (β : ℕ) (hin : ∀ j, Encrypts P t ((x j).toNat : ℤ) β (cts j)) :
    Encrypts P t ((c.eval x).toNat : ℤ) (4 ^ c.depth * (2 * (P.columns * β)))
      (homEvalFormula P c cts) := by
  rw [homEvalFormula_eq]
  -- G2 for Barrington's program, a permutation program, from `0`, read at `sigma1 0`
  have h := encrypts_homEvalPBP P _ (BranchingProgram.isPermutation_barrington c
    BranchingProgram.sigma1) x cts β hin 0 (BranchingProgram.sigma1 0)
  -- the five-cycle `sigma1` moves `0` (`sigma1_eq`, kernel `decide` on `Fin 5`)
  have h0 : BranchingProgram.sigma1 0 ≠ 0 := by
    rw [BranchingProgram.sigma1_eq]
    decide
  -- the message: the yield at `0` is `sigma1 0` on accepted inputs and `0` otherwise
  have hm : ((decide ((BranchingProgram.barrington c BranchingProgram.sigma1).yield x 0 =
      BranchingProgram.sigma1 0)).toNat : ℤ) = ((c.eval x).toNat : ℤ) := by
    rw [BranchingProgram.barrington_yield_zero hc BranchingProgram.isFiveCycle_sigma1 x]
    cases c.eval x
    · rw [if_neg Bool.false_ne_true, decide_eq_false (Ne.symm h0)]
    · rw [if_pos rfl, decide_eq_true rfl]
  rw [hm] at h
  -- the noise: `length ≤ 4 ^ depth` (`barrington_length_le`)
  exact Encrypts.mono P h (Nat.mul_le_mul_right _
    (BranchingProgram.barrington_length_le hc BranchingProgram.sigma1))

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
