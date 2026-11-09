/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Quantum.Basic.Measure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# No-cloning, teleportation and superdense coding

Three first results about qubits, stated on registers with the gates of `Gates.lean` placed by
`applyOn`. Teleportation and superdense coding also serve as sanity checks of `applyOn`
(plan FD-3): each one composes gates on different wires of one register.

## Main definitions

* `Quantum.bell` — the EPR pair `(|00⟩ + |11⟩)/√2` [dW26, §1.5].
* `Quantum.teleportInit ψ`, `Quantum.teleportState ψ` — the teleportation protocol's state
  before and after Alice's gates [dW26, §1.5].
* `Quantum.bobVec ψ m₀ m₁` — Bob's (unnormalized) qubit after Alice measures `m₀ m₁`.
* `Quantum.denseCode b₀ b₁`, `Quantum.superdenseState b₀ b₁` — superdense coding [NC10, §2.3].

## Main results

* `Quantum.no_cloning_of_overlap` — no unitary copies two states whose overlap has modulus
  strictly between `0` and `1`, even up to a separate phase on each copy [NC10, Box 12.1].
* `Quantum.no_cloning` — the standard no-cloning theorem: on a basis with at least two elements,
  no unitary copies every state, even up to a state-dependent phase [NC10, Box 12.1], [WZ82].
* `Quantum.no_exact_cloning` — a weaker, vector-level statement: no unitary maps every
  `|ψ⟩|e⟩` to exactly `|ψ⟩|ψ⟩`. It holds even on a one-element basis, where the single physical
  state can be copied, so it is a fact about vector representatives, not about physical states.
* `Quantum.teleportState_vec` — after Alice's gates, the state is
  `½ ∑_{m₀ m₁} |m₀ m₁⟩ ⊗ X^{m₁} Z^{m₀} |ψ⟩` [dW26, §1.5].
* `Quantum.teleport_outcome_prob` — each of Alice's four outcomes has probability `1/4`.
* `Quantum.teleport_correct` — Bob's correction `Z^{m₀} X^{m₁}` recovers `ψ` [dW26, §1.5].
* `Quantum.superdense_decode` — Bob decodes Alice's two bits with certainty [NC10, §2.3].

## Divergences

* Kets are vectors, not rays: they keep their global phase. A cloning statement that demands
  exact vector equality is therefore weaker than physical no-cloning: it already fails for `ψ` and
  `-ψ` by linearity, since `(-ψ) ⊗ (-ψ) = ψ ⊗ ψ`. `no_exact_cloning` is that statement.
  `no_cloning_of_overlap` and `no_cloning` allow a unit-modulus phase on each output and carry the
  physical content (round-1 audit, finding 1).
* `denseCode`'s message labels follow the decoder used here: `(b₀, b₁)` is encoded as
  `X^{b₁} Z^{b₀}` and decoded as the basis state `|b₀ b₁⟩`. [NC10, §2.3] sends `01` with `Z` and
  `10` with `X`, the other way round, and its `11` operator `iY` differs from `X Z = -iY` by a
  global sign. The protocols are the same up to relabelling the messages and a phase that no
  measurement sees (round-1 audit, finding 3).
* States of one qubit are kets over `Reg 1`, the basis the gates of `Gates.lean` act on.

## References

* [dW26] R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415, version 6 (2026).
* [NC10] M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, 10th
  anniversary edition, Cambridge University Press, 2010.
* [WZ82] W. K. Wootters, W. H. Zurek, *A single quantum cannot be cloned*, Nature 299,
  802–803, 1982.
-/

noncomputable section

namespace Quantum

open Matrix
open scoped Quantum

/-! ### No-cloning -/

/-- **No-cloning for two states.** Let `ψ` and `φ` be states whose overlap
`t = |⟨ψ, φ⟩| = |∑ₓ conj (ψ x) φ x|` satisfies `0 < t < 1`. Then no unitary `U` maps `|ψ⟩|e⟩` to
`c₁ |ψ⟩|ψ⟩` and `|φ⟩|e⟩` to `c₂ |φ⟩|φ⟩` for any phases `|c₁| = |c₂| = 1`, whatever the blank
state `|e⟩`. Distinct states that are not orthogonal cannot be copied, even up to phase.
[NC10, Box 12.1]

**Proof sketch.** A unitary preserves inner products. The inputs have inner product
`⟨ψ, φ⟩ ⟨e, e⟩ = ⟨ψ, φ⟩`, and the outputs have inner product `conj c₁ · c₂ · ⟨ψ, φ⟩²`. Taking
moduli gives `t = t²`, so `t ∈ {0, 1}`, contradicting `0 < t < 1`. -/
theorem no_cloning_of_overlap {d : Type*} [Fintype d] [DecidableEq d] (e : d) (ψ φ : Ket d)
    (h₀ : 0 < ‖∑ x, star (ψ.vec x) * φ.vec x‖) (h₁ : ‖∑ x, star (ψ.vec x) * φ.vec x‖ < 1) :
    ¬ ∃ (U : 𝐔[d × d]) (c₁ c₂ : ℂ), ‖c₁‖ = 1 ∧ ‖c₂‖ = 1 ∧
      (U : Matrix (d × d) (d × d) ℂ) *ᵥ (ψ ⊗ᵠ Ket.basis e).vec = c₁ • (ψ ⊗ᵠ ψ).vec ∧
      (U : Matrix (d × d) (d × d) ℂ) *ᵥ (φ ⊗ᵠ Ket.basis e).vec = c₂ • (φ ⊗ᵠ φ).vec := by
  rintro ⟨U, c₁, c₂, hc₁, hc₂, hψ, hφ⟩
  set t := ∑ x, star (ψ.vec x) * φ.vec x with ht
  have hin : star (ψ ⊗ᵠ Ket.basis e).vec ⬝ᵥ (φ ⊗ᵠ Ket.basis e).vec = t := by
    simp only [dotProduct, Pi.star_apply, Ket.prod_vec, Ket.basis_vec, Fintype.sum_prod_type,
      mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq, ht, mul_comm]
  have hout : star (c₁ • (ψ ⊗ᵠ ψ).vec) ⬝ᵥ (c₂ • (φ ⊗ᵠ φ).vec) = star c₁ * c₂ * t ^ 2 := by
    simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Ket.prod_vec,
      Fintype.sum_prod_type, star_mul']
    rw [ht, sq, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have heq : t = star c₁ * c₂ * t ^ 2 :=
    calc t = star (ψ ⊗ᵠ Ket.basis e).vec ⬝ᵥ (φ ⊗ᵠ Ket.basis e).vec := hin.symm
      _ = star ((U : Matrix (d × d) (d × d) ℂ) *ᵥ (ψ ⊗ᵠ Ket.basis e).vec) ⬝ᵥ
          ((U : Matrix (d × d) (d × d) ℂ) *ᵥ (φ ⊗ᵠ Ket.basis e).vec) :=
            (inner_mulVec_of_mem_unitaryGroup U.2 _ _).symm
      _ = star (c₁ • (ψ ⊗ᵠ ψ).vec) ⬝ᵥ (c₂ • (φ ⊗ᵠ φ).vec) := by rw [hψ, hφ]
      _ = star c₁ * c₂ * t ^ 2 := hout
  have hn : ‖t‖ = ‖t‖ ^ 2 := by
    conv_lhs => rw [heq]
    rw [norm_mul, norm_mul, norm_star, hc₁, hc₂, norm_pow]; ring
  nlinarith

/-- **No-cloning theorem.** On a basis with at least two elements, no unitary `U` maps
`|ψ⟩|e⟩` to `c_ψ |ψ⟩|ψ⟩` for every state `ψ`, even allowing a phase `|c_ψ| = 1` that depends on
`ψ`, whatever the blank state `|e⟩`. This is the physical statement: kets differing by a phase
are the same state. [NC10, Box 12.1], [WZ82]

**Proof sketch.** Pick basis states `i ≠ j` (`Nontrivial`). The states `|i⟩` and
`(|i⟩ + |j⟩)/√2` have overlap `1/√2`, strictly between `0` and `1`, so `no_cloning_of_overlap`
forbids copying both. -/
theorem no_cloning {d : Type*} [Fintype d] [DecidableEq d] [Nontrivial d] (e : d) :
    ¬ ∃ U : 𝐔[d × d], ∀ ψ : Ket d, ∃ c : ℂ, ‖c‖ = 1 ∧
      (U : Matrix (d × d) (d × d) ℂ) *ᵥ (ψ ⊗ᵠ Ket.basis e).vec = c • (ψ ⊗ᵠ ψ).vec := by
  rintro ⟨U, hU⟩
  obtain ⟨i, j, hij⟩ := exists_pair_ne d
  let φ : Ket d := ⟨fun x => ((Real.sqrt 2 : ℂ))⁻¹ * ((if i = x then 1 else 0) + (if j = x then 1 else 0)), by
    simp only [norm_mul, mul_pow, ← Finset.mul_sum]
    rw [Finset.sum_eq_add (s := Finset.univ) i j hij]
    · simp [hij, Ne.symm hij]
      norm_num
    · intro c _ hc; simp [Ne.symm hc.1, Ne.symm hc.2]
    · simp
    · simp⟩
  have hov : ∑ x, star ((Ket.basis i).vec x) * φ.vec x = ((Real.sqrt 2 : ℂ))⁻¹ := by
    simp [φ, Ket.basis_vec, Ne.symm hij]
  obtain ⟨c₁, hc₁, h1⟩ := hU (Ket.basis i)
  obtain ⟨c₂, hc₂, h2⟩ := hU φ
  refine no_cloning_of_overlap e (Ket.basis i) φ ?_ ?_ ⟨U, c₁, c₂, hc₁, hc₂, h1, h2⟩
  · rw [hov, norm_pos_iff]; simp
  · rw [hov, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [inv_lt_one_iff₀]; right
    rw [Real.lt_sqrt (by norm_num)]; norm_num

/-- **No exact cloning of vectors.** No unitary `U` maps `|ψ⟩|e⟩` to exactly `|ψ⟩|ψ⟩` for every
ket `ψ`, on any basis. This is weaker than `no_cloning`: it forbids copying vector
representatives, phase included, and holds even on a one-element basis, where the single
physical state is trivially copied. Kept as a vector-level fact (round-1 audit, finding 1).

**Proof sketch.** Apply the hypothesis to `|e⟩` and to `-|e⟩` (also a ket). By linearity,
`U ((-|e⟩)|e⟩) = -U(|e⟩|e⟩) = -|ee⟩`, but the hypothesis says it is
`(-|e⟩)(-|e⟩) = |ee⟩`. So `|ee⟩ = 0`, contradicting its amplitude `1` at `(e, e)`. -/
theorem no_exact_cloning {d : Type*} [Fintype d] [DecidableEq d] (e : d) :
    ¬ ∃ U : 𝐔[d × d], ∀ ψ : Ket d,
      (U : Matrix (d × d) (d × d) ℂ) *ᵥ (ψ ⊗ᵠ Ket.basis e).vec = (ψ ⊗ᵠ ψ).vec := by
  rintro ⟨U, hU⟩
  let ψ := Ket.basis e
  let ψn : Ket d := ⟨fun x => -ψ.vec x, by simpa using ψ.normalized'⟩
  have h1 := hU ψ
  have h2 := hU ψn
  have hlin : (ψn ⊗ᵠ Ket.basis e).vec = -(ψ ⊗ᵠ Ket.basis e).vec := by
    funext p; simp [ψn, Ket.prod_vec]
  have hsq : (ψn ⊗ᵠ ψn).vec = (ψ ⊗ᵠ ψ).vec := by
    funext p; simp [ψn, Ket.prod_vec]
  rw [hlin, mulVec_neg, h1, hsq] at h2
  have := congrFun h2 (e, e)
  simp [ψ, Ket.prod_vec, Ket.basis_vec] at this
  norm_num at this

/-! ### The EPR pair -/

/-- The amplitudes of the EPR pair: `1/√2` on `|00⟩` and `|11⟩`, `0` elsewhere. -/
def bellVec (x : Reg 2) : ℂ := if x 0 = x 1 then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- `bellVec x` is `1/√2` if the two wires of `x` agree, and `0` otherwise. -/
theorem bellVec_eq (x : Reg 2) :
    bellVec x = if x 0 = x 1 then ((Real.sqrt 2)⁻¹ : ℂ) else 0 := rfl

/-- The EPR amplitudes have squared norm `1`: two terms of `1/2`.

**Proof sketch.** Exactly two of the four basis states have equal wires, and
`‖1/√2‖² = 1/2`. -/
theorem sum_norm_sq_bellVec : ∑ x, ‖bellVec x‖ ^ 2 = 1 := by
  rw [← (finTwoArrowEquiv Qubit).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, bellVec, finTwoArrowEquiv]
  norm_num

/-- The EPR pair `(|00⟩ + |11⟩)/√2`. [dW26, §1.5] -/
def bell : Ket (Reg 2) := ⟨bellVec, sum_norm_sq_bellVec⟩

/-- The amplitudes of `bell` are `bellVec`. -/
theorem bell_vec : bell.vec = bellVec := rfl

/-! ### Teleportation -/

/-- The wires `0, 1` of a three-wire register, in order. -/
def wires01 : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by decide)

/-- `wires01` is the order-preserving inclusion `Fin 2 ↪ Fin 3`. -/
theorem wires01_apply (j : Fin 2) : wires01 j = Fin.castLE (by decide) j := rfl

/-- The initial state of teleportation: Alice's qubit `ψ` on wire `0`, and an EPR pair on
wires `1, 2` (wire `1` is Alice's half, wire `2` is Bob's). [dW26, §1.5] -/
def teleportInit (ψ : Ket (Reg 1)) : Ket (Reg 3) := (ψ ⊗ᵠ bell).relabel (regAppendEquiv 1 2).symm

/-- The amplitude of the initial state at `y` is `ψ (y 0) · bell (y 1, y 2)`.

**Proof sketch.** Unfold `relabel` and `prod`, and read `(regAppendEquiv 1 2).symm y` with
`regAppendEquiv_apply_castAdd` and `regAppendEquiv_apply_natAdd`. -/
theorem teleportInit_vec (ψ : Ket (Reg 1)) (y : Reg 3) :
    (teleportInit ψ).vec y = ψ.vec (fun _ => y 0) * bellVec ![y 1, y 2] := by
  rw [teleportInit, Ket.relabel_vec, Ket.prod_vec, regAppendEquiv_symm_apply, bell_vec]
  congr 2
  · funext i; fin_cases i; rfl
  · funext i; fin_cases i <;> rfl

/-- The state after Alice's gates: `CNOT` from wire `0` to wire `1`, then `H` on wire `0`.
Alice then measures wires `0, 1`. [dW26, §1.5] -/
def teleportState (ψ : Ket (Reg 1)) : Ket (Reg 3) :=
  ((teleportInit ψ).evolve (applyOnU wires01 Gate.CNOT)).evolve (applyOnU (wire 0) Gate.H)

/-- `teleportState ψ` is `teleportInit ψ` after `CNOT` on wires `0, 1` and `H` on wire `0`. -/
theorem teleportState_eq (ψ : Ket (Reg 1)) :
    teleportState ψ =
      ((teleportInit ψ).evolve (applyOnU wires01 Gate.CNOT)).evolve (applyOnU (wire 0) Gate.H) :=
  rfl

/-- `(1/√2)² = 1/2` in `ℂ`, in the `^ 2` form `ring_nf` produces (from `inv_sqrt_two_mul_self`). -/
private theorem inv_sqrt_two_sq : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = 1 / 2 := by
  rw [sq, inv_sqrt_two_mul_self]

/-- `CNOT` on wires `0, 1` of a three-wire register adds wire `0` into wire `1`. -/
private theorem cnot_extend_wires01 (z : Reg 3) :
    Function.extend wires01 (cnotMap (z ∘ wires01)) z = Function.update z 1 (z 1 + z 0) := by
  funext j
  fin_cases j
  · exact (wires01.injective.extend_apply _ z 0).trans (by simp [cnotMap, wires01_apply])
  · exact (wires01.injective.extend_apply _ z 1).trans (by simp [cnotMap, wires01_apply])
  · rw [Function.extend_apply' _ _ _ (by decide)]; simp

/-- The teleportation state after Alice's gates, as a two-term sum over the value `a` of wire `0`
before the Hadamard gate. -/
private theorem teleportState_vec_sum (ψ : Ket (Reg 1)) (y : Reg 3) :
    (teleportState ψ).vec y = ∑ a : Qubit, hadamardMat (fun _ => y 0) (fun _ => a) *
      (ψ.vec (fun _ => a) * bellVec ![y 1 + a, y 2]) := by
  rw [teleportState, Ket.evolve_vec, Ket.evolve_vec, applyOnU_coe, applyOnU_coe,
    applyOn_wire_mulVec_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Gate.H_coe, Gate.CNOT_coe, applyOn_permMat_mulVec_apply, Function.Involutive.toPerm_symm,
    Function.Involutive.coe_toPerm, cnot_extend_wires01, teleportInit_vec]
  congr 2

/-- A permutation matrix relabels a vector's entries: `(permMat σ v) c = v (σ⁻¹ c)`. -/
private theorem permMat_mulVec_apply {d : Type*} [Fintype d] [DecidableEq d] (σ : Equiv.Perm d)
    (w : d → ℂ) (c : d) : (permMat σ *ᵥ w) c = w (σ.symm c) := by
  simp only [mulVec, dotProduct, permMat_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm c)]
  · rw [if_pos (by simp)]
  · intro z _ hz; rw [if_neg (fun h => hz (by rw [h, Equiv.symm_apply_apply]))]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- On one wire, `flipAt 0` adds `1` to the wire's value. -/
private theorem flipAt_const (c : Qubit) : flipAt 0 (fun _ : Fin 1 => c) = fun _ => c + 1 := by
  funext j; fin_cases j; simp [flipAt]

/-- `X` flips the argument of a one-qubit amplitude vector. -/
private theorem X_mulVec_apply (w : Reg 1 → ℂ) (c : Qubit) :
    ((Gate.X : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ w) (fun _ => c) = w (fun _ => c + 1) := by
  rw [Gate.X_coe, permMat_mulVec_apply, Function.Involutive.toPerm_symm,
    Function.Involutive.coe_toPerm, flipAt_const]

/-- `Z` multiplies the amplitude at `|c⟩` by `(-1)^c`. -/
private theorem Z_mulVec_apply (w : Reg 1 → ℂ) (c : Qubit) :
    ((Gate.Z : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ w) (fun _ => c) = (-1) ^ (c : ℕ) * w (fun _ => c) := by
  rw [Gate.Z_coe, mulVec_diagonal, zPhase_eq]

/-- **Teleportation, the key identity.** After Alice's gates the state is
`½ ∑_{m₀ m₁} |m₀ m₁⟩ ⊗ X^{m₁} Z^{m₀} |ψ⟩`: its amplitude at `y` is `½` times the amplitude of
`X^{y 1} Z^{y 0} ψ` at Bob's wire value `y 2`. [dW26, §1.5]

**Proof sketch.** Write `ψ = α|0⟩ + β|1⟩`. After `CNOT` on wires `0, 1`, the amplitude at
`(a, b, c)` is `ψ(a) · [b + a = c] / √2`. After `H` on wire `0` it is
`½ ∑_a (-1)^{a y₀} ψ(a) [y₁ + a = y₂]`. For each `(y₀, y₁)` the only surviving `a` is
`a = y₂ + y₁`, which gives `½ (-1)^{(y₂ + y₁) y₀} ψ(y₂ + y₁)`: the amplitude of
`X^{y₁} Z^{y₀} ψ` at `y₂`. Each step reads `applyOn` through `applyOn_mulVec_basis`, so the
proof exercises `applyOn` on two different wire sets of one register. -/
theorem teleportState_vec (ψ : Ket (Reg 1)) (y : Reg 3) :
    (teleportState ψ).vec y =
      (1 / 2 : ℂ) *
        (((Gate.X ^ (y 1).val * Gate.Z ^ (y 0).val : Gate 1) : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ
          ψ.vec) (fun _ => y 2) := by
  rw [teleportState_vec_sum, Fin.sum_univ_two, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    SubmonoidClass.coe_pow, ← mulVec_mulVec]
  generalize y 0 = c0
  generalize y 1 = c1
  generalize y 2 = c2
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;>
    simp [hadamardMat, bellVec, X_mulVec_apply, Z_mulVec_apply] <;>
    ring_nf <;> rw [inv_sqrt_two_sq] <;> ring

/-- Each of Alice's four measurement outcomes `(m₀, m₁)` occurs with probability `1/4`,
whatever `ψ` is. [dW26, §1.5]

**Proof sketch.** By `teleportState_vec`, the outcome's probability is
`¼ ∑_c ‖(X^{m₁} Z^{m₀} ψ)(c)‖²`, and `X^{m₁} Z^{m₀}` is unitary
(`sum_norm_sq_mulVec_of_mem_unitaryGroup`), so the sum is `‖ψ‖² = 1`. -/
theorem teleport_outcome_prob (ψ : Ket (Reg 1)) (m₀ m₁ : Qubit) :
    ∑ y ∈ Finset.univ.filter (fun y : Reg 3 => y 0 = m₀ ∧ y 1 = m₁), (teleportState ψ).prob y =
      1 / 4 := by
  set M : Matrix (Reg 1) (Reg 1) ℂ := ((Gate.X ^ m₁.val * Gate.Z ^ m₀.val : Gate 1) :
    Matrix (Reg 1) (Reg 1) ℂ) with hM
  have hU : M ∈ 𝐔[Reg 1] := (Gate.X ^ m₁.val * Gate.Z ^ m₀.val).2
  rw [Finset.sum_nbij' (fun y => y 2) (fun c => ![m₀, m₁, c])
    (t := Finset.univ) (g := fun c => ‖(1 / 2 : ℂ) * (M *ᵥ ψ.vec) (fun _ => c)‖ ^ 2)]
  · simp only [norm_mul, mul_pow, ← Finset.mul_sum]
    rw [← (Equiv.funUnique (Fin 1) Qubit).sum_comp]
    have h1 : ∑ x : Reg 1, ‖(M *ᵥ ψ.vec) (fun _ => (Equiv.funUnique (Fin 1) Qubit) x)‖ ^ 2 =
        ∑ x : Reg 1, ‖(M *ᵥ ψ.vec) x‖ ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 3; funext j; fin_cases j; rfl
    rw [h1, sum_norm_sq_mulVec_of_mem_unitaryGroup hU, ψ.normalized']
    norm_num
  · intros; exact Finset.mem_univ _
  · intro c _; simp
  · intro y hy
    obtain ⟨h0, h1⟩ := (Finset.mem_filter.1 hy).2
    funext j; fin_cases j <;> simp [h0, h1]
  · intros; rfl
  · intro y hy
    obtain ⟨h0, h1⟩ := (Finset.mem_filter.1 hy).2
    rw [Ket.prob_eq, teleportState_vec, h0, h1]

/-- Bob's qubit after Alice measures `(m₀, m₁)`, unnormalized: the amplitudes of
`teleportState ψ` with wires `0, 1` fixed to `m₀, m₁`. -/
def bobVec (ψ : Ket (Reg 1)) (m₀ m₁ : Qubit) : Reg 1 → ℂ :=
  fun b => (teleportState ψ).vec ![m₀, m₁, b 0]

/-- `bobVec ψ m₀ m₁ b` is the amplitude of `teleportState ψ` at `(m₀, m₁, b)`. -/
theorem bobVec_apply (ψ : Ket (Reg 1)) (m₀ m₁ : Qubit) (b : Reg 1) :
    bobVec ψ m₀ m₁ b = (teleportState ψ).vec ![m₀, m₁, b 0] := rfl

/-- `Xᵐ Xᵐ = 1`, from `X X = 1`. -/
private theorem X_pow_mul_self (m : ℕ) : Gate.X ^ m * Gate.X ^ m = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, sq, Gate.X_mul_X, one_pow]

/-- `Zᵐ Zᵐ = 1`, from `Z Z = 1`. -/
private theorem Z_pow_mul_self (m : ℕ) : Gate.Z ^ m * Gate.Z ^ m = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, sq, Gate.Z_mul_Z, one_pow]

/-- **Teleportation is correct.** After Alice's outcome `(m₀, m₁)`, Bob applies `X^{m₁}` and
then `Z^{m₀}`, and holds `ψ` (scaled by `½`, the amplitude of the outcome). [dW26, §1.5]

**Proof sketch.** By `teleportState_vec`, `bobVec ψ m₀ m₁ = ½ X^{m₁} Z^{m₀} ψ`. Then
`Z^{m₀} X^{m₁} X^{m₁} Z^{m₀} = 1`, since `X X = 1` and `Z Z = 1` (from `H_mul_H`,
`S_mul_S` and `H_mul_Z_mul_H`, or by computing the four entries). -/
theorem teleport_correct (ψ : Ket (Reg 1)) (m₀ m₁ : Qubit) :
    ((Gate.Z ^ m₀.val * Gate.X ^ m₁.val : Gate 1) : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ
        bobVec ψ m₀ m₁ =
      (1 / 2 : ℂ) • ψ.vec := by
  have hb : bobVec ψ m₀ m₁ = (1 / 2 : ℂ) •
      (((Gate.X ^ m₁.val * Gate.Z ^ m₀.val : Gate 1) : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ ψ.vec) := by
    funext b
    rw [bobVec_apply, teleportState_vec, Pi.smul_apply, smul_eq_mul]
    have hb' : (fun _ : Fin 1 => b 0) = b := by funext j; fin_cases j; rfl
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hb']
  have key : (Gate.Z ^ m₀.val * Gate.X ^ m₁.val) * (Gate.X ^ m₁.val * Gate.Z ^ m₀.val) = 1 := by
    rw [mul_assoc, ← mul_assoc (Gate.X ^ m₁.val), X_pow_mul_self, one_mul, Z_pow_mul_self]
  rw [hb, mulVec_smul, mulVec_mulVec, ← Submonoid.coe_mul, key, Submonoid.coe_one, one_mulVec]

/-! ### Superdense coding -/

/-- Alice's encoding of two bits `(b₀, b₁)` in superdense coding: `Z^{b₀}`, then `X^{b₁}`, on
her half of the EPR pair. [NC10, §2.3] -/
def denseCode (b₀ b₁ : Qubit) : Gate 1 := Gate.X ^ b₁.val * Gate.Z ^ b₀.val

/-- `denseCode b₀ b₁ = X^{b₁} Z^{b₀}`. -/
theorem denseCode_eq (b₀ b₁ : Qubit) : denseCode b₀ b₁ = Gate.X ^ b₁.val * Gate.Z ^ b₀.val :=
  rfl

/-- The state Bob holds after decoding: Alice applies `denseCode b₀ b₁` to wire `0` of the EPR
pair and sends that qubit to Bob, who applies `CNOT` (control wire `0`) and then `H` on wire
`0`. [NC10, §2.3] -/
def superdenseState (b₀ b₁ : Qubit) : Ket (Reg 2) :=
  ((bell.evolve (applyOnU (wire 0) (denseCode b₀ b₁))).evolve Gate.CNOT).evolve
    (applyOnU (wire 0) Gate.H)

/-- `superdenseState b₀ b₁` is the EPR pair after `denseCode b₀ b₁` on wire `0`, `CNOT`, and
`H` on wire `0`. -/
theorem superdenseState_eq (b₀ b₁ : Qubit) :
    superdenseState b₀ b₁ =
      ((bell.evolve (applyOnU (wire 0) (denseCode b₀ b₁))).evolve Gate.CNOT).evolve
        (applyOnU (wire 0) Gate.H) := rfl

/-- A two-term sum over a wire's value against a one-qubit matrix is that matrix applied to a
vector, evaluated at a basis state. -/
private theorem wire_sum_eq_mulVec (D : Matrix (Reg 1) (Reg 1) ℂ) (g : Qubit → ℂ) (c : Qubit) :
    ∑ a : Qubit, D (fun _ => c) (fun _ => a) * g a = (D *ᵥ fun x => g (x 0)) (fun _ => c) := by
  simp only [mulVec, dotProduct]
  rw [← (Equiv.funUnique (Fin 1) Qubit).symm.sum_comp]
  rfl

/-- `CNOT` relabels a two-qubit vector's entries by `cnotMap`. -/
private theorem cnot_mulVec_apply (w : Reg 2 → ℂ) (z : Reg 2) :
    ((Gate.CNOT : Matrix (Reg 2) (Reg 2) ℂ) *ᵥ w) z = w (cnotMap z) := by
  rw [Gate.CNOT_coe, permMat_mulVec_apply, Function.Involutive.toPerm_symm,
    Function.Involutive.coe_toPerm]

/-- The decoded superdense state, computed case by case; `superdenseState_vec` restates it. -/
private theorem superdenseState_vec_aux (b₀ b₁ : Qubit) :
    (superdenseState b₀ b₁).vec = ((-1 : ℂ) ^ (b₀.val * b₁.val)) • (Ket.basis ![b₀, b₁]).vec := by
  funext y
  rw [superdenseState, Ket.evolve_vec, Ket.evolve_vec, Ket.evolve_vec, applyOnU_coe,
    applyOnU_coe, applyOn_wire_mulVec_apply, Fin.sum_univ_two, cnot_mulVec_apply,
    cnot_mulVec_apply, applyOn_wire_mulVec_apply, applyOn_wire_mulVec_apply,
    wire_sum_eq_mulVec, wire_sum_eq_mulVec, denseCode_eq, Submonoid.coe_mul,
    SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← mulVec_mulVec, ← mulVec_mulVec,
    Pi.smul_apply, Ket.basis_vec, bell_vec]
  have hy : y = ![y 0, y 1] := by funext j; fin_cases j <;> rfl
  rw [hy]
  generalize y 0 = c0
  generalize y 1 = c1
  fin_cases b₀ <;> fin_cases b₁ <;> fin_cases c0 <;> fin_cases c1 <;>
    simp [Gate.H_coe, hadamardMat, cnotMap, bellVec, X_mulVec_apply, Z_mulVec_apply] <;>
    ring_nf <;> first | rfl | (rw [inv_sqrt_two_sq]; ring)

/-- **Superdense coding.** Measuring Bob's two qubits gives Alice's bits `(b₀, b₁)` with
certainty: one qubit carries two classical bits, given shared entanglement. [NC10, §2.3]

**Proof sketch.** Compute the four cases. `Z` on wire `0` turns `|00⟩ + |11⟩` into
`|00⟩ - |11⟩`, and `X` swaps the value of wire `0`; then `CNOT` and `H` map the four Bell states
`X^{b₁} Z^{b₀} ⊗ I (|00⟩ + |11⟩)/√2` to `±|b₀ b₁⟩`. A global sign does not change the
probability. -/
theorem superdense_decode (b₀ b₁ : Qubit) : (superdenseState b₀ b₁).prob ![b₀, b₁] = 1 := by
  rw [Ket.prob_eq, superdenseState_vec_aux]
  simp [Ket.basis_vec]

/-- **Superdense coding, exact state.** Bob's decoded state is the basis state `|b₀ b₁⟩` times the
sign `(-1)^(b₀ b₁)`: it is `-|11⟩` for the message `11` and `+|b₀ b₁⟩` otherwise. This pins down
the phase that `superdense_decode` deliberately ignores (round-1 audit, sanity statement 10).

**Proof sketch.** As for `superdense_decode`, computing the four cases: the sign comes from
applying `Z` before `X` in `denseCode`, since `X Z = -Z X`. -/
theorem superdenseState_vec (b₀ b₁ : Qubit) :
    (superdenseState b₀ b₁).vec = ((-1 : ℂ) ^ (b₀.val * b₁.val)) • (Ket.basis ![b₀, b₁]).vec :=
  superdenseState_vec_aux b₀ b₁

end Quantum
