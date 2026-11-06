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

* `Quantum.no_cloning` — no unitary copies every state [NC10, Box 12.1], [WZ82].
* `Quantum.teleportState_vec` — after Alice's gates, the state is
  `½ ∑_{m₀ m₁} |m₀ m₁⟩ ⊗ X^{m₁} Z^{m₀} |ψ⟩` [dW26, §1.5].
* `Quantum.teleport_outcome_prob` — each of Alice's four outcomes has probability `1/4`.
* `Quantum.teleport_correct` — Bob's correction `Z^{m₀} X^{m₁}` recovers `ψ` [dW26, §1.5].
* `Quantum.superdense_decode` — Bob decodes Alice's two bits with certainty [NC10, §2.3].

## Divergences

* `no_cloning` is proved by linearity on a superposition of two basis states (the argument of
  [WZ82]), not by the inner-product argument of [NC10, Box 12.1]; the statement is the same.
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

/-- **No-cloning theorem.** On a basis with at least two elements, no unitary `U` maps
`|ψ⟩|e⟩` to `|ψ⟩|ψ⟩` for every state `ψ`, whatever the blank state `|e⟩`. [NC10, Box 12.1],
[WZ82]

**Proof sketch.** Pick basis states `i ≠ j` and let `ψ₊ = (|i⟩ + |j⟩)/√2`. By linearity of `U`,
`U |ψ₊⟩|e⟩ = (U|i⟩|e⟩ + U|j⟩|e⟩)/√2 = (|ii⟩ + |jj⟩)/√2`, whose amplitude at `(i, j)` is `0`. But
`|ψ₊⟩|ψ₊⟩` has amplitude `1/2` at `(i, j)`. -/
theorem no_cloning {d : Type*} [Fintype d] [DecidableEq d] [Nontrivial d] (e : d) :
    ¬ ∃ U : 𝐔[d × d], ∀ ψ : Ket d,
      (U : Matrix (d × d) (d × d) ℂ) *ᵥ (ψ ⊗ᵠ Ket.basis e).vec = (ψ ⊗ᵠ ψ).vec := by
  sorry

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
  sorry

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
  sorry

/-- The state after Alice's gates: `CNOT` from wire `0` to wire `1`, then `H` on wire `0`.
Alice then measures wires `0, 1`. [dW26, §1.5] -/
def teleportState (ψ : Ket (Reg 1)) : Ket (Reg 3) :=
  ((teleportInit ψ).evolve (applyOnU wires01 Gate.CNOT)).evolve (applyOnU (wire 0) Gate.H)

/-- `teleportState ψ` is `teleportInit ψ` after `CNOT` on wires `0, 1` and `H` on wire `0`. -/
theorem teleportState_eq (ψ : Ket (Reg 1)) :
    teleportState ψ =
      ((teleportInit ψ).evolve (applyOnU wires01 Gate.CNOT)).evolve (applyOnU (wire 0) Gate.H) :=
  rfl

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
  sorry

/-- Each of Alice's four measurement outcomes `(m₀, m₁)` occurs with probability `1/4`,
whatever `ψ` is. [dW26, §1.5]

**Proof sketch.** By `teleportState_vec`, the outcome's probability is
`¼ ∑_c ‖(X^{m₁} Z^{m₀} ψ)(c)‖²`, and `X^{m₁} Z^{m₀}` is unitary
(`sum_norm_sq_mulVec_of_mem_unitaryGroup`), so the sum is `‖ψ‖² = 1`. -/
theorem teleport_outcome_prob (ψ : Ket (Reg 1)) (m₀ m₁ : Qubit) :
    ∑ y ∈ Finset.univ.filter (fun y : Reg 3 => y 0 = m₀ ∧ y 1 = m₁), (teleportState ψ).prob y =
      1 / 4 := by
  sorry

/-- Bob's qubit after Alice measures `(m₀, m₁)`, unnormalized: the amplitudes of
`teleportState ψ` with wires `0, 1` fixed to `m₀, m₁`. -/
def bobVec (ψ : Ket (Reg 1)) (m₀ m₁ : Qubit) : Reg 1 → ℂ :=
  fun b => (teleportState ψ).vec ![m₀, m₁, b 0]

/-- `bobVec ψ m₀ m₁ b` is the amplitude of `teleportState ψ` at `(m₀, m₁, b)`. -/
theorem bobVec_apply (ψ : Ket (Reg 1)) (m₀ m₁ : Qubit) (b : Reg 1) :
    bobVec ψ m₀ m₁ b = (teleportState ψ).vec ![m₀, m₁, b 0] := rfl

/-- **Teleportation is correct.** After Alice's outcome `(m₀, m₁)`, Bob applies `X^{m₁}` and
then `Z^{m₀}`, and holds `ψ` (scaled by `½`, the amplitude of the outcome). [dW26, §1.5]

**Proof sketch.** By `teleportState_vec`, `bobVec ψ m₀ m₁ = ½ X^{m₁} Z^{m₀} ψ`. Then
`Z^{m₀} X^{m₁} X^{m₁} Z^{m₀} = 1`, since `X X = 1` and `Z Z = 1` (from `H_mul_H`,
`S_mul_S` and `H_mul_Z_mul_H`, or by computing the four entries). -/
theorem teleport_correct (ψ : Ket (Reg 1)) (m₀ m₁ : Qubit) :
    ((Gate.Z ^ m₀.val * Gate.X ^ m₁.val : Gate 1) : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ
        bobVec ψ m₀ m₁ =
      (1 / 2 : ℂ) • ψ.vec := by
  sorry

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

/-- **Superdense coding.** Measuring Bob's two qubits gives Alice's bits `(b₀, b₁)` with
certainty: one qubit carries two classical bits, given shared entanglement. [NC10, §2.3]

**Proof sketch.** Compute the four cases. `Z` on wire `0` turns `|00⟩ + |11⟩` into
`|00⟩ - |11⟩`, and `X` swaps the value of wire `0`; then `CNOT` and `H` map the four Bell states
`X^{b₁} Z^{b₀} ⊗ I (|00⟩ + |11⟩)/√2` to `±|b₀ b₁⟩`. A global sign does not change the
probability. -/
theorem superdense_decode (b₀ b₁ : Qubit) : (superdenseState b₀ b₁).prob ![b₀, b₁] = 1 := by
  sorry

end Quantum
