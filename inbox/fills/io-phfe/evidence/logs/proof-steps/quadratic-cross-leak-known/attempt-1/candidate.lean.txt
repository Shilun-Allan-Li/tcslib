/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The raw stateful quadratic simulator

Setup creates the two group masking matrices and Π's simulated public key. Encryption
chooses scalar masks `y1,y2`, publishes their group representations, and retains the scalars
for all later adaptive key queries. Before encryption those retained vectors are defined
as zero, giving a total core without extending the security notion to premature queries.

## Main definitions

* `Wee20.Quadratic.SimState`, `SimSetupDraw`, `SimEncDraw`: state and exact draw types.
* `Wee20.Quadratic.simSetupCore`, `simEncCore`, `simKeyCore`: simulator algorithms.
* `Wee20.Quadratic.crossLeak`: compute the source-group cross-term value from the allowed
  SOURCE-GROUP value and retained scalar masks.
* `Wee20.Quadratic.simSetup`, `simEnc`, `simKey`: exact core-plus-draw laws.

## Main results

* Equation readers expose every algorithm, draw type and law.
* `Wee20.Quadratic.crossLeak_known_value`: with a known scalar allowed value the group
  computation equals the corresponding difference in the exponent.

The source's group-tag misprint in Enc* is read in its intended source group. The allowed
value in KeyGen* and the computed cross-term value are source-group values, as Π requires;
no target-group value is inverted to a source-group element.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §3.2, p. 7, Setup*, Enc*,
  KeyGen* (group tags read with §3.1 and §3.3, Game 2), and §4.2, p. 10.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- The simulator stores its fixed public group matrix, Π's state and its scalar ciphertext
masks [Wee20, §3.2, p. 7]. Zero masks specify the state before the single challenge. -/
structure SimState (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The fixed public group matrix used in every function key. -/
  matrix : Matrix (Fin ((piDim n1 n2).eval κ)) (Fin ((n1.mul n2).eval κ)) pp.group.G
  /-- The linear simulator's state. -/
  linear : Linear.SimState G ℓ (piDim n1 n2) κ pp
  /-- The retained first scalar ciphertext mask. -/
  y1 : Fin (n1.eval κ) → ZMod pp.group.order
  /-- The retained second scalar ciphertext mask. -/
  y2 : Fin (n2.eval κ) → ZMod pp.group.order

/-- Simulated setup draws its two scalar public masks and Π's simulator setup draw
[Wee20, §3.2, p. 7, Setup*]. -/
abbrev SimSetupDraw (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  Matrix (Fin 2) (Fin (n1.eval κ)) (ZMod pp.group.order) ×
    Matrix (Fin 2) (Fin (n2.eval κ)) (ZMod pp.group.order) ×
    Linear.SimSetupDraw G ℓ (piDim n1 n2) κ pp

/-- The setup draw consists of its two outer masks and the linear simulator's draw. -/
theorem simSetupDraw_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) :
    SimSetupDraw G ℓ n1 n2 κ pp =
      (Matrix (Fin 2) (Fin (n1.eval κ)) (ZMod pp.group.order) ×
        Matrix (Fin 2) (Fin (n2.eval κ)) (ZMod pp.group.order) ×
        Linear.SimSetupDraw G ℓ (piDim n1 n2) κ pp) := rfl

/-- Simulated encryption draws two independent scalar masks
[Wee20, §3.2, p. 7, Enc*]. The scalar field is the order of the public group. -/
abbrev SimEncDraw (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  (Fin (n1.eval κ) → ZMod pp.group.order) × (Fin (n2.eval κ) → ZMod pp.group.order)

/-- The encryption draw is exactly the pair of scalar vector masks. -/
theorem simEncDraw_eq (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    SimEncDraw G n1 n2 κ pp =
      ((Fin (n1.eval κ) → ZMod pp.group.order) ×
        (Fin (n2.eval κ) → ZMod pp.group.order)) := rfl

instance instSimSetupDrawFinite (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G
  κ) :
    Fintype (SimSetupDraw G ℓ n1 n2 κ pp) := inferInstance

instance instSimSetupDrawNonempty (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams
  G κ) :
    Nonempty (SimSetupDraw G ℓ n1 n2 κ pp) := inferInstance

instance instSimEncDrawFinite (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    Fintype (SimEncDraw G n1 n2 κ pp) := inferInstance

instance instSimEncDrawNonempty (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
  :
    Nonempty (SimEncDraw G n1 n2 κ pp) := inferInstance

/-- Simulator setup computes its public group matrices and retains the fixed group matrix
with Π's simulator state [Wee20, §3.2, p. 7, Setup*]. The two retained ciphertext masks are
initialized to zero. Π's total scalar inverse also specifies singular setups. -/
noncomputable def simSetupCore (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : SimSetupDraw G ℓ n1 n2 κ pp) :
    MPK G ℓ n1 n2 κ pp × SimState G ℓ n1 n2 κ pp :=
  let A1 := pp.group.expMat pp.generator ω.1
  let A2 := pp.group.expMat pp.generator ω.2.1
  let linear := Linear.simSetupCore G ℓ (piDim n1 n2) κ pp ω.2.2
  (⟨A1, A2, linear.1⟩, ⟨mixGroup G n1 n2 κ pp A1 A2, linear.2, 0, 0⟩)

/-- Simulated setup exposes its public matrices, linear state and zero initial masks. -/
theorem simSetupCore_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : SimSetupDraw G ℓ n1 n2 κ pp) :
    simSetupCore G ℓ n1 n2 κ pp ω =
      let A1 := pp.group.expMat pp.generator ω.1
      let A2 := pp.group.expMat pp.generator ω.2.1
      let linear := Linear.simSetupCore G ℓ (piDim n1 n2) κ pp ω.2.2
      (⟨A1, A2, linear.1⟩, ⟨mixGroup G n1 n2 κ pp A1 A2, linear.2, 0, 0⟩) := rfl

/-- Simulated encryption publishes its freshly drawn masks and retains their scalars for
later keys [Wee20, §3.2, p. 7, Enc*]. Both group components use the source group, reading
the second component's printed subscript with §3.1. -/
def simEncCore (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ n1 n2 κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (ω : SimEncDraw G n1 n2 κ pp) : CT G n1 n2 κ pp × SimState G ℓ n1 n2 κ pp :=
  (⟨pp.group.expVec pp.generator ω.1, pp.group.expVec pp.generator ω.2,
    Linear.simEncCore G ℓ (piDim n1 n2) κ pp st.linear x⟩,
    ⟨st.matrix, st.linear, ω.1, ω.2⟩)

/-- The ideal ciphertext masks and next state's retained masks are the same draw. -/
theorem simEncCore_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (st : SimState G ℓ n1 n2 κ pp)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (ω : SimEncDraw G n1 n2 κ pp) :
    simEncCore G ℓ n1 n2 κ pp st x ω =
      (⟨pp.group.expVec pp.generator ω.1, pp.group.expVec pp.generator ω.2,
        Linear.simEncCore G ℓ (piDim n1 n2) κ pp st.linear x⟩,
        ⟨st.matrix, st.linear, ω.1, ω.2⟩) := rfl

/-- The cross-term leakage is `g^((y1⊗y2)f(x)^T) / [mu]` in the SOURCE group
[Wee20, §3.2, p. 7, KeyGen*, read with §3.3, Game 2]. Only the retained scalar masks are
used to form the first factor; the allowed source-group value is inverted as a group element. -/
def crossLeak (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ n1 n2 κ pp) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G) : pp.group.G :=
  pp.generator ^ (value G n1 n2 PG κ pp f x st.y1 st.y2).val * mu⁻¹

/-- The allowed cross term is the displayed quotient in the source group. -/
theorem crossLeak_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (st : SimState G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G) :
    crossLeak G n1 n2 PG κ pp st f x mu =
      pp.generator ^ (value G n1 n2 PG κ pp f x st.y1 st.y2).val * mu⁻¹ := rfl

/-- With known scalar allowed value, the simulated cross term represents the corresponding
scalar difference [Wee20, §3.3, p. 7, Game 2 and (5)].

**Proof sketch.** Read `crossLeak_eq`, then use the published source-group additive and
negation exponent laws. This uses a supplied scalar value, not an exponent extracted from mu. -/
theorem crossLeak_known_value (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (st : SimState G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (mu : ZMod pp.group.order) :
    crossLeak G n1 n2 PG κ pp st f x (pp.generator ^ mu.val) =
      pp.generator ^ (value G n1 n2 PG κ pp f x st.y1 st.y2 - mu).val := by
  simp only [crossLeak_eq, value_eq, sub_eq_add_neg,
    pp.group.pow_val_add, pp.group.pow_val_neg]

/-- Simulator key generation computes the cross-term group value and forwards it to Π's
simulator [Wee20, §3.2, p. 7, KeyGen*]. The fixed public matrix is retained as key metadata. -/
def simKeyCore (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr) {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ n1 n2 κ pp) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G)
    (ω : Linear.SimKeyDraw G PG κ pp f) : Key G n1 n2 PG κ pp f :=
  ⟨st.matrix, Linear.simKeyCore G PG (piDim n1 n2) κ pp st.linear f st.matrix x
    (crossLeak G n1 n2 PG κ pp st f x mu) ω⟩

/-- The simulated key forwards precisely the group cross-term value to Π. -/
theorem simKeyCore_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (st : SimState G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G)
    (ω : Linear.SimKeyDraw G PG κ pp f) :
    simKeyCore G n1 n2 PG κ pp st f x mu ω =
      ⟨st.matrix, Linear.simKeyCore G PG (piDim n1 n2) κ pp st.linear f st.matrix x
        (crossLeak G n1 n2 PG κ pp st f x mu) ω⟩ := rfl

/-- Simulated setup has its exact core-plus-draw law [Wee20, §3.2, p. 7]. -/
noncomputable def simSetup (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : ProbComp (MPK G ℓ n1 n2 κ pp × SimState G ℓ n1 n2 κ pp) :=
  (simSetupCore G ℓ n1 n2 κ pp <$> (ProbComp.sample (SimSetupDraw G ℓ n1 n2 κ pp)))

/-- Simulated setup is one uniform draw followed by its total core. -/
theorem simSetup_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    simSetup G ℓ n1 n2 κ pp =
      (simSetupCore G ℓ n1 n2 κ pp <$> (ProbComp.sample (SimSetupDraw G ℓ n1 n2 κ pp))) := rfl

/-- Simulated encryption draws the masks once and returns the ciphertext and updated state
[Wee20, §3.2, p. 7]. -/
noncomputable def simEnc (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (st : SimState G ℓ n1 n2 κ pp)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    ProbComp (CT G n1 n2 κ pp × SimState G ℓ n1 n2 κ pp) :=
  (simEncCore G ℓ n1 n2 κ pp st x <$> (ProbComp.sample (SimEncDraw G n1 n2 κ pp)))

/-- Simulated encryption has the displayed stateful core-plus-draw law. -/
theorem simEnc_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (st : SimState G ℓ n1 n2 κ pp) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    simEnc G ℓ n1 n2 κ pp st x =
      (simEncCore G ℓ n1 n2 κ pp st x <$> (ProbComp.sample (SimEncDraw G n1 n2 κ pp))) := rfl

/-- Simulated function keys use Π's single function-dependent draw
[Wee20, §3.2, p. 7]. -/
noncomputable def simKey (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (st : SimState G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G) :
    ProbComp (Key G n1 n2 PG κ pp f) :=
  (simKeyCore G n1 n2 PG κ pp st f x mu <$> (ProbComp.sample (Linear.SimKeyDraw G PG κ pp f)))

/-- Simulated keys have the displayed core-plus-draw law. -/
theorem simKey_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (st : SimState G ℓ n1 n2 κ pp)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) (mu : pp.group.G) :
    simKey G n1 n2 PG κ pp st f x mu =
      (simKeyCore G n1 n2 PG κ pp st f x mu <$> (ProbComp.sample (Linear.SimKeyDraw G PG κ pp f)))
        := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
