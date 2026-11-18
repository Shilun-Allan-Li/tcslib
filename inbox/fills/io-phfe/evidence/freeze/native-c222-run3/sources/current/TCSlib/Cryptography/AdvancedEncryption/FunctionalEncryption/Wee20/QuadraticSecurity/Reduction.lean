/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Derived

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The two explicit outer MDDH reductions

## Main definitions

* `Wee20.Quadratic.crossLeakLeft`, `crossLeakRight`: source-group leakage from one unknown
  GROUP vector and the other known scalar vector.
* `Wee20.Quadratic.red2Handler`, `red3Handler`: deterministic adaptive handlers.
* `Wee20.Quadratic.red2`, `red3`: singleton-bit L2 reductions for the two mask replacements.

## Main results

Equation readers expose the complete algorithms. No handler or reduction samples. The
unknown challenge matrix and vector remain group elements; scalar advice supplies only
independent setup masks, Π randomness and the known other vector.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §3.3, pp. 7–8,
  Game 2 to Game 3 and Game 3 to Game 4. The source-group value is read with §3.1, (5).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- Compute the tensor leakage with GROUP y1 and known scalar y2, then divide by the
allowed source-group value [Wee20, §3.3, pp. 7–8, Game 2 to Game 3]. -/
def crossLeakLeft (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → pp.group.G) (y2 : Fin (n2.eval κ) → ZMod pp.group.order)
    (mu : pp.group.G) : pp.group.G :=
  groupDot (fun i => let j := finProdFinEquiv.symm i; y1 j.1 ^ (y2 j.2).val)
    (PG.eval κ pp.orderParam f x) * mu⁻¹

/-- Left tensor leakage uses only known scalar powers of the supplied group vector. -/
theorem crossLeakLeft_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → pp.group.G) (y2 : Fin (n2.eval κ) → ZMod pp.group.order)
    (mu : pp.group.G) : crossLeakLeft G n1 n2 PG κ pp f x y1 y2 mu =
      groupDot (fun i => let j := finProdFinEquiv.symm i; y1 j.1 ^ (y2 j.2).val)
        (PG.eval κ pp.orderParam f x) * mu⁻¹ := rfl

/-- Compute tensor leakage with known scalar y1 and GROUP y2, then divide by the allowed
source-group value [Wee20, §3.3, pp. 7–8, Game 3 to Game 4]. -/
def crossLeakRight (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → ZMod pp.group.order) (y2 : Fin (n2.eval κ) → pp.group.G)
    (mu : pp.group.G) : pp.group.G :=
  groupDot (fun i => let j := finProdFinEquiv.symm i; y2 j.2 ^ (y1 j.1).val)
    (PG.eval κ pp.orderParam f x) * mu⁻¹

/-- Right tensor leakage uses only known scalar powers of the supplied group vector. -/
theorem crossLeakRight_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) (f : Fn κ pp.orderParam)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → ZMod pp.group.order) (y2 : Fin (n2.eval κ) → pp.group.G)
    (mu : pp.group.G) : crossLeakRight G n1 n2 PG κ pp f x y1 y2 mu =
      groupDot (fun i => let j := finProdFinEquiv.symm i; y2 j.2 ^ (y1 j.1).val)
        (PG.eval κ pp.orderParam f x) * mu⁻¹ := rfl

/-- Replace the first vector using MDDH¹_{2,n1}. The public first matrix and ciphertext
first vector remain GROUP data; all key leakage uses known scalar y2
[Wee20, §3.3, pp. 7–8, Game 2 to Game 3]. -/
def red2Handler (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) n1 κ) (m : Masks G n1 n2 κ c.pp)
    (st : Linear.SimState G ℓ (piDim n1 n2) κ c.pp)
    (ω : Linear.SecurityDraw G PG (piDim n1 n2) q κ c.pp) :
    ∀ i, (saSpec G n1 n2 PG κ c.pp).dom i → SAState G ℓ n1 n2 κ c.pp →
      (saSpec G n1 n2 PG κ c.pp).rng i × SAState G ℓ n1 n2 κ c.pp :=
  let A2 := c.pp.group.expMat c.pp.generator m.A2
  let M := mixGroup G n1 n2 κ c.pp c.matrixᵀ A2
  let first := fun (msg : Challenge G ℓ n1 n2 κ c.pp) => (fun i => c.response i (0 : Fin 1)) *
    c.pp.group.expVec c.pp.generator msg.2.1
  let second := fun (msg : Challenge G ℓ n1 n2 κ c.pp) => Matrix.vecMul m.s2 m.A2 + msg.2.2
  protocolHandler G n1 n2 PG (q.eval κ) κ c.pp
    (fun msg => ⟨first msg, c.pp.group.expVec c.pp.generator (second msg),
      Linear.simEncCore G ℓ (piDim n1 n2) κ c.pp st msg.1⟩)
    (fun j msg f => ⟨f, ⟨M, Linear.simKeyCore G PG (piDim n1 n2) κ c.pp st f M msg.1
      (crossLeakLeft G n1 n2 PG κ c.pp f msg.1 (first msg) (second msg)
        (c.pp.generator ^ (value G n1 n2 PG κ c.pp f msg.1 msg.2.1 msg.2.2).val))
      (Linear.simKeyAt G PG (piDim n1 n2) q κ c.pp ω j f)⟩⟩)

/-- The first replacement handler is the displayed pure protocol. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem red2Handler_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) n1 κ) (m : Masks G n1 n2 κ c.pp)
    (st : Linear.SimState G ℓ (piDim n1 n2) κ c.pp)
    (ω : Linear.SecurityDraw G PG (piDim n1 n2) q κ c.pp) :
    red2Handler G n1 n2 q PG κ c m st ω =
      let A2 := c.pp.group.expMat c.pp.generator m.A2
      let M := mixGroup G n1 n2 κ c.pp c.matrixᵀ A2
      let first := fun (msg : Challenge G ℓ n1 n2 κ c.pp) => (fun i => c.response i (0 : Fin 1)) *
        c.pp.group.expVec c.pp.generator msg.2.1
      let second := fun (msg : Challenge G ℓ n1 n2 κ c.pp) => Matrix.vecMul m.s2 m.A2 + msg.2.2
      protocolHandler G n1 n2 PG (q.eval κ) κ c.pp
        (fun msg => ⟨first msg, c.pp.group.expVec c.pp.generator (second msg),
          Linear.simEncCore G ℓ (piDim n1 n2) κ c.pp st msg.1⟩)
        (fun j msg f => ⟨f, ⟨M, Linear.simKeyCore G PG (piDim n1 n2) κ c.pp st f M msg.1
          (crossLeakLeft G n1 n2 PG κ c.pp f msg.1 (first msg) (second msg)
            (c.pp.generator ^ (value G n1 n2 PG κ c.pp f msg.1 msg.2.1 msg.2.2).val))
          (Linear.simKeyAt G PG (piDim n1 n2) q κ c.pp ω j f)⟩⟩) := rfl

/-- Replace the second vector using MDDH¹_{2,n2}; y1 is already a known uniform scalar
advice vector [Wee20, §3.3, pp. 7–8, Game 3 to Game 4]. -/
def red3Handler (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) n2 κ) (m : Masks G n1 n2 κ c.pp)
    (st : Linear.SimState G ℓ (piDim n1 n2) κ c.pp)
    (ω : Linear.SecurityDraw G PG (piDim n1 n2) q κ c.pp) :
    ∀ i, (saSpec G n1 n2 PG κ c.pp).dom i → SAState G ℓ n1 n2 κ c.pp →
      (saSpec G n1 n2 PG κ c.pp).rng i × SAState G ℓ n1 n2 κ c.pp :=
  let A1 := c.pp.group.expMat c.pp.generator m.A1
  let M := mixGroup G n1 n2 κ c.pp A1 c.matrixᵀ
  let second := fun (msg : Challenge G ℓ n1 n2 κ c.pp) => (fun i => c.response i (0 : Fin 1)) *
    c.pp.group.expVec c.pp.generator msg.2.2
  protocolHandler G n1 n2 PG (q.eval κ) κ c.pp
    (fun msg => ⟨c.pp.group.expVec c.pp.generator m.y1, second msg,
      Linear.simEncCore G ℓ (piDim n1 n2) κ c.pp st msg.1⟩)
    (fun j msg f => ⟨f, ⟨M, Linear.simKeyCore G PG (piDim n1 n2) κ c.pp st f M msg.1
      (crossLeakRight G n1 n2 PG κ c.pp f msg.1 m.y1 (second msg)
        (c.pp.generator ^ (value G n1 n2 PG κ c.pp f msg.1 msg.2.1 msg.2.2).val))
      (Linear.simKeyAt G PG (piDim n1 n2) q κ c.pp ω j f)⟩⟩)

/-- The second replacement handler is the displayed pure protocol. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem red3Handler_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) n2 κ) (m : Masks G n1 n2 κ c.pp)
    (st : Linear.SimState G ℓ (piDim n1 n2) κ c.pp)
    (ω : Linear.SecurityDraw G PG (piDim n1 n2) q κ c.pp) :
    red3Handler G n1 n2 q PG κ c m st ω =
      let A1 := c.pp.group.expMat c.pp.generator m.A1
      let M := mixGroup G n1 n2 κ c.pp A1 c.matrixᵀ
      let second := fun (msg : Challenge G ℓ n1 n2 κ c.pp) => (fun i => c.response i (0 : Fin 1)) *
        c.pp.group.expVec c.pp.generator msg.2.2
      protocolHandler G n1 n2 PG (q.eval κ) κ c.pp
        (fun msg => ⟨c.pp.group.expVec c.pp.generator m.y1, second msg,
          Linear.simEncCore G ℓ (piDim n1 n2) κ c.pp st msg.1⟩)
        (fun j msg f => ⟨f, ⟨M, Linear.simKeyCore G PG (piDim n1 n2) κ c.pp st f M msg.1
          (crossLeakRight G n1 n2 PG κ c.pp f msg.1 m.y1 (second msg)
            (c.pp.generator ^ (value G n1 n2 PG κ c.pp f msg.1 msg.2.1 msg.2.2).val))
          (Linear.simKeyAt G PG (piDim n1 n2) q κ c.pp ω j f)⟩⟩) := rfl

/-- The first outer L2 reduction fixes the finite advice and runs the original typed
adversary without sampling [Wee20, §3.3, pp. 7–8, Game 2 to Game 3]. -/
noncomputable def red2 (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (ω : ∀ κ, Advice n1 n2 A.budget PG p κ) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) n1 κ) (r : List Bool) : List Bool :=
  let tape := adviceDraw G n1 n2 A.budget PG p hp κ c.pp (ω κ)
  let m := masksAt G n1 n2 κ c.pp tape.1
  let ctx := Linear.simSetupCore G ℓ (piDim n1 n2) κ c.pp
    (Linear.setupAt G PG (piDim n1 n2) A.budget κ c.pp tape.2)
  let pk : MPK G ℓ n1 n2 κ c.pp :=
    ⟨c.matrixᵀ, c.pp.group.expMat c.pp.generator m.A2, ctx.1⟩
  [(runDet (A.next κ c.pp pk r) false
    (red2Handler G n1 n2 A.budget PG κ c m ctx.2 tape.2)
    (A.budget.eval κ) [] ⟨none, 0⟩).1]

/-- The first L2 reduction exposes its exact advice, public key and runDet result. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem red2_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (ω : ∀ κ, Advice n1 n2 A.budget PG p κ) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) n1 κ) (r : List Bool) :
    red2 G n1 n2 PG p hp A ω κ c r =
      let tape := adviceDraw G n1 n2 A.budget PG p hp κ c.pp (ω κ)
      let m := masksAt G n1 n2 κ c.pp tape.1
      let ctx := Linear.simSetupCore G ℓ (piDim n1 n2) κ c.pp
        (Linear.setupAt G PG (piDim n1 n2) A.budget κ c.pp tape.2)
      let pk : MPK G ℓ n1 n2 κ c.pp :=
        ⟨c.matrixᵀ, c.pp.group.expMat c.pp.generator m.A2, ctx.1⟩
      [(runDet (A.next κ c.pp pk r) false
        (red2Handler G n1 n2 A.budget PG κ c m ctx.2 tape.2)
        (A.budget.eval κ) [] ⟨none, 0⟩).1] := rfl

/-- The second outer L2 reduction fixes its independent finite advice and never samples
[Wee20, §3.3, pp. 7–8, Game 3 to Game 4]. -/
noncomputable def red3 (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (ω : ∀ κ, Advice n1 n2 A.budget PG p κ) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) n2 κ) (r : List Bool) : List Bool :=
  let tape := adviceDraw G n1 n2 A.budget PG p hp κ c.pp (ω κ)
  let m := masksAt G n1 n2 κ c.pp tape.1
  let ctx := Linear.simSetupCore G ℓ (piDim n1 n2) κ c.pp
    (Linear.setupAt G PG (piDim n1 n2) A.budget κ c.pp tape.2)
  let pk : MPK G ℓ n1 n2 κ c.pp :=
    ⟨c.pp.group.expMat c.pp.generator m.A1, c.matrixᵀ, ctx.1⟩
  [(runDet (A.next κ c.pp pk r) false
    (red3Handler G n1 n2 A.budget PG κ c m ctx.2 tape.2)
    (A.budget.eval κ) [] ⟨none, 0⟩).1]

/-- The second L2 reduction exposes its exact advice, public key and runDet result. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem red3_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (ω : ∀ κ, Advice n1 n2 A.budget PG p κ) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) n2 κ) (r : List Bool) :
    red3 G n1 n2 PG p hp A ω κ c r =
      let tape := adviceDraw G n1 n2 A.budget PG p hp κ c.pp (ω κ)
      let m := masksAt G n1 n2 κ c.pp tape.1
      let ctx := Linear.simSetupCore G ℓ (piDim n1 n2) κ c.pp
        (Linear.setupAt G PG (piDim n1 n2) A.budget κ c.pp tape.2)
      let pk : MPK G ℓ n1 n2 κ c.pp :=
        ⟨c.pp.group.expMat c.pp.generator m.A1, c.matrixᵀ, ctx.1⟩
      [(runDet (A.next κ c.pp pk r) false
        (red3Handler G n1 n2 A.budget PG κ c m ctx.2 tape.2)
        (A.budget.eval κ) [] ⟨none, 0⟩).1] := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
