/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Data

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The five explicit quadratic security games

## Main definitions

* `Wee20.Quadratic.maskedVectors`: the two real or uniform scalar masks in each game.
* `Wee20.Quadratic.gameHandler`: actual Games 0–4, including the distinct leakage formulas.
* `Wee20.Quadratic.runGameDet`, `game`: deterministic bounded runs and exact draw laws.
* `Wee20.Quadratic.saGame`, `saSimAdv`: the unfiltered endpoints and their advantage.

## Main results

Every handler and law has an equation reader. Π's singular-basis behavior remains total;
no additional rank filter is added by the outer games.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §3.3, pp. 7–8, Games 0–4,
  with §3.1, equation (5), p. 6 and §3.2, p. 7. Leakage values are in the source group.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- Games 0–2 use both real masks, Game 3 replaces y1, and Game 4 replaces y2 as well
[Wee20, §3.3, pp. 7–8]. All scalar values here come from explicit scalar draws. -/
def maskedVectors (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (mode : Fin 5)
    (κ : ℕ) (pp : PublicParams G κ) (m : Masks G n1 n2 κ pp)
    (msg : Challenge G ℓ n1 n2 κ pp) :
    (Fin (n1.eval κ) → ZMod pp.group.order) × (Fin (n2.eval κ) → ZMod pp.group.order) :=
  (if 3 ≤ mode.val then m.y1 else Matrix.vecMul m.s1 m.A1 + msg.2.1,
    if 4 ≤ mode.val then m.y2 else Matrix.vecMul m.s2 m.A2 + msg.2.2)

/-- The two scalar mask choices expose the exact thresholds of the outer hybrids. -/
theorem maskedVectors_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (mode : Fin 5)
    (κ : ℕ) (pp : PublicParams G κ) (m : Masks G n1 n2 κ pp)
    (msg : Challenge G ℓ n1 n2 κ pp) : maskedVectors G ℓ n1 n2 mode κ pp m msg =
      (if 3 ≤ mode.val then m.y1 else Matrix.vecMul m.s1 m.A1 + msg.2.1,
        if 4 ≤ mode.val then m.y2 else Matrix.vecMul m.s2 m.A2 + msg.2.2) := rfl

/-- Public outer matrices are exponentiated known setup draws, with the supplied Π key
[Wee20, §3.1, p. 6]. -/
def publicFromMasks (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (m : Masks G n1 n2 κ pp)
    (pk : Linear.MPK G ℓ (piDim n1 n2) κ pp) : MPK G ℓ n1 n2 κ pp :=
  ⟨pp.group.expMat pp.generator m.A1, pp.group.expMat pp.generator m.A2, pk⟩

/-- Public-mask assembly is its two exponentiations and supplied linear public key. -/
theorem publicFromMasks_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (m : Masks G n1 n2 κ pp)
    (pk : Linear.MPK G ℓ (piDim n1 n2) κ pp) : publicFromMasks G ℓ n1 n2 κ pp m pk =
      ⟨pp.group.expMat pp.generator m.A1, pp.group.expMat pp.generator m.A2, pk⟩ := rfl

/-- The five handlers use honest Π, simulated Π with actual signal leakage, its equation
(5) rewrite, and two successive uniform-vector replacements [Wee20, §3.3, pp. 7–8].
The first leakage is computed directly from the fixed GROUP matrix and known signal;
the later leakage is the SOURCE-GROUP quotient. No target-group inversion is used. -/
def gameHandler (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (mode : Fin 5)
    (κ : ℕ) (pp : PublicParams G κ) (m : Masks G n1 n2 κ pp)
    (pk : Linear.MPK G ℓ (piDim n1 n2) κ pp)
    (st : Linear.SimState G ℓ (piDim n1 n2) κ pp)
    (ω : Linear.SecurityDraw G PG (piDim n1 n2) q κ pp) :
    ∀ i, (saSpec G n1 n2 PG κ pp).dom i → SAState G ℓ n1 n2 κ pp →
      (saSpec G n1 n2 PG κ pp).rng i × SAState G ℓ n1 n2 κ pp :=
  let pub := publicFromMasks G ℓ n1 n2 κ pp m pk
  let M := mixGroup G n1 n2 κ pp pub.A1 pub.A2
  protocolHandler G n1 n2 PG (q.eval κ) κ pp
    (fun msg => if mode.val = 0 then encCore G ℓ n1 n2 κ pp pub msg.1 msg.2.1 msg.2.2
      ⟨m.s1, m.s2, Linear.seedAt G PG (piDim n1 n2) q κ pp ω⟩
    else
      let ys := maskedVectors G ℓ n1 n2 mode κ pp m msg
      ⟨pp.group.expVec pp.generator ys.1, pp.group.expVec pp.generator ys.2,
        Linear.simEncCore G ℓ (piDim n1 n2) κ pp st msg.1⟩)
    (fun j msg f =>
      let ys := maskedVectors G ℓ n1 n2 mode κ pp m msg
      let sr := Linear.simKeyAt G PG (piDim n1 n2) q κ pp ω j f
      ⟨f, ⟨M, if mode.val = 0 then
          Linear.keyCore G PG (piDim n1 n2) κ pp ⟨st.W, st.U, st.V⟩ f M
            (Linear.keyAt G PG (piDim n1 n2) q κ pp ω j f)
        else
          let mu := if mode.val = 1 then Linear.leak G PG (piDim n1 n2) κ pp f M msg.1
              (signalScalar (p := pp.orderParam) m.s1 msg.2.2 ys.1 m.s2)
            else crossLeak G n1 n2 PG κ pp ⟨M, st, ys.1, ys.2⟩ f msg.1
              (pp.generator ^ (value G n1 n2 PG κ pp f msg.1 msg.2.1 msg.2.2).val)
          Linear.simKeyCore G PG (piDim n1 n2) κ pp st f M msg.1 mu sr⟩⟩)

/-- The handler exposes the five distinct ciphertext and key formulas. 

**Proof sketch.** Each branch and named block is the same as in the deterministic
definition, so the equation follows by reducing that definition alone. -/
theorem gameHandler_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (mode : Fin 5)
    (κ : ℕ) (pp : PublicParams G κ) (m : Masks G n1 n2 κ pp)
    (pk : Linear.MPK G ℓ (piDim n1 n2) κ pp)
    (st : Linear.SimState G ℓ (piDim n1 n2) κ pp)
    (ω : Linear.SecurityDraw G PG (piDim n1 n2) q κ pp) :
    gameHandler G n1 n2 q PG mode κ pp m pk st ω =
      let pub := publicFromMasks G ℓ n1 n2 κ pp m pk
      let M := mixGroup G n1 n2 κ pp pub.A1 pub.A2
      protocolHandler G n1 n2 PG (q.eval κ) κ pp
        (fun msg => if mode.val = 0 then encCore G ℓ n1 n2 κ pp pub msg.1 msg.2.1 msg.2.2
          ⟨m.s1, m.s2, Linear.seedAt G PG (piDim n1 n2) q κ pp ω⟩
        else
          let ys := maskedVectors G ℓ n1 n2 mode κ pp m msg
          ⟨pp.group.expVec pp.generator ys.1, pp.group.expVec pp.generator ys.2,
            Linear.simEncCore G ℓ (piDim n1 n2) κ pp st msg.1⟩)
        (fun j msg f =>
          let ys := maskedVectors G ℓ n1 n2 mode κ pp m msg
          let sr := Linear.simKeyAt G PG (piDim n1 n2) q κ pp ω j f
          ⟨f, ⟨M, if mode.val = 0 then
              Linear.keyCore G PG (piDim n1 n2) κ pp ⟨st.W, st.U, st.V⟩ f M
                (Linear.keyAt G PG (piDim n1 n2) q κ pp ω j f)
            else
              let mu := if mode.val = 1 then Linear.leak G PG (piDim n1 n2) κ pp f M msg.1
                  (signalScalar (p := pp.orderParam) m.s1 msg.2.2 ys.1 m.s2)
                else crossLeak G n1 n2 PG κ pp ⟨M, st, ys.1, ys.2⟩ f msg.1
                  (pp.generator ^ (value G n1 n2 PG κ pp f msg.1 msg.2.1 msg.2.2).val)
              Linear.simKeyCore G PG (piDim n1 n2) κ pp st f M msg.1 mu sr⟩⟩) := rfl

section NamedHandlers

variable (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr) {Fn : ℕ → ℕ+ → Type}
  (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) (κ : ℕ) (pp : PublicParams G κ)
  (m : Masks G n1 n2 κ pp) (pk : Linear.MPK G ℓ (piDim n1 n2) κ pp)
  (st : Linear.SimState G ℓ (piDim n1 n2) κ pp)
  (ω : Linear.SecurityDraw G PG (piDim n1 n2) q κ pp)

/-- Honest outer encryption and keys [Wee20, §3.3, Game 0, p. 7]. -/
def game0Handler := gameHandler G n1 n2 q PG 0 κ pp m pk st ω
/-- Actual simulated Π with actual group signal leakage [Wee20, §3.3, Game 1, p. 7]. -/
def game1Handler := gameHandler G n1 n2 q PG 1 κ pp m pk st ω
/-- The equivalent difference leakage [Wee20, §3.3, Game 2, p. 7]. -/
def game2Handler := gameHandler G n1 n2 q PG 2 κ pp m pk st ω
/-- The first uniformly replaced vector [Wee20, §3.3, Game 3, p. 8]. -/
def game3Handler := gameHandler G n1 n2 q PG 3 κ pp m pk st ω
/-- Both uniformly replaced vectors [Wee20, §3.3, Game 4, p. 8]. -/
def game4Handler := gameHandler G n1 n2 q PG 4 κ pp m pk st ω

/-- Game 0 is its explicit formula. -/
theorem game0Handler_eq : game0Handler G n1 n2 q PG κ pp m pk st ω =
    gameHandler G n1 n2 q PG 0 κ pp m pk st ω := rfl
/-- Game 1 is its explicit formula. -/
theorem game1Handler_eq : game1Handler G n1 n2 q PG κ pp m pk st ω =
    gameHandler G n1 n2 q PG 1 κ pp m pk st ω := rfl
/-- Game 2 is its explicit formula. -/
theorem game2Handler_eq : game2Handler G n1 n2 q PG κ pp m pk st ω =
    gameHandler G n1 n2 q PG 2 κ pp m pk st ω := rfl
/-- Game 3 is its explicit formula. -/
theorem game3Handler_eq : game3Handler G n1 n2 q PG κ pp m pk st ω =
    gameHandler G n1 n2 q PG 3 κ pp m pk st ω := rfl
/-- Game 4 is its explicit formula. -/
theorem game4Handler_eq : game4Handler G n1 n2 q PG κ pp m pk st ω =
    gameHandler G n1 n2 q PG 4 κ pp m pk st ω := rfl

end NamedHandlers

/-- The pure game fixes both finite tapes and uses the shared interpreter at the TOTAL
budget [Wee20, §3.3, pp. 7–8]. There is no outer singular-basis filter. -/
noncomputable def runGameDet (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (mode : Fin 5) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G n1 n2 A.budget PG κ pp) (r : List Bool) : Bool :=
  let m := masksAt G n1 n2 κ pp ω.1
  let ctx := Linear.simSetupCore G ℓ (piDim n1 n2) κ pp
    (Linear.setupAt G PG (piDim n1 n2) A.budget κ pp ω.2)
  (runDet (A.next κ pp (publicFromMasks G ℓ n1 n2 κ pp m ctx.1) r) false
    (gameHandler G n1 n2 A.budget PG mode κ pp m ctx.1 ctx.2 ω.2)
    (A.budget.eval κ) [] ⟨none, 0⟩).1

/-- The pure game is its displayed setup and exact total-budget run. -/
theorem runGameDet_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (mode : Fin 5) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G n1 n2 A.budget PG κ pp) (r : List Bool) :
    runGameDet G n1 n2 PG A mode κ pp ω r =
      let m := masksAt G n1 n2 κ pp ω.1
      let ctx := Linear.simSetupCore G ℓ (piDim n1 n2) κ pp
        (Linear.setupAt G PG (piDim n1 n2) A.budget κ pp ω.2)
      (runDet (A.next κ pp (publicFromMasks G ℓ n1 n2 κ pp m ctx.1) r) false
        (gameHandler G n1 n2 A.budget PG mode κ pp m ctx.1 ctx.2 ω.2)
        (A.budget.eval κ) [] ⟨none, 0⟩).1 := rfl

/-- Each of the five laws samples public parameters, the complete finite tapes and the
adversary's independent coins [Wee20, §3.3, pp. 7–8]. -/
noncomputable def game (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (mode : Fin 5) (κ : ℕ) : ProbComp Bool :=
  (publicParamsGen G κ).bind fun pp =>
  (ProbComp.sample (SecurityDraw G n1 n2 A.budget PG κ pp)).bind fun ω =>
  (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
    .pure (runGameDet G n1 n2 PG A mode κ pp ω (List.ofFn r))

/-- The game law is its exact draw-and-run sequence. -/
theorem game_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (mode : Fin 5) (κ : ℕ) : game G n1 n2 PG A mode κ =
      (publicParamsGen G κ).bind fun pp =>
      (ProbComp.sample (SecurityDraw G n1 n2 A.budget PG κ pp)).bind fun ω =>
      (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
        .pure (runGameDet G n1 n2 PG A mode κ pp ω (List.ofFn r)) := rfl

/-- The endpoint experiment selects honest Game 0 or total ideal Game 4
[Wee20, §2.2, p. 5; §3.3, pp. 7–8]. Fresh-law correspondence is stated separately. -/
noncomputable def saGame (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (ideal : Bool) (κ : ℕ) : ProbComp Bool :=
  game G n1 n2 PG A (if ideal then 4 else 0) κ

/-- The endpoint choice is its displayed indexed game. -/
theorem saGame_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (ideal : Bool) (κ : ℕ) : saGame G n1 n2 PG A ideal κ =
      game G n1 n2 PG A (if ideal then 4 else 0) κ := rfl

/-- Simulation advantage compares the two unfiltered outer endpoints
[Wee20, §3, p. 6, main security claim; §3.3, pp. 7–8]. -/
noncomputable def saSimAdv (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) : ℝ :=
  advantage (saGame G n1 n2 PG A false κ) (saGame G n1 n2 PG A true κ)

/-- The outer advantage is the shared two-experiment advantage. -/
theorem saSimAdv_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) : saSimAdv G n1 n2 PG A κ =
      advantage (saGame G n1 n2 PG A false κ) (saGame G n1 n2 PG A true κ) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
