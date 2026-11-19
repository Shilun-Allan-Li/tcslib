/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Keys
import TCSlib.Cryptography.Games.Advantage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Six explicit semi-adaptive games for linear PHFE

## Main definitions

* `Wee20.Linear.gameHandler`: the six actual ciphertext/key formulas of the source games.
* `Wee20.Linear.game0Handler` through `game5Handler`: named oracle implementations.
* `Wee20.Linear.runGameDet`, `game`: bounded deterministic runs and their exact laws.
* `Wee20.Linear.saGame`, `saSimAdv`: the unfiltered real and ideal experiments.

## Main results

Equation readers expose every formula and run. The total adversary budget is unchanged.
Intermediate games 2–5 return false on singular augmented bases. The first computational
hop is unfiltered; the theorem compares the two endpoint bad portions together, charging
one exact rank-failure probability rather than two triangle-inequality losses.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.2, p. 5 and Appendix B,
  pp. 12–14, Games 0–5 and Lemmas 2–5.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- The actual six handlers implement honest keys, the basis decomposition, the two
middle key formulas, and the ideal group-leakage simulator in that order
[Wee20, Appendix B, pp. 12–14, Games 0–5]. -/
def gameHandler (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (mode : Fin 6)
    (κ : ℕ) (pp : PublicParams G κ) (st : SimState G ℓ zDim κ pp)
    (ω : SecurityDraw G PG zDim q κ pp) :
    ∀ i, (saSpec G PG zDim κ pp).dom i → SAState G ℓ zDim κ pp →
      (saSpec G PG zDim κ pp).rng i × SAState G ℓ zDim κ pp :=
  protocolHandler G PG zDim (q.eval κ) κ pp
    (fun msg => if mode.val ≤ 2 then
      let c := if mode.val = 0 then
          pp.group.expVec pp.generator (Matrix.vecMul (seedAt G PG zDim q κ pp ω) st.Aᵀ)
        else pp.group.expVec pp.generator st.c
      maskedCipher G ℓ zDim κ pp ⟨st.W, st.U, st.V⟩ c msg
    else simEncCore G ℓ zDim κ pp st msg.1)
    (fun j msg query =>
      let kr := keyAt G PG zDim q κ pp ω j query.fn
      let sr := simKeyAt G PG zDim q κ pp ω j query.fn
      ⟨query.fn,
        if mode.val ≤ 1 then keyCore G PG zDim κ pp ⟨st.W, st.U, st.V⟩ query.fn query.matrix kr
        else if mode.val = 2 then decomposedKey G PG zDim κ pp st query kr
        else if mode.val = 3 then
          let tensorR := Matrix.kroneckerMap (fun a b => a * b)
            (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) sr.2.2.1
          semiKey G PG zDim κ pp st msg query sr.1 sr.2.2.2
            (pp.group.expMat pp.generator sr.2.2.1)
            (pp.group.expVec pp.generator
              (Matrix.vecMul (globalUAt G PG zDim q κ pp ω) tensorR))
        else if mode.val = 4 then semiKey G PG zDim κ pp st msg query sr.1 sr.2.2.2
          (pp.group.expMat pp.generator sr.2.2.1) (pp.group.expVec pp.generator sr.2.1)
        else simKeyCore G PG zDim κ pp st query.fn query.matrix msg.1
          (leak G PG zDim κ pp query.fn query.matrix msg.1 msg.2) sr⟩)

/-- The game handler is the displayed protocol with the six explicit source formulas. 

**Proof sketch.** The equation displays the same branch formulas and named blocks as the
deterministic definition, so reducing that definition alone gives the stated equation. -/
theorem gameHandler_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (mode : Fin 6)
    (κ : ℕ) (pp : PublicParams G κ) (st : SimState G ℓ zDim κ pp)
    (ω : SecurityDraw G PG zDim q κ pp) :
    gameHandler G PG zDim q mode κ pp st ω =
      protocolHandler G PG zDim (q.eval κ) κ pp
        (fun msg => if mode.val ≤ 2 then
          let c := if mode.val = 0 then
              pp.group.expVec pp.generator (Matrix.vecMul (seedAt G PG zDim q κ pp ω) st.Aᵀ)
            else pp.group.expVec pp.generator st.c
          maskedCipher G ℓ zDim κ pp ⟨st.W, st.U, st.V⟩ c msg
        else simEncCore G ℓ zDim κ pp st msg.1)
        (fun j msg query =>
          let kr := keyAt G PG zDim q κ pp ω j query.fn
          let sr := simKeyAt G PG zDim q κ pp ω j query.fn
          ⟨query.fn,
            if mode.val ≤ 1 then
              keyCore G PG zDim κ pp ⟨st.W, st.U, st.V⟩ query.fn query.matrix kr
            else if mode.val = 2 then decomposedKey G PG zDim κ pp st query kr
            else if mode.val = 3 then
              let tensorR := Matrix.kroneckerMap (fun a b => a * b)
                (1 : Matrix (Fin (ℓ.eval κ)) (Fin (ℓ.eval κ)) (ZMod pp.group.order)) sr.2.2.1
              semiKey G PG zDim κ pp st msg query sr.1 sr.2.2.2
                (pp.group.expMat pp.generator sr.2.2.1)
                (pp.group.expVec pp.generator
                  (Matrix.vecMul (globalUAt G PG zDim q κ pp ω) tensorR))
            else if mode.val = 4 then semiKey G PG zDim κ pp st msg query sr.1 sr.2.2.2
              (pp.group.expMat pp.generator sr.2.2.1) (pp.group.expVec pp.generator sr.2.1)
            else simKeyCore G PG zDim κ pp st query.fn query.matrix msg.1
              (leak G PG zDim κ pp query.fn query.matrix msg.1 msg.2) sr⟩) := rfl

section NamedHandlers

variable (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
  (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ)
  (pp : PublicParams G κ) (st : SimState G ℓ zDim κ pp)
  (ω : SecurityDraw G PG zDim q κ pp)

/-- The real handler uses the honest mask and honest key formula [Wee20, Game 0, p. 12]. -/
def game0Handler := gameHandler G PG zDim q 0 κ pp st ω
/-- The first handler replaces only the ciphertext mask [Wee20, Game 1, p. 12]. -/
def game1Handler := gameHandler G PG zDim q 1 κ pp st ω
/-- The second handler uses explicit basis-decomposed keys [Wee20, Game 2, p. 13]. -/
def game2Handler := gameHandler G PG zDim q 2 κ pp st ω
/-- The third handler has a global hidden row times each R [Wee20, Game 3, p. 13]. -/
def game3Handler := gameHandler G PG zDim q 3 κ pp st ω
/-- The fourth handler has independent hidden key rows [Wee20, Game 4, p. 13]. -/
def game4Handler := gameHandler G PG zDim q 4 κ pp st ω
/-- The fifth handler is the actual group-leakage simulator [Wee20, Game 5, p. 13]. -/
def game5Handler := gameHandler G PG zDim q 5 κ pp st ω

/-- The real handler is its indexed explicit formula. -/
theorem game0Handler_eq : game0Handler G PG zDim q κ pp st ω =
    gameHandler G PG zDim q 0 κ pp st ω := rfl
/-- The first handler is its indexed explicit formula. -/
theorem game1Handler_eq : game1Handler G PG zDim q κ pp st ω =
    gameHandler G PG zDim q 1 κ pp st ω := rfl
/-- The second handler is its indexed explicit formula. -/
theorem game2Handler_eq : game2Handler G PG zDim q κ pp st ω =
    gameHandler G PG zDim q 2 κ pp st ω := rfl
/-- The third handler is its indexed explicit formula. -/
theorem game3Handler_eq : game3Handler G PG zDim q κ pp st ω =
    gameHandler G PG zDim q 3 κ pp st ω := rfl
/-- The fourth handler is its indexed explicit formula. -/
theorem game4Handler_eq : game4Handler G PG zDim q κ pp st ω =
    gameHandler G PG zDim q 4 κ pp st ω := rfl
/-- The ideal handler is its indexed explicit formula. -/
theorem game5Handler_eq : game5Handler G PG zDim q κ pp st ω =
    gameHandler G PG zDim q 5 κ pp st ω := rfl

end NamedHandlers

/-- Run the adversary with exactly its TOTAL call budget. Intermediate games are filtered
on the known scalar basis; singular cases return false before any next move is run.
This is the good-event form of [Wee20, Appendix B, Games 2–5, p. 13]. -/
noncomputable def runGameDet (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (mode : Fin 6) (filtered : Bool) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim A.budget κ pp) (r : List Bool) : Bool :=
  let ctx := simSetupCore G ℓ zDim κ pp (setupAt G PG zDim A.budget κ pp ω)
  if filtered && decide (2 ≤ mode.val) &&
      decide ((basisMatrix G κ pp ctx.2.A ctx.2.c).det = 0) then false
  else (runDet (A.next κ pp ctx.1 r) false
    (gameHandler G PG zDim A.budget mode κ pp ctx.2 ω)
    (A.budget.eval κ) [] ⟨none, 0⟩).1

/-- The deterministic game run has its exact bad-event filter and total-budget interpreter. -/
theorem runGameDet_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (mode : Fin 6) (filtered : Bool) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim A.budget κ pp) (r : List Bool) :
    runGameDet G PG zDim A mode filtered κ pp ω r =
      let ctx := simSetupCore G ℓ zDim κ pp (setupAt G PG zDim A.budget κ pp ω)
      if filtered && decide (2 ≤ mode.val) &&
          decide ((basisMatrix G κ pp ctx.2.A ctx.2.c).det = 0) then false
      else (runDet (A.next κ pp ctx.1 r) false
        (gameHandler G PG zDim A.budget mode κ pp ctx.2 ω)
        (A.budget.eval κ) [] ⟨none, 0⟩).1 := rfl

/-- The six exact game laws draw shared public parameters, one uniform scalar tape and the
adversary's independent coins [Wee20, Appendix B, pp. 12–14]. -/
noncomputable def game (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (mode : Fin 6) (κ : ℕ) : ProbComp Bool :=
  (publicParamsGen G κ).bind fun pp =>
  (ProbComp.sample (SecurityDraw G PG zDim A.budget κ pp)).bind fun ω =>
  (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
    .pure (runGameDet G PG zDim A mode true κ pp ω (List.ofFn r))

/-- Each game law is its displayed sequence of uniform draws and deterministic run. -/
theorem game_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (mode : Fin 6) (κ : ℕ) :
    game G PG zDim A mode κ =
      (publicParamsGen G κ).bind fun pp =>
      (ProbComp.sample (SecurityDraw G PG zDim A.budget κ pp)).bind fun ω =>
      (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
        .pure (runGameDet G PG zDim A mode true κ pp ω (List.ofFn r)) := rfl

/-- The real and ideal experiments are UNFILTERED; ideal keys receive exactly the group
leakage for each adaptive function/matrix query [Wee20, §2.2, p. 5; §4, p. 8]. -/
noncomputable def saGame (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (ideal : Bool) (κ : ℕ) : ProbComp Bool :=
  (publicParamsGen G κ).bind fun pp =>
  (ProbComp.sample (SecurityDraw G PG zDim A.budget κ pp)).bind fun ω =>
  (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
    .pure (runGameDet G PG zDim A (if ideal then 5 else 0) false κ pp ω (List.ofFn r))

/-- The semi-adaptive game is its unfiltered exact draw-and-run law. -/
theorem saGame_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (ideal : Bool) (κ : ℕ) :
    saGame G PG zDim A ideal κ =
      (publicParamsGen G κ).bind fun pp =>
      (ProbComp.sample (SecurityDraw G PG zDim A.budget κ pp)).bind fun ω =>
      (ProbComp.sample (Fin (A.coins.eval κ) → Bool)).bind fun r =>
        .pure (runGameDet G PG zDim A (if ideal then 5 else 0) false κ pp ω (List.ofFn r)) := rfl

/-- Π's simulation advantage compares its actual unfiltered endpoint experiments
[Wee20, Appendix B, Theorem 1, p. 12]. -/
noncomputable def saSimAdv (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim) (κ : ℕ) : ℝ :=
  advantage (saGame G PG zDim A false κ) (saGame G PG zDim A true κ)

/-- The simulation advantage is the library's two-experiment advantage. -/
theorem saSimAdv_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim) (κ : ℕ) :
    saSimAdv G PG zDim A κ =
      advantage (saGame G PG zDim A false κ) (saGame G PG zDim A true κ) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
