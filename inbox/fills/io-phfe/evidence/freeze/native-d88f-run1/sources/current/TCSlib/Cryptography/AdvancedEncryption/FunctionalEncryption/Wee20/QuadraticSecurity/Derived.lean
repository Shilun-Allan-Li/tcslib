/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Advice

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The explicit quadratic-to-linear semi-adaptive adversary

## Main definitions

* `Wee20.Quadratic.wrapLinearCT`, `wrapLinearKey`: typed response translation.
* `Wee20.Quadratic.replayLinear`: replay the outer machine from a typed Π transcript.
* `Wee20.Quadratic.derivedNext`, `toLinear`: pure next-move reduction with fixed scalar advice.

## Main results

Equation readers expose the complete reduction. Coins and TOTAL query budget are preserved
exactly. No generic group-word decoder, oracle-machine construction or exponent extraction
is introduced. The replay has explicit false output on malformed or mismatched histories.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §3.3, Game 0 to Game 1,
  p. 7, made explicit as a typed adaptive reduction.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- Translate a Π ciphertext by adjoining the two masks computed from known scalar advice
[Wee20, §3.3, Game 0 to Game 1, p. 7]. -/
def wrapLinearCT (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (m : Masks G n1 n2 κ pp) (msg : Challenge G ℓ n1 n2 κ pp)
    (ct : Linear.CT G (piDim n1 n2) κ pp) : CT G n1 n2 κ pp :=
  ⟨pp.group.expVec pp.generator (Matrix.vecMul m.s1 m.A1 + msg.2.1),
    pp.group.expVec pp.generator (Matrix.vecMul m.s2 m.A2 + msg.2.2), ct⟩

/-- Ciphertext translation is exactly the two exponentiated known masks and Π's answer. -/
theorem wrapLinearCT_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (m : Masks G n1 n2 κ pp) (msg : Challenge G ℓ n1 n2 κ pp)
    (ct : Linear.CT G (piDim n1 n2) κ pp) : wrapLinearCT G ℓ n1 n2 κ pp m msg ct =
      ⟨pp.group.expVec pp.generator (Matrix.vecMul m.s1 m.A1 + msg.2.1),
        pp.group.expVec pp.generator (Matrix.vecMul m.s2 m.A2 + msg.2.2), ct⟩ := rfl

/-- Key translation retains the fixed public GROUP matrix as metadata
[Wee20, §3.1, p. 6; §4, p. 8]. The returned function index is data, not compared by a decoder. -/
def wrapLinearKey (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ)
    (M : Matrix (Fin ((piDim n1 n2).eval κ)) (Fin ((n1.mul n2).eval κ)) pp.group.G)
    (key : Linear.KeyPack G PG κ pp) : KeyPack G n1 n2 PG κ pp :=
  ⟨key.1, ⟨M, key.2⟩⟩

/-- Key translation is the displayed dependent pair with public metadata. -/
theorem wrapLinearKey_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ)
    (M : Matrix (Fin ((piDim n1 n2).eval κ)) (Fin ((n1.mul n2).eval κ)) pp.group.G)
    (key : Linear.KeyPack G PG κ pp) : wrapLinearKey G n1 n2 PG κ pp M key =
      ⟨key.1, ⟨M, key.2⟩⟩ := rfl

/-- Replay the outer adversary to reconstruct its typed log from Π's answers. On the
reachable histories the query payload is exactly the translated outer move; on arbitrary
histories only oracle indices are matched, and impossible continuations return none.
This is total adaptive reduction glue for [Wee20, §3.3, pp. 7–8]. -/
def replayLinear (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) (pp : PublicParams G κ)
    (m : Masks G n1 n2 κ pp) (pk : MPK G ℓ n1 n2 κ pp) (r : List Bool) :
    QueryLog (Linear.saSpec G PG (piDim n1 n2) κ pp) →
      QueryLog (saSpec G n1 n2 PG κ pp) → Option (QueryLog (saSpec G n1 n2 PG κ pp))
  | [], h => some h
  | e :: es, h => match A.next κ pp pk r h, e with
    | .query false msg, ⟨false, pair⟩ =>
        let answer := pair.2.map (wrapLinearCT G ℓ n1 n2 κ pp m msg)
        replayLinear G n1 n2 PG A κ pp m pk r es (h ++ [⟨false, msg, answer⟩])
    | .query true f, ⟨true, pair⟩ =>
        let answer := pair.2.map
          (wrapLinearKey G n1 n2 PG κ pp (mixGroup G n1 n2 κ pp pk.A1 pk.A2))
        replayLinear G n1 n2 PG A κ pp m pk r es (h ++ [⟨true, f, answer⟩])
    | _, _ => none

/-- Empty replay returns the accumulated outer history. -/
theorem replayLinear_nil (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) (pp : PublicParams G κ)
    (m : Masks G n1 n2 κ pp) (pk : MPK G ℓ n1 n2 κ pp) (r : List Bool)
    (h : QueryLog (saSpec G n1 n2 PG κ pp)) :
    replayLinear G n1 n2 PG A κ pp m pk r [] h = some h := rfl

/-- Nonempty replay uses the displayed next move and answer translation. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem replayLinear_cons (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) (pp : PublicParams G κ)
    (m : Masks G n1 n2 κ pp) (pk : MPK G ℓ n1 n2 κ pp) (r : List Bool)
    (e : Σ i, (Linear.saSpec G PG (piDim n1 n2) κ pp).dom i ×
      (Linear.saSpec G PG (piDim n1 n2) κ pp).rng i)
    (es : QueryLog (Linear.saSpec G PG (piDim n1 n2) κ pp))
    (h : QueryLog (saSpec G n1 n2 PG κ pp)) :
    replayLinear G n1 n2 PG A κ pp m pk r (e :: es) h =
      match A.next κ pp pk r h, e with
      | .query false msg, ⟨false, pair⟩ =>
          let answer := pair.2.map (wrapLinearCT G ℓ n1 n2 κ pp m msg)
          replayLinear G n1 n2 PG A κ pp m pk r es (h ++ [⟨false, msg, answer⟩])
      | .query true f, ⟨true, pair⟩ =>
          let answer := pair.2.map
            (wrapLinearKey G n1 n2 PG κ pp (mixGroup G n1 n2 κ pp pk.A1 pk.A2))
          replayLinear G n1 n2 PG A κ pp m pk r es (h ++ [⟨true, f, answer⟩])
      | _, _ => none := rfl

/-- Translate the next outer move into Π's typed scalar challenge or group-matrix key
query [Wee20, §3.3, Game 0 to Game 1, p. 7]. Only known mask scalars enter signalScalar. -/
def derivedNext (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) (pp : PublicParams G κ)
    (m : Masks G n1 n2 κ pp) (pk : Linear.MPK G ℓ (piDim n1 n2) κ pp) (r : List Bool)
    (h : QueryLog (Linear.saSpec G PG (piDim n1 n2) κ pp)) :
    Move (Linear.saSpec G PG (piDim n1 n2) κ pp) Bool :=
  let pub := publicFromMasks G ℓ n1 n2 κ pp m pk
  match replayLinear G n1 n2 PG A κ pp m pub r h [] with
  | none => .ret false
  | some outer => match A.next κ pp pub r outer with
    | .ret b => .ret b
    | .query false msg => .query false (msg.1,
        signalScalar (p := pp.orderParam) m.s1 msg.2.2 (Matrix.vecMul m.s1 m.A1 + msg.2.1) m.s2)
    | .query true f => .query true ⟨f, mixGroup G n1 n2 κ pp pub.A1 pub.A2⟩

/-- The derived next move is the displayed total replay-and-translation algorithm. 

**Proof sketch.** The defining case and record projections reduce to the displayed expression
by reflexivity. -/
theorem derivedNext_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) (pp : PublicParams G κ)
    (m : Masks G n1 n2 κ pp) (pk : Linear.MPK G ℓ (piDim n1 n2) κ pp) (r : List Bool)
    (h : QueryLog (Linear.saSpec G PG (piDim n1 n2) κ pp)) :
    derivedNext G n1 n2 PG A κ pp m pk r h =
      let pub := publicFromMasks G ℓ n1 n2 κ pp m pk
      match replayLinear G n1 n2 PG A κ pp m pub r h [] with
      | none => .ret false
      | some outer => match A.next κ pp pub r outer with
        | .ret b => .ret b
        | .query false msg => .query false (msg.1,
            signalScalar (p := pp.orderParam) m.s1 msg.2.2
              (Matrix.vecMul m.s1 m.A1 + msg.2.1) m.s2)
        | .query true f => .query true ⟨f, mixGroup G n1 n2 κ pp pub.A1 pub.A2⟩ := rfl

/-- The explicit derived Π adversary fixes outer scalar randomness as nonuniform advice
and keeps the original coins and TOTAL budget [Wee20, §3.3, pp. 7–8]. -/
def toLinear (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (ω : ∀ κ, MaskAdvice n1 n2 p κ) : Linear.SAAdv G PG (piDim n1 n2) where
  coins := A.coins
  budget := A.budget
  next := fun κ pp pk r => derivedNext G n1 n2 PG A κ pp
    (masksAt G n1 n2 κ pp (maskAdviceDraw G n1 n2 p hp κ pp (ω κ))) pk r

/-- The derived adversary exposes all three fields. -/
theorem toLinear_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (ω : ∀ κ, MaskAdvice n1 n2 p κ) : toLinear G n1 n2 PG p hp A ω =
      { coins := A.coins
        budget := A.budget
        next := fun κ pp pk r => derivedNext G n1 n2 PG A κ pp
          (masksAt G n1 n2 κ pp (maskAdviceDraw G n1 n2 p hp κ pp (ω κ))) pk r } := rfl

/-- The derived coin layout is exactly the outer layout. -/
theorem toLinear_coins (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (ω : ∀ κ, MaskAdvice n1 n2 p κ) : (toLinear G n1 n2 PG p hp A ω).coins = A.coins := rfl

/-- The derived total call budget is exactly the outer budget. -/
theorem toLinear_budget (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G n1 n2 PG)
    (ω : ∀ κ, MaskAdvice n1 n2 p κ) : (toLinear G n1 n2 PG p hp A ω).budget = A.budget := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
