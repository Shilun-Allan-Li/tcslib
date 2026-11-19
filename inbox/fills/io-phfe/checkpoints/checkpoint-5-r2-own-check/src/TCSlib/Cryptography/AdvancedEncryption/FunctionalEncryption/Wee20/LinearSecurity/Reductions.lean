/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Games
import TCSlib.Cryptography.Pairing.MatrixDH.SelfReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic MDDH reduction functions for linear PHFE

## Main definitions

* `Wee20.Linear.Advice`, `adviceEnc`, `adviceLen`: fixed-schedule scalar advice and encoding.
* `Wee20.Linear.adviceDraw`: transport advice into the public field through the order reader.
* `Wee20.Linear.red0Handler`, `red0`: the unfiltered ciphertext hop against MDDH¹_{2,3}.
* `Wee20.Linear.challengeR`, `challengeUhat`: padded per-query group blocks of MDDH data.
* `Wee20.Linear.red1Handler`, `red1`: the good-filtered adaptive-key hop against
  MDDH^ℓ_{2,mBound·q}.

## Main results

Readers expose every encoding, cast and deterministic run. Advice is finite and nonempty
under the shared fixed prime schedule. No reduction samples or computes a group exponent.
The shared realisation predicate constrains only encoded challenges and layout-length coins.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Appendix B, pp. 12–14,
  Lemmas 2 and 4 (the two computational hops).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open scoped Matrix

/-- Fixed-schedule advice stores all scalar tape coordinates, before the group draw.
It contains no group elements or sampled response [Wee20, Appendix B, Lemmas 2 and 4]. -/
abbrev Advice {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (p : ℕ → ℕ) (κ : ℕ) :=
  Fin ((securityCount PG zDim q).eval κ) → ZMod (p κ)

/-- Advice is exactly its fixed-schedule scalar vector. -/
theorem advice_eq {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (p : ℕ → ℕ) (κ : ℕ) :
    Advice PG zDim q p κ = (Fin ((securityCount PG zDim q).eval κ) → ZMod (p κ)) := rfl

/-- The all-zero tape inhabits advice at every parameter. Technical glue. -/
theorem advice_nonempty {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (p : ℕ → ℕ) (κ : ℕ) :
    Nonempty (Advice PG zDim q p κ) := ⟨0⟩

/-- Advice is finite by the shared prime-schedule reader, without an extra nonzero premise. -/
theorem advice_finite (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) : Finite (Advice PG zDim q p κ) :=
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  inferInstance

/-- Transport known advice scalars through the actual public-order equality. This is the
shared Mathlib ring equivalence, not a new scalar extraction primitive. -/
def adviceDraw (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (pp : PublicParams G κ)
    (ω : Advice PG zDim q p κ) : SecurityDraw G PG zDim q κ pp :=
  fun i => ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ pp).symm (ω i)

/-- The advice cast is coordinatewise `ZMod.ringEquivCongr`. -/
theorem adviceDraw_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (pp : PublicParams G κ)
    (ω : Advice PG zDim q p κ) :
    adviceDraw G PG zDim q p hp κ pp ω =
      fun i => ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ pp).symm (ω i) := rfl

/-- Public advice metadata explicitly supplies κ,ℓ,n',zDim,q and the uniform node bound. -/
def adviceMeta {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) : List Bool :=
  let num := fun n => Candidates.natToList (Nat.size n) n
  pairEncode (List.replicate κ true) (pairEncode (num (ℓ.eval κ))
    (pairEncode (num (n'.eval κ)) (pairEncode (num (zDim.eval κ))
      (pairEncode (num (q.eval κ)) (num (PG.mBound.eval κ))))))

/-- The metadata word uses the displayed unary parameter and binary dimension headers. -/
theorem adviceMeta_eq {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) :
    adviceMeta PG zDim q κ =
      let num := fun n => Candidates.natToList (Nat.size n) n
      pairEncode (List.replicate κ true) (pairEncode (num (ℓ.eval κ))
        (pairEncode (num (n'.eval κ)) (pairEncode (num (zDim.eval κ))
          (pairEncode (num (q.eval κ)) (num (PG.mBound.eval κ)))))) := rfl

/-- Encode advice with public dimension headers and the existing modular-vector encoder. -/
def adviceEnc (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (ω : Advice PG zDim q p κ) : List Bool :=
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  pairEncode (adviceMeta PG zDim q κ) (Encoding.Modular.encodeVector (G.wG.eval κ) ω)

/-- Advice encoding pairs its public metadata and fixed-width scalar vector. -/
theorem adviceEnc_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (ω : Advice PG zDim q p κ) :
    adviceEnc G PG zDim q p hp κ ω =
      letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
      pairEncode (adviceMeta PG zDim q κ) (Encoding.Modular.encodeVector (G.wG.eval κ) ω) := rfl

/-- A polynomial bounds public headers and all scalar advice bits. Technical glue. -/
def adviceLen (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) : PolyExpr :=
  (((((((PolyExpr.var.mul (PolyExpr.const 4)).add ((PolyExpr.const 4).mul ℓ)).add ((PolyExpr.const
    4).mul n')).add
    ((PolyExpr.const 4).mul zDim)).add ((PolyExpr.const 4).mul q)).add ((PolyExpr.const 2).mul
      PG.mBound)).add
    (PolyExpr.const 40)).add ((securityCount PG zDim q).mul G.wG)

/-- The advice-length polynomial is its displayed header and scalar-block bound. -/
theorem adviceLen_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) :
    adviceLen G PG zDim q =
      (((((((PolyExpr.var.mul (PolyExpr.const 4)).add ((PolyExpr.const 4).mul ℓ)).add
        ((PolyExpr.const 4).mul n')).add
        ((PolyExpr.const 4).mul zDim)).add ((PolyExpr.const 4).mul q)).add ((PolyExpr.const 2).mul
          PG.mBound)).add
        (PolyExpr.const 40)).add ((securityCount PG zDim q).mul G.wG) := rfl

/-- The first reduction's public key uses only GROUP A and known scalar masks
[Wee20, Appendix B, p. 12, Lemma 2]. -/
def publicFromGroupA (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (A : Matrix (Fin 2) (Fin 3) pp.group.G) (st : MSK G ℓ zDim κ pp) : MPK G ℓ zDim κ pp :=
  ⟨A, groupMatMul A st.W, groupMatMul A st.U, groupMatMul A st.V⟩

/-- The public-key computation is its displayed known-scalar group matrix actions. -/
theorem publicFromGroupA_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (A : Matrix (Fin 2) (Fin 3) pp.group.G)
    (st : MSK G ℓ zDim κ pp) :
    publicFromGroupA G ℓ zDim κ pp A st =
      ⟨A, groupMatMul A st.W, groupMatMul A st.U, groupMatMul A st.V⟩ := rfl

/-- The first L2 handler uses the challenge's GROUP c and hardwired W,U,V,T,R. It answers
adaptive key queries honestly and never samples [Wee20, Appendix B, Lemma 2, p. 13]. -/
def red0Handler (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) (PolyExpr.const 3) κ)
    (ω : SecurityDraw G PG zDim q κ c.pp) :
    ∀ i, (saSpec G PG zDim κ c.pp).dom i → SAState G ℓ zDim κ c.pp →
      (saSpec G PG zDim κ c.pp).rng i × SAState G ℓ zDim κ c.pp :=
  let ss := setupAt G PG zDim q κ c.pp ω
  let msk : MSK G ℓ zDim κ c.pp := ⟨ss.2.2.1, ss.2.2.2.1, ss.2.2.2.2.1⟩
  protocolHandler G PG zDim (q.eval κ) κ c.pp
    (maskedCipher G ℓ zDim κ c.pp msk (fun i => c.response i (0 : Fin 1)))
    (fun j _ query => ⟨query.fn,
      keyCore G PG zDim κ c.pp msk query.fn query.matrix (keyAt G PG zDim q κ c.pp ω j query.fn)⟩)

/-- The first handler is the displayed closed deterministic protocol. -/
theorem red0Handler_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) (PolyExpr.const 3) κ)
    (ω : SecurityDraw G PG zDim q κ c.pp) :
    red0Handler G PG zDim q κ c ω =
      let ss := setupAt G PG zDim q κ c.pp ω
      let msk : MSK G ℓ zDim κ c.pp := ⟨ss.2.2.1, ss.2.2.2.1, ss.2.2.2.2.1⟩
      protocolHandler G PG zDim (q.eval κ) κ c.pp
        (maskedCipher G ℓ zDim κ c.pp msk (fun i => c.response i (0 : Fin 1)))
        (fun j _ query => ⟨query.fn, keyCore G PG zDim κ c.pp msk query.fn query.matrix
          (keyAt G PG zDim q κ c.pp ω j query.fn)⟩) := rfl

/-- The first L2 reduction runs the typed adversary on the MDDH¹_{2,3} challenge with
hardwired answers. It contributes exactly the Game0-to-Game1 gap, with no statistical
slack [Wee20, Appendix B, Lemma 2, p. 13]. -/
def red0 (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G PG zDim)
    (ω : ∀ κ, Advice PG zDim A.budget p κ) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) (PolyExpr.const 3) κ) (r : List Bool) : List Bool :=
  let tape := adviceDraw G PG zDim A.budget p hp κ c.pp (ω κ)
  let ss := setupAt G PG zDim A.budget κ c.pp tape
  let msk : MSK G ℓ zDim κ c.pp := ⟨ss.2.2.1, ss.2.2.2.1, ss.2.2.2.2.1⟩
  let pk := publicFromGroupA G ℓ zDim κ c.pp c.matrixᵀ msk
  [(runDet (A.next κ c.pp pk r) false (red0Handler G PG zDim A.budget κ c tape)
    (A.budget.eval κ) [] ⟨none, 0⟩).1]

/-- The first reduction is exactly the displayed deterministic run, with A's original coins. -/
theorem red0_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G PG zDim)
    (ω : ∀ κ, Advice PG zDim A.budget p κ) (κ : ℕ)
    (c : G.MDDHChallenge (PolyExpr.const 1) (PolyExpr.const 3) κ) (r : List Bool) :
    red0 G PG zDim p hp A ω κ c r =
      let tape := adviceDraw G PG zDim A.budget p hp κ c.pp (ω κ)
      let ss := setupAt G PG zDim A.budget κ c.pp tape
      let msk : MSK G ℓ zDim κ c.pp := ⟨ss.2.2.1, ss.2.2.2.1, ss.2.2.2.2.1⟩
      let pk := publicFromGroupA G ℓ zDim κ c.pp c.matrixᵀ msk
      [(runDet (A.next κ c.pp pk r) false (red0Handler G PG zDim A.budget κ c tape)
        (A.budget.eval κ) [] ⟨none, 0⟩).1] := rfl

/-- Read the query's R block from the MDDH base matrix. Rows are ordered by node then query;
out-of-range inputs return the identity. Accepted queries satisfy the published size bound. -/
def challengeR (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (q : PolyExpr) (κ : ℕ)
    (c : G.MDDHChallenge ℓ (PG.mBound.mul q) κ) (j : ℕ) (f : Fn κ c.pp.orderParam) :
    Matrix (Fin 2) (PG.MIdx κ c.pp.orderParam f) c.pp.group.G :=
  fun i u =>
    let row := (PG.mCoord κ c.pp.orderParam f u).val * q.eval κ + j
    if h : row < (PG.mBound.mul q).eval κ then c.matrix ⟨row, h⟩ i else 1

/-- The group R lookup is exactly the displayed interleaved block extraction. -/
theorem challengeR_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (q : PolyExpr) (κ : ℕ)
    (c : G.MDDHChallenge ℓ (PG.mBound.mul q) κ) (j : ℕ) (f : Fn κ c.pp.orderParam) :
    challengeR G PG q κ c j f = fun i u =>
      let row := (PG.mCoord κ c.pp.orderParam f u).val * q.eval κ + j
      if h : row < (PG.mBound.mul q).eval κ then c.matrix ⟨row, h⟩ i else 1 := rfl

/-- Read uhat from the SAME query/node rows of the MDDH response matrix. In the real branch
this is the hidden global row times R; in the random branch it is independently uniform. -/
def challengeUhat (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (q : PolyExpr) (κ : ℕ)
    (c : G.MDDHChallenge ℓ (PG.mBound.mul q) κ) (j : ℕ) (f : Fn κ c.pp.orderParam) :
    (Fin (ℓ.eval κ) × PG.MIdx κ c.pp.orderParam f) → c.pp.group.G :=
  fun u =>
    let row := (PG.mCoord κ c.pp.orderParam f u.2).val * q.eval κ + j
    if h : row < (PG.mBound.mul q).eval κ then c.response ⟨row, h⟩ u.1 else 1

/-- The hidden-row lookup is the displayed response block on the matching R rows. -/
theorem challengeUhat_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (q : PolyExpr) (κ : ℕ)
    (c : G.MDDHChallenge ℓ (PG.mBound.mul q) κ) (j : ℕ) (f : Fn κ c.pp.orderParam) :
    challengeUhat G PG q κ c j f = fun u =>
      let row := (PG.mCoord κ c.pp.orderParam f u.2).val * q.eval κ + j
      if h : row < (PG.mBound.mul q).eval κ then c.response ⟨row, h⟩ u.1 else 1 := rfl

/-- The second L2 handler answers with GROUP R and GROUP uhat from the MDDH challenge,
using all other coefficients from advice [Wee20, Appendix B, Lemma 4, p. 14]. -/
def red1Handler (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ)
    (c : G.MDDHChallenge ℓ (PG.mBound.mul q) κ) (st : SimState G ℓ zDim κ c.pp)
    (ω : SecurityDraw G PG zDim q κ c.pp) :
    ∀ i, (saSpec G PG zDim κ c.pp).dom i → SAState G ℓ zDim κ c.pp →
      (saSpec G PG zDim κ c.pp).rng i × SAState G ℓ zDim κ c.pp :=
  protocolHandler G PG zDim (q.eval κ) κ c.pp (fun msg => simEncCore G ℓ zDim κ c.pp st msg.1)
    (fun j msg query =>
      let sr := simKeyAt G PG zDim q κ c.pp ω j query.fn
      ⟨query.fn, semiKey G PG zDim κ c.pp st msg query sr.1 sr.2.2.2
        (challengeR G PG q κ c j query.fn) (challengeUhat G PG q κ c j query.fn)⟩)

/-- The second handler is its displayed deterministic middle-game oracle. -/
theorem red1Handler_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ)
    (c : G.MDDHChallenge ℓ (PG.mBound.mul q) κ) (st : SimState G ℓ zDim κ c.pp)
    (ω : SecurityDraw G PG zDim q κ c.pp) :
    red1Handler G PG zDim q κ c st ω =
      protocolHandler G PG zDim (q.eval κ) κ c.pp (fun msg => simEncCore G ℓ zDim κ c.pp st msg.1)
        (fun j msg query =>
          let sr := simKeyAt G PG zDim q κ c.pp ω j query.fn
          ⟨query.fn, semiKey G PG zDim κ c.pp st msg query sr.1 sr.2.2.2
            (challengeR G PG q κ c j query.fn) (challengeUhat G PG q κ c j query.fn)⟩) := rfl

/-- The second L2 reduction filters singular known bases, then runs the adversary against
its deterministic MDDH-block answers. It contributes the Game3-to-Game4 gap with no further
slack [Wee20, Appendix B, Lemma 4, p. 14]. No response exponent is recovered. -/
noncomputable def red1 (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G PG zDim)
    (ω : ∀ κ, Advice PG zDim A.budget p κ) (κ : ℕ)
    (c : G.MDDHChallenge ℓ (PG.mBound.mul A.budget) κ) (r : List Bool) : List Bool :=
  let tape := adviceDraw G PG zDim A.budget p hp κ c.pp (ω κ)
  let ctx := simSetupCore G ℓ zDim κ c.pp (setupAt G PG zDim A.budget κ c.pp tape)
  if (basisMatrix G κ c.pp ctx.2.A ctx.2.c).det = 0 then [false]
  else [(runDet (A.next κ c.pp ctx.1 r) false
    (red1Handler G PG zDim A.budget κ c ctx.2 tape) (A.budget.eval κ) [] ⟨none, 0⟩).1]

/-- The second reduction is exactly its displayed good-filtered deterministic run. -/
theorem red1_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (A : SAAdv G PG zDim)
    (ω : ∀ κ, Advice PG zDim A.budget p κ) (κ : ℕ)
    (c : G.MDDHChallenge ℓ (PG.mBound.mul A.budget) κ) (r : List Bool) :
    red1 G PG zDim p hp A ω κ c r =
      let tape := adviceDraw G PG zDim A.budget p hp κ c.pp (ω κ)
      let ctx := simSetupCore G ℓ zDim κ c.pp (setupAt G PG zDim A.budget κ c.pp tape)
      if (basisMatrix G κ c.pp ctx.2.A ctx.2.c).det = 0 then [false]
      else [(runDet (A.next κ c.pp ctx.1 r) false
        (red1Handler G PG zDim A.budget κ c ctx.2 tape) (A.budget.eval κ) [] ⟨none, 0⟩).1] := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
