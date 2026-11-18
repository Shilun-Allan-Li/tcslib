/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Run

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Typed adversaries and fixed tapes for linear PHFE

## Main definitions

* `Wee20.Linear.Challenge`, `KeyQuery`, `KeyPack`, `saSpec`: the typed semi-adaptive oracles.
* `Wee20.Linear.SAAdv`, `SAState`, `protocolHandler`: bounded next moves and stateful refusals.
* `Wee20.Linear.securityCount`, `SecurityDraw`, `securityAt`: one finite scalar tape.
* `Wee20.Linear.setupAt`, `seedAt`, `globalUAt`, `keyAt`, `simKeyAt`: explicit tape blocks.

## Main results

Equation and oracle-case readers expose every definition. The total call budget is used
without adding a challenge call. Every accepted key consumes a tape block, and a challenge
must already have been accepted. The tapes use the supplied uniform garbling size bound.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.2, p. 5 and Appendix B,
  pp. 12–14 (semi-adaptive queries and game randomness).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- The single challenge commits to scalar public and private inputs
[Wee20, §2.2, p. 5]. -/
abbrev Challenge (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  (Fin (ℓ.eval κ) → ZMod pp.group.order) × (Fin (zDim.eval κ) → ZMod pp.group.order)

/-- The challenge type is its pair of scalar input vectors. -/
theorem challenge_eq (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    Challenge G ℓ zDim κ pp =
      ((Fin (ℓ.eval κ) → ZMod pp.group.order) ×
        (Fin (zDim.eval κ) → ZMod pp.group.order)) := rfl

/-- Each adaptive key query specifies a function and a GROUP matrix
[Wee20, §4, p. 8]. No group-word-to-exponent decoder is introduced. -/
structure KeyQuery (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- The queried function. -/
  fn : Fn κ pp.orderParam
  /-- The group matrix specified by that key. -/
  matrix : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G

/-- An answer retains its function index alongside its typed key. This dependent pair is
DATA only; no finite-type instance or sampler on the pair is constructed. -/
abbrev KeyPack (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ) :=
  Σ f : Fn κ pp.orderParam, Key G PG κ pp f

/-- A packed answer is a function index and a key at that index. -/
theorem keyPack_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ) :
    KeyPack G PG κ pp = (Σ f : Fn κ pp.orderParam, Key G PG κ pp f) := rfl

/-- The challenge oracle is `false`; the adaptive-key oracle is `true`
[Wee20, §2.2, p. 5; §4, p. 8]. Rejected requests return none. -/
abbrev saSpec (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    OracleSpec Bool where
  dom := fun | false => Challenge G ℓ zDim κ pp | true => KeyQuery G PG zDim κ pp
  rng := fun | false => Option (CT G zDim κ pp) | true => Option (KeyPack G PG κ pp)

/-- The oracle specification has its two displayed typed query and response families. -/
theorem saSpec_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    saSpec G PG zDim κ pp =
      { dom := fun | false => Challenge G ℓ zDim κ pp | true => KeyQuery G PG zDim κ pp
        rng := fun | false => Option (CT G zDim κ pp) | true => Option (KeyPack G PG κ pp) } :=
  rfl

/-- A typed semi-adaptive adversary fixes one coin polynomial, a TOTAL call budget, and
next moves after seeing the public key [Wee20, §2.2, p. 5]. -/
structure SAAdv (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) where
  /-- Coins shared by the whole adaptive interaction. -/
  coins : PolyExpr
  /-- Total oracle-call budget, including the challenge call. -/
  budget : PolyExpr
  /-- The next move after the current typed history. -/
  next : ∀ κ (pp : PublicParams G κ), MPK G ℓ zDim κ pp → List Bool →
    QueryLog (saSpec G PG zDim κ pp) → Move (saSpec G PG zDim κ pp) Bool

/-- Run the typed next-move adversary through the shared bounded oracle computation.
The budget is total, so no challenge call is added [Wee20, §2.2, p. 5]. -/
def SAAdv.run (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ zDim κ pp) (r : List Bool) :
    OracleComp (saSpec G PG zDim κ pp) Bool :=
  buildComp (A.next κ pp pk r) false (A.budget.eval κ) []

/-- The typed run uses exactly the shared buildComp next-move interpreter. -/
theorem SAAdv.run_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ zDim κ pp) (r : List Bool) :
    SAAdv.run G PG zDim A κ pp pk r =
      buildComp (A.next κ pp pk r) false (A.budget.eval κ) [] := rfl

/-- The protocol retains the one committed challenge and the accepted-key count
[Wee20, §2.2, p. 5]. -/
structure SAState (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- No key is answered before this challenge is committed. -/
  challenge : Option (Challenge G ℓ zDim κ pp)
  /-- The next unused per-key tape block. -/
  used : ℕ

/-- A deterministic stateful protocol refuses repeated challenges, keys before the
challenge, and keys exceeding the total call budget. Technical oracle glue. -/
def protocolHandler (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (q κ : ℕ) (pp : PublicParams G κ)
    (makeCT : Challenge G ℓ zDim κ pp → CT G zDim κ pp)
    (makeKey : ℕ → Challenge G ℓ zDim κ pp → KeyQuery G PG zDim κ pp → KeyPack G PG κ pp) :
    ∀ i, (saSpec G PG zDim κ pp).dom i → SAState G ℓ zDim κ pp →
      (saSpec G PG zDim κ pp).rng i × SAState G ℓ zDim κ pp
  | false, msg, st => match st.challenge with
    | none => (some (makeCT msg), ⟨some msg, st.used⟩)
    | some _ => (none, st)
  | true, query, st => match st.challenge with
    | none => (none, st)
    | some msg => if st.used < q then
        (some (makeKey st.used msg query), ⟨st.challenge, st.used + 1⟩)
      else (none, st)

/-- The challenge branch either commits once or returns none without changing state. -/
theorem protocolHandler_challenge (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr)
    (q κ : ℕ) (pp : PublicParams G κ)
    (makeCT : Challenge G ℓ zDim κ pp → CT G zDim κ pp)
    (makeKey : ℕ → Challenge G ℓ zDim κ pp → KeyQuery G PG zDim κ pp → KeyPack G PG κ pp)
    (msg : Challenge G ℓ zDim κ pp) (st : SAState G ℓ zDim κ pp) :
    protocolHandler G PG zDim q κ pp makeCT makeKey false msg st =
      match st.challenge with
      | none => (some (makeCT msg), ⟨some msg, st.used⟩)
      | some _ => (none, st) := rfl

/-- The key branch answers only after a challenge and within the accepted-key cap. -/
theorem protocolHandler_key (G : BilinearGen) {ℓ n' : PolyExpr}
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr)
    (q κ : ℕ) (pp : PublicParams G κ)
    (makeCT : Challenge G ℓ zDim κ pp → CT G zDim κ pp)
    (makeKey : ℕ → Challenge G ℓ zDim κ pp → KeyQuery G PG zDim κ pp → KeyPack G PG κ pp)
    (query : KeyQuery G PG zDim κ pp) (st : SAState G ℓ zDim κ pp) :
    protocolHandler G PG zDim q κ pp makeCT makeKey true query st =
      match st.challenge with
      | none => (none, st)
      | some msg => if st.used < q then
          (some (makeKey st.used msg query), ⟨st.challenge, st.used + 1⟩)
        else (none, st) := rfl

/-- The fixed scalar tape allocates setup blocks followed by padded per-key blocks.
This is exact-law bookkeeping for [Wee20, Appendix B, pp. 12–14]. -/
def securityCount {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) : PolyExpr :=
  (((PolyExpr.const 19).add ((PolyExpr.const 4).mul zDim)).add ((PolyExpr.const 8).mul ℓ)).add
    (q.mul ((((PolyExpr.const 6).add ℓ).mul PG.mBound).add ((PolyExpr.const 4).mul n')))

/-- The scalar-tape count has its displayed setup and per-query polynomial terms. -/
theorem securityCount_eq {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) :
    securityCount PG zDim q =
      (((PolyExpr.const 19).add ((PolyExpr.const 4).mul zDim)).add ((PolyExpr.const 8).mul ℓ)).add
        (q.mul ((((PolyExpr.const 6).add ℓ).mul PG.mBound).add ((PolyExpr.const 4).mul n'))) := rfl

/-- One uniform scalar tape supplies all game randomness, with no dependent-sum sampler. -/
abbrev SecurityDraw (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  Fin ((securityCount PG zDim q).eval κ) → ZMod pp.group.order

/-- The draw type is the displayed finite scalar vector. -/
theorem securityDraw_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :
    SecurityDraw G PG zDim q κ pp =
      (Fin ((securityCount PG zDim q).eval κ) → ZMod pp.group.order) := rfl

/-- A total tape read returns zero outside the allocated array. Actual accepted-query
coordinates lie within their padded blocks by the supplied uniform garbling bound. -/
def securityAt (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) (i : ℕ) : ZMod pp.group.order :=
  if h : i < (securityCount PG zDim q).eval κ then ω ⟨i, h⟩ else 0

/-- The tape lookup is the in-bounds coordinate or its zero default. -/
theorem securityAt_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) (i : ℕ) :
    securityAt G PG zDim q κ pp ω i =
      if h : i < (securityCount PG zDim q).eval κ then ω ⟨i, h⟩ else 0 := rfl

/-- The four per-query blocks start after setup, then T, R, and uhat respectively. -/
def securityOffsets {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) : Fin 4 → ℕ :=
  let base := 19 + 4 * zDim.eval κ + 8 * ℓ.eval κ
  let T := 3 * q.eval κ * (PG.mBound.eval κ + n'.eval κ)
  let R := 2 * q.eval κ * PG.mBound.eval κ
  let U := q.eval κ * ℓ.eval κ * PG.mBound.eval κ
  ![base, base + T, base + T + R, base + T + R + U]

/-- The block offsets are their displayed prefix sums. -/
theorem securityOffsets_eq {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) :
    securityOffsets PG zDim q κ =
      let base := 19 + 4 * zDim.eval κ + 8 * ℓ.eval κ
      let T := 3 * q.eval κ * (PG.mBound.eval κ + n'.eval κ)
      let R := 2 * q.eval κ * PG.mBound.eval κ
      let U := q.eval κ * ℓ.eval κ * PG.mBound.eval κ
      ![base, base + T, base + T + R, base + T + R + U] := rfl

/-- Read the simulator-compatible setup draw A,c,W,U,V,w,v from the fixed tape. -/
def setupAt (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) : SimSetupDraw G ℓ zDim κ pp :=
  let getScalar := securityAt G PG zDim q κ pp ω
  let z := zDim.eval κ
  let l := ℓ.eval κ
  ⟨(fun i j => getScalar (2 * i.val + j.val)), (fun i => getScalar (6 + i.val)),
    (fun i j => getScalar (9 + i.val * z + j.val)),
    (fun i j => getScalar (9 + 3 * z + i.val * (2 * l) + 2 * j.1.val + j.2.val)),
    (fun i j => getScalar (9 + 3 * z + 6 * l + 2 * i.val + j.val)),
    (fun j => getScalar (15 + 3 * z + 6 * l + j.val)),
    (fun j => getScalar (15 + 4 * z + 6 * l + j.val))⟩

/-- The setup lookup exposes its exact coordinate formulas. -/
theorem setupAt_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) :
    setupAt G PG zDim q κ pp ω =
      let getScalar := securityAt G PG zDim q κ pp ω
      let z := zDim.eval κ
      let l := ℓ.eval κ
      ⟨(fun i j => getScalar (2 * i.val + j.val)), (fun i => getScalar (6 + i.val)),
        (fun i j => getScalar (9 + i.val * z + j.val)),
        (fun i j => getScalar (9 + 3 * z + i.val * (2 * l) + 2 * j.1.val + j.2.val)),
        (fun i j => getScalar (9 + 3 * z + 6 * l + 2 * i.val + j.val)),
        (fun j => getScalar (15 + 3 * z + 6 * l + j.val)),
        (fun j => getScalar (15 + 4 * z + 6 * l + j.val))⟩ := rfl

/-- Read the honest encryption seed from its separate two-scalar block. -/
def seedAt (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) : EncDraw G κ pp :=
  fun i => securityAt G PG zDim q κ pp ω (17 + 4 * zDim.eval κ + 8 * ℓ.eval κ + i.val)

/-- The honest seed uses the two coordinates immediately before the key tapes. -/
theorem seedAt_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) :
    seedAt G PG zDim q κ pp ω = fun i =>
      securityAt G PG zDim q κ pp ω (17 + 4 * zDim.eval κ + 8 * ℓ.eval κ + i.val) := rfl

/-- Read the global hidden public-variable row used in the third game. -/
def globalUAt (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) : (Fin (ℓ.eval κ) × Fin 2) → ZMod pp.group.order :=
  fun i => securityAt G PG zDim q κ pp ω
    (17 + 4 * zDim.eval κ + 6 * ℓ.eval κ + 2 * i.1.val + i.2.val)

/-- The hidden global row is its displayed setup block. -/
theorem globalUAt_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) :
    globalUAt G PG zDim q κ pp ω = fun i => securityAt G PG zDim q κ pp ω
      (17 + 4 * zDim.eval κ + 6 * ℓ.eval κ + 2 * i.1.val + i.2.val) := rfl

/-- Actual draw coordinates embed auxiliary indices before a padded final output block. -/
def paddedDrawIndex {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (p : ℕ+) (f : Fn κ p) :
    (PG.TIdx κ p f ⊕ Fin (n'.eval κ)) → ℕ :=
  Sum.elim (fun i => (PG.tCoord κ p f i).val) (fun j => PG.mBound.eval κ + j.val)

/-- The padded index uses the supplied auxiliary coordinates and the final output offset. -/
theorem paddedDrawIndex_eq {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (p : ℕ+) (f : Fn κ p) :
    paddedDrawIndex PG κ p f =
      Sum.elim (fun i => (PG.tCoord κ p f i).val) (fun j => PG.mBound.eval κ + j.val) := rfl

/-- Read one actual function-dependent key draw from the padded T/R tapes. -/
def keyAt (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) (j : ℕ) (f : Fn κ pp.orderParam) : KeyDraw G PG κ pp f :=
  let getScalar := securityAt G PG zDim q κ pp ω
  let off := securityOffsets PG zDim q κ
  let b := PG.mBound.eval κ
  let n := n'.eval κ
  ⟨(fun i u => getScalar (off 0 + j * (3 * (b + n)) + i.val * (b + n) +
      paddedDrawIndex PG κ pp.orderParam f u)),
    (fun i u => getScalar (off 1 + j * (2 * b) + i.val * b + (PG.mCoord κ pp.orderParam f u).val))⟩

/-- The actual key draw is the displayed padded T/R restriction. -/
theorem keyAt_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) (j : ℕ) (f : Fn κ pp.orderParam) :
    keyAt G PG zDim q κ pp ω j f =
      let getScalar := securityAt G PG zDim q κ pp ω
      let off := securityOffsets PG zDim q κ
      let b := PG.mBound.eval κ
      let n := n'.eval κ
      ⟨(fun i u => getScalar (off 0 + j * (3 * (b + n)) + i.val * (b + n) +
          paddedDrawIndex PG κ pp.orderParam f u)),
        (fun i u => getScalar
          (off 1 + j * (2 * b) + i.val * b + (PG.mCoord κ pp.orderParam f u).val))⟩ := rfl

/-- Read the T,uhat,R,partial-garbling draw used by the ideal and intermediate games. -/
def simKeyAt (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) (j : ℕ) (f : Fn κ pp.orderParam) :
    SimKeyDraw G PG κ pp f :=
  let kr := keyAt G PG zDim q κ pp ω j f
  let getScalar := securityAt G PG zDim q κ pp ω
  let off := securityOffsets PG zDim q κ
  let b := PG.mBound.eval κ
  let n := n'.eval κ
  ⟨kr.1, (fun u => getScalar (off 2 + j * (ℓ.eval κ * b) + u.1.val * b +
      (PG.mCoord κ pp.orderParam f u.2).val)), kr.2,
    (fun u => getScalar (off 3 + j * (b + n) + paddedDrawIndex PG κ pp.orderParam f u))⟩

/-- The ideal key draw uses the displayed four padded blocks. -/
theorem simKeyAt_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim q : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : SecurityDraw G PG zDim q κ pp) (j : ℕ) (f : Fn κ pp.orderParam) :
    simKeyAt G PG zDim q κ pp ω j f =
      let kr := keyAt G PG zDim q κ pp ω j f
      let getScalar := securityAt G PG zDim q κ pp ω
      let off := securityOffsets PG zDim q κ
      let b := PG.mBound.eval κ
      let n := n'.eval κ
      ⟨kr.1, (fun u => getScalar (off 2 + j * (ℓ.eval κ * b) + u.1.val * b +
          (PG.mCoord κ pp.orderParam f u.2).val)), kr.2,
        (fun u => getScalar (off 3 + j * (b + n) + paddedDrawIndex PG κ pp.orderParam f u))⟩ := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
