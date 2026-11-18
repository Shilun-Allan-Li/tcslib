/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Endpoint

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Typed semi-adaptive data for the quadratic construction

## Main definitions

* `Wee20.Quadratic.Challenge`, `KeyPack`, `saSpec`: scalar input and function-only key queries.
* `Wee20.Quadratic.SAAdv`, `SAAdv.run`: bounded typed next moves with a TOTAL call budget.
* `Wee20.Quadratic.protocolHandler`: deterministic refusal and state rules.
* `Wee20.Quadratic.MaskDraw`, `Masks`, `masksAt`, `SecurityDraw`: finite scalar tapes.

## Main results

Equation and case readers expose every new definition. The five games and reductions are
in the sibling modules. No finite instance is declared for a dependent packed key answer.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.2, p. 5 and §3.3,
  pp. 7–8, Games 0–4. The present interface makes the source's polynomial call cap explicit.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- The challenge contains scalar public input and both scalar private blocks
[Wee20, §2.2, p. 5; §3.1, p. 6]. -/
abbrev Challenge (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  (Fin (ℓ.eval κ) → ZMod pp.group.order) ×
    (Fin (n1.eval κ) → ZMod pp.group.order) × (Fin (n2.eval κ) → ZMod pp.group.order)

/-- The outer challenge is the displayed triple of scalar vectors. -/
theorem challenge_eq (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : Challenge G ℓ n1 n2 κ pp =
      ((Fin (ℓ.eval κ) → ZMod pp.group.order) ×
        (Fin (n1.eval κ) → ZMod pp.group.order) ×
        (Fin (n2.eval κ) → ZMod pp.group.order)) := rfl

/-- A packed function key retains its type index. This dependent pair is data only;
no sampler or finite-type instance on it is constructed. -/
abbrev KeyPack (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) := Σ f : Fn κ pp.orderParam, Key G n1 n2 PG κ pp f

/-- A packed outer key is a function index paired with its typed key. -/
theorem keyPack_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) : KeyPack G n1 n2 PG κ pp =
      (Σ f : Fn κ pp.orderParam, Key G n1 n2 PG κ pp f) := rfl

/-- False is the once-only challenge; true queries a function using the fixed public
matrix [Wee20, §2.2, p. 5; §3.1, p. 6]. Refused queries return none. -/
abbrev saSpec (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) : OracleSpec Bool where
  dom := fun | false => Challenge G ℓ n1 n2 κ pp | true => Fn κ pp.orderParam
  rng := fun | false => Option (CT G n1 n2 κ pp) | true => Option (KeyPack G n1 n2 PG κ pp)

/-- The outer query and response families are the displayed two branches. -/
theorem saSpec_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) : saSpec G n1 n2 PG κ pp =
      { dom := fun | false => Challenge G ℓ n1 n2 κ pp | true => Fn κ pp.orderParam
        rng := fun
          | false => Option (CT G n1 n2 κ pp)
          | true => Option (KeyPack G n1 n2 PG κ pp) } := rfl

/-- A typed adversary sees the public key before selecting its challenge and its later
adaptive functions [Wee20, §2.2, p. 5]. Its budget counts every oracle call. -/
structure SAAdv (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn) where
  /-- Shared adversary coin length. -/
  coins : PolyExpr
  /-- TOTAL call budget, including the challenge. -/
  budget : PolyExpr
  /-- Next move after the current typed history. -/
  next : ∀ κ (pp : PublicParams G κ), MPK G ℓ n1 n2 κ pp → List Bool →
    QueryLog (saSpec G n1 n2 PG κ pp) → Move (saSpec G n1 n2 PG κ pp) Bool

/-- Run the outer adversary through the shared bounded interpreter, with no added call
[Wee20, §2.2, p. 5]. -/
def SAAdv.run (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) (pp : PublicParams G κ)
    (pk : MPK G ℓ n1 n2 κ pp) (r : List Bool) :
    OracleComp (saSpec G n1 n2 PG κ pp) Bool :=
  buildComp (A.next κ pp pk r) false (A.budget.eval κ) []

/-- The run is exactly buildComp at the total budget. -/
theorem SAAdv.run_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (A : SAAdv G n1 n2 PG) (κ : ℕ) (pp : PublicParams G κ)
    (pk : MPK G ℓ n1 n2 κ pp) (r : List Bool) :
    SAAdv.run G n1 n2 PG A κ pp pk r =
      buildComp (A.next κ pp pk r) false (A.budget.eval κ) [] := rfl

/-- The protocol retains the scalar challenge and the next unused accepted-key block
[Wee20, §2.2, p. 5]. -/
structure SAState (G : BilinearGen) (ℓ n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- Committed challenge, absent until the unique accepted challenge call. -/
  challenge : Option (Challenge G ℓ n1 n2 κ pp)
  /-- Accepted-key counter. -/
  used : ℕ

/-- This deterministic protocol refuses pre-challenge keys, repeated challenges and keys
beyond the total cap [Wee20, §2.2, p. 5, with explicit total behavior]. -/
def protocolHandler (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (q κ : ℕ) (pp : PublicParams G κ)
    (makeCT : Challenge G ℓ n1 n2 κ pp → CT G n1 n2 κ pp)
    (makeKey : ℕ → Challenge G ℓ n1 n2 κ pp → Fn κ pp.orderParam → KeyPack G n1 n2 PG κ pp) :
    ∀ i, (saSpec G n1 n2 PG κ pp).dom i → SAState G ℓ n1 n2 κ pp →
      (saSpec G n1 n2 PG κ pp).rng i × SAState G ℓ n1 n2 κ pp
  | false, msg, st => match st.challenge with
    | none => (some (makeCT msg), ⟨some msg, st.used⟩)
    | some _ => (none, st)
  | true, f, st => match st.challenge with
    | none => (none, st)
    | some msg => if st.used < q then
        (some (makeKey st.used msg f), ⟨st.challenge, st.used + 1⟩)
      else (none, st)

/-- A challenge commits once and otherwise leaves state unchanged. -/
theorem protocolHandler_challenge (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (q κ : ℕ) (pp : PublicParams G κ)
    (makeCT : Challenge G ℓ n1 n2 κ pp → CT G n1 n2 κ pp)
    (makeKey : ℕ → Challenge G ℓ n1 n2 κ pp → Fn κ pp.orderParam → KeyPack G n1 n2 PG κ pp)
    (msg : Challenge G ℓ n1 n2 κ pp) (st : SAState G ℓ n1 n2 κ pp) :
    protocolHandler G n1 n2 PG q κ pp makeCT makeKey false msg st =
      match st.challenge with
      | none => (some (makeCT msg), ⟨some msg, st.used⟩)
      | some _ => (none, st) := rfl

/-- A key consumes a fresh block only after the challenge and below the cap. -/
theorem protocolHandler_key (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (q κ : ℕ) (pp : PublicParams G κ)
    (makeCT : Challenge G ℓ n1 n2 κ pp → CT G n1 n2 κ pp)
    (makeKey : ℕ → Challenge G ℓ n1 n2 κ pp → Fn κ pp.orderParam → KeyPack G n1 n2 PG κ pp)
    (f : Fn κ pp.orderParam) (st : SAState G ℓ n1 n2 κ pp) :
    protocolHandler G n1 n2 PG q κ pp makeCT makeKey true f st =
      match st.challenge with
      | none => (none, st)
      | some msg => if st.used < q then
          (some (makeKey st.used msg f), ⟨st.challenge, st.used + 1⟩)
        else (none, st) := rfl

/-- The outer tape stores A1,A2,s1,s2 and fresh scalar y1,y2
[Wee20, §3.3, pp. 7–8, Games 0–4]. -/
def maskCount (n1 n2 : PolyExpr) : PolyExpr :=
  ((PolyExpr.const 3).mul n1).add (((PolyExpr.const 3).mul n2).add (PolyExpr.const 4))

/-- The mask tape length is 3*n1+3*n2+4. -/
theorem maskCount_eq (n1 n2 : PolyExpr) : maskCount n1 n2 =
    ((PolyExpr.const 3).mul n1).add (((PolyExpr.const 3).mul n2).add (PolyExpr.const 4)) := rfl

/-- Outer masks are a uniform finite scalar vector, without a sampler construction. -/
abbrev MaskDraw (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) :=
  Fin ((maskCount n1 n2).eval κ) → ZMod pp.group.order

/-- The outer scalar draw has exactly its displayed vector type. -/
theorem maskDraw_eq (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : MaskDraw G n1 n2 κ pp =
      (Fin ((maskCount n1 n2).eval κ) → ZMod pp.group.order) := rfl

/-- The six known scalar blocks used in the proof games [Wee20, §3.3, pp. 7–8]. -/
structure Masks (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ) where
  /-- First public mask. -/
  A1 : Matrix (Fin 2) (Fin (n1.eval κ)) (ZMod pp.group.order)
  /-- Second public mask. -/
  A2 : Matrix (Fin 2) (Fin (n2.eval κ)) (ZMod pp.group.order)
  /-- Honest first encryption seed. -/
  s1 : Fin 2 → ZMod pp.group.order
  /-- Honest second encryption seed. -/
  s2 : Fin 2 → ZMod pp.group.order
  /-- Independent first simulated vector. -/
  y1 : Fin (n1.eval κ) → ZMod pp.group.order
  /-- Independent second simulated vector. -/
  y2 : Fin (n2.eval κ) → ZMod pp.group.order

/-- Total coordinate access defaults to zero beyond the allocated tape. Technical glue. -/
def maskAt (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : MaskDraw G n1 n2 κ pp) (i : ℕ) : ZMod pp.group.order :=
  if h : i < (maskCount n1 n2).eval κ then ω ⟨i, h⟩ else 0

/-- Mask coordinate access exposes its in-bounds/default split. -/
theorem maskAt_eq (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : MaskDraw G n1 n2 κ pp) (i : ℕ) : maskAt G n1 n2 κ pp ω i =
      if h : i < (maskCount n1 n2).eval κ then ω ⟨i, h⟩ else 0 := rfl

/-- Split the outer tape into disjoint row-major mask blocks
[Wee20, §3.3, pp. 7–8, with explicit finite coordinates]. -/
def masksAt (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : MaskDraw G n1 n2 κ pp) : Masks G n1 n2 κ pp :=
  let getScalar := maskAt G n1 n2 κ pp ω
  let off := 2 * n1.eval κ + 2 * n2.eval κ
  ⟨(fun i j => getScalar (i.val * n1.eval κ + j.val)),
    (fun i j => getScalar (2 * n1.eval κ + i.val * n2.eval κ + j.val)),
    (fun i => getScalar (off + i.val)), (fun i => getScalar (off + 2 + i.val)),
    (fun i => getScalar (off + 4 + i.val)), (fun i => getScalar (off + 4 + n1.eval κ + i.val))⟩

/-- The mask blocks use the displayed disjoint offsets. -/
theorem masksAt_eq (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : MaskDraw G n1 n2 κ pp) : masksAt G n1 n2 κ pp ω =
      let getScalar := maskAt G n1 n2 κ pp ω
      let off := 2 * n1.eval κ + 2 * n2.eval κ
      ⟨(fun i j => getScalar (i.val * n1.eval κ + j.val)),
        (fun i j => getScalar (2 * n1.eval κ + i.val * n2.eval κ + j.val)),
        (fun i => getScalar (off + i.val)), (fun i => getScalar (off + 2 + i.val)),
        (fun i => getScalar (off + 4 + i.val)),
        (fun i => getScalar (off + 4 + n1.eval κ + i.val))⟩ := rfl

/-- The common game draw combines outer masks with Π's padded scalar tape. Technical glue. -/
abbrev SecurityDraw (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) :=
  MaskDraw G n1 n2 κ pp × Linear.SecurityDraw G PG (piDim n1 n2) q κ pp

/-- The common draw is exactly the product of the two finite vector tapes. -/
theorem securityDraw_eq (G : BilinearGen) {ℓ : PolyExpr} (n1 n2 q : PolyExpr)
    {Fn : ℕ → ℕ+ → Type} (PG : PartialGarbling.Raw ℓ (n1.mul n2) Fn)
    (κ : ℕ) (pp : PublicParams G κ) : SecurityDraw G n1 n2 q PG κ pp =
      (MaskDraw G n1 n2 κ pp × Linear.SecurityDraw G PG (piDim n1 n2) q κ pp) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
