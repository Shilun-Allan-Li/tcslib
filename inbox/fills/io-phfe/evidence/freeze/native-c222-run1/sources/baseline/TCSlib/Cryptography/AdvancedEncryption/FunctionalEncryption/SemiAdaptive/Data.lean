/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounded semi-adaptive adversaries

The adversary sees public parameters and the public key, asks its single challenge,
and then requests function keys. Its fixed-width oracle interface uses the library's
bitSpec and bitCodec. Typed internal handlers encode optional keys and ciphertexts.
The budget counts every oracle call, including the challenge and rejected calls.

## Main definitions

* `FEScheme.Raw.saSpec`, `saCodec`: the two fixed-width oracles and machine codec.
* `FEScheme.Raw.SAAdv`: a bounded next-move adversary with explicit coins.
* `toSAAdv`: an oracle machine as a typed bounded adversary.

## Main results

* Component readers expose every query/answer wire conversion.
* `SAAdv.run_costBoundedBy`: run makes at most budget calls.
* `toSAAdv_run`: run agrees with toCompOn using the library bitCodec.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; ePrint 2020/1420, §2.2, p.5.
* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, §4.1, pp.11–12.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open TCSlib.Cryptography.Pairing
open Complexity Turing TCSlib.Cryptography.Games

namespace FEScheme.Raw

variable {C : FnClass} (S : FEScheme.Raw C)

/-- Challenge queries contain the public and private words; key queries contain
one function description. [Wee20, §2.2, p.5]. -/
abbrev saIn (S : FEScheme.Raw C) (kappa : ℕ) : Fin 2 → ℕ
  | 0 => C.pubLen.eval kappa + C.privLen.eval kappa
  | 1 => C.fnLen.eval kappa

/-- The challenge-query width is the sum of the input widths. -/
theorem saIn_zero (kappa : ℕ) :
    S.saIn kappa 0 = C.pubLen.eval kappa + C.privLen.eval kappa := rfl

/-- The key-query width is the function-description width. -/
theorem saIn_one (kappa : ℕ) : S.saIn kappa 1 = C.fnLen.eval kappa := rfl

/-- Oracle answers contain one validity bit and a ciphertext or key encoding. -/
abbrev saOut (kappa : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval kappa + 1
  | 1 => S.skLen.eval kappa + 1

/-- The challenge answer has one validity bit and its ciphertext payload. -/
theorem saOut_zero (kappa : ℕ) : S.saOut kappa 0 = S.ctLen.eval kappa + 1 := rfl

/-- The key answer has one validity bit and its key payload. -/
theorem saOut_one (kappa : ℕ) : S.saOut kappa 1 = S.skLen.eval kappa + 1 := rfl

/-- The semi-adaptive specification is the library's fixed-width bit specification. -/
abbrev saSpec (kappa : ℕ) : OracleSpec (Fin 2) := bitSpec (S.saIn kappa) (S.saOut kappa)

/-- The oracle specification has exactly the displayed input and output widths. -/
theorem saSpec_eq (kappa : ℕ) :
    S.saSpec kappa = bitSpec (S.saIn kappa) (S.saOut kappa) := rfl

/-- The machine codec is the library's bitCodec with a one-bit final output. -/
def saCodec (kappa : ℕ) : MachineCodec (S.saSpec kappa) (Fin 1 → Bool) :=
  bitCodec (S.saIn kappa) (S.saOut kappa) 1

/-- The semi-adaptive codec is the displayed instance of bitCodec. -/
theorem saCodec_eq (kappa : ℕ) :
    S.saCodec kappa = bitCodec (S.saIn kappa) (S.saOut kappa) 1 := rfl

/-- Combine the typed public/private challenge words into one oracle query. -/
def saChallengeQuery (kappa : ℕ) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) : (S.saSpec kappa).dom 0 :=
  Fin.append x y

/-- Challenge queries append the private word to the public word. -/
theorem saChallengeQuery_eq (kappa : ℕ) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) :
    S.saChallengeQuery kappa x y = Fin.append x y := rfl

/-- Split a challenge query into its typed public and private input words. -/
def saSplitChallenge (kappa : ℕ) (xy : (S.saSpec kappa).dom 0) :
    (Fin (C.pubLen.eval kappa) → Bool) × (Fin (C.privLen.eval kappa) → Bool) :=
  (fun i => xy (Fin.castAdd (C.privLen.eval kappa) i),
    fun j => xy (Fin.natAdd (C.pubLen.eval kappa) j))

/-- The challenge's public word occupies its first input block. -/
theorem saSplitChallenge_fst (kappa : ℕ) (xy : (S.saSpec kappa).dom 0) :
    (S.saSplitChallenge kappa xy).1 =
      fun i => xy (Fin.castAdd (C.privLen.eval kappa) i) := rfl

/-- The challenge's private word occupies its second input block. -/
theorem saSplitChallenge_snd (kappa : ℕ) (xy : (S.saSpec kappa).dom 0) :
    (S.saSplitChallenge kappa xy).2 =
      fun j => xy (Fin.natAdd (C.pubLen.eval kappa) j) := rfl

/-- Read the typed function description from a key query. -/
def saKeyFunction (kappa : ℕ) (f : (S.saSpec kappa).dom 1) :
    Fin (C.fnLen.eval kappa) → Bool := f

/-- The key query is already the function-description word. -/
theorem saKeyFunction_eq (kappa : ℕ) (f : (S.saSpec kappa).dom 1) :
    S.saKeyFunction kappa f = f := rfl

/-- A typed challenge request is a query to oracle zero. -/
def saChallengeMove (kappa : ℕ) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) : Move (S.saSpec kappa) Bool :=
  .query 0 (S.saChallengeQuery kappa x y)

/-- The challenge move has the displayed oracle and combined query. -/
theorem saChallengeMove_eq (kappa : ℕ) (x : Fin (C.pubLen.eval kappa) → Bool)
    (y : Fin (C.privLen.eval kappa) → Bool) :
    S.saChallengeMove kappa x y = .query 0 (S.saChallengeQuery kappa x y) := rfl

/-- A typed key request is a query to oracle one. -/
def saKeyMove (kappa : ℕ) (f : Fin (C.fnLen.eval kappa) → Bool) :
    Move (S.saSpec kappa) Bool := .query 1 f

/-- The key move has the displayed oracle and function description. -/
theorem saKeyMove_eq (kappa : ℕ) (f : Fin (C.fnLen.eval kappa) → Bool) :
    S.saKeyMove kappa f = .query 1 f := rfl

/-- Encode an optional typed ciphertext using the common validity-bit answer format. -/
def saCTAnswer (kappa : ℕ) (pp : PublicParams S.G kappa) (ct : Option (S.CT kappa pp)) :
    (S.saSpec kappa).rng 0 :=
  TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer (ct.map (S.encCT kappa pp))

/-- Ciphertext answers use decAnswer on the optional ciphertext encoding. -/
theorem saCTAnswer_eq (kappa : ℕ) (pp : PublicParams S.G kappa)
    (ct : Option (S.CT kappa pp)) : S.saCTAnswer kappa pp ct =
    TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer (ct.map (S.encCT kappa pp)) := rfl

/-- Encode an optional typed key using the common validity-bit answer format. -/
def saSKAnswer (kappa : ℕ) (pp : PublicParams S.G kappa) (sk : Option (S.SK kappa pp)) :
    (S.saSpec kappa).rng 1 :=
  TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer (sk.map (S.encSK kappa pp))

/-- Key answers use decAnswer on the optional key encoding. -/
theorem saSKAnswer_eq (kappa : ℕ) (pp : PublicParams S.G kappa)
    (sk : Option (S.SK kappa pp)) : S.saSKAnswer kappa pp sk =
    TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer (sk.map (S.encSK kappa pp)) := rfl

/-- Extract a challenge payload from a successful challenge answer, without
inverting its typed ciphertext encoding. Other oracle answers give none. -/
def saCTPayload (kappa : ℕ) :
    (i : Fin 2) → (S.saSpec kappa).rng i → Option (Fin (S.ctLen.eval kappa) → Bool)
  | 0, a =>
    let v : Fin (S.ctLen.eval kappa + 1) → Bool := a
    if v 0 then some (Fin.tail v) else none
  | 1, _ => none

/-- A challenge payload is present exactly when its validity bit is true. -/
theorem saCTPayload_zero (kappa : ℕ) (a : Fin (S.ctLen.eval kappa + 1) → Bool) :
    S.saCTPayload kappa 0 a = if a 0 then some (Fin.tail a) else none := rfl

/-- A key answer never supplies a challenge payload. -/
theorem saCTPayload_one (kappa : ℕ) (a : (S.saSpec kappa).rng 1) :
    S.saCTPayload kappa 1 a = none := rfl

/-- Extract a key payload from a successful key answer without recovering a typed
key. Challenge answers give none. This is wire-reading glue for two-stage adversaries. -/
def saSKPayload (kappa : ℕ) :
    (i : Fin 2) → (S.saSpec kappa).rng i → Option (Fin (S.skLen.eval kappa) → Bool)
  | 0, _ => none
  | 1, a =>
    let v : Fin (S.skLen.eval kappa + 1) → Bool := a
    if v 0 then some (Fin.tail v) else none

/-- A challenge answer never supplies a key payload. -/
theorem saSKPayload_zero (kappa : ℕ) (a : (S.saSpec kappa).rng 0) :
    S.saSKPayload kappa 0 a = none := rfl

/-- A key payload is present exactly when its validity bit is true. -/
theorem saSKPayload_one (kappa : ℕ) (a : Fin (S.skLen.eval kappa + 1) → Bool) :
    S.saSKPayload kappa 1 a = if a 0 then some (Fin.tail a) else none := rfl

/-- The initial adversary word contains public parameters and the master public key.
[Wee20, §2.2, p.5]. -/
def saInputWord (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp) :
    List Bool := pairEncode pp.encode (List.ofFn (S.encMPK kappa pp pk))

/-- The adversary's initial word is the displayed pair. -/
theorem saInputWord_eq (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp) :
    S.saInputWord kappa pp pk = pairEncode pp.encode (List.ofFn (S.encMPK kappa pp pk)) := rfl

/-- A typed semi-adaptive adversary has one coin polynomial, a total query budget,
and a next move depending on its initial public view, fixed coins and full history.
[Wee20, §2.2, p.5]. Its run is derived by the bounded library interpreter. -/
structure SAAdv where
  /-- The number of independent fair coins. -/
  coins : PolyExpr
  /-- The total number of oracle calls allowed, including the challenge. -/
  budget : PolyExpr
  /-- The next move for any public view, coin word and oracle history. -/
  next : (kappa : ℕ) → (pp : PublicParams S.G kappa) → S.MPK kappa pp → List Bool →
    QueryLog (S.saSpec kappa) → Move (S.saSpec kappa) Bool

namespace SAAdv

variable {S} (A : SAAdv S)

/-- Run the next-move adversary with its total query budget, timing out to false. -/
def run (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp) (r : List Bool) :
    OracleComp (S.saSpec kappa) Bool :=
  buildComp (A.next kappa pp pk r) false (A.budget.eval kappa) []

/-- Adversary run is precisely the existing bounded buildComp interpreter. -/
theorem run_eq (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp)
    (r : List Bool) : A.run kappa pp pk r =
    buildComp (A.next kappa pp pk r) false (A.budget.eval kappa) [] := rfl

/-- The derived adversary computation never exceeds its total call budget. -/
theorem run_costBoundedBy (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (r : List Bool) :
    (A.run kappa pp pk r).CostBoundedBy (fun _ => 1) (A.budget.eval kappa) :=
  buildComp_costBoundedBy (A.next kappa pp pk r) false (A.budget.eval kappa) []

end SAAdv

/-- A one-bit codec move is read as a Boolean verdict without changing any query. -/
def saReadMove (kappa : ℕ) (w : List Bool) : Move (S.saSpec kappa) Bool :=
  match (S.saCodec kappa).decodeMove w with
  | .ret b => .ret (b 0)
  | .query i x => .query i x

/-- The move reader changes only the final one-bit output into Bool. -/
theorem saReadMove_eq (kappa : ℕ) (w : List Bool) : S.saReadMove kappa w =
    match (S.saCodec kappa).decodeMove w with
    | .ret b => .ret (b 0)
    | .query i x => .query i x := rfl

end FEScheme.Raw

/-- An oracle NUPPT uses the standard bitCodec and its encoded initial public view.
[Wee20, §2.2, p.5], instantiated by the library's oracle-machine convention. -/
def toSAAdv {C : FnClass} {S : FEScheme.Raw C}
    (A : NUPPT) (q : PolyExpr) : S.SAAdv where
  coins := A.coins
  budget := q
  next := fun kappa pp pk r hist => S.saReadMove kappa
    (A.runAtL kappa (pairEncode (S.saInputWord kappa pp pk)
      ((S.saCodec kappa).encodeLog hist)) r)

/-- The oracle-machine adversary uses its machine's original coin polynomial. -/
theorem toSAAdv_coins {C : FnClass} {S : FEScheme.Raw C}
    (A : NUPPT) (q : PolyExpr) : (toSAAdv (S := S) A q).coins = A.coins := rfl

/-- The oracle-machine adversary's budget is q total oracle calls. -/
theorem toSAAdv_budget {C : FnClass} {S : FEScheme.Raw C}
    (A : NUPPT) (q : PolyExpr) : (toSAAdv (S := S) A q).budget = q := rfl

/-- Each next move is one machine activation on its initial view and encoded log. -/
theorem toSAAdv_next {C : FnClass} {S : FEScheme.Raw C}
    (A : NUPPT) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (r : List Bool) (hist : QueryLog (S.saSpec kappa)) :
    (toSAAdv (S := S) A q).next kappa pp pk r hist = S.saReadMove kappa
      (A.runAtL kappa (pairEncode (S.saInputWord kappa pp pk)
        ((S.saCodec kappa).encodeLog hist)) r) := rfl

/-- The typed run is exactly toCompOn with bitCodec, followed by reading its one bit.

**Proof sketch.** Read toCompOn_eq and runAt_eq. Induct on the remaining budget;
both computations use the same encoded history. Query branches append the same
entry; return and timeout branches differ only by reading the final bit. -/
theorem toSAAdv_run {C : FnClass} {S : FEScheme.Raw C}
    (A : NUPPT) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (r : A.Coins kappa) :
    (toSAAdv (S := S) A q).run kappa pp pk (List.ofFn r) =
      (fun b => b 0) <$> A.toCompOn
        (bitCodec (S.saIn kappa) (S.saOut kappa) 1)
        kappa (q.eval kappa) (S.saInputWord kappa pp pk) r := sorry

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
