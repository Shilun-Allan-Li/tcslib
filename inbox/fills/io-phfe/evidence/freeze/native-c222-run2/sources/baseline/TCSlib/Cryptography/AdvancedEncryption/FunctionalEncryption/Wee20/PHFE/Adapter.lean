/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Correctness
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Fresh

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Replay from wire adversaries to typed quadratic adversaries

Scalar decoding may identify distinct fixed-width words. Reencoding decoded inputs would
therefore change an adaptive machine's history. The adapter instead replays the original
wire adversary from its initial public view and coins. It keeps each original query word,
and reencodes only typed answers. A key is packaged with that original function word after
its decoded tensor is checked against the returned key's type index.

## Main definitions

* `PHFE.decodeChallenge`: scalar decoding with the private vector duplicated.
* `PHFE.wrapKey`: checked packaging that retains the original function bits.
* `PHFE.replayStep`, `replay`: the existing List.foldl applied to wire-log reconstruction.
* `PHFE.toQuadratic`: the concrete bounded typed adversary with identical coins and budget.

## Main results

* Equation readers specify every conversion and total refusal branch.
* `PHFE.expect_saGame_eq_fresh`: exact endpoint laws, including noncanonical aliases.
* `PHFE.saSimAdv_eq_fresh`: the adapter has no advantage loss.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Section 9.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Sections 2.2 and 3.1-3.2.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

section

variable (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
variable (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d))

local notation "S" => wee20PHFE_raw G ℓ n d PG
local notation "params" => publicParamsEquiv G ℓ n d PG

/-- Decode a wire challenge without changing the stored wire word
[GJLS21, Section 9; Wee20, Section 3.1]. -/
def decodeChallenge (κ : ℕ) (pp : PublicParams (S).G κ) (xy : ((S).saSpec κ).dom 0) :
    Quadratic.Challenge G ℓ n n κ (params κ pp) :=
  let msg := (S).saSplitChallenge κ xy
  let z := decodePrivate G ℓ n d κ (params κ pp) msg.2
  (decodePublic G ℓ n d κ (params κ pp) msg.1, z, z)

/-- The decoded challenge uses the same private vector in both typed slots. -/
theorem decodeChallenge_eq (κ : ℕ) (pp : PublicParams (S).G κ)
    (xy : ((S).saSpec κ).dom 0) : decodeChallenge G ℓ n d PG κ pp xy =
      let msg := (S).saSplitChallenge κ xy
      let z := decodePrivate G ℓ n d κ (params κ pp) msg.2
      (decodePublic G ℓ n d κ (params κ pp) msg.1, z, z) := rfl

/-- Package a typed key under its original wire function after checking its tensor index.
This is total adapter glue for [Wee20, Section 3.1]. No function encoding is inverted. -/
def wrapKey (κ : ℕ) (pp : PublicParams (S).G κ) (f : ((S).saSpec κ).dom 1)
    (key : Quadratic.KeyPack G n n PG κ (params κ pp)) : Option ((S).SK κ pp) :=
  let bits := (S).saKeyFunction κ f
  let decoded := decodeFunction G ℓ n d κ (params κ pp) bits
  if h : decoded = key.1 then
    some ((keyEquiv G ℓ n d PG κ pp).symm ⟨bits, Eq.mp (congrArg (fun f => Quadratic.Key G n n PG κ
      (params κ pp) f) h.symm) key.2⟩)
  else none

/-- The key wrapper's only accepted branch retains the original function word. -/
theorem wrapKey_eq (κ : ℕ) (pp : PublicParams (S).G κ) (f : ((S).saSpec κ).dom 1)
    (key : Quadratic.KeyPack G n n PG κ (params κ pp)) :
    wrapKey G ℓ n d PG κ pp f key =
      let bits := (S).saKeyFunction κ f
      let decoded := decodeFunction G ℓ n d κ (params κ pp) bits
      if h : decoded = key.1 then
        some ((keyEquiv G ℓ n d PG κ pp).symm ⟨bits, Eq.mp (congrArg (fun f => Quadratic.Key G n n
          PG κ (params κ pp) f) h.symm) key.2⟩)
      else none := rfl

/-- One replay step recovers the original next query from the original-bit history.
Its typed query and key index must agree with scalar decoding; inconsistent histories
are rejected. This is adaptive bookkeeping for [Wee20, Section 2.2]. -/
def replayStep (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams (S).G κ)
    (pk : Quadratic.MPK G ℓ n n κ (params κ pp)) (r : List Bool)
    (acc : Option (QueryLog ((S).saSpec κ)))
    (entry : Σ i, (Quadratic.saSpec G n n PG κ (params κ pp)).dom i ×
      (Quadratic.saSpec G n n PG κ (params κ pp)).rng i) :
    Option (QueryLog ((S).saSpec κ)) :=
  acc.bind fun hist =>
    match A.next κ pp ((mpkEquiv G ℓ n d PG κ pp).symm pk) r hist, entry with
    | .query 0 xy, ⟨false, query, answer⟩ =>
        if decodeChallenge G ℓ n d PG κ pp xy = query then
          some (hist ++ [⟨0, xy, (S).saCTAnswer κ pp
            (answer.map (ctEquiv G ℓ n d PG κ pp).symm)⟩])
        else none
    | .query 1 f, ⟨true, query, answer⟩ =>
        if decodeFunction G ℓ n d κ (params κ pp) ((S).saKeyFunction κ f) = query then
          let wireAnswer := match answer with
            | none => some ((S).saSKAnswer κ pp none)
            | some key => (wrapKey G ℓ n d PG κ pp f key).map
                (fun sk => (S).saSKAnswer κ pp (some sk))
          wireAnswer.map fun a => hist ++ [⟨1, f, a⟩]
        else none
    | _, _ => none

/-- The replay step has precisely the displayed checked query and answer branches. 

**Proof sketch.** Each branch and named block is the same as in the deterministic
definition, so the equation follows by reducing that definition alone. -/
theorem replayStep_eq (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams (S).G κ)
    (pk : Quadratic.MPK G ℓ n n κ (params κ pp)) (r : List Bool)
    (acc : Option (QueryLog ((S).saSpec κ)))
    (entry : Σ i, (Quadratic.saSpec G n n PG κ (params κ pp)).dom i ×
      (Quadratic.saSpec G n n PG κ (params κ pp)).rng i) :
    replayStep G ℓ n d PG A κ pp pk r acc entry =
      acc.bind fun hist =>
        match A.next κ pp ((mpkEquiv G ℓ n d PG κ pp).symm pk) r hist, entry with
        | .query 0 xy, ⟨false, query, answer⟩ =>
            if decodeChallenge G ℓ n d PG κ pp xy = query then
              some (hist ++ [⟨0, xy, (S).saCTAnswer κ pp
                (answer.map (ctEquiv G ℓ n d PG κ pp).symm)⟩])
            else none
        | .query 1 f, ⟨true, query, answer⟩ =>
            if decodeFunction G ℓ n d κ (params κ pp) ((S).saKeyFunction κ f) = query then
              let wireAnswer := match answer with
                | none => some ((S).saSKAnswer κ pp none)
                | some key => (wrapKey G ℓ n d PG κ pp f key).map
                    (fun sk => (S).saSKAnswer κ pp (some sk))
              wireAnswer.map fun a => hist ++ [⟨1, f, a⟩]
            else none
        | _, _ => none := rfl

/-- Reconstruct the wire log by the library list fold, never by a new recursion host.
Every accepted entry retains its original query bits [Wee20, Section 2.2]. -/
def replay (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams (S).G κ)
    (pk : Quadratic.MPK G ℓ n n κ (params κ pp)) (r : List Bool)
    (hist : QueryLog (Quadratic.saSpec G n n PG κ (params κ pp))) :
    Option (QueryLog ((S).saSpec κ)) :=
  hist.foldl (replayStep G ℓ n d PG A κ pp pk r) (some [])

/-- Replay is exactly the displayed fold from the empty wire history. -/
theorem replay_eq (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams (S).G κ)
    (pk : Quadratic.MPK G ℓ n n κ (params κ pp)) (r : List Bool)
    (hist : QueryLog (Quadratic.saSpec G n n PG κ (params κ pp))) :
    replay G ℓ n d PG A κ pp pk r hist =
      hist.foldl (replayStep G ℓ n d PG A κ pp pk r) (some []) := rfl

/-- Empty typed history reconstructs the empty original wire history. -/
theorem replay_nil (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams (S).G κ)
    (pk : Quadratic.MPK G ℓ n n κ (params κ pp)) (r : List Bool) :
    replay G ℓ n d PG A κ pp pk r [] = some [] := rfl

/-- Appending one typed answer is exactly one replay step after the previous replay. -/
theorem replay_append (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams (S).G κ)
    (pk : Quadratic.MPK G ℓ n n κ (params κ pp)) (r : List Bool)
    (hist : QueryLog (Quadratic.saSpec G n n PG κ (params κ pp)))
    (entry : Σ i, (Quadratic.saSpec G n n PG κ (params κ pp)).dom i ×
      (Quadratic.saSpec G n n PG κ (params κ pp)).rng i) :
    replay G ℓ n d PG A κ pp pk r (hist ++ [entry]) =
      replayStep G ℓ n d PG A κ pp pk r (replay G ℓ n d PG A κ pp pk r hist) entry :=
  List.foldl_append

/-- The next typed move decodes only the newly replayed wire query
[Wee20, Section 2.2; GJLS21, Section 9]. An inconsistent history terminates with false. -/
def quadraticNext (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams (S).G κ)
    (pk : Quadratic.MPK G ℓ n n κ (params κ pp)) (r : List Bool)
    (hist : QueryLog (Quadratic.saSpec G n n PG κ (params κ pp))) :
    Move (Quadratic.saSpec G n n PG κ (params κ pp)) Bool :=
  match replay G ℓ n d PG A κ pp pk r hist with
  | none => .ret false
  | some wire => match A.next κ pp ((mpkEquiv G ℓ n d PG κ pp).symm pk) r wire with
    | .ret b => .ret b
    | .query 0 xy => .query false (decodeChallenge G ℓ n d PG κ pp xy)
    | .query 1 f => .query true
        (decodeFunction G ℓ n d κ (params κ pp) ((S).saKeyFunction κ f))

/-- The typed next move is the displayed replay-and-decode operation. -/
theorem quadraticNext_eq (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams (S).G κ)
    (pk : Quadratic.MPK G ℓ n n κ (params κ pp)) (r : List Bool)
    (hist : QueryLog (Quadratic.saSpec G n n PG κ (params κ pp))) :
    quadraticNext G ℓ n d PG A κ pp pk r hist =
      match replay G ℓ n d PG A κ pp pk r hist with
      | none => .ret false
      | some wire => match A.next κ pp ((mpkEquiv G ℓ n d PG κ pp).symm pk) r wire with
        | .ret b => .ret b
        | .query 0 xy => .query false (decodeChallenge G ℓ n d PG κ pp xy)
        | .query 1 f => .query true
            (decodeFunction G ℓ n d κ (params κ pp) ((S).saKeyFunction κ f)) := rfl

/-- Transport the replayed move along the public codec's round trip. This explicit
transport keeps foreign public-parameter and key types sealed. -/
def toQuadraticNext (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams G κ)
    (pk : Quadratic.MPK G ℓ n n κ pp) (r : List Bool)
    (hist : QueryLog (Quadratic.saSpec G n n PG κ pp)) :
    Move (Quadratic.saSpec G n n PG κ pp) Bool :=
  let wire := (params κ).symm pp
  let h := (params κ).apply_symm_apply pp
  let key : Quadratic.MPK G ℓ n n κ (params κ wire) := h.symm ▸ pk
  let log : QueryLog (Quadratic.saSpec G n n PG κ (params κ wire)) := h.symm ▸ hist
  h ▸ quadraticNext G ℓ n d PG A κ wire key r log

/-- The next-move codec transports key, log and result using one public round trip. -/
theorem toQuadraticNext_eq (A : (S).SAAdv) (κ : ℕ) (pp : PublicParams G κ)
    (pk : Quadratic.MPK G ℓ n n κ pp) (r : List Bool)
    (hist : QueryLog (Quadratic.saSpec G n n PG κ pp)) :
    toQuadraticNext G ℓ n d PG A κ pp pk r hist =
      let wire := (params κ).symm pp
      let h := (params κ).apply_symm_apply pp
      let key : Quadratic.MPK G ℓ n n κ (params κ wire) := h.symm ▸ pk
      let log : QueryLog (Quadratic.saSpec G n n PG κ (params κ wire)) := h.symm ▸ hist
      h ▸ quadraticNext G ℓ n d PG A κ wire key r log := rfl

/-- The explicit typed quadratic adversary preserves the original coins and TOTAL call
budget [Wee20, Section 2.2; GJLS21, Section 9]. It constructs no oracle machine. -/
def toQuadratic (A : (S).SAAdv) : Quadratic.SAAdv G n n PG where
  coins := A.coins
  budget := A.budget
  next := toQuadraticNext G ℓ n d PG A

/-- The adapter preserves the original coin layout. -/
theorem toQuadratic_coins (A : (S).SAAdv) :
    (toQuadratic G ℓ n d PG A).coins = A.coins := rfl

/-- The adapter preserves the TOTAL query budget without adding a call. -/
theorem toQuadratic_budget (A : (S).SAAdv) :
    (toQuadratic G ℓ n d PG A).budget = A.budget := rfl

/-- The adapter uses precisely the published replayed next move. -/
theorem toQuadratic_next (A : (S).SAAdv) :
    (toQuadratic G ℓ n d PG A).next = toQuadraticNext G ℓ n d PG A := rfl

/-- The wire and typed fresh experiments have identical laws on both branches
[Wee20, Sections 2.2 and 3.1-3.2; GJLS21, Section 9]. The wire flag is true for real,
whereas the typed fresh flag is true for ideal.

**Proof sketch.** Reuse the public-parameter, MPK, CT and key codec readers, and couple
actual setup and every complete finite draw by their published pushforward laws. Relate
the buildComp histories by replay_append. Each accepted challenge retains its original
x/y words, and each key retains its original function word; decoded aliases are never
reencoded as inputs. Query and packed-key checks are equalities on these reachable
histories. Duplicate challenges and pre-challenge keys give the same none encoding; the
extra typed accepted-key cap cannot be reached within the identical TOTAL call budget.
On the ideal branch class_eval_eq identifies the allowed scalar, and scalarValueEquiv_eq
identifies its codec before known-scalar exponentiation. Apply expect_simulate_rel and
average setup, public parameters and adversary coins. No exponent is recovered. -/
theorem expect_saGame_eq_fresh (hPG : PGSound PG) (A : (S).SAAdv) (real : Bool)
    (κ : ℕ) (test : Bool → ℝ) :
    ProbComp.expect ((S).saGame (wee20SASim_raw G ℓ n d PG) A real κ) test =
      ProbComp.expect
        (Quadratic.freshSaGame G n n PG (toQuadratic G ℓ n d PG A) (!real) κ) test := sorry

/-- Wire PHFE advantage equals the actual fresh typed quadratic advantage, without loss
[Wee20, Section 3, main claim; GJLS21, Section 9].

**Proof sketch.** Apply expect_saGame_eq_fresh to the two acceptance tests. Read both
advantage equations and the shared advantage/acceptance reader. -/
theorem saSimAdv_eq_fresh (hPG : PGSound PG) (A : (S).SAAdv) (κ : ℕ) :
    (S).saSimAdv (wee20SASim_raw G ℓ n d PG) A κ =
      Quadratic.freshSaSimAdv G n n PG (toQuadratic G ℓ n d PG A) κ := sorry

end

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE
