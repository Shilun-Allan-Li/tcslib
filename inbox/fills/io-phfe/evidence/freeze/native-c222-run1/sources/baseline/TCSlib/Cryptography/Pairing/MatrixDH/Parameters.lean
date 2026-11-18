/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public parameters for group-based experiments

The common public data are a generated group description and a uniformly drawn nonidentity
source-group generator. Reachability is a proposition, so different coins producing the same
public data do not create different parameter objects.

## Main definitions

* `GroupDescription`, `PublicParams`: generated descriptions and their public generators.
* `GeneratorDraw`, `publicParamsCore`: the conditional draw and deterministic core.
* `publicParamsGen`: exact sequential sampling of the description and generator.

## Main results

Equation readers expose the public encoding and the exact generation law.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Section 3 and Definition 4.1.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Section 2.1.
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.Games

/-- A group description is reachable when the bilinear generator outputs it on some coin
string. Technical glue: the witness is a proposition, so it does not distinguish equal
descriptions or supply advice to an algorithm. -/
abbrev GroupDescription (G : BilinearGen) (κ : ℕ) : Type :=
  {d : List Bool // ∃ r : G.gen.Coins κ, G.desc κ r = d}

/-- The description type consists of strings in the image of the bilinear generator. -/
theorem groupDescription_eq (G : BilinearGen) (κ : ℕ) :
    GroupDescription G κ = {d : List Bool // ∃ r : G.gen.Coins κ, G.desc κ r = d} := rfl

/-- Public parameters contain a reachable group description and a nonidentity generator
[GJLS21, Definition 4.1; Wee20, Section 2.1]. The generator is sampled uniformly from the
nonidentity source-group elements, separately after drawing the group description. -/
structure PublicParams (G : BilinearGen) (κ : ℕ) where
  /-- A description output by the group generator. -/
  description : GroupDescription G κ
  /-- The source-group generator used throughout this setup. -/
  generator : (G.group κ description.val).G
  /-- In a prime-order group every nonidentity element is a generator. -/
  generator_ne_one : generator ≠ 1

namespace PublicParams

/-- The group carried by public parameters is the group described by their public word. -/
abbrev group {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    BilinearGroup (G.wG.eval κ) (G.wT.eval κ) := G.group κ pp.description.val

/-- Reading the public group returns the generator's interpretation of the description. -/
theorem group_eq {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    pp.group = G.group κ pp.description.val := rfl

/-- The positive modulus of public parameters is read from their group order. Honest
algorithms use this value, without computing an external prime schedule. -/
abbrev orderParam {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) : ℕ+ :=
  ⟨pp.group.order, pp.group.order_prime.pos⟩

/-- The positive public modulus has the same natural value as the public group's order. -/
theorem orderParam_val {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    (pp.orderParam : ℕ) = (G.group κ pp.description.val).order := rfl

/-- Encode public parameters as the pair of the description and generator encoding.
This is the wire representation of the public parameters [GJLS21, Definition 4.1]. -/
def encode {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) : List Bool :=
  pairEncode pp.description.val
    (List.ofFn ((G.group κ pp.description.val).encG pp.generator))

/-- The public-parameter word pairs the group description and encoded generator. -/
theorem encode_eq {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    pp.encode = pairEncode pp.description.val
      (List.ofFn ((G.group κ pp.description.val).encG pp.generator)) := rfl

end PublicParams

/-- A nonidentity group element is the additional draw made after the group description
[Wee20, Section 2.1]. This is one draw type; no product sampler is constructed. -/
abbrev GeneratorDraw (G : BilinearGen) (κ : ℕ) (d : GroupDescription G κ) : Type :=
  {g : (G.group κ d.val).G // g ≠ 1}

/-- The generator draw is the subtype of nonidentity source-group elements. -/
theorem generatorDraw_eq (G : BilinearGen) (κ : ℕ) (d : GroupDescription G κ) :
    GeneratorDraw G κ d = {g : (G.group κ d.val).G // g ≠ 1} := rfl

/-- Attach a sampled generator to its public group description. This is the deterministic
core of the second stage of public-parameter generation [GJLS21, Definition 4.1]. -/
def publicParamsCore (G : BilinearGen) (κ : ℕ) (d : GroupDescription G κ)
    (g : GeneratorDraw G κ d) : PublicParams G κ :=
  ⟨d, g.val, g.property⟩

/-- The public-parameter core attaches the nonidentity generator without changing it. -/
theorem publicParamsCore_eq (G : BilinearGen) (κ : ℕ) (d : GroupDescription G κ)
    (g : GeneratorDraw G κ d) : publicParamsCore G κ d g = ⟨d, g.val, g.property⟩ := rfl

/-- Generate the group description, then sample a nonidentity generator in that group
[Wee20, Section 2.1]. The dependent draws are sequenced; no uniform law on a dependent
sum is substituted for their joint law. -/
noncomputable def publicParamsGen (G : BilinearGen) (κ : ℕ) :
    ProbComp (PublicParams G κ) :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
    let d : GroupDescription G κ := ⟨G.desc κ r, ⟨r, rfl⟩⟩
    publicParamsCore G κ d <$> ProbComp.sample (GeneratorDraw G κ d)

/-- Public-parameter generation is the displayed pair of sequential dependent draws. -/
theorem publicParamsGen_eq (G : BilinearGen) (κ : ℕ) :
    publicParamsGen G κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
        let d : GroupDescription G κ := ⟨G.desc κ r, ⟨r, rfl⟩⟩
        publicParamsCore G κ d <$> ProbComp.sample (GeneratorDraw G κ d) := rfl

/-- A fixed order schedule agrees with the order of every reachable public parameter.
This is transport glue from the generated-instance reader, not an algorithm computing the
schedule or modulus. -/
theorem order_eq_of_publicParams (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) (pp : PublicParams G κ) :
    (G.group κ pp.description.val).order = p κ :=
  pp.description.property.elim (fun r hr =>
    (congrArg (fun d => (G.group κ d).order) hr).symm.trans
      ((congrArg (fun B : BilinearGroup (G.wG.eval κ) (G.wT.eval κ) => B.order)
        (G.inst_eq κ r)).symm.trans (hp κ r)))

/-- A fixed order schedule of a prime-order group generator is prime at each parameter.
This proof reads one generated instance; honest algorithms do not evaluate the schedule. -/
theorem orderSchedule_prime (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) : (p κ).Prime :=
  (hp κ (fun _ => false)) ▸ (G.inst κ (fun _ => false)).order_prime

/-- A fixed prime order schedule is nonzero, so its residue types are finite. -/
theorem orderSchedule_neZero (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) : NeZero (p κ) :=
  ⟨(orderSchedule_prime G p hp κ).ne_zero⟩

end TCSlib.Cryptography.Pairing
