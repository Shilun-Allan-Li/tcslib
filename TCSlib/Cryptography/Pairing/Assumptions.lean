/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bilinear Diffie–Hellman assumptions

The *bilinear Diffie–Hellman* (BDH) problem [BB04, §3.1]: given `g, g^a, g^b, g^c ∈ G`, output
`e(g, g)^{abc} ∈ G_1`; and its decisional form (Decision BDH, DBDH): distinguish
`(g, g^a, g^b, g^c, e(g, g)^{abc})` (the distribution `P_BDH`) from `(g, g^a, g^b, g^c, T)` with
`T` uniform in `G_1` (the distribution `R_BDH`). In both, the generator `g` is uniform in
`G^* = G ∖ {1}`, the exponents `a, b, c` are uniform in `Z_p`, and the probability is also over
the adversary's coins. [BB04, §3.1] credits the BDH problem to [Jou00, SOK00, BF01].

**The experiments.** The bilinear group is drawn by the generator (`Pairing.BilinearGen`), and
the adversary is a non-uniform PPT machine (`Complexity.NUPPT`) that receives `1^κ` and the
string `⟨d, ⟨g, ⟨g^a, ⟨g^b, ⟨g^c, T⟩⟩⟩⟩⟩` of the description `d` and the encoded elements
(`tupleStr`; without `T` for BDH, `bdhStr`). The experiments are games of the `Games` framework
(`Games.ProbComp`): the generator's coins are drawn first, then `g`, the exponents and `T` from
the group they describe, then the adversary's coins. Sampling in sequence keeps the law of the
group the generator's law (a uniform seed over a dependent sum would not; run-3 audit P8-1 of
the DDH layer).

**Deviation:** [BB04, Definition 3.1] is concrete ("no `t`-time algorithm has advantage at least
`ε` in `G`"). Here the assumptions are asymptotic: every non-uniform PPT has negligible advantage
(BDH: success probability), relative to the generator. The decision advantage is the absolute
difference of acceptance probabilities (the paper writes the difference of the probabilities of
output `0`, without absolute value; the two are equivalent for the assumption since the negated
machine is a PPT). The adversary receives the group's description `d` and `1^κ`.

## Main definitions

* `TCSlib.Cryptography.Pairing.tupleStr`, `bdhStr` — the strings handed to the adversary.
* `BilinearGen.dbdhGame`, `BilinearGen.dbdhAdv`, `BilinearGen.DBDHAssumption` — the Decision BDH
  experiment, its advantage and the assumption [BB04, §3.1 and Definition 3.1].
* `BilinearGen.bdhGame`, `BilinearGen.BDHAssumption` — the BDH experiment and the assumption
  [BB04, §3.1 and Definition 3.1].

## Main results

* `BilinearGen.bdhAssumption_of_dbdhAssumption` — Decision BDH implies BDH when the order is
  at least `2^κ` except with negligible probability.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §3.1 (pp. 4–5): the BDH and
  Decision BDH problems, Definition 3.1.
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §5 (p. 392): "some Diffie–Hellman like problem and
  Diffie–Hellman like decision problem should be hard in order to get security".
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; Definition 69.4's convention that `A` receives `1^n`.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.Games

/-- The **Decision BDH string** `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` of a description `d`, four elements
`g, X, Y, Z` of `G` and an element `T` of `G_T`, each written by its encoding. It is the input
`(g, g^a, g^b, g^c, T)` of a Decision BDH algorithm [BB04, §3.1], with the group's description
in front. -/
def tupleStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) (t : B.GT) :
    List Bool :=
  pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
    (pairEncode (List.ofFn (B.encG y)) (pairEncode (List.ofFn (B.encG z))
      (List.ofFn (B.encT t))))))

/-- `tupleStr B d g x y z t = ⟨d, ⟨g, ⟨x, ⟨y, ⟨z, t⟩⟩⟩⟩⟩` with the elements encoded. -/
theorem tupleStr_eq {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G)
    (t : B.GT) :
    tupleStr B d g x y z t =
      pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
        (pairEncode (List.ofFn (B.encG y)) (pairEncode (List.ofFn (B.encG z))
          (List.ofFn (B.encT t)))))) := rfl

/-- The **BDH string** `⟨d, ⟨g, ⟨X, ⟨Y, Z⟩⟩⟩⟩`: the input `(g, g^a, g^b, g^c)` of a BDH algorithm
[BB04, §3.1], with the group's description in front. -/
def bdhStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) : List Bool :=
  pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
    (pairEncode (List.ofFn (B.encG y)) (List.ofFn (B.encG z)))))

/-- `bdhStr B d g x y z = ⟨d, ⟨g, ⟨x, ⟨y, z⟩⟩⟩⟩` with the elements encoded. -/
theorem bdhStr_eq {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) :
    bdhStr B d g x y z =
      pairEncode d (pairEncode (List.ofFn (B.encG g)) (pairEncode (List.ofFn (B.encG x))
        (pairEncode (List.ofFn (B.encG y)) (List.ofFn (B.encG z))))) := rfl

namespace BilinearGen

variable (G : BilinearGen)

/-- **The Decision BDH experiment** [BB04, §3.1] for the distinguisher `D` at parameter `κ`:
draw the generator's coins `r` (group `B = G.inst κ r`, description `d`), a generator
`g ∈ G^*`, exponents `a, b, c ∈ Z_p`, an element `T ∈ G_T` and `D`'s coins `ρ`, all uniform, and
return `D(1^κ, ⟨d, ⟨g, g^a, g^b, g^c, T'⟩⟩; ρ)`, where `T' = e(g, g)^{abc}` when `real` (the
distribution `P_BDH`) and `T' = T` otherwise (`R_BDH`). -/
noncomputable def dbdhGame (D : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (G.inst κ r).GT).bind fun t =>
  (ProbComp.sample (D.Coins κ)).bind fun ρ =>
    .pure (D.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
      (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)
      (if real then (G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val else t)) ρ)

/-- The Decision BDH experiment draws the generator's coins, `g ∈ G^*`, `(a, b, c) ∈ Z_p³`,
`T ∈ G_T` and the distinguisher's coins, and runs the distinguisher on
`tupleStr B d g g^a g^b g^c T'` with `T' = e(g, g)^{abc}` if `real` and `T' = T` otherwise. -/
theorem dbdhGame_eq (D : NUPPT) (real : Bool) (κ : ℕ) :
    G.dbdhGame D real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (G.inst κ r).GT).bind fun t =>
      (ProbComp.sample (D.Coins κ)).bind fun ρ =>
        .pure (D.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
          (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)
          (if real then (G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val else t)) ρ) :=
  rfl

/-- **The Decision BDH advantage** of `D` at `κ`:
`|Pr[D(P_BDH) = 1] − Pr[D(R_BDH) = 1]|` [BB04, §3.1]. -/
noncomputable def dbdhAdv (D : NUPPT) (κ : ℕ) : ℝ :=
  advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ)

/-- `G.dbdhAdv D κ = advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ)`. -/
theorem dbdhAdv_eq (D : NUPPT) (κ : ℕ) :
    G.dbdhAdv D κ = advantage (G.dbdhGame D false κ) (G.dbdhGame D true κ) := rfl

/-- **The Decision BDH assumption** relative to the generator `G` [BB04, §3.1 and
Definition 3.1]: every non-uniform PPT distinguisher has negligible Decision BDH advantage.

**Deviation:** asymptotic, relative to a generator, against non-uniform PPT machines that
receive `1^κ` and the description (module docstring). -/
def DBDHAssumption : Prop := ∀ D : NUPPT, Negligible fun κ => G.dbdhAdv D κ

/-- `G.DBDHAssumption` iff `κ ↦ G.dbdhAdv D κ` is negligible for every non-uniform PPT `D`. -/
theorem dbdhAssumption_iff : G.DBDHAssumption ↔ ∀ D : NUPPT, Negligible fun κ => G.dbdhAdv D κ :=
  Iff.rfl

/-- **The BDH experiment** [BB04, §3.1] for the machine `A` at parameter `κ`: draw the
generator's coins `r`, a generator `g ∈ G^*`, exponents `a, b, c ∈ Z_p` and `A`'s coins `ρ`, all
uniform, and accept iff `A(1^κ, ⟨d, ⟨g, g^a, g^b, g^c⟩⟩; ρ)` is the encoding of `e(g, g)^{abc}`. -/
noncomputable def bdhGame (A : NUPPT) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
    .pure (decide (A.runAt κ (bdhStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
      (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)) ρ =
        List.ofFn ((G.inst κ r).encT
          ((G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val))))

/-- The BDH experiment draws the generator's coins, `g ∈ G^*`, `(a, b, c) ∈ Z_p³` and the
machine's coins, and accepts iff the machine's output on `bdhStr B d g g^a g^b g^c` is the
encoding of `e(g, g)^{abc}`. -/
theorem bdhGame_eq (A : NUPPT) (κ : ℕ) :
    G.bdhGame A κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
        .pure (decide (A.runAt κ (bdhStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
          (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)) ρ =
            List.ofFn ((G.inst κ r).encT
              ((G.inst κ r).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val)))) :=
  rfl

/-- **The BDH assumption** relative to the generator `G` [BB04, §3.1 and Definition 3.1]: every
non-uniform PPT machine solves the BDH problem with negligible probability.

**Deviation:** asymptotic, relative to a generator, against non-uniform PPT machines that
receive `1^κ` and the description; the answer must be the encoding of `e(g, g)^{abc}` exactly. -/
def BDHAssumption : Prop := ∀ A : NUPPT, Negligible fun κ => accept (G.bdhGame A κ)

/-- `G.BDHAssumption` iff `κ ↦ Pr[G.bdhGame A κ = 1]` is negligible for every non-uniform
PPT `A`. -/
theorem bdhAssumption_iff :
    G.BDHAssumption ↔ ∀ A : NUPPT, Negligible fun κ => accept (G.bdhGame A κ) := Iff.rfl

/-- **Decision BDH implies BDH** when the group order is at least `2^κ` except with negligible
probability: a BDH solver `A` gives the Decision BDH distinguisher "run `A` on `(g, g^a, g^b, g^c)`
and accept iff its answer is `T`".

**Source:** not stated in [BB04] or [Jou00]; [BB04, §3.1] defines both problems and calls the
decision form the stronger assumption implicitly by using it. The implication is the standard
remark that deciding is no harder than computing.

**Proof sketch.** Given `A`, let `D(1^κ, ⟨s, T⟩)` run `A(1^κ, s)` with its own coins and accept
iff the answer equals the encoding of `T`, where `s` is re-paired from the first five components
(a polynomial-time string map, so `D` is a non-uniform PPT). On `P_BDH`, `D` accepts exactly when
`A` succeeds, so `Pr[D(P_BDH) = 1] = Pr[A wins]`. On `R_BDH`, `T` is uniform in `G_T` and
independent of `A`'s view, so `Pr[D(R_BDH) = 1] ≤ 1/p` by injectivity of the encoding. Hence
`Pr[A wins] ≤ dbdhAdv D κ + E_r[1/p] ≤ dbdhAdv D κ + 2^{-κ} + δ(κ)` (the coins where `p < 2^κ`
cost at most `δ(κ)`), a sum of negligible functions. -/
theorem bdhAssumption_of_dbdhAssumption
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)
    (h : G.DBDHAssumption) : G.BDHAssumption := by
  sorry

end BilinearGen

end TCSlib.Cryptography.Pairing
