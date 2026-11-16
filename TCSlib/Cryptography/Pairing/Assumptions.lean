/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.OneWayFunctions.Basic

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
difference of acceptance probabilities; the paper writes the absolute difference of the
probabilities of output `0` [BB04, §3.1], which is the same number, since outputs `0` and `1` are
complementary. The adversary receives the group's description `d` and `1^κ`.

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

/-! ### The Decision BDH distinguisher of a BDH solver

The machine behind `BilinearGen.bdhAssumption_of_dbdhAssumption`: on a Decision BDH string it
re-pairs the first five components into a BDH string, runs the solver on it and compares the
answer with the last component. These helpers are internal to that proof. -/

/-- The BDH part of a Decision BDH string, by the pair projections:
`⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩ ↦ ⟨d, ⟨g, ⟨X, ⟨Y, Z⟩⟩⟩⟩` (every string is mapped to some string). -/
private def tupleBdh (w : List Bool) : List Bool :=
  pairEncode (pairFstD w) (pairEncode (pairFstD (pairSndD w))
    (pairEncode (pairFstD (pairSndD (pairSndD w)))
      (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD w))))
        (pairFstD (pairSndD (pairSndD (pairSndD (pairSndD w))))))))

/-- The last component of a Decision BDH string: `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩ ↦ T`, the fifth
iterate of the second projection. -/
private def tupleTgt (w : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (pairSndD (pairSndD w))))

/-- The BDH part of a Decision BDH string is the BDH string of its first five components:
`tupleBdh (tupleStr B d g x y z t) = bdhStr B d g x y z`. -/
private theorem tupleBdh_tupleStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool)
    (g x y z : B.G) (t : B.GT) : tupleBdh (tupleStr B d g x y z t) = bdhStr B d g x y z := by
  rw [tupleStr_eq, bdhStr_eq, tupleBdh]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- The last component of a Decision BDH string is the encoding of its target element:
`tupleTgt (tupleStr B d g x y z t) = List.ofFn (B.encT t)`. -/
private theorem tupleTgt_tupleStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool)
    (g x y z : B.G) (t : B.GT) : tupleTgt (tupleStr B d g x y z t) = List.ofFn (B.encT t) := by
  rw [tupleStr_eq, tupleTgt]
  simp only [pairSndD_pairEncode]

/-- The re-pairing `tupleBdh` is polynomial-time (pair projections and `pairEncode`). -/
private theorem polyTimeComputable_tupleBdh : PolyTimeComputable tupleBdh := by
  have s₁ := polyTimeComputable_pairSndD
  have s₂ := s₁.comp' s₁
  have s₃ := s₁.comp' s₂
  have s₄ := s₁.comp' s₃
  have f := polyTimeComputable_pairFstD
  unfold tupleBdh
  exact f.pairEncode ((f.comp' s₁).pairEncode ((f.comp' s₂).pairEncode
    ((f.comp' s₃).pairEncode (f.comp' s₄))))

/-- The projection `tupleTgt` is polynomial-time (five second projections). -/
private theorem polyTimeComputable_tupleTgt : PolyTimeComputable tupleTgt := by
  have s := polyTimeComputable_pairSndD
  unfold tupleTgt
  exact s.comp' (s.comp' (s.comp' (s.comp' s)))

/-- **The Decision BDH distinguisher of a BDH solver** (the machine of
`BilinearGen.bdhAssumption_of_dbdhAssumption`): for every `NUPPT` `A` there is an `NUPPT` `D`
with `A`'s coins that, at parameter `κ` on a string `w` with coins `r`, runs `A` on the BDH part
of `w` with the same coins and outputs `[true]` iff the answer is the last component of `w`:
`D(1^κ, w; r) = [A(1^κ, tupleBdh w; r) = tupleTgt w]`.

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^κ, w⟩, α⟩, r⟩` runs `A.output` on
`⟨⟨⟨1^κ, tupleBdh w⟩, α⟩, r⟩` and compares the answer with `tupleTgt w`; it is polynomial-time by
`polyTimeComputable_layout`, the layout projections and `polyTimeComputable_pairEq`.
`D := NUPPT.ofPolyTime` of it with `A`'s coins and advice, and the identity is
`runAtL_ofPolyTime`, `runAtL_eq_output_layout` and the projection identities of the layout. -/
private theorem exists_bdhDistinguisher (A : NUPPT) :
    ∃ D : NUPPT, D.coins = A.coins ∧ ∀ (κ : ℕ) (w r : List Bool),
      D.runAtL κ w r = [decide (A.runAtL κ (tupleBdh w) r = tupleTgt w)] := by
  have ha := A.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam
    (polyTimeComputable_tupleBdh.comp' NUPPT.polyTimeComputable_inArg)
    NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)
  have ht := polyTimeComputable_tupleTgt.comp' NUPPT.polyTimeComputable_inArg
  have hF : PolyTimeComputable fun z => [decide (A.output (NUPPT.layout (NUPPT.inParam z)
      (tupleBdh (NUPPT.inArg z)) (NUPPT.inAdvice z) (NUPPT.inCoins z)) =
        tupleTgt (NUPPT.inArg z))] :=
    (polyTimeComputable_pairEq.comp' (ha.pairEncode ht)).congr fun z => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨NUPPT.ofPolyTime hF A.coins A.adv A.advice A.advice_length,
    NUPPT.coins_ofPolyTime _ _ _ _ _, fun κ w r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime, NUPPT.runAtL_eq_output_layout, NUPPT.advInput_eq,
    ← NUPPT.layout_eq]
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.inCoins_layout]

/-- The verdict of the distinguisher of `exists_bdhDistinguisher` on a Decision BDH string is the
BDH test of `A` with the same coins: `D(1^κ, tupleStr B d g x y z t; ρ) = 1` iff
`A(1^κ, bdhStr B d g x y z; ρ)` is the encoding of `t` (coins carried over by `coinsCongr`). -/
private theorem distinguisherL_tupleStr {A D : NUPPT} (hc : D.coins = A.coins)
    (hD : ∀ (κ : ℕ) (w r : List Bool),
      D.runAtL κ w r = [decide (A.runAtL κ (tupleBdh w) r = tupleTgt w)])
    (κ : ℕ) {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) (t : B.GT)
    (ρ : D.Coins κ) :
    D.distinguisherL κ (tupleStr B d g x y z t) ρ =
      decide (A.runAt κ (bdhStr B d g x y z) (NUPPT.coinsCongr hc κ ρ) =
        List.ofFn (B.encT t)) := by
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hD, NUPPT.runAt_coinsCongr, tupleBdh_tupleStr,
    tupleTgt_tupleStr]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]

/-- A fixed string is the encoding of a uniform element of `G_T` with probability at most `1/p`:
`Pr_{t ← G_T}[w = enc(t)] ≤ 1/p`, since `encT` is injective, so at most one `t` qualifies. -/
private theorem prob_eq_encT_le {wG wT : ℕ} (B : BilinearGroup wG wT) (w : List Bool) :
    ProbComp.prob (ProbComp.sample B.GT) (fun t => w = List.ofFn (B.encT t)) ≤
      (B.order : ℝ)⁻¹ := by
  rw [Bridge.prob_sample_eq_uprob]
  by_cases hw : ∃ t₀, w = List.ofFn (B.encT t₀)
  · obtain ⟨t₀, rfl⟩ := hw
    rw [OneWay.uprob_congr (q := fun t => t = t₀) fun t =>
        ⟨fun h => (B.encT_injective (List.ofFn_injective h)).symm, fun h => by rw [h]⟩,
      OneWay.uprob_eq_one_div_card, B.card_GT, one_div]
  · rw [OneWay.uprob_congr (q := fun _ => False) fun t => ⟨fun h => hw ⟨t, h⟩, False.elim⟩,
      uprob_false]
    positivity

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

/-- **The reduction's bound** behind `bdhAssumption_of_dbdhAssumption`: if `D` is the
distinguisher of the BDH solver `A` (`exists_bdhDistinguisher`) and the order is at least `2^κ`
except with probability `δ(κ)`, then `Pr[A wins the BDH game] ≤ dbdhAdv D κ + 2^{-κ} + δ(κ)`.

**Proof sketch.** On `P_BDH` the target is `e(g, g)^{abc}`, the sample of `T` is unused, and `D`
accepts exactly when `A`, run with the same coins (`coinsCongr`), outputs its encoding; so
`Pr[D(P_BDH) = 1] = Pr[A wins]` (`distinguisherL_tupleStr`, `expect_const`,
`expect_sample_equiv`). On `R_BDH`, exchange the samples of `T` and of the coins
(`expect_sample_comm`): for fixed coins, `A`'s answer is a fixed string, which is the encoding of
the uniform `T` with probability at most `1/p` (`prob_eq_encT_le`); so `Pr[D(R_BDH) = 1]` is at
most `E_r[1/p]`. Pointwise `1/p ≤ 2^{-κ} + [p < 2^κ]`, and the probability of `p < 2^κ` over the
generator's coins is at most `δ(κ)`. Finally
`Pr[D(P_BDH) = 1] ≤ Pr[D(R_BDH) = 1] + dbdhAdv D κ`. -/
private theorem accept_bdhGame_le {A D : NUPPT} (hc : D.coins = A.coins)
    (hD : ∀ (κ : ℕ) (w r : List Bool),
      D.runAtL κ w r = [decide (A.runAtL κ (tupleBdh w) r = tupleTgt w)])
    {δ : ℕ → ℝ} (hN : G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ) (κ : ℕ) :
    accept (G.bdhGame A κ) ≤ G.dbdhAdv D κ + ((2 : ℝ)⁻¹ ^ κ + δ κ) := by
  -- `P_BDH`: `D` accepts exactly when `A` wins.
  have hreal : accept (G.dbdhGame D true κ) = accept (G.bdhGame A κ) := by
    rw [accept_eq, accept_eq, dbdhGame_eq, bdhGame_eq]
    simp only [ProbComp.prob_bind, ProbComp.prob_pure, distinguisherL_tupleStr hc hD,
      ↓reduceIte, decide_eq_true_eq, ProbComp.expect_const]
    refine congrArg (ProbComp.expect _) (funext fun r => ?_)
    refine congrArg (ProbComp.expect _) (funext fun g => ?_)
    refine congrArg (ProbComp.expect _) (funext fun abc => ?_)
    rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr hc κ)]
  -- `R_BDH`: for fixed coins the answer hits the uniform target with probability `≤ 1/p`.
  have hpt : ∀ (r : G.gen.Coins κ) (w : List Bool),
      ProbComp.expect (ProbComp.sample (G.inst κ r).GT)
        (fun t => if w = List.ofFn ((G.inst κ r).encT t) then (1 : ℝ) else 0) ≤
          ((G.inst κ r).order : ℝ)⁻¹ := fun r w => by
    have h := prob_eq_encT_le (G.inst κ r) w
    rwa [ProbComp.prob_eq_expect] at h
  have hrand : accept (G.dbdhGame D false κ) ≤
      ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
        (fun r => ((G.inst κ r).order : ℝ)⁻¹) := by
    rw [accept_eq, dbdhGame_eq]
    simp only [ProbComp.prob_bind, ProbComp.prob_pure, distinguisherL_tupleStr hc hD,
      Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    refine ProbComp.expect_mono _ fun r => ?_
    have hin : ∀ (g : {x : (G.inst κ r).G // x ≠ 1})
        (abc : ZMod (G.inst κ r).order × ZMod (G.inst κ r).order × ZMod (G.inst κ r).order),
        ProbComp.expect (ProbComp.sample (G.inst κ r).GT) (fun t =>
          ProbComp.expect (ProbComp.sample (D.Coins κ)) (fun ρ =>
            if A.runAt κ (bdhStr (G.inst κ r) (G.desc κ r) g.1 (g.1 ^ abc.1.val)
                (g.1 ^ abc.2.1.val) (g.1 ^ abc.2.2.val)) (NUPPT.coinsCongr hc κ ρ) =
              List.ofFn ((G.inst κ r).encT t) then (1 : ℝ) else 0)) ≤
          ((G.inst κ r).order : ℝ)⁻¹ := fun g abc => by
      rw [ProbComp.expect_sample_comm]
      calc _ ≤ ProbComp.expect (ProbComp.sample (D.Coins κ))
              (fun _ => ((G.inst κ r).order : ℝ)⁻¹) :=
            ProbComp.expect_mono _ fun ρ => hpt r _
        _ = _ := ProbComp.expect_const _ _
    calc _ ≤ ProbComp.expect (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}) (fun _ =>
            ProbComp.expect (ProbComp.sample (ZMod (G.inst κ r).order ×
              ZMod (G.inst κ r).order × ZMod (G.inst κ r).order))
                (fun _ => ((G.inst κ r).order : ℝ)⁻¹)) :=
          ProbComp.expect_mono _ fun g => ProbComp.expect_mono _ fun abc => hin g abc
      _ = _ := by rw [ProbComp.expect_const, ProbComp.expect_const]
  -- The order: `1/p ≤ 2^{-κ} + [p < 2^κ]`, and `Pr_r[p < 2^κ] ≤ δ(κ)`.
  have hord : ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
      (fun r => ((G.inst κ r).order : ℝ)⁻¹) ≤ (2 : ℝ)⁻¹ ^ κ + δ κ := by
    have hu : uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ κ) ≤ δ κ :=
      (G.orderAtLeastExcept_iff _ δ).1 hN κ
    rw [← Bridge.prob_sample_eq_uprob, ProbComp.prob_eq_expect] at hu
    have hp : ∀ r : G.gen.Coins κ, ((G.inst κ r).order : ℝ)⁻¹ ≤
        (2 : ℝ)⁻¹ ^ κ + if (G.inst κ r).order < 2 ^ κ then 1 else 0 := fun r => by
      have h2 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ κ := by positivity
      split_ifs with hlt
      · have h1 : (1 : ℝ) ≤ (G.inst κ r).order := by
          exact_mod_cast (G.inst κ r).order_prime.one_lt.le
        linarith [inv_le_one_of_one_le₀ h1]
      · have hle : (2 : ℝ) ^ κ ≤ (G.inst κ r).order := by exact_mod_cast not_lt.1 hlt
        rw [add_zero, inv_pow]
        exact inv_anti₀ (by positivity) hle
    calc _ ≤ ProbComp.expect (ProbComp.sample (G.gen.Coins κ)) (fun r =>
          (2 : ℝ)⁻¹ ^ κ + if (G.inst κ r).order < 2 ^ κ then 1 else 0) :=
          ProbComp.expect_mono _ hp
      _ = (2 : ℝ)⁻¹ ^ κ + ProbComp.expect (ProbComp.sample (G.gen.Coins κ)) (fun r =>
          if (G.inst κ r).order < 2 ^ κ then (1 : ℝ) else 0) := by
          rw [ProbComp.expect_add, ProbComp.expect_const]
      _ ≤ _ := by linarith
  -- The advantage bounds the gap between the two experiments.
  have hadv := G.dbdhAdv_eq D κ
  rw [advantage_eq] at hadv
  have hsym := abs_sub_comm (accept (G.dbdhGame D false κ)) (accept (G.dbdhGame D true κ))
  have hle := le_abs_self (accept (G.dbdhGame D true κ) - accept (G.dbdhGame D false κ))
  linarith

/-- **Decision BDH implies BDH** when the group order is at least `2^κ` except with negligible
probability: a BDH solver `A` gives the Decision BDH distinguisher "run `A` on `(g, g^a, g^b, g^c)`
and accept iff its answer is `T`".

**Source:** not stated in [BB04] or [Jou00], which define the two problems ([BB04, §3.1]). The
implication is independently derived here: the folklore fact that deciding is no harder than
computing.

**Proof sketch.** Given `A`, let `D` be the machine with `A`'s coins that, on `1^κ` and a string
`w`, re-pairs the first five components of `w` into a BDH string `s` by the pair projections,
runs `A(1^κ, s)` with its own coins and outputs `1` iff the answer equals the last component of
`w` (a string-equality test). Its raw function is polynomial-time, so `D` is a non-uniform PPT
(`exists_bdhDistinguisher`). On a Decision BDH string `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩`, `s` is the
BDH string `⟨d, ⟨g, ⟨X, ⟨Y, Z⟩⟩⟩⟩` and the last component is the encoding of `T`. On `P_BDH`
(`T = e(g, g)^{abc}`, the sample of `T` unused), `D` accepts exactly when `A` wins, so
`Pr[D(P_BDH) = 1] = Pr[A wins]`. On `R_BDH`, exchange the sample of `T` with that of the coins:
for fixed coins `A`'s answer is a fixed string, which is the encoding of the uniform `T ∈ G_T`
with probability at most `1/p` (the encoding is injective). So `Pr[D(R_BDH) = 1] ≤ E_r[1/p]`,
and `1/p ≤ 2^{-κ} + [p < 2^κ]` pointwise, where `p < 2^κ` has probability at most `δ(κ)` over the
generator's coins. Hence `Pr[A wins] ≤ dbdhAdv D κ + 2^{-κ} + δ(κ)` (`accept_bdhGame_le`), a sum
of negligible functions (`h`, `negligible_two_pow_neg`, the hypothesis on `δ`). Neither the group
operations nor decoding are needed (`Ops` is not assumed). -/
theorem bdhAssumption_of_dbdhAssumption
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)
    (h : G.DBDHAssumption) : G.BDHAssumption := by
  obtain ⟨δ, hδ, hN⟩ := hN
  rw [bdhAssumption_iff]
  intro A
  obtain ⟨D, hc, hD⟩ := exists_bdhDistinguisher A
  refine ((G.dbdhAssumption_iff.1 h D).add (negligible_two_pow_neg.add hδ)).mono
    ⟨0, fun κ _ => ?_⟩
  rw [abs_of_nonneg (accept_nonneg _)]
  exact (G.accept_bdhGame_le hc hD hN κ).trans (le_abs_self _)

end BilinearGen

end TCSlib.Cryptography.Pairing
