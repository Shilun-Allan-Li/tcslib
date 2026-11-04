/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bridge: the concrete layer's experiments are games

The concrete security layer of the ch. 2–4 development measures its experiments with `uprob`,
the probability that a uniformly random element of a finite type satisfies an event. Its four
experiments are inversion (`invProb`), prediction (`predProb`), acceptance (`acceptProb`) and
distinguishing (`distAdv`). This file shows that each is the probability of a one-line game of the
`Games` framework: sample the seed and the adversary's coins, run the adversary, test. So every
concrete-layer result stated through these quantities transfers to the framework unchanged.

The basic fact is `prob_sample_eq_uprob`: sampling a finite type and testing an event has
probability `uprob` of the event. It reads `uprob` only through its published equation
`uprob_eq_card_filter`. Sampling a pair one component at a time is sampling the product
(`prob_sample_pair`), so the games may sample the seed and the coins in sequence.

**Disclosure.** The four experiments are one-line definitions of `uprob` with no published
equation in `Foundations/Experiments.lean`. Their bridges read the definitions' bodies (`rfl` and
`unfold`); a request to publish equations is recorded (coordination point F-3).

## Main results

* `Games.Bridge.prob_sample_eq_uprob`: `Pr[x ← $ α : p x] = uprob p`.
* `Games.Bridge.prob_sample_pair`: sampling `α` then `β` is sampling `α × β`.
* `Games.Bridge.invProb_eq`, `predProb_eq`, `acceptProb_eq`, `distAdv_eq`: the four concrete
  experiments as games.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the experiments).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games.Bridge

open Finset ProbComp

variable {α β ρ σ τ γ : Type}

/-- **Sampling and `uprob` agree:** the probability that a uniform sample of the nonempty finite
type `α` satisfies `p` is `uprob p`.

**Proof sketch.** Both are the number of elements satisfying `p` divided by `|α|`: the sample's
probability is the uniform average of the indicator (`expect_sample`), and `uprob` is the
filter's cardinality over `|α|` (`uprob_eq_card_filter`). -/
theorem prob_sample_eq_uprob [Fintype α] [Nonempty α] (p : α → Prop) :
    prob (sample α) p = uprob p := by
  classical
  rw [prob_eq_expect, expect_sample, uprob_eq_card_filter, sum_boole, inv_mul_eq_div]

/-- **Sampling a pair in sequence is sampling the product:** for every function `g` on pairs,
its expectation over `a ← $ α; b ← $ β; (a, b)` equals its expectation over a uniform pair. -/
theorem expect_sample_pair [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (g : α × β → ℝ) :
    expect ((sample α).bind fun a => (sample β).bind fun b => .pure (a, b)) g =
      expect (sample (α × β)) g := by
  rw [expect_bind, expect_sample, expect_sample, Fintype.card_prod, Fintype.sum_prod_type]
  simp only [expect_bind, expect_sample, expect_pure, Nat.cast_mul, mul_inv, mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  ring

/-- Sampling a pair in sequence is sampling the product, for probabilities. -/
theorem prob_sample_pair [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (p : α × β → Prop) :
    prob ((sample α).bind fun a => (sample β).bind fun b => .pure (a, b)) p =
      prob (sample (α × β)) p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, expect_sample_pair]

/-- **Inversion as a game:** `invProb f A` is the probability that the game "sample `x` and the
adversary's coins `r`; win if `A (f x) r` is a preimage of `f x`" is won. [Gar26, Def 2.1] -/
theorem invProb_eq [Fintype α] [Nonempty α] [Fintype ρ] [Nonempty ρ] (f : α → β)
    (A : β → ρ → α) :
    invProb f A =
      prob ((sample α).bind fun x => (sample ρ).bind fun r => .pure (x, r))
        (fun z => f (A (f z.1) z.2) = f z.1) := by
  rw [prob_sample_pair, prob_sample_eq_uprob]
  rfl

/-- **Prediction as a game:** `predProb f B A` is the probability that `A`, given `f x` and its
coins, outputs `B x`. [Gar26, Def 2.3] -/
theorem predProb_eq [Fintype α] [Nonempty α] [Fintype ρ] [Nonempty ρ] (f : α → β)
    (B : α → Bool) (A : β → ρ → Bool) :
    predProb f B A =
      prob ((sample α).bind fun x => (sample ρ).bind fun r => .pure (x, r))
        (fun z => A (f z.1) z.2 = B z.1) := by
  rw [prob_sample_pair, prob_sample_eq_uprob]
  rfl

/-- The acceptance game of a sampler `X` and a distinguisher `D`: sample the seed and the coins,
and output `D`'s verdict on the sample. -/
noncomputable def acceptGame [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
    (D : γ → ρ → Bool) : ProbComp Bool :=
  (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r)

/-- **Acceptance as a game:** `acceptProb X D` is the acceptance probability of `acceptGame X D`.
[Gar26, Defs 3.2 and 3.4] -/
theorem acceptProb_eq [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
    (D : γ → ρ → Bool) : acceptProb X D = accept (acceptGame X D) := by
  have h : acceptGame X D =
      (fun z : σ × ρ => D (X z.1) z.2) <$>
        ((sample σ).bind fun s => (sample ρ).bind fun r => .pure (s, r)) := by
    simp only [acceptGame, OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [accept, h, prob_eq_expect, expect_map, ← prob_eq_expect (p := fun z : σ × ρ =>
    D (X z.1) z.2 = true), prob_sample_pair, prob_sample_eq_uprob]
  rfl

/-- **Distinguishing as a game:** `distAdv X Y D` is the advantage between the acceptance games
of `X` and of `Y`. [Gar26, Defs 3.2 and 3.4] -/
theorem distAdv_eq [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ] [Fintype ρ] [Nonempty ρ]
    (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D = advantage (acceptGame X D) (acceptGame Y D) := by
  unfold distAdv advantage
  rw [acceptProb_eq, acceptProb_eq]

end TCSlib.Cryptography.Games.Bridge
