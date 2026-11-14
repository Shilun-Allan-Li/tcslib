/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Drawing one-query oracle randomness in advance

## Main definitions

This module introduces no definitions.

## Main results

* `HashSignFill.expect_simulate_sample_once`: for a computation making at most one query,
  freshly sampling the oracle's answer tape has the same law, including its query log, as
  drawing that tape before the computation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 144.1 (technical support for the collision-finding reduction).
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open TCSlib.Cryptography.Games

/-- For a computation making at most one query, sampling an independent tape for every
oracle answer is equivalent to sampling one tape before the computation, for every real
payoff of the returned value and full query log.

**Proof sketch.** A computation of unit cost at most one either returns immediately or
asks a fixed query and returns a function of its answer (`one_query_cases`). In the first
case the extra sample integrates a constant. In the second case both expectations reduce
to the same expectation over the single answer tape, with the same one-entry log. -/
theorem expect_simulate_sample_once {ι α R : Type} {spec : OracleSpec ι}
    [Fintype R] [Nonempty R] (ans : ∀ i, spec.dom i → R → spec.rng i)
    (c : OracleComp spec α) (hc : c.CostBoundedBy (fun _ => 1) 1)
    (g : α × (Unit × QueryLog spec) → ℝ) :
    ProbComp.expect
        (simulate
          (QueryImpl.ofComp (σ := Unit) (fun i x =>
            (ProbComp.sample R).bind fun r => .pure (ans i x r))).withLog c ((), [])) g =
      ProbComp.expect (ProbComp.sample R) (fun r =>
        ProbComp.expect
          (simulate
            (QueryImpl.withLog (fun (i : ι) (x : spec.dom i) (_ : Unit) =>
              (OracleComp.pure (ans i x r, ()) : ProbComp (spec.rng i × Unit))))
            c ((), [])) g) := by
  rcases one_query_cases c hc with ⟨a, rfl⟩ | ⟨i, x, f, rfl⟩
  · simp only [simulate_pure, ProbComp.expect_pure]
    exact (ProbComp.expect_const _ _).symm
  · simp only [simulate_query, QueryImpl.withLog_apply, QueryImpl.ofComp_apply,
      ProbComp.expect_bind, ProbComp.expect_pure, simulate_pure]

end TCSlib.Cryptography.Authentication.HashSignFill
