<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.EncodedMaximizationProblem.gapPromiseReal_reducible_of_thresholds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Gap Promises

**Claim.** When the weaker soundness threshold is at least the original soundness threshold and the weaker completeness threshold is at most the original completeness threshold, the original gap promise reduces to the weaker one.

**Proof.** Use the identity map on inputs, which is polynomial-time. An original yes input is valid and has optimum at least the original completeness threshold; because the weaker completeness threshold is no larger, it is also a yes input for the weaker promise. An original no input is valid and has optimum at most the original soundness threshold; because the weaker soundness threshold is no smaller, it is also a no input for the weaker promise. Thus the identity map preserves both promised cases.
