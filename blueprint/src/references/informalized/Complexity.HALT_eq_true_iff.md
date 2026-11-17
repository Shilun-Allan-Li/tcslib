<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Uncomputability/Halting.lean :: Complexity.HALT_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of the Halting Function

**Claim.** The halting function returns true on $s$ exactly when $s$ is a pairing encoding of two bit strings $\alpha,x$ and the machine decoded from $\alpha$ produces some output on input $x$ within finitely many steps.

**Proof.** Unfold the definition of the halting function. It is a Boolean conditional whose test is exactly the existential statement in the theorem. If that test holds, the function returns true and the existential statement follows. If it fails, the function returns false, and the existential statement is false. This proves both directions.
