<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.factorial_isEquivalent_factorialStirlingApprox -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stirling Asymptotic Formula

**Claim.** As $n$ tends to infinity through the natural numbers, $n!$ is asymptotic to $\sqrt{2n\pi}(n/e)^n$, equivalently their ratio tends to $1$.

**Proof.** Rewrite the defined approximation as $\sqrt{2n\pi}(n/e)^n$. Stirling's factorial asymptotic states that $n!$ is asymptotic to precisely this expression; applying that theorem gives the result.
