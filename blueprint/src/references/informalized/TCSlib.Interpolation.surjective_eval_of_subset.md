<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Interpolation.lean :: TCSlib.Interpolation.surjective_eval_of_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpolation on a Subset

**Claim.** If $v$ is injective on a finite set $s$ and $t\subseteq s$, then any prescribed values on the nodes indexed by $t$ are attained by some polynomial of degree less than $|s|$.

**Proof.** Use the fixed evaluation equivalence between polynomials of degree less than $|s|$ and their values at the nodes indexed by $s$, with the values on $t$ fixed to the prescribed function and, for example, zero values on the remaining indices. The inverse equivalence supplies such a polynomial. Its membership in the degree-bounded polynomial space gives degree less than $|s|$, and the defining evaluation property gives the required values on $t$.
