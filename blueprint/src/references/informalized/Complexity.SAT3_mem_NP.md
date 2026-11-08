<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.SAT3_mem_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-SAT belongs to NP

**Claim.** Serialized three-SAT belongs to NP: membership is certified by a polynomial-time verifier using a witness of the prescribed polynomial length.

**Proof.** Choose certificate-length constants $C=c=1$ and let the verifier be the three-SAT verifier `satVerifier true`. The verifier is polynomial-time because deciding its verdict is polynomial-time (`satVerdict_true_poly` and `satVerifier_of_poly`). For each input $x$, the equivalence `sat3_verifier_equiv` says that $x$ belongs to three-SAT exactly when there is a witness $u$ of length $|x|+1$ such that $xu$ is accepted by this verifier. Since $1\cdot(|x|+1)^1=|x|+1$, this is precisely the required NP certificate characterization.

**Key facts.** `Complexity.satVerdict_true_poly`, `Complexity.satVerifier_of_poly`, `Complexity.sat3_verifier_equiv`.
