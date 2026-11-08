<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.SAT_mem_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# SAT belongs to NP

**Claim.** SAT belongs to NP: membership is certified by a polynomial-time verifier using a witness of the prescribed polynomial length.

**Proof.** Choose certificate-length constants $C=c=1$ and the verifier `satVerifier false`. Its verdict is polynomial-time computable (`satVerdict_false_poly`), and hence the verifier itself defines a language in P (`satVerifier_of_poly`). For each input $x$, `sat_verifier_equiv` states that $x$ belongs to SAT exactly when there is a witness $u$ of length $|x|+1$ for which $xu$ is accepted by this verifier. This length is $1\cdot(|x|+1)^1$, as required by the NP definition.

**Key facts.** `Complexity.satVerdict_false_poly`, `Complexity.satVerifier_of_poly`, `Complexity.sat_verifier_equiv`.
