<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Primality.lean :: Randomized.inCoRP_PRIMESBin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primality Testing in coRP

**Claim.** The binary language of prime numbers belongs to coRP in the polynomial-time verifier model.

**Proof.** Use the composite-number verifier with six times the input-length-plus-one random bits, and use the supplied efficiency result for this verifier. Since coRP membership is RP membership for the complement, consider separately inputs encoding a nonprime and a prime. If the encoded number is less than $2$ or even, the verifier declares compositeness deterministically; the only prime exception in this case is $2$, which is excluded by nonprimality. Otherwise the encoded number is odd and at least $3$. The bit-length bound on its value ensures that the verifier's random tape contains enough bits for the prescribed liar-round experiment. The verifier's acceptance probability is then one minus the probability that all those rounds report a liar: this follows by identifying the longer random tape with its needed prefix and taking the complement event. The bound on the probability of passing the Euler-liar rounds for an odd composite makes the verifier declare compositeness with probability at least $2/3$. For a prime input, the value is at least $2$; the case $2$ is handled directly, and for any other prime it is odd. The prime-round theorem says every round passes, so the verifier always declares prime and never declares compositeness. This gives the required one-sided guarantee for the complement of the primes.

**Key facts.** `Randomized.eff_compositeVerifier`, `Complexity.LogProg.bitsVal_lt_two_pow`, `Randomized.randProb_take`, `Randomized.randProb_not`, `Randomized.eulerLiarRounds_two_take`, `Randomized.randProb_eulerLiarRounds_two_le`, `Randomized.eulerLiarRounds_of_prime`, `Randomized.randProb_congr`, `Randomized.randProb_true`.
