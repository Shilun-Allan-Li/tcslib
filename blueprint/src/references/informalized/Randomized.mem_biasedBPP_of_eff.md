<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.mem_biasedBPP_of_eff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Biased BPP from an Efficient Verifier

**Claim.** If an efficient Boolean verifier has $\rho-biased acceptance weight at least $2/3$ for the membership indicator on every input, then its language belongs to biased polynomial-time BPP.

**Proof.** From verifier efficiency, the machine construction theorem (`exists_FinNDTM_biased_of_eff`) provides a finite nondeterministic machine and polynomial time bound. For every input, the machine halts within that bound, and its probability of outputting either Boolean value under the biased choice distribution equals the verifier's biased probability of producing that value. In particular, its probability of outputting the membership indicator is at least $2/3$ by the hypothesis. The machine and time bound therefore witness membership in biased BPP.

**Key facts.** `Randomized.exists_FinNDTM_biased_of_eff`.

**Caveat.** The payload's informal statement corrupts the parameter as `$
ho$`; the proof itself only transfers the success inequality for the given parameter $\rho$.
