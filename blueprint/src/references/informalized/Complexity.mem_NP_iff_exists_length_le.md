<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.mem_NP_iff_exists_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Certificates of Bounded Length

**Claim.** A language is in $\mathsf{NP}$ exactly when membership can be witnessed by a polynomially bounded binary string accepted by a polynomial-time verifier on the encoded pair.

**Proof.** For the forward direction, take an NP verifier whose certificates have the fixed length $C(|x|+1)^c$. Use the paired verifier that parses the encoded pair, checks that the certificate has this required length, and then runs the original verifier on the decoded input and certificate. It remains polynomial-time (`Complexity.pairedVerifier_mem_P`). By the paired-verifier characterization (`Complexity.pairedVerifier_pair`), a certificate of the required length is accepted exactly when the original verifier accepts it. Its fixed length is in particular at most the same polynomial bound, giving the claimed bounded-length witness description.

Conversely, suppose witnesses of length at most $C(|x|+1)^c$ are accepted by a polynomial-time verifier on encoded pairs. Pad a witness to the fixed length $(C+1)(|x|+1)^c$. The padded verifier searches a bounded range of possible original witness lengths, strips the padding, checks the original length bound, forms the encoded pair, and runs the given verifier. This is polynomial-time (`Complexity.paddedVerifier_mem_P`). The padded-witness equivalence (`Complexity.paddedVerifier_witness`) says that a fixed-length witness is accepted by this verifier exactly when some original witness within the bound is accepted. Applying these equivalences to each input proves both directions.

**Key facts.** `Complexity.pairedVerifier_mem_P`, `Complexity.pairedVerifier_pair`, `Complexity.paddedVerifier_mem_P`, `Complexity.paddedVerifier_witness`.
