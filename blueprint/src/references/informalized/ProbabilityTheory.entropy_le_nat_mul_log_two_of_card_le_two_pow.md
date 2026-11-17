<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.entropy_le_nat_mul_log_two_of_card_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entropy bound from the range size

**Claim.** If a finite-valued random variable has at most $2^c$ possible values, then its entropy is at most $c\log 2$.

**Proof.** The entropy bound by the logarithm of the number of possible values gives $H[X;\mu]\leq \log N$ whenever the range has at most $N$ elements (`ProbabilityTheory.entropy_le_log_of_card_le`). Take $N=2^c$ using the assumed cardinality bound. Since $\log(2^c)=c\log 2$, this yields the stated inequality.

**Key facts.** `ProbabilityTheory.entropy_le_log_of_card_le`.
