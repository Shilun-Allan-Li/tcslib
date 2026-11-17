<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.seedAcceptanceCNF_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed acceptance formula size bound

**Claim.** For a Boolean PCPP system with $r$ verifier queries and any seed $s$, the CNF formula encoding acceptance for $s$ has size at most $2^r$.

**Proof.** The seed acceptance formula is the truth-table CNF associated with the seed's local acceptance predicate. The truth-table CNF size bound says that the formula associated with any predicate on $r$ Boolean coordinates has size at most $2^r$ (`FABL.truthTableCNF_size_le`). Apply it to this local acceptance predicate.

**Key facts.** `FABL.truthTableCNF_size_le`.
