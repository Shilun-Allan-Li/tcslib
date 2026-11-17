<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.seedAcceptanceCNF_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed acceptance formula width bound

**Claim.** For a Boolean PCPP system with $r$ verifier queries and any seed $s$, the CNF formula encoding acceptance for $s$ has width at most $r$.

**Proof.** The seed acceptance formula is the truth-table CNF of the local acceptance predicate on $r$ sign coordinates. Every clause in a truth-table CNF has width $r$, and consequently its maximum clause width is at most $r$ (`FABL.truthTableCNF_width_le`). Applying this bound to the local acceptance predicate gives the claim.

**Key facts.** `FABL.truthTableCNF_width_le`.
