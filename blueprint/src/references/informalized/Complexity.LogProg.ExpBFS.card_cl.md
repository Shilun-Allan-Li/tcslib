<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.card_cl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Reachability Count Equality

**Claim.** Under the stated bound on $K$, the number of values below $K$ satisfying the oracle-based bounded reachability predicate equals the number of configuration codes in the prescribed finite range reachable from the initial configuration code.

**Proof.** The proof first uses the configuration-code counting result (\texttt{Complexity.ExpBFS.card_filter_rcode}) to replace the count of reachable configuration codes in their natural range by the cardinality of the set of all numbers below $K$ satisfying the machine-code reachability relation. It then applies the pointwise equivalence between oracle-based reachability and machine-code reachability (\texttt{Complexity.LogProg.ExpBFS.cl_iff}) to the elements of the range $[0,K)$. Equivalent predicates select the same elements of that finite range, so their filtered sets—and hence their cardinalities—are equal.

**Key facts.** `Complexity.ExpBFS.card_filter_rcode`, `Complexity.LogProg.ExpBFS.cl_iff`.
