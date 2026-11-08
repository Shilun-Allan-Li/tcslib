<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Nondeterministic Choice

**Claim.** If the instruction at $l$ chooses between $l_1$ and $l_0$, the current configuration satisfies $G$, and the two successors satisfy the semantics for $P_1$ and $P_0$, respectively, then the current configuration satisfies the semantics for $P_1\lor P_0$.

**Proof.** The termination component follows by applying the step rule for termination: the current configuration satisfies $G$, and each of its two possible successors terminates by the corresponding hypothesis. For acceptance, acceptance from a live configuration is equivalent to acceptance from at least one of its choice successors (`nacc_live`). The choice instruction sends the true bit to $l_1$ and the false bit to $l_0$ (`nastep_choose`). Thus acceptance at the current configuration implies acceptance at one of those successors, which by the respective semantic equivalence gives $P_1$ or $P_0$. Conversely, if $P_1$ holds, the first successor's semantics gives an accepting run from $l_1$, and choosing true supplies an accepting run from the current configuration; if $P_0$ holds, choose false and use the corresponding run from $l_0$. This proves the acceptance equivalence with $P_1\lor P_0$.

**Key facts.** `Complexity.LogProg.nastep_choose`, `Complexity.LogProg.nacc_live`.
