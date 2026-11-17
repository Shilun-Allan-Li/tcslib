<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.prefixFrequency_succ_mem_goldreichLevinCandidates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor prefix candidate

**Claim.** If the prefix of $U$ through indices below $k$ is active and $k<n$, then the prefix through indices below $k+1$ is a candidate child of an active set at index $k$.

**Proof.** The prefix through indices below $k+1$ is obtained from the prefix through indices below $k$ by adding coordinate $k$ if it belongs to $U`, and otherwise leaving the prefix unchanged (`prefixFrequency_succ`). In the first case it is the active prefix with coordinate $k$ inserted; in the second it is the active prefix itself. The candidate characterization says that a candidate is either an active set or that set with coordinate $k$ inserted (`mem_goldreichLevinCandidates_iff`). Since the original prefix is active, either case gives the required membership.

**Key facts.** `FABL.prefixFrequency_succ`, `FABL.mem_goldreichLevinCandidates_iff`.
