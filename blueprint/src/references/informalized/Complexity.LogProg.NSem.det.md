<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Across a Deterministic Instruction

**Claim.** If the instruction at a live state is deterministic and its successor configuration terminates under the guard and accepts exactly when $P$ holds, then, provided the original configuration satisfies the guard, the original configuration has those same properties.

**Proof.** Form the termination derivation at the original live configuration by one step: the guard holds there by assumption, and for either choice bit the next configuration is exactly the result of executing the deterministic instruction. Thus both successors inherit the successor's termination derivation. For acceptance, acceptance from a live configuration is equivalent to acceptance from at least one of its choice-bit successors (\texttt{nacc_live}). Both successors here are the same deterministic successor, so this is equivalent to acceptance there. The successor's assumed acceptance equivalence then gives precisely $P$.

**Key facts.** `Complexity.LogProg.nastep_det'`, `Complexity.LogProg.nacc_live`.
