<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collapse from a Level Inclusion

**Claim.** For $1\le i$, if every language in $\Pi_i^P$ belongs to $\Sigma_i^P$, then $\mathsf{PH}=\Sigma_i^P$.

**Proof.** The assumed inclusion also gives equality $\Sigma_i^P=\Pi_i^P$ (`Complexity.SigmaP_eq_PiP_of_PiP_subset_SigmaP`). The collapse theorem for equality of the two classes at a level $i\ge1$ then yields $\mathsf{PH}=\Sigma_i^P$ (`Complexity.PH_eq_SigmaP_of_SigmaP_eq_PiP`).

**Key facts.** `Complexity.SigmaP_eq_PiP_of_PiP_subset_SigmaP`, `Complexity.PH_eq_SigmaP_of_SigmaP_eq_PiP`.
