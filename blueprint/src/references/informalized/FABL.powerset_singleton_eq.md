<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.powerset_singleton_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power set of a singleton

**Claim.** For any element $i$, the power set of the singleton $\{i\}$ is exactly $\{\varnothing,\{i\}\}$.

**Proof.** A subset $U$ of $\{i\}$ either contains $i$ or does not. If it contains $i$, then it must equal $\{i\}$; if it does not, then it is empty. Conversely, both $\varnothing$ and $\{i\}$ are subsets of $\{i\}$, proving the equality.
