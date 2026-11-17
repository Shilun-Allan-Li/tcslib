<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.PH_eq_SigmaP_of_SigmaP_eq_PiP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collapse from Level Equality

**Claim.** If $1\le i$ and $\Sigma_i^P=\Pi_i^P$, then $\mathsf{PH}=\Sigma_i^P$.

**Proof.** We show that every level at or above $i$ is contained in $\Sigma_i^P$. Use induction over levels $j\ge i$. At the base level $j=i$, the containment is immediate. For the successor step, take a language in $\Sigma_{j+1}^P$. Its level characterization represents it by a polynomially bounded existential witness followed by a language $L'$ in $\Pi_j^P$ (`Complexity.mem_SigmaP_succ_iff`). By induction, $L'$ lies in $\Sigma_i^P$; since $\Sigma_i^P=\Pi_i^P$, it also lies in $\Pi_i^P$. The witness characterization for adjoining an existential polynomially bounded witness to a language in $\Sigma_i^P$ (using $i\ne0$) puts the original language in $\Sigma_i^P$ (`Complexity.mem_SigmaP_of_exists`). Thus all levels $j\ge i$ lie within $\Sigma_i^P$. Now take any language in $\mathsf{PH}$. The hierarchy membership characterization places it in some $\Sigma_j^P$ (`Complexity.mem_PH_iff`). If $j\le i$, monotonicity of the existential levels gives its membership in $\Sigma_i^P$ (`Complexity.SigmaP_mono`); if $i\le j$, use the containment just proved. This proves $\mathsf{PH}\subseteq\Sigma_i^P$. Conversely, every $\Sigma_i^P$ language belongs to $\mathsf{PH}$ (`Complexity.SigmaP_subset_PH`), so equality follows.

**Key facts.** `Complexity.mem_SigmaP_succ_iff`, `Complexity.mem_SigmaP_of_exists`, `Complexity.mem_PH_iff`, `Complexity.SigmaP_mono`, `Complexity.SigmaP_subset_PH`.
