<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.PiP_subset_PH -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pi-Level Containment in PH

**Claim.** For every natural number $i$, the class $\Pi_i^P$ is contained in the polynomial hierarchy $\mathrm{PH}$.

**Proof.** Take a language in $\Pi_i^P$. The inclusion of the $i$th Pi level in the next Sigma level places it in $\Sigma_{i+1}^P$ (\texttt{PiP\_subset\_SigmaP\_succ}). By the definition of the polynomial hierarchy, every Sigma level is contained in $\mathrm{PH}$ (\texttt{SigmaP\_subset\_PH}); composing these inclusions proves the claim.

**Key facts.** `Complexity.PiP_subset_SigmaP_succ`, `Complexity.SigmaP_subset_PH`.
