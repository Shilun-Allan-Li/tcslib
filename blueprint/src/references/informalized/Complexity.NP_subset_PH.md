<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.NP_subset_PH -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Lies in the Polynomial Hierarchy

**Claim.** Every language in NP belongs to the polynomial hierarchy; that is, $\mathrm{NP}\subseteq\mathrm{PH}$.

**Proof.** The one-quantifier level of the polynomial hierarchy is exactly NP (`SigmaP_one`). That level is contained in PH (`SigmaP_subset_PH`, applied at level $1$), so NP is contained in PH.

**Key facts.** `Complexity.SigmaP_one`, `Complexity.SigmaP_subset_PH`.
