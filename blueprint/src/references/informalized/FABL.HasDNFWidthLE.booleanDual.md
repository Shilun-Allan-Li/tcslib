<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.HasDNFWidthLE.booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Transfers DNF Width to CNF

**Claim.** If a Boolean function has a DNF of width at most $w$, then its Boolean dual has a CNF of width at most $w$.

**Proof.** Choose a DNF $\phi$ of width at most $w$ representing $f$, and form a CNF $\psi$ whose clauses are exactly the terms of $\phi$. Its width is therefore the same as the width of $\phi$. Switching conjunctions and disjunctions in a CNF represents its Boolean dual (`switchAndOr_toBooleanFunction`), so the dual of the function represented by $\psi$ is represented by the original DNF $\phi$, hence equals $f$. Applying Boolean duality again recovers the function represented by $\psi$; because Boolean duality is injective (`booleanDual_injective`), $\psi$ represents the dual of $f$. Thus $\psi$ is the required CNF.

**Key facts.** `FABL.CNFFormula.switchAndOr_toBooleanFunction`, `FABL.booleanDual_injective`.
