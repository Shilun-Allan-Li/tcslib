<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductVerificationCost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of verification work cost

**Claim.** For all natural numbers $n,r$, the cost consisting of $r$ units of work plus the verification's local work equals the verification cost at parameters $n,r$.

**Proof.** Represent each cost by its triple of counts. The triple representation is injective (\texttt{FABL.LearningCost.toTriple_injective}), so it suffices to compare triples. Their first two coordinates are both zero; the work coordinate on each side is $r+\mathrm{localWork}(n)$. Hence the triples, and therefore the costs, agree.

**Key facts.** `FABL.LearningCost.toTriple_injective`.
