<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.concentration_optimized_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimized concentration moment identity

**Claim.** For positive integer $k$ and $t>0$, setting $q=t^{2/k}/e$ gives $\bigl((\sqrt q)^k/t\bigr)^q=\exp\bigl(-k t^{2/k}/(2e)\bigr).

**Proof.** Apply the concentration moment identity already established in the auxiliary namespace, with the same $k$ and $t$. Its hypotheses are exactly $k>0$ and $t>0$, and its conclusion is the claimed identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ConcentrationAux.concentration_optimized_moment`.
