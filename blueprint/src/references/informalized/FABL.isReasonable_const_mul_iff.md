<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.isReasonable_const_mul_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scale Invariance of the Fourth-Moment Condition

**Claim.** For nonzero $c$, the fourth-moment condition defining reasonableness for $cX$ is equivalent to the corresponding condition for $X$, with the same bound $B$.

**Proof.** In either direction, the lower bound $1\le B$ is unchanged. The moment terms scale by powers of $c$: the second moment of $cX$ is $c^2$ times that of $X$, and the fourth moment is $c^4$ times that of $X$; this follows by pulling a constant through the finite probability expectation (\texttt{FABL.pmfExpectation_const_mul}). Thus the inequality for $cX$ is the inequality for $X$ multiplied by $c^4$. Since $c\ne0$, this factor is strictly positive, so the inequality is equivalent in both directions.

**Key facts.** `FABL.pmfExpectation_const_mul`.
