<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticLinearPCPPDescription_or_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-dimensional case or PCPP existence

**Claim.** For every $n$, either $n=0$ and no Boolean vector satisfies the complete quadratic condition, or $n$ is nonzero and a PCPP description for that condition exists.

**Proof.** Split on whether $n=0$. In the zero case, the condition is never satisfied, by the result that no length-zero Boolean vector has complete quadratic bit $1$ (`not_isCompleteQuadraticOne_zero`). In the nonzero case, the nonzero hypothesis supplies a witness that $n$ is nonzero, and the stated PCPP description is provided by the construction `completeQuadraticLinearPCPPDescription`.

**Key facts.** `FABL.not_isCompleteQuadraticOne_zero`.

**Caveat.** The proof invokes completeQuadraticLinearPCPPDescription directly; its construction is not included among the supplied upstream facts.
