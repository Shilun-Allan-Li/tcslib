<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductVerificationLocalWork_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic local-work bound

**Claim.** The verification’s local work, as a function of the natural-number dimension $n$, is asymptotically bounded by a constant multiple of $(n+1)^2$.

**Proof.** For every $n$, the preceding pointwise estimate gives $\mathrm{matrixProductVerificationLocalWork}(n)\le 11(n+1)^2$ (\texttt{FABL.matrixProductVerificationLocalWork\_le}). Regard both sides as real numbers; since the quantities are nonnegative, their norms are the same quantities. Thus the function giving local work is everywhere bounded in norm by $11$ times the comparison function $n\mapsto(n+1)^2$. The definition of big-$O$ with this constant bound yields the claim.

**Key facts.** `FABL.matrixProductVerificationLocalWork_le`.
