<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.signAnd_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign conjunction indicator formula

**Claim.** For signs $a,b,c\in\{−1,1\}$, the indicator of $a\wedge b=c$ equals $\frac{2+c+ac+bc-abc}{4}$, with the signs on the right viewed as real numbers.

**Proof.** Each of $a,b,c$ is either $1$ or $-1$, so there are eight cases. In each case, evaluate the definition of $a\wedge b$ and the indicator on the left, and substitute the three signs into the expression on the right. When $a=b=-1$, the conjunction is $-1$, and the expression is $1$ exactly when $c=-1$. In the other three choices of $(a,b)$, the conjunction is $1$, and the expression is $1$ exactly when $c=1$. In all other cases both sides are zero, proving the identity.
