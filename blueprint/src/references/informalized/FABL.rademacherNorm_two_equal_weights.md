<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.rademacherNorm_two_equal_weights -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-coordinate Rademacher norm

**Claim.** For every sign vector $x=(x_1,x_2)\in\{-1,1\}^2$, the norm of the sum of its coordinates equals $1+x_1x_2$.

**Proof.** Write each coordinate as either $1$ or $-1$. If the signs agree, their sum has absolute value $2$ and their product is $1$, so both sides equal $2$. If they disagree, the sum has absolute value $0$ and the product is $-1$, so both sides equal $0$. These four sign choices exhaust the possibilities and give the stated norm identity.
