<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.mean_abs_sharpLevelOneSignedCounterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean absolute value on the two-sign cube

**Claim.** For $g(x_1,x_2)=(x_1+x_2)/2$ on the uniform two-dimensional sign cube, the mean of $|g|$ is $1/2$.

**Proof.** Identify the two coordinates of the cube with a pair $(s,t)$ of signs. Under this identification, the function is $|(s+t)/2|$, and the uniform mean on the cube becomes the iterated uniform mean over the two signs. Averaging first over one sign uses the fact that the mean of a function on the sign set is the average of its values at $1$ and $-1$ ($\texttt{FABL.expect_sign}$). Applying this to both signs, the two equal-sign pairs contribute $1$ each and the two opposite-sign pairs contribute $0$ each. Their average is $1/2$.

**Key facts.** `FABL.expect_sign`.
