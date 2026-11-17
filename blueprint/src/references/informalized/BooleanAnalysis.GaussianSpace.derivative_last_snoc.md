<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Cube.lean :: BooleanAnalysis.GaussianSpace.derivative_last_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last derivative at an appended point

**Claim.** For every bit $b$ and every $x\in\{0,1\}^n$, the discrete derivative of $f$ in the last coordinate at the point obtained by appending $b$ to $x$ equals the last-coordinate half-difference of $f$ at $x$.

**Proof.** In the definition of the discrete derivative, updating the appended point in its last coordinate replaces its final bit by false or true. Both updates leave the first $n$ coordinates equal to $x$. Thus the derivative is the difference between the restrictions of $f$ with final bit false and true, divided by $2$, which is exactly the last-coordinate half-difference at $x$.
