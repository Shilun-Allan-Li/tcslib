<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.sqrt_theorem9_28Threshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square Root of the Influence Threshold

**Claim.** If the total influence $I(f)$ of the real-valued version of a Boolean function $f$ is positive, then for $\varepsilon>0$ and $k\in\mathbb N$, the square root of $\varepsilon^2/I(f)^2\cdot9^{-k}$ equals $\varepsilon/I(f)\cdot(1/3)^k$.

**Proof.** Set $r=\varepsilon/I(f)\,(1/3)^k$. The hypotheses $\varepsilon>0$ and $I(f)>0$ imply $r\ge0$. Squaring and using $((1/3)^k)^2=(1/9)^k$ gives $r^2=\varepsilon^2/I(f)^2\cdot(1/9)^k$, the stated threshold. The square root of a square is the absolute value, and $r\ge0$, so its square root is exactly $r$.
