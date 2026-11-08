<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.mul_le_klFun_add_exp_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A KL function inequality

**Claim.** For every $u\ge 0$ and every real $y$, $uy\le u\ln u-u+1+e^y-1$, with $u\ln u$ interpreted as zero at $u=0$.

**Proof.** If $u=0$, the left side vanishes, and the claimed inequality reduces to the nonnegativity of $e^y$. Now suppose $u>0$. Apply $\ln t\le t-1$ to $t=e^y/u$, which is positive. Since $u\ge0$, multiplying preserves the inequality and gives $u(y-\ln u)\le e^y-u$. Rearranging this inequality yields $uy\le u\ln u-u+e^y$, which is the desired bound.
