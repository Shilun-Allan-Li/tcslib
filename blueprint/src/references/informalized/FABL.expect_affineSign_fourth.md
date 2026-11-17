<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.expect_affineSign_fourth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment of an affine random sign

**Claim.** For a uniform sign $S\in\{-1,1\}$, $\mathbb{E}(a+bS)^4=a^4+6a^2b^2+b^4$.

**Proof.** Average over the two possible signs. The result is $\big((a+b)^4+(a-b)^4\big)/2$. Expanding both fourth powers cancels the terms with odd powers of $b$ and leaves $a^4+6a^2b^2+b^4$.
