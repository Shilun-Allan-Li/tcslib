<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.thresholdSign_centralProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity determines the central product sign

**Claim.** For natural numbers $j,d$, the threshold sign of $\prod_{t=0}^{j+d-1}(2j-2t-1)$ is $1$ if $d$ is even and $-1$ if $d$ is odd.

**Proof.** The signed-product estimate `centralProduct_signed_pos` states that $(-1)^d$ times the displayed product is positive. If $d$ is even, $(-1)^d=1$, so the product is positive and its threshold sign is $1$. If $d$ is odd, $(-1)^d=-1$, so positivity of the signed product says the original product is negative; its threshold sign is then $-1$. The threshold sign takes these values on nonnegative and negative inputs, respectively (`thresholdSign_of_nonneg`, `thresholdSign_of_neg`).

**Key facts.** `FABL.centralProduct_signed_pos`, `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
