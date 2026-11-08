<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.centralProduct_signed_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the signed central product

**Claim.** For all natural numbers $j$ and $d$, $(-1)^d\prod_{t=0}^{j+d-1}(2j-2t-1)>0$, with the empty product understood to be $1$.

**Proof.** Induct on $d$. For $d=0$, every factor in the product has index $t<j$, so $t+1\le j$ and therefore $2j-2t-1>0$. The product is positive. For the successor step, extend the product from indices below $j+d$ by its final factor, and multiply the sign factor by one additional $-1$. The new product factor is $2j-2(j+d)-1=-(2d+1)$, which is negative. The added sign factor is also negative, so their product is positive; multiplying this by the positive expression from the induction hypothesis proves the successor case.
