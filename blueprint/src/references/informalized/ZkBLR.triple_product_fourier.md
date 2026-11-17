<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.triple_product_fourier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triple-Product Fourier Identity

**Claim.** For the $j$-twisted lift $F$, the average of $F(x+y)\overline{F(x)}\overline{F(y)}$ over independent uniform $x,y$ equals $\sum_s |\widehat F(s)|^2\overline{\widehat F(s)}$.

**Proof.** First prove the identity for an arbitrary complex-valued function $F$ on the finite group. Expand $F(x+y)$ in its Fourier series, using the Fourier expansion theorem. The character identity $\chi_s(x+y)=\chi_s(x)\chi_s(y)$ then separates the sums over $x$ and $y$; exchanging the finite sums gives, for each frequency $s$, the product of its Fourier coefficient and two copies of $\sum_x\overline{F(x)}\chi_s(x)$. By the definition of the Fourier coefficient and conjugation, each such inner sum is $k^n\overline{\widehat F(s)}$. Substituting into the averaged expression cancels the normalization factors from the two averages, leaving $\widehat F(s)\overline{\widehat F(s)}\overline{\widehat F(s)}=|\widehat F(s)|^2\overline{\widehat F(s)}$. Summing over $s$ proves the identity for arbitrary $F$, and taking $F$ to be the twisted lift gives the claim.

**Key facts.** `ZkFourier.fourier_expansion`, `ZkFourier.char_s_add`.
