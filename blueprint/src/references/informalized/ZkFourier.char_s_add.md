<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.char_s_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characters respect addition

**Claim.** For every frequency $s$ and vectors $x,y$, the character at $s$ evaluated at $x+y$ is the product of its values at $x$ and $y$.

**Proof.** The dot product with fixed frequency $s$ is additive in its vector argument, so $s\cdot(x+y)=s\cdot x+s\cdot y$ (`ZkFourier.zkDot_add_right`). The map sending a residue to its root of unity is multiplicative with respect to addition (`ZkFourier.toOmega_add`). Applying this fact to the additive dot-product identity gives $\chi_s(x+y)=\chi_s(x)\chi_s(y)$.

**Key facts.** `ZkFourier.zkDot_add_right`, `ZkFourier.toOmega_add`.
