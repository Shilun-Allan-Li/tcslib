<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.ac0ThresholdParityTarget_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Target as a Product of Block Outputs

**Claim.** For $m\ge7$ and an input $x\in\{-1,1\}^{2^m}$, the parity target evaluated at $x$ is the product, over all block indices $b$, of the sign-valued mod-two inner product outputs on the corresponding $2m$ coordinates of $x$.

**Proof.** By definition, the target at $x$ is the product over $b\in\{0,\ldots,m-1\}$ of the mod-two inner product function applied to the coordinates selected by that block's index rule. For each fixed $b$, those selected coordinates are exactly the block input used to define its block output. Thus each factor agrees with the corresponding block output, and the products agree term by term.
