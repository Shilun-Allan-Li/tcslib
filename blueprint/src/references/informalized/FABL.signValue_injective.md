<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.signValue_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of sign evaluation

**Claim.** The map sending each sign $s\in\{\pm1\}$ to its real value is injective.

**Proof.** Suppose two signs $a$ and $b$ have the same real value. By definition, this says their underlying integers have equal images in $\mathbb R$. The embedding of the integers into the reals is injective, so the underlying integers are equal. Equality of the underlying elements implies equality of the units, hence $a=b$.
