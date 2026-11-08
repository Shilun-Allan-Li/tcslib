<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.booleanRealEmbedding_innerProductModTwoBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Embedding of a Mod-Two Inner Product

**Claim.** For vectors $x,y\in(\mathbb F_2)^m$, the real embedding of their mod-two inner product is $(1-(-1)^{\langle x,y\rangle})/2$.

**Proof.** The mod-two inner product is either $0$ or $1$ (\texttt{FABL.f₂_eq_zero_or_one}). If it is $0$, its sign encoding is $1$, whose real value is $1$; the Boolean real embedding is $0$, and $(1-1)/2=0$. If it is $1$, its sign encoding is $-1$, whose real value is $-1$; the Boolean real embedding is $1$, and $(1-(-1))/2=1$. These two cases prove the identity.

**Key facts.** `FABL.f₂_eq_zero_or_one`.
