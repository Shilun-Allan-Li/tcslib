<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasOutputBit.lean :: FABL.executableSmallBiasOutputBitWork_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joint Output-Bit Work Growth

**Claim.** As $\ell$ and $j$ vary jointly over the natural numbers, the work for output bit $j$ is $O((j+1)(\ell+1)^2)$.

**Proof.** The pointwise bound (FABL.executableSmallBiasOutputBitWork_le) bounds the work by $16(j+1)(\ell+1)^2$ for every pair $(\ell,j)$. After viewing both natural-valued functions as real-valued functions, the same inequality gives a uniform norm bound with constant $16$. A uniform bound of this form implies the asserted big-$O$ relation along the joint filter at infinity.

**Key facts.** `FABL.executableSmallBiasOutputBitWork_le`.
