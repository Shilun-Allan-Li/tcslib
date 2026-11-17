<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.boolPrefixParity_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive prefix parity

**Claim.** If $w$ is a Boolean string of length $m+2$ and $k<m+2$, then its parity on the first $k+1$ entries equals its parity on the first $k$ entries plus the encoding of its entry at position $k$, with addition in $\mathbb{F}_2$.

**Proof.** The sum defining the parity on the first $k+1$ positions is the sum over the first $k$ positions together with its final term, by the range-sum decomposition. The hypothesis $k<m+2$ ensures that this last term is the encoded entry $w(k)$ rather than the out-of-range default value. Thus the new prefix parity is the previous prefix parity plus that entry's encoding.
