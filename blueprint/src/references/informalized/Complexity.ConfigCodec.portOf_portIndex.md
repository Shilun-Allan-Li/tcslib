<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.ConfigCodec.portOf_portIndex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Port index decoding

**Claim.** For every $k$ and every port for $k$ work tapes, decoding its assigned index returns that same port.

**Proof.** Check the port constructors. For a work-head port with tape index $i<k$, its assigned index $3+i$ lies in the work-head interval, and the decoder subtracts $3$ to recover $i$. For a work-symbol port, its index is $3+k+2i+t$, with $t$ indicating which Boolean symbol port is meant. The decoder's quotient by $2$ recovers $i$, and its remainder recovers $t$; the index lies in the work-symbol interval because $i<k$. For a summary port, the two Boolean choices give exactly the two dedicated summary indices, which decode to the matching choice. The state, input-head, input-symbol, old-bit, and new-bit constructors likewise have their designated indices, so the decoder returns each unchanged.
