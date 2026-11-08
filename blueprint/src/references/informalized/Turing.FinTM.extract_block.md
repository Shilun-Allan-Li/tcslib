<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.extract_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-step extractor block behavior

**Claim.** On an aligned pair of input bits, the pair extractor takes the stated two-step transition: equal bits extend the buffer and restart the block scan, the pair $1,0$ halts, and the pair $0,1$ enters rewind.

**Proof.** First read the leading bit $b$: the one-step extractor lemma (`Turing.FinTM.extract_first`) advances the input head and records $b$ in the control state, leaving the buffer, work-head position, and output unchanged. The next input position contains $c$, by the decomposition $x=pre\mathbin{++}[b,c]\mathbin{++}rest$; the input-head movement lemma (`Turing.moveInputPos_pos_of_ne_right`) confirms that the next positive move advances to the position just after this pair. The transition rule now has three cases. If $b=c$, it writes $b$ at the end of the buffer and advances the work head; the buffer-extension identity (`Turing.FinTM.bufferTape_append`) identifies this updated tape with the buffer $a\mathbin{++}[b]$. If $b=1$ and $c=0$, the transition halts without changing the work tape. If $b=0$ and $c=1$, it moves the work head back one cell and enters rewind. In all cases the output remains empty, giving the claimed configurations.

**Key facts.** `Turing.FinTM.extract_first`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
