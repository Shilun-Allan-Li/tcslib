<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalInput_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Masked Read on the Paired Input

**Claim.** Masking the embedded input read by assigning blank when the marker tape has a $1$ at the current coordinate gives exactly the symbol read by the original configuration.

**Proof.** The marker tape contains a $1$ exactly at coordinate zero (`Turing.universal_marker`). If the input head is at zero, the masked read is blank, as is the original read at the left boundary. Otherwise the marker contributes no symbol, and the head is at a positive coordinate. Write that coordinate as $j+1$; the original input read is then the $j$th symbol of $x$ (`Turing.FinTM.inputSymbol_at`). The embedded head has coordinate $2|\alpha|+2+j$, using the paired-input length formula (`Turing.universal_pair_length`), and the input symbol there is also the $j$th symbol of $x$ by the suffix property of the paired encoding (`Turing.universal_pair_suffix`). Thus the embedded read equals the original read, proving the masked equality.

**Key facts.** `Turing.universal_marker`, `Turing.FinTM.inputSymbol_at`, `Turing.universal_pair_length`, `Turing.universal_pair_suffix`.
