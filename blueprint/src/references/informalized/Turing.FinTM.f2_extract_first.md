<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extract_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Step of Pair Extraction

**Claim.** From the extractor's initial reading state at position $|pre|$, where $x=pre++[b]++rest$, one step reaches position $|pre|+1$ with $b$ recorded in the state and the tape, work head, and output unchanged.

**Proof.** The input-symbol calculation for an extractor configuration identifies the scanned symbol with the symbol of $x$ at index $|pre|$ ($\texttt{Turing.FinTM.f2_extractCfg_read}$). The decomposition of $x$ makes that symbol $b$. In the initial reading state, the machine's transition records $b$ in its state, writes nothing, and leaves the work head and output unchanged. The input head moves right to position $|pre|+1$ by the right-move formula ($\texttt{Turing.moveInputPos_pos_of_ne_right}$); the decomposition ensures this is not the right boundary. Thus all components are those of the claimed configuration.

**Key facts.** `Turing.FinTM.f2_extractCfg_read`, `Turing.moveInputPos_pos_of_ne_right`.
