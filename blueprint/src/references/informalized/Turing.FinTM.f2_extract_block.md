<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extract_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Extraction of a Pair

**Claim.** Starting at the extractor configuration poised to read the first bit of the pair in $x=pre++[b,c]++rest$, after two steps the machine has the specified configuration according as the bits agree, differ with $b$ true, or differ with $b$ false.

**Proof.** First, the machine reads $b$ and enters the state recording it, advancing the input head by one; this is the first-symbol transition ($\texttt{Turing.FinTM.f2_extract_first}$). At the next position, the input-read calculation gives $c$, since the input has the displayed decomposition ($\texttt{Turing.FinTM.f2_extractCfg_read}$). The head advances once more ($\texttt{Turing.moveInputPos_pos_of_ne_right}$). Now split into the four possibilities for $b,c$. If they agree, the transition writes $b$ at the end of the tape and moves the work head right, returning to the initial reading state. The tape extension is precisely an update at its former endpoint ($\texttt{Turing.FinTM.bufferTape_append}$). If $b$ is true and the bits differ, the machine halts without changing the tape or output. If $b$ is false and they differ, it enters state $0$ and moves the work head one place left, with the stated truncated position. In each case the components of the resulting configuration match the claimed one.

**Key facts.** `Turing.FinTM.f2_extract_first`, `Turing.FinTM.f2_extractCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
