<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_rawStrip_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the final buffer symbol

**Claim.** From the stated state-1 configuration with work tape $w++[b]$, one step leaves the input head fixed, erases the final buffer symbol, places the work head at $|w|-1$, emits nothing, and enters state $2$ when $b$ is true and state $1$ otherwise.

**Proof.** The work head starts at $|(w++[b])|-1=|w|$. At that position the buffer contains exactly $b$ (`bufferTape_nat`), so the state-1 transition selects the successor state $2$ if $b$ is true and state $1$ if it is false, while writing blank at the current cell and moving the work head left. Erasing the cell at position $|w|$ from the buffer for $w++[b]$ leaves precisely the buffer for $w$ (`f2_catalogBuffer_erase`). The input head does not move (`moveInputPos_zero`), and no output is appended, yielding the claimed configuration.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.f2_catalogBuffer_erase`, `Turing.moveInputPos_zero`.
