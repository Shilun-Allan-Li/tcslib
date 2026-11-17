<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStage_rightWindow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Zone Window

**Claim.** For a zone contents $z$, a zone index $i$, and $p<2$ times the capacity of zone $i$, the tape at $2b_i+2+p$ equals position $p$ of the encoded right word, with blank content beyond that word.

**Proof.** The indicated cell is at least $2$ and is neither $0$ nor $1$, so the right branch of the tape definition applies. Subtracting $2$ gives offset $2b_i+p$; division by two yields slot $b_i+p/2$, and the remainder is the parity of $p$. The bound on $p$ ensures that $p/2$ is within the zone capacity, so the zone-slot characterization (`zoneStageSlot`) identifies the selected entry with position $p/2$ in the right word. The encoding lemma (`zoneStageWord_getElem`) places the entry's presence bit first and its default Boolean value second, matching the tape's parity convention. If the entry is absent, both lookups are blank. Buffering at this natural position is list lookup (`bufferTape_nat`).

**Key facts.** `Turing.zoneStageSlot`, `Turing.zoneStageWord_getElem`, `Turing.FinTM.bufferTape_nat`.
