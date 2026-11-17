<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStage_leftWindow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Zone Window

**Claim.** For a zone contents $z$, a zone index $i$, and $p<2$ times the capacity of zone $i$, the tape at $-(2b_i)-1-p$ equals position $p$ of the encoded left word, with blank content beyond that word.

**Proof.** The indicated cell is neither $0$ nor $1$ and lies to the left of the origin, so the left branch of the tape definition applies. Its left-side offset is $2b_i+p$; dividing by two gives slot $b_i+p/2$, with parity equal to that of $p$. Since $p<2$ times the zone capacity, $p/2$ is within that capacity, and the zone-slot characterization (`zoneStageSlot`) identifies this slot with position $p/2$ in the left word. The encoding lemma (`zoneStageWord_getElem`) says that the two positions associated to each word entry store its default Boolean value first and its presence bit second. Thus the tape value agrees with the encoded word at position $p$ when the corresponding entry exists; if it does not, both are blank. Finally, buffering at a natural position is list lookup (`bufferTape_nat`).

**Key facts.** `Turing.zoneStageSlot`, `Turing.zoneStageWord_getElem`, `Turing.FinTM.bufferTape_nat`.
