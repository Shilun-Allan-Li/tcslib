<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneTape_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Zone Tape

**Claim.** For empty zone contents, the tape has value $\mathrm{some}(\mathrm{false})$ at $0$ and $1$, and is blank at every other integer position.

**Proof.** The empty contents have no home symbol and every left and right zone word is empty. At positions $0$ and $1$, the tape definition therefore returns the presence bit and default Boolean value of the absent home symbol, both false. At any other position, the tape selects a side slot; that slot comes from an empty word, so it is absent and the tape value is blank.
