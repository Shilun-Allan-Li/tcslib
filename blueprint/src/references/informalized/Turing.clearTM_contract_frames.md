<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean :: Turing.clearTM_contract_frames -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frames Preserved by the Clearing Machine

**Claim.** The clearing machine's contract preserves every work-tape cell outside the cleared interval on tape $i$, and every cell on each other tape.

**Proof.** Fix a word, a starting configuration satisfying the contract, a tape $j$, and a position $q$ outside the specified frame set. The contract's endpoint leaves the cell unchanged unless $j=i$ and the position lies between the head position on tape $j$ and that position plus the word length, including the lower endpoint but excluding the upper endpoint. If this exceptional case held, then $j=i$ and the interval inequalities would put $q$ inside the frame set, contradicting the choice of $q$. Thus the endpoint uses its unchanged-cell case, proving preservation.
