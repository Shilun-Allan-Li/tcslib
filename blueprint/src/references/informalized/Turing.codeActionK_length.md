<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeActionK_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimum action-code length

**Claim.** Every action of a $k$-tape machine over Boolean symbols with $n+1$ states has an encoding of length at least $4k+5$.

**Proof.** The input-head movement contributes two bits, the output contributes two bits, and the successor-state encoding contributes at least one bit. For each work tape, its write instruction and head movement each contribute two bits, hence at least four bits per tape. The concatenation over all $k$ tapes has length at least $4k$ by the flat-map length bound (`codeFlatMap_length`). Adding the fixed contributions gives a total of at least $2+4k+2+1=4k+5$.

**Key facts.** `Turing.codeFlatMap_length`.
