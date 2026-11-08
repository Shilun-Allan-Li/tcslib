<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecInputRead_wire -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol read from its wire

**Claim.** When the encoded input-head position equals $p$, reading the encoded input wire at $p$ yields the configuration's scanned input symbol, with boundary positions yielding no symbol.

**Proof.** The equality of encoded and actual head positions gives equality of their natural-number values. If $p$ is an interior position, the wire selects the input bit at index $p-1$, and the input-read function returns that bit. The head-position equality identifies this with the configuration's input position; the definition of the scanned input symbol then gives the same list entry. If $p$ is not interior, the finite bounds on the head position force it to be one of the two boundary positions: the left boundary or the position just past the input. At either boundary the encoded input-read function returns no symbol, and the configuration's scanned-symbol definition does too. This proves the identity in all cases.
