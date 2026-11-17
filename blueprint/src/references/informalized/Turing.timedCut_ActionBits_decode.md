<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_ActionBits_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the Action Bits

**Claim.** The eight fixed action bits of a one-work-tape action decode its input-head movement, work-tape write instruction, work-head movement, and optional output symbol.

**Proof.** For the input head, the first two bits record whether its movement is nonzero and whether it is negative. The three possible movements, $-1,0,1$, therefore decode respectively as $(1,1),(0,0),(1,0)$, giving back the original movement. For the work-tape write instruction, the next two bits distinguish no write, writing blank, and writing a Boolean symbol: their patterns are $(0,0),(0,1),(1,b)$, respectively. The definition of the decoder maps each pattern back to its instruction. The following two bits use the same nonzero-and-negative encoding for the work-head movement, so the three cases again recover the movement. Finally, the output bits record whether an output is present and, if present, its Boolean value. With no output, the decoded result is none; with an output, the presence bit selects the stored value. These cases exhaust the possibilities and prove all four equalities.
