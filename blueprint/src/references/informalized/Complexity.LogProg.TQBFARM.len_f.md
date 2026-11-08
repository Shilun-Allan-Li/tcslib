<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.len_f -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Branch of a Length Query

**Claim.** When the pointer is at or beyond the input length, a whole-input query to the input-length decider takes its negative branch; consequently, any guarded run from that branch can be prefixed by the query instruction.

**Proof.** The query forms the virtual input by pairing $x$ with the bit word for the pointer value in the pointer register. The register projection identifies that value with $st.P$ (`St.toV_P`), and the whole-input query encoding is exactly this pair (`vword_whole₁`). The input-length oracle accepts this pair precisely when the encoded number is less than the length of the first component (`orc_len`). Since $st.P\not<|x|$, the oracle answers false, so the query transitions to $l_0$ without changing the registers. The supplied guarded run from $l_0$ can therefore be prefixed with this transition; the register bound ensures the initial configuration meets the guard (`step_of`).

**Key facts.** `Complexity.LogProg.TQBFARM.St.toV_P`, `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.TQBFARM.orc_len`, `Complexity.LogProg.TQBFARM.step_of`.
