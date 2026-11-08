<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.len_t -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Branch of a Length Query

**Claim.** When the pointer is strictly within the input, a whole-input query to the input-length decider takes its positive branch; consequently, any guarded run from that branch can be prefixed by the query instruction.

**Proof.** The whole-input query encodes the pair of the input $x$ and the bit word for the pointer value. The pointer register in the configuration represents $st.P$ (`St.toV_P`), and this query’s virtual input is the required pair (`vword_whole₁`). By the characterization of the input-length oracle (`orc_len`), it answers true exactly when the encoded pointer is less than the length of the first component. The hypothesis gives $st.P<|x|$, so the machine branches to $l_1$ without changing the registers. Prefix the given guarded run from $l_1$ with this query step; the register bound supplies the guard for the initial configuration (`step_of`).

**Key facts.** `Complexity.LogProg.TQBFARM.St.toV_P`, `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.TQBFARM.orc_len`, `Complexity.LogProg.TQBFARM.step_of`.
