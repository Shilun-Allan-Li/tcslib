<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean :: Complexity.LogProg.TQBFARM.read_f -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a False-Bit Read

**Claim.** If the instruction at $l$ calls the first oracle in whole-input mode with the input-pointer register as its sole argument, the registers of $st$ are bounded by $B$, and the bit at position $st.P$ is false, then any bounded, precondition-preserving run from $l_0$ with registers $st$ to $c$ can be preceded by starting from $l$ with those same registers.

**Proof.** The proof first computes the single transition from $l$. A whole-input call with sole argument $P$ forms the oracle input by pairing $x$ with the binary word for the value in $P$ (\texttt{Complexity.LogProg.vword_whole₁}); the register representation gives that value as $st.P$ (\texttt{Complexity.LogProg.TQBFARM.St.toV_P}). The first oracle answers the bit of $x$ at that position (\texttt{Complexity.LogProg.TQBFARM.orc_bit}), which is false by hypothesis. Thus the call transitions to $l_0$ without changing registers. The assumed reach from $l_0$ therefore continues from the configuration immediately after this transition. The one-step extension principle (\texttt{Complexity.LogProg.TQBFARM.step_of}) then prepends the transition while preserving the precondition and register bound.

**Key facts.** `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.TQBFARM.St.toV_P`, `Complexity.LogProg.TQBFARM.orc_bit`, `Complexity.LogProg.TQBFARM.step_of`.
