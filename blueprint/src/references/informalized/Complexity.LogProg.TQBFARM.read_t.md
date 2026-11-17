<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean :: Complexity.LogProg.TQBFARM.read_t -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability from a Successful Read

**Claim.** If the instruction at $l$ queries the first oracle on the whole input followed by the binary word in register $P$, all registers of $st$ are bounded by $B$, and the bit at position $st.P$ is true, then any bounded, precondition-preserving run from $l_1$ with registers $st$ to $c$ can be preceded by starting at $l$.

**Proof.** The call at $l$ builds the paired input consisting of $x$ and the binary representation of register $P$ (\texttt{Complexity.LogProg.vword_whole₁}). By the register-coordinate identity, that register is $st.P$ (\texttt{Complexity.LogProg.TQBFARM.St.toV_P}); the first oracle returns the input bit at that position (\texttt{Complexity.LogProg.TQBFARM.orc_bit}), which is true by assumption. Hence one transition from $l$ goes to $l_1$ without changing the registers. The given reach from $l_1$ can now be prefixed with that transition using the one-step extension principle (\texttt{Complexity.LogProg.TQBFARM.step_of}); the register bound ensures the transition begins within the required guard.

**Key facts.** `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.TQBFARM.St.toV_P`, `Complexity.LogProg.TQBFARM.orc_bit`, `Complexity.LogProg.TQBFARM.step_of`.
