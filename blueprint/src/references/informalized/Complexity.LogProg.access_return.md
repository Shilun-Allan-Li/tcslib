<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Returning from a restoring state

**Claim.** From a restoring configuration with the stated bounds on the registers and counter head, there is a finite safe computation path to the configuration specified by the exit rule, with the first register reset to zero.

**Proof.** Let $c$ be the configuration with state `restore eq` and parameters $i,k,p$. The restoring transition moves the head on work tape $2$ left while that tape contains the binary word for $k$. The return lemma for a register whose transition moves left across its stored word (`regBack_x`) therefore gives a run to `clear eq false`, with the head back at position $0$. It also bounds every intermediate position between $-1$ and the starting position. The binary word for $k$ fits within the safety bound because $k\le |y|+1$ and binary-word length is monotone (`length_bits_mono`). Thus each configuration in this run is safe (`accessCfg_safe`), and the run gives an `AccessPath` to the clear state (`accessPath_of_run`). Finally, the clearing routine removes the first register's contents and reaches the exit configuration (`access_clear`); composing the two paths proves the claim.

**Key facts.** `Complexity.LogProg.regBack_x`, `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.accessCfg_safe`, `Complexity.LogProg.accessPath_of_run`, `Complexity.LogProg.access_clear`.
