<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.memCfg_symbols_castSucc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbols on original tapes

**Claim.** After adjoining a memory tape to a configuration, the symbol under the head of each original tape is unchanged.

**Proof.** The enlarged configuration is formed by appending the new tape and head position to the original families. An original index is embedded as a successor index, and appending preserves the tape contents and head position at that index. Evaluating the tape at its head position therefore gives the same symbol as before.
