<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.ccfg_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the First Tape Family

**Claim.** For each tape index in the first family, the combined configuration reads the content of that tape at its head position.

**Proof.** The combined configuration concatenates the tape contents and head positions in the same order. An index from the first block selects the corresponding original tape and head position; evaluating the read-symbol function therefore gives $D_t(i)(D_p(i))$.
