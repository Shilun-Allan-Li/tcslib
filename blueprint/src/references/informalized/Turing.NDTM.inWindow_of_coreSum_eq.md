<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.inWindow_of_coreSum_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Window membership from core-summary equality

**Claim.** If two configurations have equal core data and output summary, and every head of the second lies within distance $s$ of the origin while its tapes are blank outside that interval, then the first configuration has those same window properties.

**Proof.** Equality of the combined core data and summary implies equality of the work-tape contents functions and equality of the work-tape head-position functions, by projecting to the corresponding components of the core. Thus each head of the first configuration has exactly the position of the corresponding head of the second, so the distance bound transfers. Likewise, at every tape and integer cell, the two configurations have the same tape symbol; therefore the second configuration's blankness outside the interval transfers cell by cell. These are precisely the two conditions for the first configuration to lie in the window.
