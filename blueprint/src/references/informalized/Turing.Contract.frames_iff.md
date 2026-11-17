<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.frames_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of frame preservation

**Claim.** The contract preserves every tape cell outside the assigned sets if and only if, for every admissible run, tape, and position outside the assigned set, the endpoint tape content equals the starting tape content.

**Proof.** Both sides assert the same pointwise equality: for every datum and admissible starting configuration, every tape index, and every position outside the assigned set for that tape, the endpoint tape content equals the initial tape content. Thus the equivalence follows directly from the definitions.
