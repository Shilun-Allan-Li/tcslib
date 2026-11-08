<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.work_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Simulated Work Step

**Claim.** From the image of a configuration in the work phase, one compiled step reaches the image of the original machine's one-step successor, with the same counter and the phase determined by the transition and the stated input-boundary data.

**Proof.** The image is in a work state, where the compiled program makes no oracle call, so its next step is its ordinary machine transition (`Complexity.LogProg.rstep_noncall`). By the definition of the lifted transition, the original machine's transition is applied to the original tapes: the added counter tape is left unchanged, while the original work-tape actions, output action, and successor state are retained. The successor phase is set to the value determined by the input-head movement and the two boundary flags. The definition of one-step running (`Complexity.LogProg.rrun_one`) identifies this transition with the compiled run of length one. Comparing the resulting configuration components gives the stated image equality.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`.
