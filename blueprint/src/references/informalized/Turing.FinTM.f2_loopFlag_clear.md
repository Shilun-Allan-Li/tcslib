<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopFlag_clear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing the Loop Flag

**Claim.** For every optional Boolean flag, writing a blank at the origin of a tape that contains that flag only at the origin produces the tape for the empty word.

**Proof.** Compare the two tape functions at an arbitrary integer position. At the origin, the update writes `none`, so the resulting tape is blank there. Away from the origin, the update leaves the tape unchanged, and the original tape is already blank there. Thus the functions agree everywhere, and the resulting tape is the empty-word buffer tape.
