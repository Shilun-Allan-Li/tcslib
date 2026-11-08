<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.idle_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of an Idle Action

**Claim.** Applying an idle action gives the specified successor state and moved input-head position, leaves all work tapes and work-tape head positions unchanged, and appends the optional output to the prior output.

**Proof.** The idle action specifies the successor state, input-head movement, and optional output directly. On each work tape it requests no write and zero head movement. Applying it therefore preserves the tape contents and adds zero to each head position. The output update appends the list represented by the optional output, as claimed.
