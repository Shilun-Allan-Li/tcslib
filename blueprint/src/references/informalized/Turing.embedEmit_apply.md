<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmit_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action respects configuration embedding

**Claim.** Applying an original action after embedding a configuration gives the same configuration as first applying that action and then embedding the result, with the same initial contents, head positions, and output prefix.

**Proof.** Configurations agree in their state and input-head position directly. For each work tape, split according to whether its index is selected by the embedding. If it is selected, the embedded action uses the original tape's write instruction and movement, and the embedded configuration supplies that tape's contents and head position; applying the action therefore agrees with embedding the updated original tape. If it is not selected, the embedded action makes no write and no movement, so its contents and head remain the arbitrary initial ones on both sides. Finally, the action appends its output to the existing output list. The two resulting lists agree by associativity of concatenation, since the embedded output is the prefix followed by the original output.
