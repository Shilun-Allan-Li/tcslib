<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedFrame_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Applying a Framed Action

**Claim.** Applying the framed action to the framed configuration gives the frame of the configuration obtained by applying the original action.

**Proof.** Compare the two configurations field by field. Their control states, input-head positions, and output lists agree directly from the definitions of the framing and action application. For the work tapes and head positions, split the framed tape indices into the original machine's tape indices and the five added tapes. Among the original indices, the chosen clock tape is updated by the framed action's clock component; every other original tape retains its contents and receives its prescribed head movement. These agree with framing the result of applying the action to the six-tape configuration, because the frame inserts the clock tape by updating precisely that selected index. On the five added indices, the explicit cases for the four core tapes and the buffer tape show that their contents and head positions also agree. Thus all configuration fields coincide.
