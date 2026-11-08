<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seam_stationary_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary Action on a Configuration

**Claim.** Applying the action with no head movements, no tape writes, no output, and successor state $q$ leaves the configuration unchanged except for replacing its state by `some q`.

**Proof.** By the definition of applying an action, the successor state becomes `some q`. The zero input movement preserves the input-head position; on every work tape, the absent write instruction preserves its contents and the zero movement preserves its head position. Since no symbol is output, the output list is unchanged. Thus every field agrees with the original configuration except the state, as asserted.
