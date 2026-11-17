<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_clock_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entering the clock rewind phase

**Claim.** If the four-tape configuration has pending-action control carrying $bits$ and $halt$, one step from its six-tape lift with clock word $b_s$ reaches clock-rewind control carrying the same data, with the word unchanged and head at $|b_s|-1$.

**Proof.** The lift places the four-tape control inside the timed interpreter's work control, so the stated hypothesis identifies its state as the pending-action case. Unfolding one interpreter step in that case gives the clock-rewind control, leaves the input head fixed, and preserves the other tape contents. The clock tape itself is unchanged, while its head moves from its initial position $|b_s|$ one place to the left, hence to $|b_s|-1$. The identity that a zero input movement leaves the input-head position unchanged (`moveInputPos_zero`) supplies the input-position component; the remaining configuration components are checked directly from the transition definition.

**Key facts.** `Turing.moveInputPos_zero`.
