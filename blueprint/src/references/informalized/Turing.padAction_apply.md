<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.padAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded action respects configuration embedding

**Claim.** For $m\le k$, padding an action on $m$ work tapes to $k$ tapes and mapping its state through an injection gives the same result as applying the original action and then embedding the resulting configuration, even when the embedded starting configuration's state is set to an arbitrary $b\in B$.

**Proof.** Compare the two resulting configurations component by component. Their states agree because the padded action maps the original action's successor state by the given injection, just as embedding does. Their input-head positions agree because both apply the same input-head movement to the same position. For each work tape index below $m$, padding selects the corresponding original tape action, so the updated tape contents and head position agree with applying that action before embedding. For an index at least $m$, the padded action makes no write and no movement, while the embedding assigns an empty tape and head position zero; these remain unchanged. The outputs also agree, since both append the action's output to the original output. Equality of all configuration fields proves the claim.
