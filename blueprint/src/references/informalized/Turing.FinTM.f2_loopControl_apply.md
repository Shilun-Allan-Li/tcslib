<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopControl_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop Control Action on a Frame

**Claim.** Applying the loop-control action to a framed configuration gives the frame with the specified next state, moved input position, updated tapes and heads, and appended output.

**Proof.** The state becomes the action's next state, the input head moves from $p$ according to $\mathrm{inp}$, and the output becomes $\mathrm{out}$ followed by the optional emitted symbol. For work tapes, consider the three distinguished indices. At $\mathrm{body.k}$ the flag tape is either unchanged or updated at cell zero according to $\mathrm{fw}$, and its head remains zero. At $\mathrm{body.k}+1$ and $\mathrm{body.k}+1+(1+F.\mathrm{k})$, the counter and payload tapes are respectively unchanged or updated at their specified head positions; their heads advance by the movement components of $\mathrm{ca}$ and $\mathrm{pa}$. Every other tape receives no write and no movement, so the frame retains its base tape and head there. This is exactly the stated reframed configuration.
