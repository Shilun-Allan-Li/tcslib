<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean :: Complexity.Codec.z_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded input-symbol reachability

**Claim.** Under the stated register bound and encoding hypothesis, the step-mode codec can reach the phase that processes the input symbol at position $p$, changing only $Z$ to a value $z\le 2$ and keeping all registers within the bound.

**Proof.** First convert the componentwise bound on the registers into a bound on every value of the register assignment, using the register-bound lemma (`Complexity.Codec.Regs.Bd.val_le`). Split according to whether the input symbol is blank. If it is blank, its code is $0$, so the hypothesis forces $Z=0$. The `zA` instruction therefore branches directly to the desired processing phase, leaving the assignment unchanged; the original register bound supplies the guard needed for this one-step reachability (`Complexity.Codec.gd_of` and `Complexity.Codec.Reach.single'`). Take $z=0$. If the symbol is a bit, its code is $1$ or $2$. The first step moves from `zA` to `zB` without changing registers. The next step decrements $Z$, reaching `zC`; the assignment remains bounded because decrementing a natural number cannot increase it. At `zC`, the new value of $Z$ is $0$ in the false-symbol case and $1$ in the true-symbol case, so the branch enters the phase for that symbol. These three one-step transitions compose by transitivity of reachability (`Complexity.Codec.Reach.trans`). Choose $z=Z-1$, which is respectively $0$ or $1$, hence at most $2$. The intermediate configurations satisfy the guard: their register values remain bounded, and the relevant codec labels satisfy the precondition used in `gd_of`.

**Key facts.** `Complexity.Codec.Regs.Bd.val_le`, `Complexity.Codec.gd_of`, `Complexity.Codec.Reach.single'`, `Complexity.Codec.Reach.trans`.
