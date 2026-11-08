<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.Inv.bd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register bound from the invariant

**Claim.** Under the invariant conditions, with $s\le w$ and $i\le w$, every register of the state is at most $2^{w^2}$.

**Proof.** The invariant sets nine registers to zero, so they satisfy the bound immediately. It identifies the radius and width with $s$ and $w$, and the level with $i$; these are also bounded by $2^{w^2}$ because $w<2^w\le 2^{w^2}$ (the size estimate `size_facts`) and $s,i\le w$. The code-bound register equals $2^w$, and the source, target, and midpoint registers are at most $2^w$, so all four satisfy the desired bound by the same estimate. Finally, $i\le w$ gives $w-i\le w$, hence $w(w-i)\le w^2$ and $w-i\le w$. Since powers of two are monotone in the exponent, the endpoint stack is below $2^{w(w-i)}\le 2^{w^2}$, and the phase stack is below $2^{w-i}\le 2^w\le 2^{w^2}$. These bounds give every conjunct in the register-bound condition.

**Key facts.** `Complexity.LogProg.SavitchARM.size_facts`.
