<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.savitch_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Savitch Procedure Halts

**Claim.** Under the stated input-length oracle hypothesis and with $1\le E$, the procedure halts from its zeroed scan state, stays within the specified register bound, and returns true exactly when the bounded initial and accepting codes are connected by the prescribed reachability relation.

**Proof.** Set $w=(|x|+2)^{2E}$ and $s=(|x|+2)^E$. The power comparison gives $s\le w$. The size bounds give $w<2^w$ and $2^w\le 2^{w^2}$. The setup run therefore reaches the outer-search state with radius $s$, width $w$, and code bound $2^w$, while respecting the larger guard bound $2^{w^2}$. From that state, apply the outer-search run theorem with source counter initially zero and midpoint counter zero. It halts with the decision that there exist an initial code $u'$ at least zero and below $2^w$, and an accepting code $v<2^w$, with the required level-$w$ reachability. Since every natural number is at least zero, this existential condition is equivalent to the one in the claim. The two finite runs concatenate, and the zero-register-vector identity identifies the initial machine state with the setup theorem’s starting state.

**Key facts.** `Complexity.LogProg.SavitchARM.size_facts`, `Complexity.LogProg.SavitchARM.St.toV_zero`, `Complexity.LogProg.SavitchARM.setup_run`, `Complexity.LogProg.SavitchARM.outerU_run`.
