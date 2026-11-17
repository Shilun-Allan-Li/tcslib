<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.exists_bpDecides_of_advantage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplifying a Decision Advantage

**Claim.** If a finite nondeterministic machine uses space at most s(|x|) and decides L with success probability at least one half plus δ for every input, then a finite nondeterministic machine achieves success at least 1−ε with space bounded by a constant multiple of s(|x|).

**Proof.** Set d=min(δ,1/4), so d is positive, no larger than δ, and at most 1/4. Thus q=1−4d² lies in [0,1). Choose n so that 2q^n≤ε; the existence of such an n follows from geometric decay (the power bound used in the proof is `exists_pow_lt_of_lt_one`).

Use the amplification machine with 2n repetitions and the majority rule: it counts the number m of accepting runs and declares acceptance exactly when 2n+1<2m, which is strict majority among 2n+1 trials. The amplified machine halts within its stated enlarged time whenever the original machine halts within T (`Randomized.Amplify.amp_haltsWithin`). Its space is at most 3(2n+1) times the number of work tapes times the original space bound (`Randomized.Amplify.amp_usesSpace_mul`), so it has the required constant-factor bound.

The majority probability estimate says that, when the original success probability is at least one half plus d, the amplified success probability is at least 1−2q^n (`Randomized.Amplify.majority_randProb_ge`). The original hypothesis gives at least one half plus δ, hence at least one half plus d. By the choice of n, the lower bound is at least 1−ε. This applies for each input using its hypothesized halting time T, yielding the required time and success guarantees.

**Key facts.** `Randomized.Amplify.amp_haltsWithin`, `Randomized.Amplify.amp_usesSpace_mul`, `Randomized.Amplify.majority_randProb_ge`.
