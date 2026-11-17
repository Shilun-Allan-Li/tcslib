<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.amplify_concrete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concrete majority error reduction

**Claim.** For every $b,e\in\mathbb N$, majority amplification gives an efficient verifier with the stated error bound and random-bit count.

**Proof.** Take the verifier that runs $M_0$ independently on $K=(18b+18)(n+1)^e$ consecutive blocks of $q=a_0(n+1)^{k_0}$ random bits and accepts exactly when more than half the runs accept. Thus the total number of random bits is $Kq=(18b+18)a_0(n+1)^{e+k_0}$. Majority closure ensures this verifier is efficient. For each input, the total number of accepting and rejecting blocks is $K$; this complementary-count identity is the proof’s `hcount` calculation.

For a member, the original verifier accepts with probability at least $2/3$, so its rejection probability is at most $1/3=1/2-1/6$. The probability that at least half the blocks reject is bounded by the majority tail estimate (`Randomized.randProb_tail_le`) with bias $1/6`. The theorem `Randomized.const_tail_bound` bounds the resulting tail by $(1/2)^{b(n+1)^e}$. Since a wrong majority is contained in this tail event, the amplified acceptance probability is at least one minus that bound.

For a nonmember, the original acceptance probability is at most $1/3$. The same tail estimate, now applied to the event that at least half the blocks accept, bounds the probability of an erroneous accepting majority by $(1/2)^{b(n+1)^e}$. Complementary Boolean probabilities (`Randomized.randProb_bool_false`) and agreement of equivalent events on all random strings (`Randomized.randProb_congr`) translate between acceptance and rejection probabilities; monotonicity of random-string probability (`Randomized.randProb_mono`) compares the relevant error events, and the complement identity (`Randomized.randProb_not`) yields the required lower bound on rejection.

**Key facts.** `Randomized.randProb_bool_false`, `Randomized.randProb_congr`, `Randomized.randProb_tail_le`, `Randomized.const_tail_bound`, `Randomized.randProb_mono`, `Randomized.randProb_not`.
