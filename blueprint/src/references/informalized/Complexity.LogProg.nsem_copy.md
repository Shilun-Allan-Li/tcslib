<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nsem_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Copy by Incrementing

**Claim.** Repeatedly incrementing $\mathrm{dst}$ until it equals $\mathrm{src}$ preserves the given terminating semantics and copies the source value into the destination.

**Proof.** Induct on the gap $k=v(\mathrm{src})-v(\mathrm{dst})$. When $k=0$, the registers are equal, so the test goes straight to $\mathrm{ex}$; updating $\mathrm{dst}$ to its already equal source value changes nothing. The equality branch rule (`NSem.jeq_pos`) gives the desired semantics. If $k$ is positive, the test takes the other branch. Increment $\mathrm{dst}$ once, producing $v'$ with $v'(\mathrm{dst})=v(\mathrm{dst})+1$ and $v'(\mathrm{src})=v(\mathrm{src})$, since the registers are distinct. This increment stays within the bound because the new destination value is at most the source value, which is at most $B$; the register-update bound lemma (`register_update_le`) preserves the bound on all registers. The gap for $v'$ is one smaller, so the induction hypothesis applies. Its endpoint agrees with the original target assignment: the source value is unchanged, and updating the destination to that value after the increment is equivalent to doing so from the original assignment. Finally, the unequal test and increment semantics rules (`NSem.jeq_neg`, `NSem.inc`) put this recursive computation back under the original test.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.NSem.jeq_pos`, `Complexity.LogProg.NSem.jeq_neg`, `Complexity.LogProg.NSem.inc`.
