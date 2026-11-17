<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean :: Complexity.Codec.halvCount_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register halving loop count

**Claim.** The loop that tests $t$, halves it when nonzero, and increments $c$ reaches its done state with $t=0$ and $c$ increased by the binary length of the initial $t$, while all configurations before arrival satisfy the guard.

**Proof.** Proceed by strong induction on the initial value $n$ of register $t$, generalizing the register valuation.

If $n=0$, the test instruction immediately transfers control to the done state without changing the registers. The binary representation of zero has length zero, so the asserted final valuation is the initial one. The initial guard holds by the register bound hypothesis; the one-step reachability principle (`AReach.single`) gives the result.

Now suppose $n>0$. The test first transfers control to the halving instruction, which replaces $t$ by $n/2$; the bump instruction then increases $c$ by one and returns to the test. The binary-length identity for halving (`access_width_half`) says that the length of the bits of $n/2$, plus one, is the length of the bits of $n$. Consequently, the new counter value plus the binary length of the new $t$ still equals the original counter value plus the binary length of $n$, and hence is at most $B$.

The register-update bound (`register_update_le`) shows that both the halved value and the incremented counter remain bounded by $B`; all other registers are unchanged. Since $n/2<n$, the induction hypothesis applies at this new test configuration and supplies the rest of the guarded reachability, ending with $t=0$ and the counter increased by the bit length of $n/2$. The bit-length identity makes this the claimed final counter value. Prepending the guarded test, halving, and bump steps using reachability composition (`AReach.step`) completes the induction.

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.access_width_half`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.step`.
