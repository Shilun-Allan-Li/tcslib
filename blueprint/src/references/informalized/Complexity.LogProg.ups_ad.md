<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.ups_ad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probabilistic Semantics at an Arithmetic Site

**Claim.** Under the register-bound and counter hypotheses, if the designated arithmetic entry state with the specified register updates has probabilistic semantics $q$, then the arithmetic instruction at the site’s initial state with the original registers has probabilistic semantics $q$.

**Proof.** The arithmetic-site program first compares the inner counter with the designated value register. While the counter is smaller, it increments the designated scratch register twice and then increments the counter, repeating this loop. The hypotheses ensure that the loop terminates when the counter reaches the value register and that all intermediate registers remain bounded by $B$. Its net effect is to add twice the difference between the comparison value and the initial counter to the scratch register, leaving the counter at the comparison value. The distinctness conditions in `adSite_ne` ensure these three registers do not interfere. Thus the loop reaches the specified entry state with exactly the two updates assumed in the premise. By the register-bound consequence of $\sigma.Le$ (`UReg.reg`), the initial configuration satisfies the required bound; the loop-preservation theorem for probabilistic semantics (`psem_addTwice`) transfers the semantics $q$ from that updated configuration back to the arithmetic instruction.

**Key facts.** `Complexity.LogProg.adSite_ne`, `Complexity.LogProg.UReg.reg`, `Complexity.LogProg.psem_addTwice`.
