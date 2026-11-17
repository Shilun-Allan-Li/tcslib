<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.d1_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Decrement Loop Register Update

**Claim.** Let $P$ be a language of bit strings, let $x$ be a bit string, and let $B,i,u\in\mathbb N$ satisfy $i\le B$ and $u\le B$. For every $a,b\in\mathbb N$ with $b+2a\le B$, the program starts at its first decrement-loop label with register values $(i,a,b,u)$ and, after finitely many steps, reaches the next loop label with values $(i,0,b+2a,u)$ and no answer recorded. At every step before reaching that configuration, all four register values are at most $B$.

**Proof.** Induct on the outer counter $a$, with the assertion quantified over $b$. At each stage the reachability construction checks the current configuration against the program precondition and register bound using the register guard (`guard_rf`).

If $a=0$, the program's instruction at the first decrement-loop label advances directly to the next loop label, leaving the registers unchanged; the target register tuple is then $(i,0,b,u)$. The one-step reach is completed by reflexivity after that transition.

For $a+1$, the program first sees that the inner counter is nonzero, decrements it once, and passes through two instructions that increment the outer accumulator twice. The registers at the next visit to the first loop label are therefore $(i,a,b+2,u)$. The hypothesis $b+2(a+1)\le B$ ensures the needed intermediate register bounds, and the induction hypothesis applies with accumulator $b+2$. Its target has accumulator $(b+2)+2a=b+2(a+1)$ and inner counter zero, as required. The successive one-step reachability rule and transitivity along these transitions give the claimed finite run.

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.WidthExample.guard_rf`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.WidthExample.rf_1`, `Complexity.LogProg.WidthExample.rf_upd1`, `Complexity.LogProg.WidthExample.rf_2`, `Complexity.LogProg.WidthExample.rf_upd2`.
