<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: krawtchouk_eval_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Krawtchouk value at zero

**Claim.** For natural numbers $n,j$ with $j\le n$, the Krawtchouk polynomial defined by the given finite sum has value $\binom{n}{j}$ at zero.

**Proof.** At $x=0$, every term in the defining sum with index $i>0$ vanishes because $\binom{0}{i}=0$. The only surviving term is the index-zero term, which is $\binom{0}{0}\binom{n}{j}=\binom{n}{j}$.
