<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitCode_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for a visit code

**Claim.** The code for the last time strictly before $t$ when tape $\tau$'s head occupied its position at time $t$ has length at most $t+2$.

**Proof.** Split according to whether the previous-visit time exists. If it does not, the visit code is empty and the bound is immediate. Otherwise write that time as $s$. The previous-visit characterization (`Complexity.clPrev_spec`) gives $s<t$, hence $s\le t$. The elapsed-time width bound (`Complexity.clElapsed_width`) then gives that the binary representation of $s$ has length at most $t$. The visit code consists of this binary representation encoded by duplicating its bits, followed by a two-bit delimiter. Its length is therefore at most $t+2$.

**Key facts.** `Complexity.clPrev_spec`, `Complexity.clElapsed_width`.
