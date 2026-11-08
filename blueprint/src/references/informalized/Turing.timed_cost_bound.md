<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_cost_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic cost bound

**Claim.** For natural numbers $S,B,t,w,s,d$, if $w\le t$, $s\le 4w+S$, and $d\le(B+2w+8)(t+1)$, then $s+d\le(S+B+14)(t+1)^2$.

**Proof.** Since $1\le t+1$, we have $t+1\le(t+1)^2$. Also $w\le t\le(t+1)^2$ and $1\le(t+1)^2$, so the startup contribution satisfies $s\le4w+S\le(S+4)(t+1)^2$. For the second contribution, $w\le t+1$ and $1\le t+1$ imply $B+2w+8\le(B+10)(t+1)$. Multiplying by $t+1$ and using the assumed bound on $d$ gives $d\le(B+10)(t+1)^2$. Adding the two estimates yields $s+d\le(S+B+14)(t+1)^2$.
