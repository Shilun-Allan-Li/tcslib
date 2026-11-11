<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_compile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time certificate compilation

**Claim.** Under the stated polynomial-length certificate characterization of $L$ and polynomial-time decision procedure for $V$, there are natural numbers $K,r$ and a finite nondeterministic machine $N$ deciding $L$ in time $K(n+C(n+1)^c+1)^r$.

**Proof.** First construct a deterministic machine that writes the unary certificate of length $C(n+1)^c$ in time bounded by $B(n+1)^{c+1}$ (`computesFunInTime_polyUnary`). Convert it to an input-normalized machine whose running time $\tau$ is no larger than that bound, which remains active until its final step (`b2_unary_first`). Use the combined host with this scheduler and the verifier $M$, and set $K=B+A+5$ and $r=c+d+1$.

For an input $x$, let $T=\tau(|x|)$ be the scheduler's time and choose the host's total time to be $H=2|x|+2+T+(|x|+C(|x|+1)^c+2+(A(|x|+C(|x|+1)^c+1)^d+1))$. The host contract (`b2_host_contract`) ensures that every choice word of length $H$ halts, and that its output is the verifier's decision on the assembled input $x\mathbin{++}u$ for the certificate $u$ guessed along that computation. Conversely, every certificate of the required length is realized by some such choice word. Therefore the certificate characterization of $L$ gives exactly the equivalence between $x\in L$ and acceptance by the host at time $H$.

The host time bound (`b2_host_bound`), applied using $T\le B(|x|+1)^{c+1}$, gives $H\le K(|x|+C(|x|+1)^c+1)^r$. Since all branches halt by $H$, halting persists through this larger time (`HaltsWithin.mono`), and acceptance at the larger time is equivalent to acceptance at $H$ (`acceptsWithin_iff_of_halts`). Hence the host decides $L$ within the claimed polynomial bound.

**Key facts.** `Turing.FinTM.computesFunInTime_polyUnary`, `Complexity.b2_unary_first`, `Complexity.b2_host_contract`, `Complexity.b2_host_bound`, `Turing.NDTM.HaltsWithin.mono`, `Complexity.acceptsWithin_iff_of_halts`.
