<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.two_pow_sup_le_one_add_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound from maximum depth

**Claim.** For a finite set $s$ and a function $d:s\to\mathbb{N}$, $2^{\max_{i\in s}d(i)}\le1+\sum_{i\in s}2^{d(i)}$, with the empty maximum equal to $0$.

**Proof.** Induct on the finite set. For the empty set, the maximum is $0$ and the sum is empty, so both sides equal $1$. For a nonempty set, write it as the insertion of an element $a$ into a set $s$ not containing $a$, and use the induction bound for $s$. If $d(a)\le\sup_{i\in s}d(i)$, the maximum is unchanged; adding the nonnegative term $2^{d(a)}$ to the sum preserves the bound. If instead $d(a)>\sup_{i\in s}d(i)$, the new maximum is $d(a)$. The right-hand side contains both the previous sum and the new term $2^{d(a)}$, which together dominate $2^{d(a)}$ (indeed, the right side also includes the initial $1$).
