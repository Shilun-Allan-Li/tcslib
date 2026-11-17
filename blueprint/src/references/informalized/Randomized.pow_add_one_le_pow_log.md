<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.pow_add_one_le_pow_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Bound in Terms of Binary Logarithm

**Claim.** For all natural numbers $k,n$, one has $n^k+1\le (2^{k^2}+2)n^{\lfloor\log_2 n\rfloor}$, with the stated convention at zero.

**Proof.** First use the fact that $n^{\lfloor\log_2 n\rfloor}\ge1$ (`Randomized.one_le_pow_log`). We show that $n^k\le 2^{k^2}+n^{\lfloor\log_2 n\rfloor}$. If $n=0$, the claim follows by checking whether $k=0$. For positive $n$, split according to whether $k\le\lfloor\log_2 n\rfloor$. In that case, monotonicity of powers gives $n^k\le n^{\lfloor\log_2 n\rfloor}$. Otherwise, the defining bound for the binary logarithm gives $n<2^{\lfloor\log_2 n\rfloor+1}\le2^k$. Raising this inequality to the $k$th power yields $n^k\le(2^k)^k=2^{k^2}$. Finally, multiply the lower bound $1\le n^{\lfloor\log_2 n\rfloor}$ by $2^{k^2}$ and add the preceding estimate for $n^k$. Rearranging gives the stated inequality.

**Key facts.** `Randomized.one_le_pow_log`.
