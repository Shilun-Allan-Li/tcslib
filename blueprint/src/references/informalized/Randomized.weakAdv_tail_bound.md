<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.weakAdv_tail_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak Advantage Tail Bound

**Claim.** For natural numbers $c,d,n$, if $\varepsilon=\min\{1/6,((n+1)^{-1})^c\}$, then $2(1-4\varepsilon^2)^{\lfloor 56(n+1)^{2c+d}/2\rfloor}\le (1/2)^{(n+1)^d+1}$.

**Proof.** Let $\varepsilon$ be the weak advantage. Its positivity and upper bound by $1/6$ (`Randomized.weakAdv_pos`, `Randomized.weakAdv_le_sixth`) give $0\le 4\varepsilon^2\le 1$. The lower bound on weak advantage (`Randomized.weakAdv_ge`) gives $((n+1)^{-1})^c\le 6\varepsilon$. Multiplying this inequality by itself and using $(n+1)^c((n+1)^{-1})^c=1$ yields $1\le 9(n+1)^{2c}(4\varepsilon^2)$. Next, the exponent in the left-hand side is $28(n+1)^{2c+d}$, and the elementary bounds $(n+1)^d\ge1$ and $(n+1)^{2c}\ge1$ show that this exponent is at least $9(n+1)^{2c}((n+1)^d+2)$. Apply the geometric decay estimate (`Randomized.one_sub_pow_le_half_pow`) with $x=4\varepsilon^2$, $m=9(n+1)^{2c}$, $T=(n+1)^d+2$, and the displayed exponent as $e$. It bounds $(1-4\varepsilon^2)^e$ by $(1/2)^{(n+1)^d+2}$. Multiplying by $2$ gives the desired right-hand side, since $2(1/2)^{(n+1)^d+2}=(1/2)^{(n+1)^d+1}$.

**Key facts.** `Randomized.weakAdv_pos`, `Randomized.weakAdv_le_sixth`, `Randomized.weakAdv_ge`, `Randomized.one_sub_pow_le_half_pow`.
