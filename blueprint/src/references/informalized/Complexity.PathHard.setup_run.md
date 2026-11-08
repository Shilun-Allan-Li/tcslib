<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun.lean :: Complexity.PathHard.setup_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Setup Run

**Claim.** Under the stated bounds on $a,b,f,X,Y,B$, the specified program has a finite guarded run from the copy phase with $y=Y$, $p=2X+2$, and all other registers zero to the width-check phase with the prescribed setup registers.

**Proof.** Put $\ell=\ell(X)$ and $E=b\ell+f$. First, $2^E\le (2^E)^2$ and $E<2^E$. Also, $2^\ell\le 2(X+1)$ and $\ell<2^\ell$, so $\ell\le Y$ using $2X+2\le Y$. Since $a\le b$, we have $a\ell\le b\ell\le E$.

Starting with the copy phase, copy $p$ into $x$; the two decrements and halving in the following instructions turn $2X+2$ into $X$. Copy $x$ into $t$ and increment it, so $t=X+1$. The bit-count loop then transfers $(\operatorname{Nat.bits}(X+1)).\mathrm{length}=\ell$ from $t$ into $c$, clearing $t$. Copy $c$ into $t$. The register-scale loop runs $a$ increments of $s$ for each unit removed from $t$, producing $s=a\ell$ and clearing $t$. A second register-scale loop similarly produces $e=b\ell$ while clearing $c$; the increment chain adds $f$, giving $e=E$.

Next copy $e$ into $c$, increment $c$, and initialize $n$ to $1$. The shift loop multiplies $n$ by $2^{E+1}$, giving $2\cdot2^E$, using $1\cdot2^{E+1}=2\cdot2^E$. Copy $n$ into $m$, then shift $m$ by $2^E$, obtaining $2\cdot(2^E)^2$. Copy $m$ into $k$, increment $c$ to $1$, and shift $k$ by $2$, obtaining $4\cdot(2^E)^2$. Finally copy $p$ into $q$. These identities put the registers in exactly the stated endpoint configuration.

Each copy, shift, and loop is supplied by its corresponding run lemma, and the intervening elementary instructions are joined as single steps. The bound $Y+8(2^E)^2\le B$, together with the estimates above, bounds every register value throughout these phases; the bit-count and scale loops are bounded by their final values, and the shifts by their assumed final products. The state bounds are converted to coordinatewise bounds by `St.Bd.toV`, and the one-step transitions preserve the guard by `step_of`. Concatenating the finite guarded runs with `AReach.trans` and matching the final arithmetic expression by `reach_of_eq` proves the claim.

**Key facts.** `Complexity.PathHard.two_pow_ell_le`, `Complexity.Codec.halvCount_loop`, `Complexity.PathHard.cp_run`, `Complexity.PathHard.registerScale_loop`, `Complexity.Codec.incChain`, `Complexity.PathHard.sh_run`, `Complexity.PathHard.St.Bd.toV`, `Complexity.PathHard.step_of`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.reach_of_eq`.
