<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_poly_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Counter Run

**Claim.** Under the stated register bounds and initialization conditions, the program runs from the polynomial start state to the tail test when the outer parameter is true, and to the length bound otherwise. The final register vector is obtained by setting register 7 to $Fv_8^q$, leaving every other register unchanged.

**Proof.** First replace register 7 by $1$, calling the resulting vector $v'$. Since $v_8\ge 1$, we have $1\le v_8^q\le B$, so every entry of $v'$ is still bounded by $B$; the other zero-register conditions are unchanged. The program's first instruction at the polynomial start increments register 7, taking this initial configuration to the power-loop state with register vector $v'$. Apply the power-loop run result (\texttt{comp\_power\_run}) with exponent $q=e+1$ in the outer case and $q=e$ otherwise. For $v'$, its product invariant $v'_7v_8^q$ is exactly $v_8^q$, and the hypotheses on $v_8^q$ and $Fv_8^q$ supply the required bounds. That result reaches the desired endpoint and sets register 7 to $Fv'_7v_8^q=Fv_8^q$, preserving the other registers. Finally, the reachability step principle (\texttt{AReach.step}) prefixes the initial increment to this run; the machine's instruction admissibility follows from \texttt{comp\_preS}, and the register bound at the starting configuration is the given bound.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.comp_power_run`, `Complexity.comp_preS`, `Complexity.LogProg.AReach.step`.
