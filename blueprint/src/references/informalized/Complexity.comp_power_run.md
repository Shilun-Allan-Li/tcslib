<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_power_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power-Loop Register Update

**Claim.** For an admissible exponent index $k$ and the stated bounded initial register vector, the power loop reaches the length-bound state when the outer flag is false and the tail-check state when it is true. It changes register 7 to $F(v_7v_8^k)$ and preserves all other registers, while maintaining admissibility and the register bound before the endpoint.

**Proof.** Generalize the induction to the numerical value $n=k.val$, keeping both the index $k$ and register vector variable. For $n=0$, the power is $1$, so the target value is $Fv_7$. One power-loop instruction transfers control to the factor-copy loop, and the factor-loop result (\texttt{comp\_factor\_run}) multiplies register 7 by $F$ to reach the required endpoint. The admissibility and bound at the initial power-loop configuration follow from \texttt{comp\_preS} and the assumed register bounds; the reachability step principle (\texttt{AReach.step}) prefixes this instruction.

For the successor case, write $n+1=k.val$ and first change register 7 to $v_7v_8$, obtaining a vector $v'$. The current product bound follows from $v_8\ge1$: $v_7v_8\le v_7v_8^{n+1}\le B$. Also, $v'_7v_8^n=v_7v_8^{n+1}$. Apply the multiplication-loop result (\texttt{comp\_multiply}) to make precisely this register update and move to the power state with exponent index $k.val-1$, whose value is $n$. The induction hypothesis then applies to $v'$, since the zero-register conditions are preserved and the product and factor bounds are the original ones under the displayed identity. It multiplies the new register 7 by $Fv_8^n$, yielding $Fv_7v_8^{n+1}$ overall, and reaches the stated endpoint. Concatenating the multiplication run and the inductive run uses the reachability transitivity principle (\texttt{AReach.trans}); the starting instruction is again prefixed by \texttt{AReach.step}. The register update bound is maintained at intermediate updates by \texttt{register\_update\_le}, and instruction admissibility by \texttt{comp\_preS}.

**Key facts.** `Complexity.comp_preS`, `Complexity.comp_factor_run`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`, `Complexity.comp_multiply`, `Complexity.LogProg.AReach.trans`.
