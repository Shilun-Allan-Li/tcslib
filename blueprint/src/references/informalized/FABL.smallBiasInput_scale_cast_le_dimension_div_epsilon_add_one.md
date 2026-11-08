<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.smallBiasInput_scale_cast_le_dimension_div_epsilon_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ceiling bound for the input scale

**Claim.** For positive integers $n,a,c$ with $2a\le c$, if $\varepsilon=a/c$ and $s=\lceil nc/a\rceil$, then $s\le n/\varepsilon+1$.

**Proof.** First use the natural-number ceiling-division formula $s=(nc+a-1)/a$. The division inequality $((nc+a-1)/a)a\le nc+a-1$, followed by $nc+a-1\le nc+a$, yields $sa\le nc+a$. Casting this inequality to the reals preserves its order. Since $a>0$, divide by $a$ to obtain $s\le nc/a+1$. Finally, with $\varepsilon=a/c$ and $c>0$, the quotient $nc/a$ equals $n/\varepsilon$, proving the claim.
