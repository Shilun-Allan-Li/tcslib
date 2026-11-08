<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitSource_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Source Output

**Claim.** For natural numbers $c,C$ and a Boolean word $s$, the specified unary-output machine, started in the bank configuration on input $s$ in the loop state indexed by $c$, halts after $\mathrm{cost}(|s|+1,C,c+1)+1$ steps with output consisting of exactly $C(|s|+1)^{c+1}$ copies of true.

**Proof.** Set $q=|s|+1$, which is positive. The loop-end theorem (`f2_splitPoly_loop_end`) gives the machine's configuration after the prescribed cost: it is in the final advance state, its output is the word of $Cq^{c+1}$ true symbols, and one additional step halts it. The bank configuration in the claim agrees with the canonical configuration used by that theorem when the input bank is $s$; unfolding those configuration descriptions therefore identifies their tape contents, head positions, and output. Substituting $q=|s|+1$ yields the claimed exponent and output length.

**Key facts.** `Turing.FinTM.f2_splitPoly_loop_end`.
