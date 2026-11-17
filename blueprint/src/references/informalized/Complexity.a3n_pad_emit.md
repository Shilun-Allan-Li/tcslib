<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_pad_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Padded Pair Emission

**Claim.** For any natural numbers $C$ and $c$, some finite Turing machine outputs the pair encoding of each input $x$ and the all-ones word of length $C(2^{|x|+1})^c$, within the stated polynomial bound in $|x|+C(2^{3(|x|+1)})^c+1$.

**Proof.** First, use the exponential scheduler (`Complexity.a2_exp_scheduler`) to produce the all-ones word of length $C2^{(|x|+1)^c}$, with running time at most $B(|x|+C2^{(|x|+1)^c}+1)^{c+2}$ for some constant $B$. Monotonicity of this time bound allows the pair-map construction (`Turing.FinTM.computesFunInTime_pairMapSnd`) to apply that scheduler to the second component of a decoded pair. Separately, pair duplication (`Turing.FinTM.computesFunInTime_pairDup`) produces $y=\operatorname{pairEncode}(x,x)$ in time at most $A(|x|+1)$. Composing these machines with the buffered composition theorem (`Complexity.a3n_comp_at`) yields a machine that, on $x$, outputs the pair encoding of $x$ and the scheduled all-ones word. Indeed, decoding the intermediate encoding recovers its two components (`Turing.pairDecode_pairEncode`), so the second-component map applies the scheduler to the intended copy of $x$. It remains to bound the composition time. Put $m=|x|+C2^{(3(|x|+1))^c}+1$ and $P=m^{c+2}$. Then $|x|+1\le m\le P$. The duplicated word has length $|y|=3|x|+2$, hence $|y|+1=3(|x|+1)$. Consequently $|y|+C2^{(|y|+1)^c}+1\le 3m$, so raising to the $(c+2)$nd power bounds the scheduler's polynomial expression by $3^{c+2}P$. The remaining duplication-time and composition-overhead terms are bounded by constant multiples of $P$ as well. Combining them gives the asserted bound with $K=A+5+D(3+B3^{c+2})$, where $D$ is the constant from the pair-map machine.

**Key facts.** `Complexity.a2_exp_scheduler`, `Turing.FinTM.computesFunInTime_pairMapSnd`, `Turing.FinTM.computesFunInTime_pairDup`, `Turing.pairDecode_pairEncode`, `Complexity.a3n_comp_at`, `Turing.FinTM.ComputesInTime.mono`.
