<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Randomized.BPTIMEWith_subset_of_amp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplification of randomized decision

**Claim.** If the original randomized machine decides with acceptance probability at least $\tfrac12+\varepsilon$, then for $2(1-4\varepsilon^2)^n\leq\eta$ the language is decidable with acceptance probability at least $1-\eta$, with only a constant-factor increase in the time bound.

**Proof.** Take a language in the first class, witnessed by a machine running in time at most $cT$. Apply the amplification theorem for bounded-error machines (\texttt{Turing.FinNDTM.BPDecidesInTime.amp}) with parameter $n$. It gives an amplified machine with success probability at least $1-2(1-4\varepsilon^2)^n$, and running time $t(l)+2n(2t(l)+3)+1$, where $t(l)=cT(l)$. The hypothesis on $\eta$ makes this success probability at least $1-\eta$. For the time comparison, the original decision bound implies $1\leq cT(l)$ (\texttt{Turing.FinNDTM.BPDecidesInTime.one_le}). Thus the additive terms in the amplified runtime are bounded by a constant multiple of $cT(l)$, and the total is at most $(10n+2)cT(l)$. Monotonicity of the time bound and weakening the success threshold preserve the decision guarantee (\texttt{Turing.FinNDTM.BPDecidesInTime.mono}); the new constant factor is absorbed into the definition of the class.

**Key facts.** `Turing.FinNDTM.BPDecidesInTime.amp`, `Turing.FinNDTM.BPDecidesInTime.one_le`, `Turing.FinNDTM.BPDecidesInTime.mono`.
