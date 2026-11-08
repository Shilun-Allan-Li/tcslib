<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigmaEXP.lean :: Complexity.Meyer.exists_compl_decider -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time-bounded complementation

**Claim.** If a finite Boolean-alphabet machine decides a language within time T, another such machine decides its complement within a bound of the stated form.

**Proof.** Use the given decider as a function-computing machine that outputs the one-bit membership indicator of the language. A second machine computes the function that maps the one-bit word [true] to [false] and every other word to [true]; this function is computable in time proportional to its input length plus one (computesFunInTime_ifEq). The time bound for this second computation is monotone. Composing the two machines therefore computes the complemented indicator, with a bound of the form $b(T(n)+a(T(n)+1)+1)$ for natural constants $a,b$ (computesFunInTime_comp). For each input, split according to whether it belongs to the original language. In the membership case the first machine outputs [true], which the second changes to [false]; outside the language it outputs [false], which the second changes to [true]. These are precisely the complement's membership indicators, so the composite decides the complement within the claimed bound.

**Key facts.** `Turing.FinTM.computesFunInTime_ifEq`, `Turing.FinTM.computesFunInTime_comp`.
