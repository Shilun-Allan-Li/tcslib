<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.mem_PPoly_of_mem_DTIMEAdvice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advice Time Yields Polynomial Circuits

**Claim.** If a language has polynomially bounded advice and is decidable with that advice in polynomial time, then it has a family of fan-in-two Boolean circuits of polynomial size.

**Proof.** Fix the advice-deciding machine and let $T(n)=c_0(n^c+1)$ be its time bound. For each input length $n$, build a configuration circuit whose inputs are the $n$ input bits together with the $a(n)$ advice bits, arranged according to the paired-input layout. The circuit evaluation theorem (`Complexity.cfgCircuit_eval`) identifies its output with whether the simulated computation emits the accepting bit; the paired-layout evaluation and fixed-length advice facts (`Complexity.pairLayout_eval`, `Complexity.ofFn_getD`) identify this circuit's inputs with the actual encoded input and advice. Since the machine decides the language within time $T(n)$, the computation-to-output result (`Complexity.decide_emits_eq_of_computesInTime`) shows that, after hardwiring the advice for length $n$, the circuit accepts exactly the words in the language. The layout is valid by `Complexity.pairLayout_valid`, and the circuit has fan-in at most two by `Complexity.cfgCircuit_isFaninTwo`.

The size bound for configuration circuits (`Complexity.cfgCircuit_size_le`), together with the pair-layout length formula (`Complexity.length_pairLayout`), bounds the size in terms of $n$, the advice length, and $T(n)$. The assumed estimate $a(n)\le C(n+1)^d$ and the arithmetic bound (`Complexity.advice_size_le`) then give a fixed constant times $(n+1)^{2(c+d+1)}$. Hardwiring the advice preserves polynomial size and fan-in two (`Language.InPPoly.of_hardwire`). The resulting circuit family recognizes exactly the language, proving it belongs to polynomial-size circuit complexity.

**Key facts.** `Complexity.cfgCircuit_eval`, `Complexity.pairLayout_eval`, `Complexity.ofFn_getD`, `Complexity.decide_emits_eq_of_computesInTime`, `Complexity.pairLayout_valid`, `Complexity.cfgCircuit_isFaninTwo`, `Complexity.cfgCircuit_size_le`, `Complexity.length_pairLayout`, `Complexity.advice_size_le`, `Language.InPPoly.of_hardwire`.
