<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample.lean :: BoolCircuit.AdjExample.leLang_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Comparison Language

**Claim.** For any Boolean values $a,b$, the language of encodings $\langle 1^n,\operatorname{bits}(i)\rangle$ with either $i<n$ and $a$ true, or $i=n$ and $b$ true, is decidable in logarithmic space.

**Proof.** Use the logarithmic-space closure result for arithmetic register programs with logspace oracle languages (`arm_decides_poly`). The program first checks that its input is a valid unary–binary pair with a canonical binary payload. On a valid input, rewrite that payload as $\operatorname{bits}(i)$ (`canon_eq_bits`), using that every natural number has a canonical bit word (`canon_bits`). The pair encoding and the bit representation uniquely determine $n$ and $i$ (`pairEncode_replicate_inj`, `bits_injective`), so the program’s membership indicator is exactly the desired Boolean condition. The program then enters its test loop; the strict-comparison oracle is logspace decidable (`ltLang_mem`). The loop lemma (`loop`) shows that the program halts with the required answer while maintaining the polynomial register bound. Prepending the initial valid-input check preserves halting and the space bound (`AHalt.step`). On an invalid input the desired indicator is false, and the program rejects immediately. Thus all inputs satisfy the correctness and space conditions required by `arm_decides_poly`.

**Key facts.** `Complexity.LogProg.arm_decides_poly`, `Complexity.LogProg.canon_eq_bits`, `Complexity.LogProg.canon_bits`, `Turing.pairEncode_replicate_inj`, `Complexity.LogProg.bits_injective`, `Complexity.LogProg.indicator_eq_decide`, `Complexity.ltLang_mem`, `BoolCircuit.AdjExample.loop`, `Complexity.LogProg.AHalt.step`.
