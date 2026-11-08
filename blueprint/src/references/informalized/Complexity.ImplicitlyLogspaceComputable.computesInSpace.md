<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitlyLogspaceComputable.computesInSpace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space-bounded computation from implicit output data

**Claim.** A polynomial output-length bound, together with LOGSPACE decision procedures for the output-bit and output-length index languages, yields a finite-state deterministic machine computing $f$ in space bounded by a constant multiple of logarithmic input length.

**Proof.** 1. Let $C,e$ bound the output length by $F=C(|x|+1)^e$. Use the two given LOGSPACE deciders as oracles: one decides whether an index is within the output length, and the other decides its output bit. The encoding lemma `pairEncode_mem_indexLang` ensures that on the encoded query for $(x,i)$ these oracles return, respectively, the truth value of $i<|f(x)|$ and the bit $(f(x))_i$.

2. The implicit enumeration program requests these two answers while constructing the output. Its run theorem (`ImplicitEnum.run`) supplies a halting run whose output is exactly $f(x)$, and describes the shape of every pre-halting configuration. The bit-length estimate `length_bits_le_log` bounds the binary index strings it places on its query tape by $W=\lfloor\log_2(F+1)\rfloor+1$. The configuration description also bounds the program's work-head position between $-1$ and $W$ throughout the run.

3. Each oracle call is on an encoded pair of length at most $2|x|+2+W$. The two deciders can be combined into a bank of machines (`bank_cleanRun`), with space at most the larger of their individual bounds and one. Monotonicity of `logSpace` and the call-length estimate bound this by $B=(c_0+c_1)\,\mathrm{logSpace}(2|x|+2+W)+1$. The call-shape analysis uses `vword_call` to identify the query word and the stored index, and `CleanRun.mono` to raise the space allowance to $B$.

4. Compile the enumerating program together with this bank of deciders. The compiler bound (`compile_space`), using the run's halting/output facts, the work-head interval, and the call-space bound, gives a finite-state machine that outputs $f(x)$. Its total space is bounded by $W+2+k_D(2B+1)$, where $k_D$ is the number of work tapes in the bank. Finally, `log_poly_bound` bounds $W+2$ and the logarithmic cost of calls by constant multiples of $\mathrm{logSpace}(|x|)$: the polynomial bound on $F$ makes both $F$ and $2|x|+2+W$ polynomially bounded in $|x|+1$. Combining these estimates yields the claimed constant-factor logarithmic space bound.

**Key facts.** `Complexity.pairEncode_mem_indexLang`, `Complexity.ImplicitEnum.run`, `Complexity.LogProg.length_bits_le_log`, `Complexity.LogProg.tapeWord_bufferTape`, `Complexity.LogProg.bank_cleanRun`, `Complexity.LogProg.CleanRun.mono`, `Complexity.ImplicitEnum.vword_call`, `Complexity.logSpace_mono`, `Complexity.LogProg.compile_space`, `Complexity.LogProg.log_poly_bound`.
