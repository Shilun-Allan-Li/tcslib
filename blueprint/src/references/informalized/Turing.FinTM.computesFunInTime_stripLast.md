<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_stripLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic-Time Last-Marker Stripping

**Claim.** There are a finite Boolean Turing machine and a constant $c$ that, on every input, output the pair encoding of the parsed first component and the prefix of the second component before its last $1$ when that marker exists; otherwise the machine outputs the empty word. Its running time is at most $c(|x|+1)^2$.

**Proof.** First compute the second component of the parsed pair, using the pair-decoding machine. Apply the test that checks whether this component contains a $1$; on inputs of length $n$, the composition result bounds this stage by a constant multiple of the sum of the first machine's time, the test machine's time on its output, and one. The test output is a one-bit word recording whether a $1$ occurs. Next, use a conditional machine: when the test is false, output the fixed empty word; when true, apply the raw stripping machine to the original input. The marker-case lemma explains why this is correct: if the decoded second component has no $1$, stripping yields no result; if it has a $1$, write it as a prefix followed by a last $1$ and a trailing string of zeros. The lemma ensures that stripping the original pair encoding then returns the pair encoding of the first component and the prefix before that last marker. The pair-decoding reconstruction fact identifies the original input with this pair encoding. Finally, the composition and conditional bounds give a running time bounded by a constant times a linear function of $n+1$: each component runs in linear time in its input length, and the intermediate lengths are themselves bounded linearly in $n+1$. Since $n+1\le(n+1)^2$, enlarging the constant yields the claimed quadratic bound.

**Key facts.** `Turing.FinTM.computesFunInTime_pairSnd`, `Turing.FinTM.anyTrue_computes`, `Turing.FinTM.computesFunInTime_comp`, `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.rawStrip_computes`, `Turing.FinTM.computesFunInTime_cond`, `Turing.FinTM.catalogMarker_cases`, `Turing.eq_pairEncode_of_pairDecode`, `Turing.FinTM.ComputesInTime.mono`.
