<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Decode_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Bounded Unary Decoding

**Claim.** If $f$ is polynomial-time computable and the unary representation of $N$ is polynomial-time computable, then outputting the unary representation of $\mathrm{clNum}(f(x))$ when it is at most $N(x)$, and the empty word otherwise, is polynomial-time computable.

**Proof.** First construct the initial decoding state for $f(x)$ at count zero. Since that state is the pair encoding of $f(x)$ and a fixed empty pair, it is polynomial-time computable from $f$ (`clA5DecodeState_zero`, `clNative_pair`, `clA5_pt_const`). Iterate the decoding step $N(x)$ times. The iterate is polynomial-time computable provided its intermediate states have polynomially bounded length (`clA5Iter_native`); here the orbit identity says the state after $j$ steps is the state at count $j$ (`clA5Decode_orbit`), and its length is at most $2|f(x)|+3j+4$ (`clA5Decode_size`). For $j\le N(x)$, this is bounded by a constant multiple of the square of the initial-state length plus $N(x)+1$: the initial state is at least as long as $f(x)$, and any positive integer is at most its square. Thus the iteration bound required by `clA5Iter_native` holds. The hypotheses provide polynomial-time computation of the decoding step and initial state, and of the unary representation of $N(x)$. After the iteration, extract the second header tail twice (`clHeaderTail_native`). Pair decoding recovers the encoded fields (`pairDecode_pairEncode`), so this tail is precisely the unary representation of $\mathrm{clNum}(f(x))$ when that value is at most $N(x)$, and empty otherwise, as required by the state definition.

**Key facts.** `Complexity.clA5DecodeState_zero`, `Complexity.clNative_pair`, `Complexity.clA5_pt_const`, `Complexity.clA5DecodeStep_native`, `Complexity.clA5Decode_orbit`, `Complexity.clA5Decode_size`, `Complexity.clA5Iter_native`, `Complexity.clHeaderTail_native`, `Turing.pairDecode_pairEncode`.
