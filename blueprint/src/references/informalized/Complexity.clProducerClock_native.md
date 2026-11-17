<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clProducerClock_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Producer Clock

**Claim.** For any natural numbers $C,e,c,A,d$, the unary word of length $c\bigl(A(|x|+C(|x|+1)^e+1)^d+1\bigr)^2+1$ is polynomial-time computable as a function of the bit string $x$.

**Proof.** First compute the preparation header from $x$ using the polynomial-time preparation-header construction (`Complexity.clPrepHeader_native`). Compose this with the header-tail constructor (`Complexity.clHeaderTail_native`), whose parameter is $5$. The composition principle for polynomial-time computable functions (`Complexity.PolyTimeComputable.comp`) shows that the resulting header-tail word is polynomial-time computable. Append a fixed number of true bits, using the constant-word machine (`Turing.FinTM.computesFunInTime_const`) and the closure of polynomial-time computability under append (`Complexity.clNative_append`). The pair decoding identity (`Turing.pairDecode_pairEncode`) identifies the composed construction’s decoded component with the desired unary word; expanding the preparation-header length and adjoining the final single bit gives the stated length.

**Key facts.** `Complexity.clPrepHeader_native`, `Complexity.clHeaderTail_native`, `Complexity.PolyTimeComputable.comp`, `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_append`, `Turing.pairDecode_pairEncode`.
