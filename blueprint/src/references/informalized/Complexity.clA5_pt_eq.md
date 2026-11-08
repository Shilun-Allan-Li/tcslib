<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_pt_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Equality Test

**Claim.** For polynomial-time computable $f$ and a fixed bit word $w$, the function returning $[1]$ when $f(x)=w$ and $[0]$ otherwise is polynomial-time computable.

**Proof.** First, equality with the fixed word $w$ can be decided in linear time: the machine that outputs $[1]$ exactly when its input equals $w$ and outputs $[0]$ otherwise is polynomial-time computable, by the linear-time equality test ( `Turing.FinTM.computesFunInTime_ifEq`) and the linear-time-to-polynomial-time principle (`Complexity.clNative_linear`). Compose this test with the machine computing $f$. The composition theorem for polynomial-time computable functions (`Complexity.PolyTimeComputable.comp`) gives a polynomial-time machine that tests whether its input to the equality test, namely $f(x)$, equals $w$. Thus it returns the required one-bit word.

**Key facts.** `Turing.FinTM.computesFunInTime_ifEq`, `Complexity.clNative_linear`, `Complexity.PolyTimeComputable.comp`.
