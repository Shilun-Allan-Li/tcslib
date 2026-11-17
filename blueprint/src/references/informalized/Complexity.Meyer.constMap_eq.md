<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.constMap_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Transduction

**Claim.** For every Boolean bit $b$ and finite Boolean word $u$, the transducer that emits $b$ on each input symbol maps $u$ to the word of $|u|$ copies of $b$.

**Proof.** Induct on $u$. The empty word produces no output, agreeing with the empty replicate. If $u=c::u'$, the transducer emits exactly one $b$ on reading $c$, then processes $u'$; by the induction hypothesis the latter output is $|u'|$ copies of $b$. Prepending one copy gives $|u'|+1=|u|$ copies, as required.
