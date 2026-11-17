<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.transduce_fT_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying the Input Word

**Claim.** For every finite Boolean word $u$, the transducer with transition rule $fTδ$ and emission rule $fTo$, started in state $\mathrm{none}$, outputs $u$.

**Proof.** Proceed by induction on $u$. The empty word produces the empty output. For a word with first bit $b$ and remaining suffix $u'$, the initial state is `none`, so the emission rule outputs $b$ and the transition rule leaves the state at `none`. The transducer's output is therefore $[b]$ followed by its output on $u'$ from `none`. By the induction hypothesis that suffix output is $u'$, giving $b :: u'$.
