<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_separator_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separator Search Run

**Claim.** From the first separator-search phase, the machine halts with the length predicate when mode is true, and otherwise returns the bit at position $p$ of the encoded output, with out-of-range positions interpreted as false; all earlier configurations satisfy the precondition and register bound.

**Proof.** Write $n=2|f(x)|$. The encoding of $f(x)$ paired with $b$ has length $n+2+|b|$ (`length_pairEncode`), and its bit at position $n$ is the first separator bit, false (`pairEncode_getD`). Hence the requested answer at $p=n$ is exactly the flag `mode`; the machine tests whether registers $13$ and $5$ agree and returns that flag. If $p\ne n$, it advances the separator index once. When $p=n+1$, the next position is the second separator bit, true, so the answer is true in either mode; the register update remains bounded by the assumed total-length bound. If $p\ge n+2$, the machine advances to the suffix-search setup. Register resets and copying preserve the bound, and the copy run (`comp_copy_run`) reaches the suffix-search state with the required registers. The suffix-search lemma (`comp_suffix_run`) then computes either the length predicate or the bit of $b$ at position $p-(n+2)$. The pair-encoding bit formula (`pairEncode_getD`) identifies this with the bit at position $p$ in the full encoding. Each transition is taken from a configuration satisfying the machine precondition, established by `comp_preS`; register updates preserve the bound by `register_update_le`. Composing the reachability segments and their final halting runs (`AReach.trans`, `AReach.halt`, `AHalt.step`) proves the claim in all cases.

**Key facts.** `Turing.length_pairEncode`, `Complexity.pairEncode_getD`, `Complexity.comp_preS`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.comp_copy_run`, `Complexity.comp_suffix_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.halt`.
