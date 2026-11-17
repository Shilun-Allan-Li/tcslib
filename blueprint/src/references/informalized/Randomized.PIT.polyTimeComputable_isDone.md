<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_isDone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Completion Recognition

**Claim.** The function returning $[1]$ exactly when the input is empty or consists of the single bit $0$, and $[0]$ otherwise, is polynomial-time computable.

**Proof.** The empty-input predicate is polynomial-time computable (`polyTimeComputable_isNil`). For the second condition, first drop the initial bit, an operation that is polynomial-time computable (`polyTimeComputable_drop`); test whether the remainder is empty by composing with the empty-input predicate (`Complexity.PolyTimeComputable.comp`). The first bit, treated as false when absent, is polynomial-time computable (`polyTimeComputable_headD`), so its negation is too (`polyTimeComputable_not`). Conjoining that negation with the test that the tail is empty recognizes precisely the singleton word $[0]$ (`polyTimeComputable_and`). Taking the disjunction with the empty-input predicate preserves polynomial-time computability (`polyTimeComputable_or`), giving the stated completion test.

**Key facts.** `Complexity.polyTimeComputable_isNil`, `Complexity.BinArith.polyTimeComputable_drop`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_headD`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_and`, `Complexity.polyTimeComputable_or`.
