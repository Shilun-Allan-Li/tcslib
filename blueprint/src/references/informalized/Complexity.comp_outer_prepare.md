<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_outer_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer Preparation Run

**Claim.** From the initial copy state on the encoded input, the counter program reaches the tail-test state with the specified register values, empty result, and register bound throughout.

**Proof.** Let $h=\langle z,t\rangle$, $a=2|z|+2$, and $B=8(2C+3)(|h|+1)^{e+1}$. The pair-encoding length formula gives $a\le |h|$, and the bound-room estimate ensures the polynomial capacity and all register values used below fit within $B$ (`Turing.length_pairEncode`, `Complexity.comp_bound_room`).

The first copy stage copies register 0 into register 2; the second copies register 2 into register 3. Each copy is valid because the destination does not exceed the source, and each run preserves the register bound (`Complexity.comp_copy_run`). Two decrement steps then reduce register 3 from $a$ to $2|z|$. The next copy stage transfers register 1, which is $|h|$, into register 8. Increment register 8 once to obtain the base $|h|+1$. Starting from zero in register 7, the polynomial subroutine computes $(2C+3)(|h|+1)^{e+1}$ there and ends at “tail test.” Its hypotheses follow from the base being positive, the unused registers being zero, and the power-bound estimate (`Complexity.comp_power_bound`, `Complexity.comp_poly_run`).

The intermediate vectors are all instances of the displayed register template with entries at most $|h|+1$, hence are bounded by $B$. The bookkeeping transitions preserve safety, and composing the stage runs yields the required endpoint and empty result (`Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`, and `Complexity.LogProg.AReach.refl`).

**Key facts.** `Turing.length_pairEncode`, `Complexity.comp_bound_room`, `Complexity.comp_copy_run`, `Complexity.comp_power_bound`, `Complexity.comp_poly_run`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.refl`.
