<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean :: Complexity.LogProg.arm_reach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability simulation

**Claim.** Every finite register computation that reaches a new state and valuation without producing an answer can be simulated by the compiled tape machine, with the invariant holding at each earlier tape step.

**Proof.** Proceed by induction on the number $N$ of register steps. If $N=0$, equality of the initial and final abstract configurations identifies the initial state and valuation with the claimed endpoint. The compiled machine then takes zero steps, and there are no earlier steps at which to check the invariant. For the successor case, the hypotheses at time zero give the precondition and register-length bound needed to simulate the first instruction. The one-step simulation theorem (`arm_step`) supplies a tape run to the encoding of the abstract successor, together with the invariant at every intermediate tape step. The abstract successor cannot be a halted configuration: if it were, the register computation would remain halted, contradicting the stipulated endpoint with no answer. Thus the first step reaches some state and valuation with no answer. Apply the induction hypothesis to the remaining $N$ steps; its earlier-time hypotheses follow by shifting time by one using the successor law for register runs (`arun_succ`). Concatenate the first tape run and the remaining simulation using the run-addition law (`rrun_add`). A tape time before the concatenation point is covered by the one-step simulation; a later time is the first run followed by a time covered by the induction hypothesis. This proves the endpoint and the invariant throughout.

**Key facts.** `Complexity.LogProg.arun_succ`, `Complexity.LogProg.astep_cases`, `Complexity.LogProg.arm_step`, `Complexity.LogProg.rrun_add`.
