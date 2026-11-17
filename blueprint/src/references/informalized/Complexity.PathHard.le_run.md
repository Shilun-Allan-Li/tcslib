<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.le_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Comparison Routine

**Claim.** Starting at phase $0$ of either comparison routine with bounded registers and zero scratch, the program reaches the success continuation when the comparison-register value is at most the index, and the failure continuation otherwise; at that point the scratch register is the minimum of those two values. Every earlier configuration satisfies the program guard.

**Proof.** Apply the bounded comparison-loop result (`Complexity.Codec.le_loop`) with the decoding-and-comparison scratch register as the loop register, the chosen phase's register as the first comparison value, and the index register as the second. The two comparisons test whether the scratch value equals each comparison value; if neither test succeeds, the routine increments the scratch value and repeats. Thus it stops at the smaller value, taking the success continuation precisely when the first comparison value is at most the index. Initially the scratch is zero, so it is at most both comparison values. The register-separation lemma (`Complexity.PathHard.le_ne`) gives the required distinctness for the first value, and the scratch and index registers are distinct by their indices. The initial register bound and these inequalities are exactly the hypotheses ensuring the loop stays bounded and guarded; the loop result gives the stated endpoint and guards all earlier configurations.

**Key facts.** `Complexity.Codec.le_loop`, `Complexity.PathHard.St.Bd.toV`, `Complexity.PathHard.le_ne`.
