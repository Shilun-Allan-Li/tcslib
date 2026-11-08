<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: cumLoss_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cumulative Loss Recurrence

**Claim.** For every round index $t$ and expert $i$, the cumulative loss through the first $t+1$ rounds is the cumulative loss through the first $t$ rounds plus the loss incurred at round $t$.

**Proof.** The set of round indices whose values are less than $t+1$ is the disjoint union of the indices less than $t$ and the singleton consisting of $t$. Indeed, an index below $t+1$ is either equal to $t$ or, if it is not, is less than $t$; conversely, either condition places it below $t+1$. Summing the expert's losses over this disjoint union splits the sum into the old prefix sum and the single term at round $t$, giving the claimed recurrence.
