<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitStep_cleanCall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time clean implementation

**Claim.** For each $M,C,e$, there are a finite-state binary machine $W$ with at least one work tape, entry and exit states, and natural numbers $a,d$ such that every input and argument has a clean, polynomial-time producer-step computation from entry to exit.

**Proof.** The producer-step function is polynomial-time computable ($\texttt{Complexity.clVisitStep\_native}$). Apply the clean-implementation theorem for polynomial-time functions ($\texttt{Complexity.clNative\_cleanCall}$). It supplies a machine with at least one work tape, entry and exit states, and a polynomial time bound. Its clean-call guarantee gives a positive halting time within that bound, excludes the exit state at all strictly intermediate positive times, and places the computed function value on the first tape at exit with the other tapes blank and the stipulated input-head position and empty output.

**Key facts.** `Complexity.clVisitStep_native`, `Complexity.clNative_cleanCall`.
