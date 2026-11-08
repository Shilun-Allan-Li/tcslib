<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_unary_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length-Indexed First Halting Times

**Claim.** Under the stated unary computation hypothesis, there is a time function indexed by input length that is bounded by $T$ and at which the normalized machine has computed the required output, with no earlier halt.

**Proof.** For each length $n$, the hypothesis ensures that $M$ halts on the all-ones word of length $n$ by time $T(n)$, using the computation characterization (`Turing.FinTM.computesInTime_iff`). Let $\tau(n)$ be the least time at which that run is halted, whose existence follows from this bound and the least-number principle. Its minimality gives $\tau(n)\le T(n)$ and says that the run is not halted at any smaller time. At time $\tau(n)$, the output agrees with the output at time $T(n)$ because output is unchanged after halting (`Turing.MultiTapeTM.runFrom_output_eq_of_halt`). Thus $M$ computes $f(n)$ at time $\tau(n)$: its state is halted by construction, and its output is the one guaranteed at time $T(n)$. For any word $x$, take this same time at $n=|x|$. The computation-transfer result (`Complexity.b2_unary_computes`) gives the required computation by the normalized machine on $x$. Finally, if that normalized run halted at some $s<\tau(|x|)$, the run correspondence (`Complexity.b2_unary_run`) and initial-configuration identity (`Complexity.b2_unary_initial`) would identify its state with the state of $M$'s unary run at $s$, contradicting the minimality of $\tau(|x|)$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_output_eq_of_halt`, `Complexity.b2_unary_computes`, `Complexity.b2_unary_run`, `Complexity.b2_unary_initial`.
