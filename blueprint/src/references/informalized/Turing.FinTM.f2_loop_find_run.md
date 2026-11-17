<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_find_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Loop Search

**Claim.** Under the stated per-round conditions, the run from $c_0$ halts within $NB$ steps and outputs the payload at the first index below $N$ where $A$ holds, or the empty word if no such index exists.

**Proof.** Proceed by induction on the number $N$ of rounds, allowing the configuration sequence, acceptance test, and payloads to vary in the induction hypothesis. If $N=0$, the endpoint assumption says that $c_0$ is already halted with empty output, so zero steps suffice. For $N+1$, apply the round condition at index $0$, obtaining a duration $t\le B$. If $A(0)$ holds, this round already halts with output $P(0)$; its duration is at most $(N+1)B$, and index $0$ is the first accepting index, so it is the required output. If $A(0)$ fails, the run for $t$ steps reaches exactly $c_1$. Apply the induction hypothesis to the shifted sequence $j\mapsto c_{j+1}$, shifted acceptance test and payload, and the remaining $N$ rounds. It gives a further duration $s\le NB$ that halts with the correct first accepting payload among those rounds, or empty output if there is none. The run composition law (`Turing.MultiTapeTM.runFrom_add`) shows that running first for $t$ steps and then for $s$ steps is one run of length $t+s$ from $c_0$. Since $t+s\le B+NB=(N+1)B$, this meets the time bound. The list-search identity after removing a nonaccepting first entry shows that the shifted result is exactly the requested first payload, or the empty word.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
