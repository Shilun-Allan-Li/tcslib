<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_exists_loopFind_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound for Bounded Loop Search

**Claim.** Under the stated computation, invariant, startup, and round hypotheses, there are a finite Turing machine $E$ and a constant $c$ that compute the least accepted iterate's output, or the empty word if none is accepted, within time $c(T(|x|)+1)(R(|x|)+2)$ and use at most $c(T(|x|)+1)$ space at every time.

**Proof.** 1. Apply the loop-host construction theorem ($\texttt{f2_loopHost_contracts}$) with search mode enabled. It supplies a host machine and a constant $c$ with a startup configuration, a sequence of seam configurations indexed by the search rounds, bounds on the startup and each round, and bounds on the head positions at the seams. The invariant hypotheses ensure that every successive state remains eligible for the round hypothesis. The resulting host either halts with the requested output at an accepted round or advances to the next seam; after the prescribed number of rounds it halts with empty output.

2. Let $E$ be this host. The finite loop-search run theorem ($\texttt{f2_loop_find_run}$), applied to the sequence of seam configurations and the round behavior just obtained, shows that the search portion halts within $(R(|x|)+1)c(T(|x|)+1)$ steps and returns the output associated with the least accepted index, or empty output when there is none. Concatenating this run with the startup uses the run-addition law ($\texttt{Turing.MultiTapeTM.runFrom_add}$). The startup is at most $c(T(|x|)+1)$, so the total is at most $c(T(|x|)+1)(R(|x|)+2)$. If necessary, the computation-time monotonicity theorem ($\texttt{Turing.FinTM.ComputesInTime.mono}$) pads this run to the stated bound.

3. For space, the seam-space estimate ($\texttt{f2_seamed_space}$) bounds all visited work-tape positions by the number of tapes times the width of the interval reached from the seam positions during the bounded rounds. Its parameters here are the number of rounds $R(|x|)+1$, the per-round bound $c(T(|x|)+1)$, the startup bound, and the seam head bound $T(|x|)$. The elementary inequality in the proof absorbs this interval width into $(2(c+1)+1)(T(|x|)+1)$. Choosing the final constant to include both $c$ and this space factor gives the claimed time and space bounds simultaneously.

**Key facts.** `Turing.FinTM.f2_loopHost_contracts`, `Turing.FinTM.f2_loop_find_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_seamed_space`.
