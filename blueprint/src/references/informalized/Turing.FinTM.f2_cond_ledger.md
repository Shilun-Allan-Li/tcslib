<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_cond_ledger -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Conditional machine head ledger

**Claim.** If $D$ computes $[b]$ on $x$ in exactly $T$ steps, then at each time $u$ the conditional machine's work-head vector is assembled from the head positions of $D$ at some $v\le T$, the selected branch machine at some $w\le u$, and a final coordinate $z\in[0,1]$.

**Proof.** Take the first time $d$ at which $D$ is halted. Since it is halted at time $T$, $d\le T$. The computation characterization (\texttt{Turing.FinTM.computesInTime_iff}) gives halting at $d$; uniqueness of output across computation times (\texttt{Turing.FinTM.ComputesInTime.output_unique}) then shows that the output at $d$ is $[b]$. Before time $d$, the conditional machine simulates $D$ while its output is recorded on an extra tape; the capture and control initialization facts (\texttt{Turing.FinTM.f2_timed_capture}, \texttt{Turing.FinTM.f2_timed_control_init}) justify this phase.

For a given $u$, split into phases. If $u\le d$, take the simulated time $v=u$, branch time $w=0$, and final coordinate equal to the length of $D$'s output so far; the output-prefix property (\texttt{Turing.MultiTapeTM.output_prefix}) bounds that length by $1$. If $d<u\le d+2$, the machine is in its two-step read phase; the read-head description (\texttt{Turing.FinTM.f2_timed_read}) and its head-position bound (\texttt{Turing.FinTM.f2_read_heads}) supply the final coordinate in $[0,1]$. If $d+2<u\le d+2+r$, where $r$ is the rewind duration, the rewind-head lemma (\texttt{Turing.FinTM.rewind_heads}) shows the other head positions stay fixed and the final coordinate remains in $[0,1]$. After this phase, the machine runs the selected branch from its initial configuration; the branch simulation identity (\texttt{Turing.FinTM.f2_timed_branch_run}) expresses its heads as those of the branch after $u-(d+2+r)$ steps. In every case the chosen indices satisfy $v\le T$ and $w\le u$, giving the asserted decomposition.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.FinTM.f2_timed_control_init`, `Turing.FinTM.f2_timed_capture`, `Turing.MultiTapeTM.output_prefix`, `Turing.FinTM.f2_timed_read`, `Turing.FinTM.f2_read_heads`, `Turing.FinTM.rewind_heads`, `Turing.FinTM.f2_timed_branch_run`.

**Caveat.** The source also relies on helper facts not listed in the upstream data (including the detailed control/read head identities and configuration equalities), so their precise statements are not available here.
