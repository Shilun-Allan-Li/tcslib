<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_model_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A complete read-model run

**Claim.** Starting in the initial read phase with register $s$ holding the binary representation of $0$, its head at $0$, and the input head at $1$, the read model reaches the exit state carrying $x[i]?$, with the head of $s$ at $0$. Before the endpoint, the output is unchanged, only register $s$'s tape may change, and the heads of $s$ and $r$ obey the stated bounds.

**Proof.** Build the run in two stages. First, by induction on $k\le\min(i,|x|)$, show that the program can reach the comparison phase at input position $k+1$ with register $s$ holding the binary representation of $k$. At $k=0$ the initial configuration already has this form. For the successor case, concatenate the inductive run with the one-position advancement supplied by `read_advance`; the run-addition law combines their times, and splitting at the earlier endpoint preserves the frame bound. This establishes the setup at $k=\min(i,|x|)$. Next apply `read_finish` to that setup, obtaining the exit state carrying $x[i]?$. Concatenate these runs once more with `rrun_add`. For times in the first stage use the inductive frame bound; for times in the second stage shift by the first-stage duration and use the frame bound from `read_finish`. The frame records the original output and allows only tape $s$'s contents to vary, while bounding both relevant heads.

**Key facts.** `Complexity.LogProg.read_advance`, `Complexity.LogProg.read_finish`, `Complexity.LogProg.rrun_add`.
