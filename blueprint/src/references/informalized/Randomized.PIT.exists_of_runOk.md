<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.exists_of_runOk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accepted Circuit Encoding and Evaluation

**Claim.** If the run on the context and word $G$ is nonempty and done, then $G$ encodes a list of gates with backward references, and the run is the encoding of the same context, terminal word $[0]$, and the successive gate values modulo $\mathrm{bitsVal}(R)+1$.

**Proof.** First translate the assumption that the run is nonempty and done into the statement that its encoded word is exactly $[0]$: the run-state characterization identifies the run condition with the decision that its word is $[0]$ (`runOk_encState`). The run itself is represented by applying the abstract parsing step $|G|$ times to $(G,[])$ (`gateRun_eq`). Write the resulting state as $(w,vs')$. The accepted-word conclusion gives $w=[0]$, so the iterated-step theorem, with modulus $\mathrm{bitsVal}(R)+1$ and input assignment $i\mapsto\mathrm{ptVal}(P,i)$, supplies a gate list $gs$ encoded by $G$, with references below their positions and values $vs'=\mathrm{evalVals}(gs)$. Substituting this state into the run representation yields the claimed encoded state and evaluation.

**Key facts.** `Randomized.PIT.runOk_encState`, `Randomized.PIT.gateRun_eq`, `Randomized.PIT.exists_of_iterate_absStep`.
