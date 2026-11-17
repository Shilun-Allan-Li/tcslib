<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_unused_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Used by an Added Tape

**Claim.** If the original machine has no work tapes, adjoining one blank stationary work tape makes the space used equal to one at every time $t$.

**Proof.** The added-tape simulation commutes with each source step (`unusedTape_step`), so the run-commutation result (`runFrom_comm_of_step`) identifies its configuration at every time $u$ with the image of the source configuration. Under this embedding the added tape’s head position is constantly $0$. Therefore, among times $0,1,\ldots,t$, the set of positions visited by that tape is the singleton $\{0\}$: the time range is nonempty, including when $t=0$, and every image under the constant head-position map is $0$. Its cardinality, which is the space used by this sole work tape, is consequently $1$.

**Key facts.** `Turing.FinTM.unusedTape_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
