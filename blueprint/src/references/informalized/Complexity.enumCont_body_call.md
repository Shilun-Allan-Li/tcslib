<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a clean call

**Claim.** When the simulated machine halts after $T$ steps with output $y$, the body machine, started in the corresponding clean-call state, reaches the specified continuation state with the candidate preserved and $y$ in the capture tape, within the stated time bound.

**Proof.** Apply the clean-machine completion result to the simulated run. It supplies a time $r\le 3T+|x|+|y|+8$ at which the clean machine has reached its canonical exit configuration, with the output captured and the other required tape data in place (\texttt{Complexity.enumCont_clean_complete}). The clean-entry and clean-exit word descriptions identify the initial and final canonical configurations with the pair configurations in the claim (\texttt{Complexity.enumCont_clean_entry_words}, \texttt{Complexity.enumCont_clean_exit_words}). The clean run may first halt before time $r$; choose its first halting time $t\le r$. The first-halt lemma ensures that the configuration at $t$ already equals the configuration at $r$, and that all earlier configurations are nonhalting (\texttt{Complexity.enumCont_first_halt}). While the clean machine is nonhalting, the body machine follows each of its transitions through the return-state embedding. The return-run lemma gives equality of these runs at time $t$ (\texttt{Complexity.enumCont_return_run}). Combining these identifications yields the desired body configuration at time $t$, and $t\le r$ gives the asserted bound.

**Key facts.** `Complexity.enumCont_clean_complete`, `Complexity.enumCont_clean_entry_words`, `Complexity.enumCont_clean_exit_words`, `Complexity.enumCont_first_halt`, `Complexity.enumCont_return_run`.
