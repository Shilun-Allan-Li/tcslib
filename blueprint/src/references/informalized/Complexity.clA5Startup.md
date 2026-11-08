<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Startup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Startup to the First Anchor

**Claim.** For the given machine and constants, there are finite machines $S,J$ and polynomial bounds such that the packed producer word has polynomial length and the five-module host reaches its designated initial anchor configuration within the stated time bound, without visiting the anchor state earlier.

**Proof.** Choose the packed-record producer $S$ and its polynomial time bound using the packed-installation result (\texttt{clA5Packed\_install}); choose the cursor initializer $J$ and its polynomial bound using the cursor-installation result (\texttt{clA5Cursor\_install}). The machine that computes the packed records also supplies a polynomial length bound $a_H(|x|+1)^{d_H}$ for those records (\texttt{clPackedRecords\_machine}). These choices establish the required size bound.

For arbitrary modules $E,I$, run the host through three calls in sequence. First the input-copying module takes at most $2|x|+3$ steps to copy $x$ onto its tape and halt (\texttt{clA5Copy\_clean}); the host call lemma turns this into a host run from module 0 to module 1 with the same tape result and no intervening visit to the loop anchor (\texttt{clA5Host\_call}). Next call $S$: the clean-host lemma applies its polynomial bound to write the packed-record word and return to module 2 (\texttt{clA5Host\_clean}). Then call $J$ on that word: the same clean-host lemma writes the empty unary cursor and transitions to the loop anchor, with duration bounded by $a_J(|\text{packed records}|+1)^{d_J}$.

The bound on packed-record length gives $a_J(|\text{packed records}|+1)^{d_J}\le a_J(a_H(|x|+1)^{d_H}+1)^{d_J}$. Add the three durations using run composition (\texttt{Turing.MultiTapeTM.runFrom\_add}). The anchor-guard lemma (\texttt{clA5\_guard\_add}) combines the no-earlier-anchor guarantees for the successive segments. The resulting final configuration is the required packed word with empty cursor in the loop-anchor state; the module tape bound needed for the host follows from \texttt{clA5Modules\_bound}.

**Key facts.** `Complexity.clA5Packed_install`, `Complexity.clA5Cursor_install`, `Complexity.clPackedRecords_machine`, `Complexity.clA5Copy_clean`, `Complexity.clA5Host_call`, `Complexity.clA5Host_clean`, `Complexity.clA5Modules_bound`, `Complexity.clA5_guard_add`, `Turing.MultiTapeTM.runFrom_add`.
