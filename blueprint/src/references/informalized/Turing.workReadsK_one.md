<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.workReadsK_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read patterns for one work tape

**Claim.** The list of all read patterns for one Boolean work tape consists exactly of the constant functions with values blank, false, or true.

**Proof.** Unfolding the recursive definition at one tape gives the three possible head readings—blank, false, and true—each paired with the unique reading pattern on zero remaining tapes. The one-coordinate cons operation turns each of these into the constant function with that value, by the fact that consing onto the empty-coordinate function gives a constant function on a one-element index type ($\texttt{Turing.fin\_cons\_one}$). This identifies the two lists term by term.

**Key facts.** `Turing.fin_cons_one`.
