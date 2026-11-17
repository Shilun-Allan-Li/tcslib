<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.workReadsK_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read patterns for two work tapes

**Claim.** The list of all read patterns for two Boolean work tapes is the nested list formed by choosing independently a blank, false, or true reading for each tape, assigning the first choice to tape $0$ and the second to tape $1$.

**Proof.** Expand the recursive definition for two tapes. It first chooses the reading $w_0$ on tape $0$, then expands the one-tape patterns to choose a reading $w_1$ on tape $1$. The one-tape cons operation gives the constant function with value $w_1$ on the remaining coordinate ($\texttt{Turing.fin\_cons\_one}$); consing $w_0$ in front of that function yields precisely the function assigning $w_0$ to index $0$ and $w_1$ to index $1$ ($\texttt{Turing.fin\_cons\_two}$). Hence the resulting nested list has the asserted entries and order.

**Key facts.** `Turing.fin_cons_one`, `Turing.fin_cons_two`.
