<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalStateTape_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of the State Tape Marker

**Claim.** The unary state tape encoding $n$ contains the marker bit $0$ at cell $0$, and no positive natural-number cell contains that marker bit.

**Proof.** Identify the unary state tape with the state window having zero consumed symbols (\texttt{Turing.universalStateWindow\_zero}). In that window, cell $0$ is assigned the marker bit. For any positive cell $j$, the marker case does not apply; the remaining condition for a cell to contain $1$ is false because the window begins strictly after zero and ends at $n$. Thus its content is not the marker bit.

**Key facts.** `Turing.universalStateWindow_zero`.
