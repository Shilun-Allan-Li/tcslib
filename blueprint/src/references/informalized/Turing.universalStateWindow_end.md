<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalStateWindow_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Cell After an Exhausted State Window

**Claim.** The state window with $j$ consumed symbols and no remaining symbols is blank at cell $j+1$.

**Proof.** At cell $j+1$, the marker condition fails because this cell is positive. The interval condition also fails: with no remaining symbols, it would require $j+1\le j$. Thus the window returns blank there.
