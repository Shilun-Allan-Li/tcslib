<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalStateWindow_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty State Windows Coincide

**Claim.** For each natural number $j$, the state window with $j$ consumed symbols and no remaining symbols equals the window with zero consumed symbols and no remaining symbols.

**Proof.** Compare the two windows at an arbitrary cell $z$. Both assign the marker at $z=0$. Away from zero, the interval condition for the first window would require $j<z\le j$, which is impossible; for the second it would require $0<z\le0$, also impossible. Both therefore return blank at every other cell, so the windows agree everywhere.
