<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDiag_inner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanned Symbol at an Interior Position

**Claim.** For every bit string $x$, control state $q$ among the six states or the halting state, output string $w$, and natural number $j<|x|$, a configuration with input head at position $j+1$ scans the bit $x_j$.

**Proof.** The configuration’s shifted head position has value $j+1$, so it is an interior position corresponding to list index $(j+1)-1=j$. The interior-position rule for reading the input says that a head at value $1+p$, with $p<|x|$, scans $x_p$ (`Turing.inputSymbolInner`). Taking $p=j$ gives the result.

**Key facts.** `Turing.inputSymbolInner`.
