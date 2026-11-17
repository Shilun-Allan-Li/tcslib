<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean :: Complexity.LogProg.pairSkip_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired-Word Skip Execution

**Claim.** Under the prescribed skip transitions and input-symbol conditions, the program scans the doubled word $u$ and its following separator $01$, ending at state $j_C$ with its input head advanced by $2|u|+2$. Throughout the run, the register head remains at $p$, only the state and input-head position change, and no visited state is an oracle-call state.

**Proof.** Proceed by induction on the word $u$. If $u$ is empty, the input hypotheses give the separator symbols $0$ and $1$. The first skip transition consumes the $0$ and enters $j_{P2F}$; the second consumes the $1$ and enters $j_C$. Each one-step transition is supplied by the skip-run calculation (`reaches_right`). The remaining run is reflexive (`Reaches.refl`), and composing these transitions while recording that their source states are not call states gives the required reachability (`Reaches.step`).

For $u=b::u'$, the input hypotheses give two consecutive copies of $b$. The first skip transition consumes the first copy and enters the false or true second-skip state according to $b$; that transition then consumes the second copy and returns to $j_{P1}$. The prescribed actions and the two input symbols justify these steps through `reaches_right`. The remaining input, starting two positions later, satisfies the same hypothesis for $u'$. Apply the induction hypothesis there, then prepend the two transitions using `Reaches.step`. This accounts for exactly two input positions per bit, followed by the two separator positions in the base case, and throughout preserves the specified configuration fields and excludes call states.

**Key facts.** `Complexity.LogProg.reaches_right`, `Complexity.LogProg.Reaches.refl`, `Complexity.LogProg.Reaches.step`.
