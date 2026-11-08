<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup.lean :: Complexity.LogProg.SavitchARM.ld_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponent-Loading Execution

**Claim.** Under the stated hypotheses on $k,j$, and the register state, there is a finite guarded run from the loading label indexed by $j$ to the power label. At the endpoint, $X=E$ and $P$ has increased by one, while every other register is unchanged.

**Proof.** Proceed by induction on $k$. When $k=0$, the equality $j+k=E$ gives $j=E$, so the loading instruction takes its final branch: it increments $P$ and moves to the power label. The resulting configuration is the required endpoint, and the one-step reach argument supplies the guard for the initial configuration. For the successor case, $k=k'+1$ implies $j<E$, so the loading instruction increments $X$ and advances the label to the index $j+1$. The modified state remains within the bound: its $X$ coordinate is $j+1\leq E\leq B$, and all other coordinates retain their bounds. The induction hypothesis, applied with index $j+1$ and remaining count $k'$, completes the run; the equalities $j+1+k'=E$ and the updated value $X=j+1$ give its required hypotheses. Prepending the initial step yields the full run. The reflexive reach fact handles the zero-length continuation in the base case (`Complexity.LogProg.AReach.refl`); one-step guarded execution is supplied by `Complexity.LogProg.SavitchARM.step_of`, and changing to the identified endpoint configuration is justified by `Complexity.LogProg.reach_of_eq`.

**Key facts.** `Complexity.LogProg.SavitchARM.step_of`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.reach_of_eq`.
