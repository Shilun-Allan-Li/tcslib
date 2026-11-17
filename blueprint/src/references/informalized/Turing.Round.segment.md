<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Round.segment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Round Is a Segment

**Claim.** If $c$ and $c'$ form a round of duration $t$ and $\mathrm{some}(a)\notin E$, then the run from $c$ to $c'$ is a segment of duration $t$: before the endpoint its state avoids $E$, and through the endpoint its work-head positions satisfy $P$.

**Proof.** The round already supplies the endpoint equation and the property $P$ at every time through $t$. It remains to show avoidance of $E$ at times $u<t$. If $u=0$, the run is still at $c$ by the zero-time run identity (`Turing.MultiTapeTM.runFrom_zero`), so its state is $\mathrm{some}(a)$, which is outside $E$ by hypothesis. If $u>0$, the round condition excludes the round-stop set at time $u$, and hence excludes $E$, which is contained in that set. These are exactly the remaining segment conditions.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`.
