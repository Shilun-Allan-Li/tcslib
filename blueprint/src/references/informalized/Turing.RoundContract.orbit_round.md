<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.RoundContract.orbit_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit rounds and their head bounds

**Claim.** Under the stated precondition and return hypotheses, each orbit transition below index $n$ is a round of the prescribed duration, and throughout it every work-head position lies within the coordinatewise hull of the contract bounds below $n$ and the heads at orbit index $n$.

**Proof.** Fix $r<n$. First, the orbit anchor theorem (`Turing.RoundContract.orbit_anchor`) shows that the configuration at index $r$ starts in the anchor state. Apply the round contract’s round theorem (`Turing.RoundContract.round`) there: it gives the positive duration, prescribed endpoint, endpoint-state condition, exclusion of halted, anchor, and escape states at intermediate positive times, and the coordinatewise head bounds throughout the round. The endpoint of this round is the next orbit configuration, because `Turing.roundOrbit_succ` identifies that configuration with the run for the contract duration and the contract run equation identifies the run with the prescribed endpoint. It remains to place each head position in the larger hull. For coordinate $j$, the index $r$ belongs to the finite set of indices from $0$ through $n$. Since $r<n$, the lower-bound entry at $r$ in the hull is the contract’s lower bound for this round, and the upper-bound entry there is its upper bound. The round’s head envelope therefore places the position above that entry and below the corresponding upper entry. A finite infimum is no greater than any member, and a finite supremum is no less than any member; applying these facts at index $r$ places the position between the hull’s lower and upper bounds. This holds for each coordinate and each time in the round.

**Key facts.** `Turing.RoundContract.orbit_anchor`, `Turing.RoundContract.round`, `Turing.roundOrbit_succ`.
