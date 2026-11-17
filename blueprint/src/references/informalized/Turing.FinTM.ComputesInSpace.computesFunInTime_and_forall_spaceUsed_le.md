<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time and Space Bounds from Space-Bounded Computation

**Claim.** If the machine computes every output using space at most $s(|x|)$, then it computes within $\mathrm{configBound}(|x|,s(|x|))$ steps, and its space use at every time on input $x$ is at most $s(|x|)$.

**Proof.** Fix an input $x$ and choose a halting time $t$ from the space-bounded computation hypothesis. At that time the machine outputs $f(x)$ and uses at most $s(|x|)$ cells. The configuration-count bound therefore yields computation of the same output within $\mathrm{configBound}(|x|,s(|x|))$ steps (`ComputesInTime.of_spaceUsed_le`). This establishes the time-bounded computation assertion for each input. For the second assertion, apply the fact that once a computation halts, its configuration—and thus its space use—remains unchanged at all later times; the space bound at the chosen halting time consequently holds at every time (`ComputesInTime.spaceUsed_le_of_halt`).

**Key facts.** `Turing.FinTM.ComputesInTime.of_spaceUsed_le`, `Turing.FinTM.ComputesInTime.spaceUsed_le_of_halt`.
