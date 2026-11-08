<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.Reach.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Is Preserved by a Step

**Claim.** If a configuration is reachable by some finite word of choice bits, then taking one additional step with either choice bit produces another reachable configuration.

**Proof.** Choose a word $u$ witnessing that $C$ is reachable, so the run on $u$ has the same core and output summary as $C$. Extend the choice word by appending $b$. The run-on-concatenation law followed by the one-bit run equation identifies this extended run with taking the $b$-step after the run on $u$. Since equal core-and-summary data remain equal after applying the same choice step (`Turing.NDTM.coreSum_stepWith`), the resulting configuration has the same core and summary as the $b$-step from $C$. This extended word witnesses reachability.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`, `Turing.NDTM.coreSum_stepWith`.
