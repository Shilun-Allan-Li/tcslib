<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bound from an interval of visited positions

**Claim.** If every head position through time $t$ lies in the integer interval $[lo,hi]$, then the number of distinct positions visited is at most $(hi+1-lo).toNat$.

**Proof.** The set of positions visited through time $t$ is the image of the times $0,1,\ldots,t$ under the head-position map. By hypothesis every such position lies in the integer interval $[lo,hi]$, so this image is a subset of that interval. Inclusion of finite sets cannot increase cardinality, hence the visited set has cardinality at most the interval’s cardinality. The cardinality formula for an integer interval gives $\lvert[lo,hi]\rvert=(hi+1-lo).toNat$ (`Int.card_Icc`), yielding the bound.
