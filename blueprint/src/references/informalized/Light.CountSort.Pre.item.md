<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CountSort.Pre.item -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of source items

**Claim.** Under the precondition and the agreement of the two memories outside the destination and counter ranges, every source item still has its specified value in the second memory.

**Proof.** Fix $i<A.n$. The precondition says the source and destination ranges are apart, and the source and counter ranges are apart. Thus the address $A.src+i$ lies outside both the destination range and the counter range. By the definition of agreement outside those ranges, the two memories have the same value there. The original memory contains $it(i)$ at that address, so the second memory does as well.
