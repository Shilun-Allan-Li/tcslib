<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.seg_cons_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Segment Lookup

**Claim.** For any segment $s$, list of segments $R$, and natural number $i$, looking up position $i+1$ in $s::R$ returns the segment at position $i$ in $R$.

**Proof.** The lookup at position $i+1$ in a cons list skips its head and looks up position $i$ in the tail. This is precisely the stated equality.
