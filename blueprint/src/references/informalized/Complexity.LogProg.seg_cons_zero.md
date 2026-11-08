<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.seg_cons_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Segment Lookup at the Head

**Claim.** For any segment $s$ and list of segments $R$, looking up position zero in $s :: R$ returns $s$.

**Proof.** By definition, segment lookup at position zero uses the list’s default lookup at index zero. For a nonempty list $s :: R$, index zero selects its head, so the result is $s$.
