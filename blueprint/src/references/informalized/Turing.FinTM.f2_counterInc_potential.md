<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counterInc_potential -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment Potential Identity

**Claim.** For every finite Boolean list $b$, the number of true entries after incrementing, plus the number of leading true entries before incrementing, equals the original number of true entries plus one.

**Proof.** Induct on the list. For the empty list, incrementing adds one true entry and the carry count is zero. If the first entry is false, incrementing changes it to true and leaves the tail unchanged, while the carry count remains zero; thus the total number of true entries increases by one. If the first entry is true, incrementing changes it to false and recursively increments the tail, while the carry count is one plus the tail's carry count. The induction identity for the tail then gives the stated equality after collecting these contributions.
