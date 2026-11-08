<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinStageRecords_covers -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage Record Coverage

**Claim.** At stage $k$, every Goldreich–Levin candidate has an estimate record with coordinates equal to the first $k+1$ coordinates and frequency prefix equal to that candidate.

**Proof.** Fix a candidate in the stated candidate family. The stage-record list is formed by mapping over the list of all candidates, assigning to each candidate a record with the prescribed coordinates and that candidate as its frequency prefix. Membership in the candidate family therefore gives membership of the corresponding candidate in the mapped list. By construction, the record’s coordinates and frequency prefix are exactly the required ones, so it matches the candidate.
