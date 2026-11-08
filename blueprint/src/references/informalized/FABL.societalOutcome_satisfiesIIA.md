<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.societalOutcome_satisfiesIIA -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of irrelevant alternatives

**Claim.** The social outcome defined by applying $f$ to each contest's pairwise votes satisfies independence of irrelevant alternatives: if two profiles give the same individual votes in a contest, their social outcomes in that contest agree.

**Proof.** Fix a contest and two ranking profiles whose vectors of individual votes in that contest are equal. The social outcome in the contest is obtained by applying the same function $f$ to each profile's vote vector. Equal inputs to a function have equal outputs, which proves the required agreement.
