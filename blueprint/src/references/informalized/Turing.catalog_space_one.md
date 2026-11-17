<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_space_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary Head Uses One Cell

**Claim.** If head $i$ is at position $0$ at every time, then it visits exactly one distinct cell through time $t$.

**Proof.** By definition, the visited positions are the image of the times from $0$ through $t$ under the function assigning the head's position. The hypothesis says this function is constantly $0$, so its image is the singleton containing $0$. The interval of times is nonempty, hence this singleton has cardinality one.
