<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.boolCube_one_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The two points of the one-bit cube

**Claim.** Every point of the one-dimensional Boolean cube is either the constant-zero string or the constant-one string.

**Proof.** Evaluate the string at its sole coordinate, $0$. If that value is false, then the string agrees with the constant-zero string there; if it is true, it agrees with the constant-one string there. Since a function on $\mathrm{Fin}(1)$ is determined by its value at that coordinate, the corresponding equality holds in each case.
