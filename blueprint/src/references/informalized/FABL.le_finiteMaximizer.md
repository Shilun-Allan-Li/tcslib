<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.le_finiteMaximizer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum on a finite set

**Claim.** For a finite nonempty set $\Omega$, every value of a real-valued function on $\Omega$ is at most its value at the chosen maximizer.

**Proof.** A real-valued function on a finite nonempty set attains a maximum. The chosen maximizer is accompanied by the defining property of that maximum: for every $x\in\Omega$, $f(x)\le f(\mathrm{finiteMaximizer}(f))$.
