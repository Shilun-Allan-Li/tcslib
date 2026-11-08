<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.headBox_lastCases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on the last coordinate

**Claim.** If the last coordinate of $p$ lies in $[clo,chi]$ and each earlier coordinate lies in its specified interval $[lo_j,hi_j]$, then every coordinate lies in the interval determined by adjoining $clo,chi$ to the earlier lower and upper bounds.

**Proof.** Fix a coordinate of $p$. Every index in $\mathrm{Fin}(k+1)$ is either the last index or the cast of an index in $\mathrm{Fin}(k)$. In the last case, the assumed bound is exactly $[clo,chi]$, which is the interval assigned to that coordinate by the adjoined bounds. In the cast case, the assumed bound is $[lo_j,hi_j]$, again exactly the interval assigned by the adjoined bounds. These two cases prove the required coordinatewise bounds.
