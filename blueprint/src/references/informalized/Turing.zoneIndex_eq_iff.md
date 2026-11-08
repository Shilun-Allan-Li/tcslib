<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneIndex_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of the Zone Index

**Claim.** For all natural numbers $s$ and $i$, the zone index of $s$ equals $i$ if and only if $2(2^i-1)\le s<2(2^{i+1}-1)$.

**Proof.** By the characterization of the base-two logarithm, the equality $\operatorname{Nat.log2}(s/2+1)=i$ is equivalent to $2^i\le s/2+1<2^{i+1}$. Subtracting one and accounting for integer division by two translates these inequalities into $2(2^i-1)\le s<2(2^{i+1}-1)$. These are precisely the lower and upper bounds defining the stated zone interval.
