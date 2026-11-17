<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.unit_mul_epsilon_far -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Farness Under Unit Scaling

**Claim.** If $f$ is normalized and $\varepsilon$-far from linear, then $x\mapsto j f(x)$ has the same properties for every unit $j$.

**Proof.** Write the farness assumptions as normalization, the bounds on $\varepsilon$, and the distance lower bound for every linear comparison map. Normalization is preserved because $f(0)=0$. For any linear map $g$, compare $j f$ with $g$: multiplying both values by the inverse unit shows that they agree at exactly the inputs where $f$ agrees with $j^{-1}g$. The latter comparison map is linear, since multiplication by a fixed scalar preserves additivity. Thus the disagreement counts, and therefore the distances, are equal; the original farness hypothesis supplies the required lower bound.
