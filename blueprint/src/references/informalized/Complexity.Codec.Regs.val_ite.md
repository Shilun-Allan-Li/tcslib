<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean :: Complexity.Codec.Regs.val_ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate of a conditional index

**Claim.** For every register record $R$, proposition $c$ with a decision procedure, and indices $r,r'\in\mathrm{Fin}(21)$, the coordinate value at the index selected by the condition is the corresponding conditional value: $R(r)$ if $c$ holds, and $R(r')$ otherwise.

**Proof.** Split on whether $c$ holds. In the true case the selected index is $r$, so both sides are $R(r)$; in the false case it is $r'$, so both sides are $R(r')$. Thus the equality holds in either case.
