<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: exists_circuit_depth_reduction_depth1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth-1 circuits collapse to a single signed gate

**Claim.** Let `c : Circuit m` have `c.depth = 1`, and let every gate function
`gates i` have a width-`l` DNF (`hDNF`) and a width-`l` CNF (`hCNF`). Then there are
`φ : DNF n` and `sign : Bool` with `φ.width ≤ l`, `φ` clean (per-term `varInj` and
`Nodup`), and `(if sign then φ.eval x else !(φ.eval x)) = c.eval (fun i => gates i x)`
for all `x`. So the whole depth-1 circuit is one width-`l` gate, up to a global sign.

**Proof.** Immediate specialisation of `child_depth_le1_has_signed_dnf` to `c` itself,
with the depth hypothesis `c.depth ≤ 1` supplied by `omega` from `c.depth = 1`. The
only work is reordering the conjuncts of the returned tuple
(`exact ⟨φ, sign, hw, hvi, hnd, he⟩`) so that the evaluation clause comes last.

**Used in.** The `D = 1` branch of `exists_circuit_depth_reduction`, where the single
gate is wrapped as `Circuit.lit ⟨0, sign⟩` over a one-element gate family.
