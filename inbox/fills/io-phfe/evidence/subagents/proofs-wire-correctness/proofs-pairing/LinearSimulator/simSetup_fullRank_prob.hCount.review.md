# hCount local fill: exact scalar specialization

Proof-only replacement for hCount's term sorry. The `by` line is followed by FOUR-space
body indentation, matching the local proof's insertion point. Exactly one tactic block,
no new helper/import/definition or admission. No Lean/lake/Git command or live source
edit was run. Native validation remains pending.

Only scalar algebra after the now-proved shared GL-probability theorem is supplied.
ZMod.card specializes field cardinality to the public prime order q. Fin.prod_univ_three
expands the EXISTING finite product; the change step reads the closed Fin-3 indices
0,1,2 and closed exponent 3*3=9, without using any TCSlib definition body.

The three natural-subtraction casts are justified separately:
- 1 <= q^3 by one_le_pow0;
- q <= q^3 by le_self_pow0;
- q^2 <= q^3 by pow_le_pow_right0.
All use q>=2 from the ORIGINAL pp.group.order_prime; no new rank/counter/probability
claim or weaker estimate is introduced. Nat.cast_sub is used before field_simp/ring.
The result remains exactly (1-1/q)*(1-1/q^2)*(1-1/q^3).

Rule 10: no public def is supplied to simp/rw/unfold. q is a local abbreviation of the
public structure field; K is the existing local ZMod alias. The only supplied rewrites
are published ZMod/Fin/natural-cast/power equations and local proved inequalities.
There is no copy of Matrix.card_GL_field, unit-subtype/range cardinality, ambient
matrix cardinality, a uniformity law, or a sampler. Those remain in the shared theorem.

Static exact API reads:
- Mathlib/Data/ZMod/Defs.lean:164 ZMod.card.
- Mathlib/Algebra/BigOperators/Fin.lean:115 Fin.prod_univ_three.
- Mathlib ordered power laws one_le_pow0, le_self_pow0, pow_le_pow_right0.
- Current live hCount statement and its unchanged local K := ZMod pp.group.order.
No mathematical obstruction found. hBasis is root-owned/pending its reindented check.
