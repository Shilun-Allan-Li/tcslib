# Layered.rec_spec proof candidate

The supplied fragment preserves the frozen header and full docstring byte for byte.
It has 26 lines, maximum width 85, one tactic block and no admission. The only substantive
source theorem used is forward_action, which the lead now reports native PASS. No
backward-action, privacy, count, coordinate or security admission is consumed.

Exact public reuse:

- PartialGarbling.pgbCore_eq, Defs:94, reads the two garbling blocks.
- Layered.rec_inl / rec_inr read reconstruction at each Sum injection. The local hrec
  combines those readers using the existing core Sum.elim_comp_inl_inr (Sum/Lemmas:122)
  and function congruence. It does not reprove generic Sum eta by cases.
- sumElim_dotProduct_sumElim, Data/Matrix/Mul:123, splits both block dot products.
- Matrix.dotProduct_mulVec, Data/Matrix/Mul:710, transfers vecMul onto forward values;
  matrix_eq identifies its input, and forward_action supplies the reconstructed vector.
- The local ht is just the same public block dot-product theorem and Sum eta applied
  to t. dotProduct_zero' (Mul:104) and zero_add remove its auxiliary zero block.
- sub_dotProduct (Mul:225) distributes the output mask; sub_add_cancel cancels it.

The initial reader bridges consume no foreign TCSlib body. The final change reduces
only core/Mathlib function composition and pointwise subtraction. Every rw/simp item is
a reader or theorem, and no generic finite-sum or matrix action proof is duplicated.
No additional import is needed. The source remains valid at p=1 and all zero dimensions.

The agent ran no Lean, lake, Git, live edit or proof checker. The lead subsequently
reported native PASS for rec_spec. Focused searches are in Layered.rec_spec.searches.txt. No new helper statement
or proof is introduced by the reconstruction fragment; the separate PrefixAlgebra
proposals remain unproved pending the lead's exact?/apply? searches.
