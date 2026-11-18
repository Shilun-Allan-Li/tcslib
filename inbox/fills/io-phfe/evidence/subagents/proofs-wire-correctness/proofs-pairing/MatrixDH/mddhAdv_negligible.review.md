# Conditional MDDH negligibility wrapper

Exact live opening prose/header preserved; one outer tactic block; no new helper, import,
machine/realiser construction, sampler, or admission. No Lean/lake/Git command or live edit
was run. This is a candidate only; root may defer integration until the main reduction is
proved, and no standard-axiom-only claim is made while dependencies remain admitted.

The proof eliminates the EXISTING mddhAdv_le existential advice family, then uses the
EXISTING mddhRealizable_iff reader to obtain its realiser B. It uses the SAME B in the
reduction bound and in dlinAssumption_iff; no independent reduction family is introduced.
The reader constrains RealizesOn only at the already frozen encoded challenge/layout
inputs, unchanged by this proof.

EXISTING EnsembleLemmas.negligible_polyExpr_mul handles d times B's DLIN advantage.
The EXISTING mddhSlack_subexpSmall at exponent 1/2 plus SubexpSmall.negligible handles
the exact 4d/p slack. Negligible.add/mono close the result. For mono's absolute-value
side condition, mddhAdv_eq plus EXISTING advantage_nonneg removes only the left absolute
value; the existing numerical bound followed by le_abs_self bounds the right. There is
no probability, polynomial absorption, decay, or negligibility theorem reproved locally.

Dependencies: the substantive mddhAdv_le reduction is provisional, and the restricted-import
primitive mddhSlack_subexpSmall candidate is pending root native checking. The former
cannot be bypassed by this closure proof. No CoinSampling import/reference appears.
No mathematical obstruction found in this conditional wrapper.
