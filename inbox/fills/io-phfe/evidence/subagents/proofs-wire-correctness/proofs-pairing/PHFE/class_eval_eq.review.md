# PHFE class/typed scalar equality candidate

The exact live opening prose/header is preserved; one tactic block, no new helper/import
or admission. No Lean/lake/Git command or live edit was run. Native validation is pending.

The proof reads Quadratic.value_eq and applies the EXISTING PHFE.pgSound_iff semantic
reader. It then uses only published class/parameter/value/decoder equation readers, the
EXISTING phfeEval_eq diagonal embedding identity, and quadEval_eq.

The original f/x/y are retained verbatim. There is no encode-after-decode replacement,
canonical-word hypothesis, efficiency target, width coverage hypothesis, or assumption of
unique modular representatives. The three decoder width transports are discharged by
EXISTING finCongr_refl and reflexive-equivalence/function-composition readers: their
endpoint widths are definitionally the same numeric expressions (as exposed by the
existing PHFE publicWidth/privateWidth/functionWidth and Classes width readers).
No TCSlib public definition body is supplied to simp/rw.

phfeClass_eval_encoded is already proved but requires canonical encoded tensor inputs
and canonical residue word hypotheses. Applying it directly to this arbitrary-alias
statement would be inappropriate; the EXISTING total phfeClass_eval reader is the exact
interface here, followed by the already-proved typed diagonal embedding identity.

The likely native verification boundary is dependent codec/Fin-width normalization,
not a mathematical assumption. If a particular simplifier reader does not normalize
these proof-irrelevant width casts, use the already public finCongr_symm_apply_coe and
Fin.ext readers rather than adding a generic transport helper. No mathematical
obstruction was found.
