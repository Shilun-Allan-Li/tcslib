# Remaining three Polys bodies: mechanical review — NOT_RUN

Reviewed the corrected halfForm_eval, G1_eval and G3_eval_of_scaled bodies against
current Polys readers, including root's reported lessons from the first seven fills.
No Lean, source edit, git, cache or spawn was used. No corrected replacement is
necessary for the three requested mechanical issues; use the existing corrected
body paths recorded in scan.json.

1. No remaining dangling local have was found, INCLUDING bullet-prefixed have
   commands. The scanner now measures the column of the have keyword after an
   optional bullet, rather than matching only line-start have. G1_eval's `· have hd`
   is already assigned with `:=`; the other local have proofs already use `:= ?_`
   and `swap`. The nested half-pub `hc` that root caught was outside these three
   bodies and is now recorded as the reason for the improved scan.
2. No body constructs a standalone MvPolynomial.X term whose coefficient ring lacks
   an expected type. There are zero literal MvPolynomial.X constructors in these
   three proof strings: eval_X is a theorem name, not a constructor. Polynomial
   coefficients are pinned through halfForm/prgPoly or eval z and the field-valued
   assignment. Thus the prior degree-proof coefficient annotation issue does not
   recur textually here.
3. halfForm_eval reads linearCoeff through simp, which also performs constructor
   match reduction. It does not call rw [linearCoeff_eq] followed by split_ifs.
   Its remaining mechanical risks are dependent castSucc/last Fin witnesses and
   cancellation of the matrix-vector sum, not an exposed unreduced match.
4. G1_eval reads the lifted sum with rw but no pattern match follows those readers.
   Sorted-list optional reads are discharged by simp only with getElem? equations,
   so iota reduction is already available there. Fin product orientation and the
   final coefficient cast remain root elaboration checks.
5. G3_eval_of_scaled expands correctionPoly through both reader equations and then
   cases the optional position. Each constructor branch begins with simp (none)
   or simp only with evaluation equations (some), so constructor-match reduction
   is already requested. If root observes a residual match anyway, the minimal
   mechanical insertion is dsimp only at the start of that branch, before those
   simplifications. It is unnecessary to unfold correctionPoly or change a header.

Recorded root feedback for future candidates: reader rw alone need not reduce a
match; use dsimp only before split_ifs. Nested bullet-have commands need the same
assignment repair. When omega treats syntactically different cardinalities as
unrelated atoms, compose the existing inequalities directly and normalize through
their readers rather than adding an arithmetic assumption. These are root-reported
verification lessons, not Lean results produced by this review.

All three still have exactly one outer tactic block. No claim is made that their
other simplifier, cast, finite-product or ring steps elaborate successfully.
