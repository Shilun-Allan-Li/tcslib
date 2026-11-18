# Probe/step error history

Initial overlap CLI call left exact? unquoted for zsh and failed to materialize
its file. No search occurred. The resulting missing-file failure was reproduced
byte-exactly after archival; see evidence/overlap/reproduced-missing/note.json.
The quoted real exact? search correctly reported no closing proof.

Step006: isWeightedHomogeneous_X has an explicit coefficient-ring argument R, unlike the preceding C theorem. Passing R first fixes the application type mismatch; source/API location verified. Failed source/log retained.

Step037: Lean parser requires `:= ?_` before bullet proofs of local have declarations. Added placeholders discharged immediately in the same existing tactic block; no statement change. Original failed source/log retained.

Step037 repair2: rw tried the first (left) absolute value with a right-side nonnegativity proof. Use the public Nat.abs_cast simplification after the norm reader instead.

Step037 repair3: a local have assigned an explicit hole puts the continuation goal first. Select the proof goal with swap before each bullet; retains one tactic block. Nat.abs_cast resolved the previous absolute-value issue.

Step039: Function.Injective quantifies the second list implicitly, so the induction hypothesis takes the equality argument directly. Removed explicit ys; statements unchanged.

Step044: Rat.cast_le leaves a casted rational one in the inferred real exponent. State the real δ≤1 bound explicitly and exact_mod_cast the rational hypothesis, then use rpow_one.

Step044 repair2: rpow_mul_natCast introduces a casted natural two. Normalize it with Nat.cast_ofNat and type two_ne_zero in ℝ before cancellation.

Step049: corrected the staged candidate local-have syntax with an assigned goal and swap, as in step037.

Step058: rw could not infer the two independent event predicates under product projections. Supply typed predicates explicitly to the existing uprob_prod_and API.

Step066: reader rewriting left a beta-redex with matrix-coordinate arguments. Explicitly change to the resulting finite sum before sum_eq_single; no foreign definition unfolding.

Step069: simp did not match the public product-membership theorem through SProd notation. Instantiate its membership proof explicitly, then simplify the filter with that fact. No Core/Mathlib definition is supplied to simp.

Step071: selected-slot simplification reduced reflexive comparisons to True, leaving if True. Use the public if_true equation rather than if_pos rfl.

Step074: iota-reduce the reader match before splitting its conditional. Compose the exact degree inequalities directly rather than asking omega to identify differently elaborated filter terms.

Step077: the standalone multiplication bound on two X terms could not infer its coefficient semiring from a later simpa. Supply R := ZMod pp.p explicitly.

Step079: rename reader uses a coerced sum equivalence while degree API uses Sum.map. Change to the definitionally equal Core/Mathlib map form before applying the existing degree theorem; no foreign TCSlib definition is read.

Step080: product-of-sums higher-order inference left the function metavariable unresolved. Supply its index types and summand explicitly to Fintype.prod_sum.

Step081: mem_restrictDegree takes its variable type σ explicitly before p,n. Supply Fin(n κ); R remains implicit.

Step086: reader rewrite left an applied lambda, so rw did not see the inverse application. simp only with the same two public equations normalizes the Core beta/iota reductions.

Step092: Function.comp_apply does not eta-expand an unapplied composition passed as an evaluation argument. Change to its Core lambda form, then simplify casts with map_natCast.

Step093: the simp matcher did not rewrite the literal noise function using a flag equation stated with a local-let alias. State the local flag equation with the reader's explicit function; later applications still fold the local alias definitionally.

Step093 repair2: after flag reduction, the remaining equalities differ only by the local e/M aliases. Close by rfl after the specific reader equations; no foreign definition needs unfolding.

Step095: congrArg leaves the coordinate accessor as an applied lambda. simp only performs its Core beta reduction before Matrix.mul_apply/of_apply; rw alone did not see the multiplication application.

Step100: dependent support hypotheses are generalized automatically by induction; remove redundant generalizing arguments. Clear the bookkeeping generalization equation so the induction hypothesis needs no impossible whole-law/subtree equality. Simplify the Boolean cases rather than relying on definitional reduction of classical decisions.

Step101: global rw over a fixed dependent index builds an ill-typed motive. Try congruence-aware simp only using the same full record reader, then verify opacity of the raw bundle explicitly.

Step104: omega normalized symbolic natural quotients into integer divisions without supplying their nonnegativity. Replace the two elementary monotonicity goals with existing Nat.add_le_add_right/le_add_right and Nat.succ_le_succ/zero_le, retaining the same bound and all parameters.

Step109: rpow_natCast introduces a casted five; normalize that literal with Nat.cast_ofNat before exponent arithmetic. Normalize the casted κ+1 in the seed inequality with push_cast to match the already-normalized power bound; retain natural quotient casting as an inequality.

Step110: exact_mod_cast could not see the natural output length behind the local real alias m. Expand only that local alias before transporting the polynomial inequality; no output bound, coefficient or exponent changes.

M3 step111: Real.pow_div_factorial_le_exp has explicit section variable x before hx,n. Corrected call with (k:ℝ); failed source/log retained.

M3 step112: recorded slow attempt stopped before next check. First bounded diagnostic also misplaced set_option after the doc comment (parser error); its separate rw error exposed an untyped uprob_fst rewrite failure. Replaced hfixed chain by typed hrelabel/hfst/hpi/hpoint compositions; bounded global diagnostic pending.

M3 step112 repaired: diagnostic showed hfixed and hcover completed. Adding explicit α and typed T,φ to uprob_exists_le (and α to uprob_mono) eliminated the remaining higher-order/cardinality elaboration slowdown. Bounded check rc0; restoring standard maxHeartbeats0 for final source-bound check. All attempts retained.

M3 step118: exact_mod_cast did not unfold local count alias q; dsimp only [q] exposes the natural-cardinality cast. No foreign definition unfolded. Failed source/log retained.

M3 step132: htransport reduced fully except `(idx g φ A).2.1 = φ` for the local tuple constructor idx. Added rfl to close this definitional projection; no foreign definition unfolded. Failed source/log retained.

M4 step135: endpoint normalization left the raw true-game branch as if True; add Core.ite_true. κ+1+1 and κ+2 then coincide definitionally. Failed source/log retained.

M4 step136: random raw-game condition remains false=true until Bool.false_eq_true is applied; then Core.ite_false closes the branch. Failed source/log retained.
