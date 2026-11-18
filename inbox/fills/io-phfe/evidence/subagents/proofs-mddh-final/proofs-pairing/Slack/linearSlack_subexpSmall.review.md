# Exact rank correction: subexponential decay candidate

The exact live header/opening prose is preserved. The draft has one outer tactic block,
no new helper/sampler/asymptotic lemma, and no admissions. No Lean/lake/Git command or
live edit was run; root native verification remains pending.

The whole decay argument reuses the imported Foundations.Subexponential APIs exactly:
- subexpSmall_two_pow_neg is SubexpSmall 1 (fun n => (2 : Real)^(-1) ^ n);
- SubexpSmall.const_mul takes the original exponent's positivity, then c < 1, then 3;
- SubexpSmall.mono takes eventual domination in ABSOLUTE values, with witness threshold 0.

Pointwise domination uses only the existing linearSlack_nonneg and fixed-order bound,
Nat-to-Real cast of hpb, the public div_le_div_of_nonneg_left, div_eq_mul_inv, inv_pow,
and le_abs_self. There is no reconstruction of the definition of SubexpSmall or proof
of exponential absorption/decay.

The source-domain hypothesis hc0 remains in the frozen header. Like the existing
CoinSampling.subexpSmall_drawSlack proof, this domination argument only needs c < 1;
keeping 0 < c states the intended source security exponent without altering the theorem.

Dependencies linearSlack_nonneg/linearSlack_le_fixedOrder and their rankSlack inputs are
existing frozen declarations with proof candidates queued at root. No standard-axiom-only
claim is made until those candidates and this one pass native checks. No mathematical
obstruction was found.
