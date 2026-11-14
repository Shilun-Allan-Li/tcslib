# Draft promotion/overlap ledger

Generic encoding helpers drafted in `Hashing/FromDiscreteLog/Encoding.lean`:
`inputWord_split`, `inputWord_take`, `inputWord_drop`, `inputWord_ext`,
`boundedInputEquiv` and its two readers, `card_boundedInput`, `card_boundedRange`.
Promote to the shared bit-vector/encoding layer after the fill freeze window.
The private natural-number lemma `residue_difference` in Algebra.lean is a
candidate for the shared arithmetic layer.

Searches before writing: all TCSlib occurrences of `padFin`, `splitBits`,
`listToNat_inj`, `natToList_length_listToNat`, arithmetic string readers,
`expGenFun`, `expSampleRaw`, and `expEval_spec`; core `List.ofFn_succ'`,
`take_left'`, `drop_left'`; generic group-power/order congruence readers.
The helper constructions use public readers and core/Mathlib lemmas.
No private provider proof was copied. The private `dla_statClose_expDec` was
inspected only to identify potential overlap; no local value equivalence has
been copied from it. Any later re-derivation will be recorded here explicitly.

overlap: TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean dlb_expo_val

`Algebra.expUnit_pow_val` rederives the general arbitrary-natural-exponent
unit-power value formula from public `val_units_pow`, `coe_expUnit`, and
`expValid_iff`. No private lemma was imported or copied; the existing private
lemma concerns its own exponentiation function on a full-order residue.

The only provider-file edits authorized by the user are the two reader equations
in Candidates/DiscreteLog.lean. That provider was already above 1000 lines at the
issue base; no split or unrelated cleanup is included in the scoped exception.

`inputWord_num_ext` also belongs in the generic encoding promotion list.
overlap: TCSlib/Cryptography/Candidates/Factoring.lean fac_listToNat_inj
The equal-width numeric injectivity argument is rederived through public
numeral canonicity inside a prefix/selector statement; no private proof is
copied or imported.

`Probability.expect_sample_eq_uexp` is requested for the generic games bridge or
probability layer, and `Probability.collision_accept_eq` for CRH's shared module.
Search also found public `Games.Bridge.prob_sample_eq_uprob` outside the issued
order. That probability-only statement was not copied; the new generic bridge
concerns arbitrary real-valued expectations and is derived through expect_sample
and uexp_def. No import outside the target closure was added.

Generic `ofFn_splitBits_fst` and `ofFn_splitBits_snd` are promotion requests for
Authentication/Encoding. The search found public `ofFn_coins_split` in
Authentication/Signatures/HashAndSign.lean; the new statements concern splitBits
specifically and read its published fst/snd projections through the stronger
public general-window theorem ofFn_drop_take. The existing coin-word statement
and proof were not copied.

`Coins.sumCoinsEquiv`, its equation reader and inverse-word reader belong in the
shared randomized/collection coin interface. Search found analogous general
coin reindexing in EnsemblesLemmas but no exact sum-polynomial machine split.
overlap: TCSlib/Cryptography/Asymptotic/UniversalPadding.lean ofFn_splitCoins_symm_cast
The cast/split concatenation fact was rederived using public
ofFn_arrowCongr_finCongr and ofFn_splitCoins_symm; no private proof was copied.
