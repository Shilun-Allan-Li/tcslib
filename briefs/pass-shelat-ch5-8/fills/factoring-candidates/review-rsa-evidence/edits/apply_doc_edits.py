# E3: sketch refreshes (docstring only, no statement change), and the reflow of E1's sentence
import sys
p=sys.argv[1]; s=open(p).read()
def rep(old,new):
    global s
    assert s.count(old)==1,(old[:70],s.count(old))
    s=s.replace(old,new)
# E1's docstring sentence, reflowed
rep('''segment: the equivalence `(Fin (2 · 2n³) → Bool) × (Fin (T(n) B(n)) → Bool) ≃ (rsaGen H).Coins n`
with `ofFn (E (s₁, s₂)) = ofFn s₁ ++ ofFn s₂` (Mathlib's `Fin.appendEquiv`, then the length cast). -/''',
'''segment: the equivalence `(Fin (2 · 2n³) → Bool) × (Fin (T(n) B(n)) → Bool) ≃ (rsaGen H).Coins n`
with `ofFn (E (s₁, s₂)) = ofFn s₁ ++ ofFn s₂` (Mathlib's `Fin.appendEquiv`, then the length
cast). -/''')
# E3a: polyTimeComputable_rsaFromFactorRaw
rep('''**Proof sketch.** `A.output` on the re-paired layout (`NUPPT.polyTimeComputable_layout`,
`A.polyTimeComputable_output`); `q'` by `H.divMod`; the test `p' q' = N` by `H.mul` and
`polyTimeComputable_pairEq` (`polyTimeComputable_ite`); the decrements `p' − 1`, `q' − 1`
by `H.sub` with `[true]` (run-3 audit P7-1); `Φ` by `H.mul`; `d` as the second component of
`xgcdStr ⟨e, Φ⟩` (`H.xgcd`); `y^d mod N` by `H.modExp`; padding to `2n` bits by
`polyTimeComputable_unaryPoly`/`_blockMap`. -/''',
'''**Proof sketch.** Compute `A'` word by word (`rsa_fOut_poly`), each word one bundle field:
`p'` is `A.output` on the re-paired layout (`NUPPT.polyTimeComputable_layout`,
`A.polyTimeComputable_output`); `q'` is the quotient of `H.divMod ⟨N, p'⟩`; the test `p' q' = N`
is `H.mul` and two `H.le` comparisons, since the widths of `p' q'` and `N` differ
(`polyTimeComputable_and`); `Φ = (p' − 1)(q' − 1)` is two decrements `H.sub` with `[true]`
(run-3 audit P7-1) and `H.mul`, behind one leading zero; `d` is the second component of
`xgcdStr ⟨e, Φ⟩` (`H.xgcd`); `y^d mod N` is `H.modExp` with `|y| + 1` leading zeros before
`N` (the zeros are `H.sub ⟨1y, 1y⟩`). The two zero prefixes make every word read exactly, also on
the degenerate inputs `Φ = 0` (where `d ≤ 1`) and `N = 0` (where `y^d mod N = y^d`). The
`2n`-bit output is the truncation `(⟦0⟧_{2n} ++ v).drop |v|` of the value word `v`
(`H.sub ⟨1^{2n}, 1^{2n}⟩`, `polyTimeComputable_pairDropPoly var`), and `polyTimeComputable_ite`
selects it or `[]` by the test. The word computation equals `rsaFromFactorRaw A`
(`rsa_fOut_eq`: `divModStr_pairEncode`, `xgcdStr_pairEncode`, `modExpStr_pairEncode`,
`listToNat_subStr`, `rsa_drop_zeros_append`). -/''')
# E3b: rsaCollection_sampleClose
rep('''**Proof sketch.** Take `δ n := 1` for `n < 2` and `δ n := e^{-n}` for `n ≥ 2`. At a generated
index `⟨N, e⟩` (`rsaCollection_index`, valid by `rsaValid_indexOf`, `N = pq < 2^{2n}`) the
sampler's output is `unitSampleStr` on the numeral of `N` (`NUPPT.runAtL_ofPolyTimeUniform`,
`rsaSampleRaw`): `T(n)` trials each reading `k = Nat.size N ≤ 2n` uniform bits
(`k ≤ B(n)`), accepted iff the value is a unit; `sampleUnitL` is `rejectBlocksL` of the unit
predicate, so `statClose_rejectBlocksL` (default `1`) gives closeness `(1 - Pr[unit])^{T(n)}`
to the uniform element of `{v < 2^k | v < N ∧ gcd(v, N) = 1} ≃ Z_N^*`, decoded by `rsaDec` to
the uniform element of `Z_N^*` (`StatClose.map`, `decodeFin`-style injectivity). The acceptance rate is `Φ(N)/2^k ≥ Φ(N)/(2N) ≥ 1/(2k)`
(`Nat.lt_size_self`, `Nat.size_le`, `NumberTheory.le_totient_mul_log_succ`) `≥ 1/(4n+8)`,
and `(1 - 1/(4n+8))^{(4n+8)n} ≤ e^{-n}` (`one_sub_one_div_pow_le_exp_neg`). Negligibility:
`exp_neg_le_half_pow`, `negligible_two_pow_neg`, `Negligible.mono`. -/''',
'''**Proof sketch.** Take `δ n := 1` for `n < 2` and `δ n := e^{-n}` for `n ≥ 2`; it is negligible
(`exp_neg_le_half_pow`, `negligible_two_pow_neg`, `Negligible.mono`). The closeness `e^{-n}`
holds at every `n`, and `e^{-n} ≤ δ n` (`StatClose.mono`). Read the clause through
`Collection.sampleClose_iff`. At a generated index `⟨N, e⟩` (`rsaCollection_index`, valid by
`rsaValid_indexOf`) the sampler's output is `unitSampleStr` on the `2m`-bit numeral of `N`, with
`m = max n 2` (`rsa_sampler_runAt`, from `NUPPT.runAtL_ofPolyTimeUniform`). As `N < 2^{2m}`,
`Nat.size N ≤ 2m ≤ B(n)` at every `n`. So S3 (`statClose_sampleUnitL` at `N`) applies, and
mapping both sides by `v ↦ rsaDec i ⟦v⟧_{2m}` turns the residue of a uniform unit `x` into
`some x`, because `⟦x.val⟧_{2m} = rsaEnc i x` at a valid index (`rsaDec_rsaEnc`;
`rsa_statClose_dec`, `StatClose.map`). Transport along the sampler's coins
(`NUPPT.coinsEquivPoly`, `StatClose.comp_equiv_left`) and the domain
(`rsaCollection_domEquiv`, `rsaCollection_decD`, `StatClose.comp_equiv_right`). -/''')
# E3c: rsaSampler_spec (last sentence)
rep('''`length_natToList`, `listToNat_natToList` (`v < N < 2^{2m}`), `sampleUnitL_spec` resp.
`Nat.coprime_one_left`; the decoded unit has value `v` (`ZMod.coe_unitOfCoprime`,
`ZMod.val_natCast`, `Nat.mod_eq_of_lt`), so `rsaEnc i x = natToList (2m) v` and
`rsaEval_spec` applies. -/''',
'''`length_natToList`, `listToNat_natToList` (`v < N < 2^{2m}`), `sampleUnitL_spec` resp. the
default `1 % N` (`rsa_getD_spec`, `rsa_dec_unitSampleStr`); the decoded unit `x` re-encodes to the
sampler's string (`rsaEnc_of_rsaDec`), so `rsaEval_spec` applies. -/''')
# E3d: statClose_sampleUnitL (S3), step (3): the citation
rep('''(3) The acceptance probability is `Φ(N)/2^k` (`uprob_eq_card_filter` and the same bijection).''',
'''(3) The acceptance probability is `Φ(N)/2^k` (`uprob_def`, `Nat.card_congr` along the same
bijection, `ZMod.card_units_eq_totient`; `rsa_uprob_units`).''')
# E3e: rsaCollection_invProbAt_le, first paragraph (injectivity and the bijection), and reflow
rep('''`rsaEnc`), and a decoded answer `x'` with `f x' = f x` has `x' = x` (`PermCollection.f_injective`),''',
'''`rsaEnc`), and a decoded answer `x'` with `f x' = f x` has `x' = x` (`rsa_rsaF_injective`:
`rsaF_perm`, `rsaDec_rsaEnc`),''')
rep('''`rsaBreaker_coinsEquiv`, `decodeFin_ofFn`, `bitsToNat_natToBits`, `val_units_pow`). Since
`x ↦ x^e` pushes uniform to uniform (`pushesUniform_rsaPerm`, `PushesUniform.uprob_eq`), the
inner probability equals the RSA inner probability at `(z, e)`: a number `h(z, e) ∈ [0, 1]`
(over `y` and `A`'s coins).''',
'''`rsaBreaker_coinsEquiv`, `decodeFin_ofFn`, `bitsToNat_natToBits`; `rsa_inv_imp`). Since
`(x, ω) ↦ (x^e, φ⁻¹ ω)` is a bijection (`rsaPermAt`, `rsaBreaker_coinsEquiv`;
`uprob_comp_equiv`, `uprob_mono`), the inner probability is at most the RSA inner probability
at `(z, e)`: a number `h(z, e) ∈ [0, 1]` (over `y` and `A`'s coins; `rsa_inner_le`).''')
rep('''coins into the two prime segments and the exponent segment (`rsaGenParams`,
`HardcoreBit.uexp_prod`, `uprob_prod`, `HardcoreBit.uexp_comp_equiv`). (i) For each fixed prime pair `z`, the exponent drawn from the exponent segment
(`sampleUnitL` modulo `Φ(N)`, fallback `1 = 1 mod Φ(N)` as `Φ(N) ≥ 2`) is within `e^{-n}` of''',
'''coins into the two prime segments and the exponent segment (`rsaGenParams`,
`HardcoreBit.uexp_prod`, `uprob_prod`, `HardcoreBit.uexp_comp_equiv`). (i) For each fixed prime
pair `z`, the exponent drawn from the exponent segment
(`sampleUnitL` modulo `Φ(N)`, fallback `1 = 1 mod Φ(N)` as `Φ(N) ≥ 2`) is within `e^{-n}` of''')
rep('''its fallback `(2, 3)` by `StatClose.map`; a uniform pair passes the test unchanged); averaging the `[0, 1]`-valued `g` over that law instead of the uniform one costs at''',
'''its fallback `(2, 3)` by `StatClose.map`; a uniform pair passes the test unchanged); averaging
the `[0, 1]`-valued `g` over that law instead of the uniform one costs at''')
open(p,'w').write(s)
print('ok')
# reflow of the two joins above
s=open(p).read()
rep('''`rsaF_perm`, `rsaDec_rsaEnc`),
so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of `x`", which implies the RSA
event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`,''',
'''`rsaF_perm`, `rsaDec_rsaEnc`), so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of
`x`", which implies the RSA event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`,''')
rep('''pair `z`, the exponent drawn from the exponent segment
(`sampleUnitL` modulo `Φ(N)`, fallback `1 = 1 mod Φ(N)` as `Φ(N) ≥ 2`) is within `e^{-n}` of''',
'''pair `z`, the exponent drawn from the exponent segment (`sampleUnitL` modulo `Φ(N)`, fallback
`1 = 1 mod Φ(N)` as `Φ(N) ≥ 2`) is within `e^{-n}` of''')
open(p,'w').write(s)
print('ok2')
