# usage: python3 -I apply_edits.py <in ElGamal.lean> <out> [--no-docrefresh] [--with-e6]
# E1 matcher-free dlc_ssLoop_poly; E2 proof sketches on 15 helpers; E3 target sketch refreshes
# (docstring only); E4 a section header and two stray blank lines; E6 (optional) base re-point.
import sys, textwrap
src = open(sys.argv[1]).read()
out = sys.argv[2]
doc = '--no-docrefresh' not in sys.argv
e6 = '--with-e6' in sys.argv

def rep(old, new, count=1):
    global src
    assert src.count(old) == count, (src.count(old), old[:80])
    src = src.replace(old, new)

def wrap(t):
    return "\n".join(textwrap.wrap(t, width=100, break_long_words=False, break_on_hyphens=False))

# ---- E1
rep('''private theorem dlc_ssLoop_poly (H : ArithmeticFP) : PolyTimeComputable dlc_ssLoop :=
  polyTimeComputable_iterateFind dlc_ssStep_poly (dlc_ssAcc_poly H) dlc_ssOut_poly
    PolyExpr.var (PolyExpr.add (.mul (.const 2) .var) (.const 4)) (fun x i _ => by
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      exact dlc_length_ssStep_iterate_le x i)
''', '''private theorem dlc_ssLoop_poly (H : ArithmeticFP) : PolyTimeComputable dlc_ssLoop := by
  refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp
    (polyTimeComputable_iterateFind dlc_ssStep_poly (dlc_ssAcc_poly H) dlc_ssOut_poly
      PolyExpr.var (PolyExpr.add (.mul (.const 2) .var) (.const 4)) (fun x i _ => by
        simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
        exact dlc_length_ssStep_iterate_le x i))
  -- the repetition lemma's `match` is split by its equation lemmas, not matched by defeq
  rw [PolyExpr.eval_var]
  unfold dlc_ssLoop
  split
  next i hi => rw [hi]
  next hn => rw [hn]
''')
rep('''/-- The trial loop is polynomial-time (the repetition lemma with `R = var`). -/''',
    '''/-- The trial loop is polynomial-time (the repetition lemma with `R = var`, its `match` read by
`split`). -/''')

# ---- E2
sk = {
'dlc_abs_uprob_sub_uprob_ne_le': "Count (`uprob_eq_card_filter`, `Fintype.card_subtype_compl`): `s` is the number of points of `T ∖ {a}` (`Equiv.subtypeSubtypeEquivSubtypeInter`), so `s ≤ t ≤ s + 1` (`card_insert_le`) and `s ≤ N − 1`. For `N = 1` the punctured side is `0` and `t ≤ 1`. Otherwise `t/N ≤ (s + 1)/N ≤ s/(N − 1) + 1/N` and `s/(N − 1) ≤ (s + 1)/N ≤ t/N + 1/N`, the step `s/(N − 1) ≤ (s + 1)/N` being `s ≤ N − 1`.",
'dlc_ssLoop_eq': "After `i` steps the header is unchanged, the counter `u` has lost `i` bits and the coins `i` blocks of `|u|` bits (`dlc_ssStep_iterate`), so the trial value is the `Nat.size ⟦m⟧`-bit prefix of block `i`, and the test accepts iff `i < |u|` and that value is below `⟦m⟧`. The search over the first `|x| + 1 ≥ |u|` rounds is the search over `[0, |u|)` (`dlc_find?_range_lt`), which is the search of `sampleBelowL` read through `sampleBelowL_eq_rejectBlocksL`, `rejectBlocksL_eq` and `dlc_findSome?_ite`. In the `some i` case the payload without its marker is the prefix of block `i`; in the `none` case both sides read `0` (`dlc_listToNat_nil`).",
'dlc_numPoly_egCanon': "`egCanon` is an `if` on `0 < m ∧ m < p ∧ m^q mod p = 1`. The first two tests are `H.le` comparisons (`dlc_poly_le`: `1 ≤ m`, `m + 1 ≤ p`), the third an equality test (`dlc_poly_eq`) of `m^q mod p'` with `1` for the safe modulus `p'` (`dlc_numPoly_safeMod`, `dlc_numPoly_powMod`), and the choice is `dlc_numPoly_ite`. The test with `p'` agrees with the test with `p` whenever it is read: `m < p` forces `p ≠ 0`, so `p' = p`.",
'dlc_poly_egEncParts': "Read `p`, `q`, `h` from the index through `dlP_eq`, `dlM_eq`, `dlG_eq` (`dlc_numPoly_of_poly` on the projections). The exponent is `dlc_numPoly_sample` and the canonical message `dlc_numPoly_egCanon`; the two `n`-bit components are `dlc_poly_natToList_powMod` (`h^b mod p`) and `dlc_poly_natToList_powMulMod` (`A^b · m' mod p`), paired.",
'dlc_poly_ddhInput': "The projections of `⟨1^n, ⟨t, mm⟩⟩` give `⟨i, X⟩` and `Y`; `p` and `q` are read from `i` (`dlP_eq`, `dlM_eq`), `m_b` is a fixed projection of `mm` (case on `b`), `m'_b` is `dlc_numPoly_egCanon`, and `⟦Z · m'_b mod p⟧_n` is `dlc_poly_natToList_powMulMod` with the exponent `1` (`pow_one`); pair, and match the definition pointwise.",
'dlc_card_sq_eq_one_le': "Map the filter into `ℕ` by `Fin.valEmbedding`. From `(x + 1)² mod p = 1`, `p ∣ (x + 1)² − 1 = x (x + 2)` (`Nat.modEq_iff_dvd'`), so `p ∣ x`, hence `x = 0` since `x < p − 1`, or `p ∣ x + 2`, hence `x = p − 2`. The image lies in `{0, p − 2}` (`card_le_card`, `card_insert_le`).",
'dlc_uprob_bad_le': "Average over `G`'s coins (`uprob_prod`). For each coin string `r` (valid and well formed from `n₀` on: `wellFormedIndex_iff`, `safePrimeValid_iff`) the inner probability is at most `[p < 2^{n−1}] + 9 · (1/2)^n`: at most `1` for a short prime, and otherwise `2/(p − 1) + (1/2)^n ≤ 9 · (1/2)^n` (`dlc_uprob_egUnit_sq_le`, `dlc_two_div_le`). The average of the indicator is at most `δ n` (`fullLengthExcept_iff`, `uprob_eq_uexp`, `HardcoreBit.uexp_mono`, `HardcoreBit.uexp_add`, `HardcoreBit.uexp_const`).",
'dlc_exists_pow_eq': "`h` and `c` are nonzero in `Z_p`, hence units `h_u`, `c_u`. `h_u` has order `q`, so it lies in `G_q` (`mem_QR_iff_pow_eq_one`) and is not `1`; `c_u^q = 1`, so `c_u ∈ G_q`. Since `G_q` is generated by `h_u` (`zpowers_eq_QR`) and is finite, `c_u = h_u^k` for some `k : ℕ` (`mem_powers_iff_mem_zpowers`); take values.",
'dlc_challenge_eq': "`dlc_genEquiv_ofFn` writes the coins of `Gen` as `r ++ (u₁ ++ u₂)`, so the cuts of `egGen_runAt` at `coinLen n` and `n · n` recover `r`, `u₁` and `u₂` (`List.take_left'`, `List.drop_left'`, `List.drop_drop`), and `NUPPT.runAt_eq` reads `G.gen.runAtL` back as `G.gen.runAt`. Unfold `challenge`, read the fields of `elGamal`, and rewrite the ciphertext by `egEnc_runAt` with `dlc_encEquiv_ofFn`.",
'dlc_hyb1_point': "Both sides are `D` on one string (`NUPPT.distinguisher_eq`, `NUPPT.distinguisherL_eq`, `he`, `dlc_challenge_eq`). The derived index `i` (`dlc_grp_runAt`) is valid and well formed, `⟨p, ⟨q, h⟩⟩` with `p`, `q` from `G`'s index (`wellFormedIndex_iff`, `safePrimeValid_iff`) and `h = egSquareGen p g = g² mod p` off the bad event, of order `q` (`egSquareGen_valid`). The padding of the tuple is lossless (`dlc_ofFn_padFin`, `length_ddhTuple`), so `D_b` reads `⟨i, X⟩`, `Y` and `Z` back. The exponent `ddhExpo n i u` has the value of the sampler `sampleBelowL q (Nat.size q) n n u` of `egGenParts`/`egEncParts` (`expOrd_of_valid`, `ZMod.val_natCast`, `sampleBelowL_lt`), `expF i z` is the numeral of `h^z mod p` (`expF_eq`, `WellFormedIndex.dlW_eq`), and `(h^x mod p)^y · c ≡ h^{xy mod q} · c (mod p)` since `h` has order `q` (`ZMod.val_mul`, `pow_mod_orderOf`, `ZMod.natCast_eq_natCast_iff'`).",
'dlc_hyb1': "Relabel both acceptance probabilities over the common coin space `((r, u₁), (u₂, (u₃, (r_M, r_D))))` (`acceptProb_def`, `uprob_comp_equiv` with `E₁`, built from `dlc_genEquiv` and `dlc_encEquiv`, and `E₂`, built from `dlc_grpEquiv` and `e`). Off the event `g² ≡ 1 (mod p)` the two events coincide (`dlc_hyb1_point`), so the gap is at most the probability of the event (`dlc_abs_uprob_sub_le_of_iff`), which depends on `(r, u₁)` only (`uprob_fst`) and is at most `δ n + 9 · (1/2)^n` (`dlc_uprob_bad_le`).",
'dlc_rand_term': "At the valid index (`safePrimeValid_iff`, `expValid_iff`) `g` has order `q = expOrd i` (`expOrd_of_valid`), and the canonical message is `1 = g^0` or an element of `G_q`, hence `g^k` (`dlc_egCanon_cases`, `dlc_exists_pow_eq`). `dlc_uprob_shift` puts the factor on the uniform side, and the remaining gap is `ddhExpo_statClose` on the test `z ↦ Ψ ⟦g^z · c mod p⟧_n`.",
'dlc_rand_accept': "Unfold `D_b` on the random tuple (`NUPPT.distinguisher_eq`, `NUPPT.distinguisherL_eq`, `he`, `ddhRandom`). The padding is lossless (`dlc_ofFn_padFin`, `length_ddhTuple`), so the projections of `dlc_ddhInput` and `dlc_tuplePk` read the components of the tuple back, and the numeral `Z = expF i z` reads as `g^z mod p` (`expF_eq`, `listToNat_natToList` below `dlP_lt_two_pow`).",
'dlc_hyb3_point': "Rewrite each event by `dlc_rand_accept` (`OneWay.uprob_congr`). With the index, `u₁`, `u₂`, `r_M` and `r_D` fixed, the two events differ only in the message `m₀` or `m₁` given to `dlc_rand_term`, which puts each within `(1/2)^n` of the same probability over a uniform `z ∈ Z_q`; the triangle inequality gives `2 · (1/2)^n`.",
'dlc_hyb3': "Relabel the seeds and the coins of `D_b` so that the coins `u₃` of `z` come last (`acceptProb_def`, `uprob_comp_equiv` with `E e_b`), split them off (`uprob_prod`), and bound the gap of the averages by the pointwise gap (`dlc_abs_uexp_sub_le`, `dlc_hyb3_point`).",
}
lines = src.split('\n')
for name, text in sk.items():
    idx = [k for k, l in enumerate(lines) if l.startswith(f'private theorem {name} ')]
    assert len(idx) == 1, name
    j = idx[0] - 1
    assert lines[j].endswith(' -/'), (name, lines[j])
    lines[j] = lines[j][:-3] + '\n\n' + wrap('**Proof sketch.** ' + text) + ' -/'
src = '\n'.join(lines)

# ---- E4 (cosmetics): a header for the algorithms after the helper group, two stray blank lines
rep('''/-- **El Gamal's `Gen` is polynomial-time** given the arithmetic bundle.''',
    '''/-! ### El Gamal's algorithms -/

/-- **El Gamal's `Gen` is polynomial-time** given the arithmetic bundle.''')
rep('''  rfl


/-- **El Gamal's key generator**''', '''  rfl

/-- **El Gamal's key generator**''')
rep('''NUPPT.polyTimeComputable_inCoins


/-- **El Gamal's encryptor**''', '''NUPPT.polyTimeComputable_inCoins

/-- **El Gamal's encryptor**''')

# ---- E3 (docstring only; needs the standing refresh ruling)
if doc:
    rep('''**Proof sketch.** Cut the coins at the unary lengths `1^{coins(n)}` and `1^{n·n}`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly` on `⟨1^n, r⟩`); run `G.gen.output` on the
layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`); the two
rejection loops are `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the
test `H.le` (the decrement `p − 1` and the bit length `Nat.size`: `H.sub`, `H.size`);
`h = g² mod p` and `h^x mod p` by `H.modExp`; the numerals are padded to width `n`
(`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/''', '''**Proof sketch.** Cut the coins at the lengths `coins(n)` and `n · n`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly` against `1^n`); run `G.gen.output` on the
layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`). The numbers are
read through a numeral calculus over the bundle (`H.add`, `H.sub`, `H.mul`, `H.divMod`,
`H.modExp`, `H.le`, `H.size`, `polyTimeComputable_ite`). The two rejection samplers are one
trial loop on `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the test `H.le`
(the decrement `p − 1` by `H.sub`, the bit length by `H.size`); its state carries a trial counter,
because the loop runs `|x| + 1` rounds and a raw coin segment may be longer than `n · n`. The loop
is matched with `sampleBelowL` through `sampleBelowL_eq_rejectBlocksL` and `rejectBlocksL_eq`.
`h = g² mod p` is `H.mul` then `H.divMod`, `h^x mod p` is `H.modExp`; every reduction uses the
modulus `2^n` where `p` reads as `0` (the `n`-bit numerals agree), so `H.modExp` stays
polynomial, and the remainder of `H.divMod` is taken against the modulus padded with leading
zeros, which keeps it lossless. Width-`n` numerals are the last `|b|` bits of `⟦0⟧_n ++ b`
(`⟦0⟧_n` by `H.sub`, `polyTimeComputable_pairDropPoly`); pair. -/''')
    rep('''**Proof sketch.** The exponent `b` by the rejection loop (`polyTimeComputable_iterateFind`,
`H.le`); `h^b`, `A^b`, the membership test `m^q mod p = 1` (`H.modExp`, `polyTimeComputable_pairEq`,
`H.le` for `0 < m < p`, `polyTimeComputable_ite` for the canonicalisation); the product by
`H.mul` and the reduction modulo `p` by `H.divMod`; width-`n` padding by
`polyTimeComputable_unaryPoly`/`_blockMap`; pair. -/''', '''**Proof sketch.** The calculus of `polyTimeComputable_egGenRaw`: `p`, `q`, `h` are read from the
key through `dlP_eq`, `dlM_eq`, `dlG_eq`; the exponent `b` by the trial loop
(`polyTimeComputable_iterateFind`, `H.le`); `h^b mod p` and `A^b · m' mod p` by `H.modExp`, `H.mul`
and `H.divMod`, with the modulus `2^n` where `p` reads as `0`; the canonicalisation test
`0 < m < p ∧ m^q mod p = 1` by `H.le` comparisons, the equality with `1` as two comparisons rather
than `polyTimeComputable_pairEq` (numerals of different widths can read as the same number), and
the choice by `polyTimeComputable_ite`; width-`n` numerals as the last bits of `⟦0⟧_n ++ b`;
pair. -/''')
    rep('''steps of `polyTimeComputable_egGenRaw`, plus the test `g² mod p = 1` by `H.modExp` and
`polyTimeComputable_pairEq` with the constant numeral of `4` on `polyTimeComputable_ite`). -/''',
        '''steps of `polyTimeComputable_egGenRaw`, plus the test `g² mod p = 1`, with `g · g` by `H.mul`,
the remainder by `H.divMod` and the equality with `1` as two `H.le` comparisons, choosing the
constant numeral of `4` on `polyTimeComputable_ite`). -/''')
    i0 = src.index('''**Proof sketch.** Fix `M, D`. For each bit `b` build the DDH distinguisher `D_b` (advice''')
    i1 = src.index('''`Negligible.mono`. -/
theorem elGamal_secure''')
    src = src[:i0] + '''**Proof sketch.** Fix `M, D`. For each bit `b` build the DDH distinguisher `D_b`
(`NUPPT.exists_comp`, `NUPPT.exists_compParam`, `NUPPT.exists_seq`; the advice is `M`'s and `D`'s,
the bit is fixed in the machine, and the coins `M.coins + D.coins` are identified with
`M.Coins n × D.Coins n`): on a tuple `t = ⟨i, ⟨X, ⟨Y, Z⟩⟩⟩` it runs `M(1^n, ⟨i, X⟩)`, takes the
`b`-th message, canonicalises it to `m'_b`, and runs `D(1^n, ⟨⟨i, X⟩, ⟨Y, ⟦Z · m'_b mod p⟧_n⟩⟩)`.
The numbers are read by value (`listToNat`), so the padding to `15n + 14`, lossless from `n₀` on
(`length_ddhTuple`), needs no cut; the pre-processing is polynomial-time over the bundle
(`H.modExp`, `H.mul`, `H.divMod`, `H.le`, `polyTimeComputable_ite`). *Hybrid 1* (the
square-versus-generator event): the coins of `challenge n M b` and of `D_b` on
`ddhReal (egGroupGen H G)` are both relabelled from `G`'s coins, the `n · n`-bit segments of `g`,
`a` and `b'`, and the coins of `M` and `D` (`uprob_comp_equiv`; `egGen_runAt`, `egEnc_runAt`,
`egGroupGenMachine_runAt`). Off the event `g² ≡ 1 (mod p)` the two runs give `D` the same string
and coins: `ddhExpo` is the sampler `sampleBelowL q (Nat.size q) n n` of `egGenParts`/`egEncParts`
(`expOrd_of_valid`), `h^{(ab' mod q)} = h^{ab'}` since `h` has order `q` (`egSquareGen_valid`,
`pow_mod_orderOf`), and `egSquareGen p g = g² mod p`. Hence the gap is at most `Pr[g² ≡ 1]`
(`statClose_of_uprob_ne`). By `statClose_sampleBelowL` with `m = p − 1` and the count of the roots
`v ∈ {0, p − 2}` of `(v + 1)² ≡ 1` in `Fin (p − 1)`, `Pr[g² ≡ 1] ≤ 2/(p − 1) + (1/2)^n`, and
`2/(p − 1) ≤ 8 (1/2)^n` when `2^{n−1} ≤ p`; for `n ≥ n₀`, `hbig` bounds the coins with
`p < 2^{n−1}` by `δ n`. Altogether the hybrid-1 gap is at most `η n := δ n + 9 (1/2)^n`.
*Hybrid 2* (DDH): `hDDH` through `ddhAssumption_iff` and `Ensemble.indist_iff_exists_negligible`
gives a negligible `ε_b` with `|Pr[D_b(ddhReal)] − Pr[D_b(ddhRandom)]| ≤ ε_b n`. *Hybrid 3* (the
two random worlds): in `ddhRandom` the coins of `z = ddhExpo n i e₃` are used nowhere else; with
the other coins fixed, replacing `z` by a uniform `z ∈ Z_q` costs `(1/2)^n` (`ddhExpo_statClose`),
and `m'_b ∈ G_q` is `h^k` (`zpowers_eq_QR`), so the shift `z ↦ z + k` (`Equiv.addRight`,
`uprob_comp_equiv`) shows that `h^z · m'_b` has the law of `h^z`; averaging (`uprob_prod`) gives
`|Pr[D_0(ddhRandom)] − Pr[D_1(ddhRandom)]| ≤ 2 (1/2)^n`. Hence the advantage is at most
`2 (|δ n| + 9 (1/2)^n) + ε_0 n + ε_1 n + 2 (1/2)^n` for `n ≥ n₀` and at most `1` below (the
indicator of `n < n₀`), negligible by `negligible_two_pow_neg`, `negligible_zero`,
`Negligible.const_mul`, `Negligible.add` and `Negligible.mono` (`|δ|`, because `δ` is known to
be nonnegative only from `n₀` on). -/
theorem elGamal_secure''' + src[i1 + len('''`Negligible.mono`. -/
theorem elGamal_secure'''):]

# ---- E6 (optional; base proof, outside the authorized re-points)
if e6:
    rep('''    StatClose X Y (uprob fun s => X s ≠ Y s) := by
  intro T''', '''    StatClose X Y (uprob fun s => X s ≠ Y s) := by
  rw [statClose_iff]
  intro T''')
open(out, 'w').write(src)
