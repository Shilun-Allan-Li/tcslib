# usage: python3 -I apply_docrefresh.py <in file> <out file>
# E4 (needs docstring authorization): refresh the frozen proof sketch of `fullDLCollection_hardCore`.
import sys
src = open(sys.argv[1]).read()
start = src.index("**Proof sketch.** *Easy:* `halfStr` with `polyTimeComputable_halfStr H` and `halfStr_spec`,")
end = src.index("theorem fullDLCollection_hardCore (H : ArithmeticFP)")
old = src[start:end]
assert old.rstrip().endswith("-/")
new = """**Proof sketch.** *Easy:* `halfStr` with `polyTimeComputable_halfStr H` and `halfStr_spec`,
read through `fullDLCollection_encD`.
*Hard* (`Collection.hardCore_iff`): the bound `ε(n) := max(succ(n) − 1/2, 0)`, with `succ(n)` the
predictor's average success, is negligible. Otherwise (`not_negligible_iff`) there is `c` with
`1/2 + n^{-c} ≤ succ(n)` for infinitely many `n`; fix such an `n`, large, and set
`ε' := n^{-c}/2`. The average moves to `G.gen`'s coins (`fullDLCollection_index`,
`fullDLCollection_coinsEquiv_uexp`). By `good_instances` (with `2ε'`) the coins with per-instance
success `≥ 1/2 + ε'` have probability `≥ ε'`; removing those with `p < 2^{n−1}` (probability
`≤ δ n ≤ ε'/2` by `hbig`, `ExpGroupGen.fullLengthExcept_iff`, `δ` negligible) leaves a *good* set
of probability `≥ ε'/2` (`uprob_or_le`). At a good index `i = ⟨p, ⟨p−1, g⟩⟩` (valid,
`WellFormedIndex`, `p ≡ 3 (mod 4)`, `16 n^c ≤ p − 1 < 2^n`) the domain is `Z_{p−1}`
(`fullDLCollection_domEquiv`, `expOrd_of_valid`, `ZMod.ringEquivCongr`), `g_u := expUnit` is a
generator (`orderOf_expUnit`, `Nat.card_zpowers`, `Subgroup.eq_top_of_card_eq`), and `A`'s
per-instance success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`
(`fullDLCollection_f`, `expF_eq`, `halfPred_eq`). Apply `invProb_dlInverter_ge` with
`ε := ε'`, `s := ⌊(p−1)/(8n^c)⌋`, `T := 2^κ` for `κ := Nat.size (16 n^c)` (so
`16 n^c < T ≤ 32 n^c` and `Ts ≥ p − 1`), `k := n` and `ℓ := 16 n^{2c+1} + 1` (odd, and
`k/(ε'²ℓ) < 1/4`): the inverter succeeds with probability `≥ (3/4)/T ≥ 3/(128 n^c)` on each good
instance, with ideal coins.
The machine `B` realising `dlInverter` is a non-uniform PPT (`NUPPT.ofPolyTime`): advice
`⟨A.advice n, ⟨⟦8n^c⟧_n, 1^κ⟩⟩`; coins `n + n·ℓ·(S.coins + A.coins)` with `S` the collection's
domain sampler (`fullDLCollection_sample`): `n` coins whose first `κ` bits are the guess `t`
(exactly uniform on `[0, 2^κ)`), and for each of the `n·ℓ` trials a block of `S`'s coins for
`r_{j,i}` and a block of `A`'s coins for `ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`;
computes `s` (`H.sub`, `H.divMod`) and `y₀ = y · (g^{ts})⁻¹ mod p` (`H.mul`, `H.modExp`, `H.xgcd`,
`H.divMod`); and runs `n` rounds of Algorithm 84.2 as guarded state loops
(`Complexity.StateLoop.gstep`, `Complexity.polyTimeComputable_iterate`) driven by the unary
counters `1^n` and `1^ℓ`, so no guard on `s` or `T` is needed (off the good set the success is
only bounded below by `0`): quadratic residuosity by Euler's test `y^{(p−1)/2} = 1` (`H.modExp`,
`H.le`), the root `base^{⌊p/4⌋+1}` (`H.modExp`, [PS10, Theorem 58.2]), the `ℓ` trials (`S` on the
index for `r`, `z = root · g^r mod p`, `A.output` on the layout `⟨⟨⟨1^n, ⟨i, z⟩⟩, A.advice n⟩, ρ⟩`,
the vote `[A = 1] = halfStr ⟨i, r⟩`), the majority (`polyTimeComputable_majority`, which is
`HardcoreBit.majority` because `ℓ` is odd), `root` or `p − root` (`H.sub`), and the parity bit;
finally `(bits + ts) mod (p−1)` as an `n`-bit numeral, which `decodeFin n` reads back. Where every
sampler block decodes, `B` computes `dlInverter` on the decoded coins.
Sampling: `S` is `δ_S`-close to uniform with `δ_S` negligible (`fullDLCollection_oneWay`,
`Collection.sampleClose_iff`); the `n·ℓ` sampled exponents are `n·ℓ·δ_S(n)`-close
(`OneWay.statClose_pi`, `StatClose.prod`, `StatClose.abs_uprob_sub_le_prod`), and the guess and
the coins of `A` are exact, so `B` succeeds with probability `≥ 3/(128 n^c) − n·ℓ·δ_S(n)` on each
good instance. Averaging over the good set (`HardcoreBit.uprob_mul_le_uexp`,
`ExpGroupGen.dlProb_eq`):
`G.dlProb B n ≥ (ε'/2)·(3/(128 n^c) − n·ℓ·δ_S(n)) ≥ 3/(1024 n^{2c})`
for infinitely many `n` (`n·ℓ·δ_S(n) ≤ 3/(1024 n^{2c})` for large `n`), an inverse polynomial,
contradicting `hDL B` (`fullDLAssumption_iff`, `negligible_iff`). -/
"""
src = src[:start] + new + src[end:]
open(sys.argv[2], "w").write(src)
