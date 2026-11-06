# apply_edits.py FILE : landing edits E1 (Fin.appendEquiv), E2 (PushesUniform.prodMap), E3 (sketch refreshes)
import sys
p=sys.argv[1]; s=open(p).read()
def rep(a,b,count=1):
    global s
    n=s.count(a)
    assert n==count, (n,a[:80])
    s=s.replace(a,b)
# ---- E1: rabin_appendEquiv is Mathlib's Fin.appendEquiv
rep('''/-- Splitting a coin string `Fin (a + b) → Bool` into its two segments (`Fin.append`). -/
private def rabin_appendEquiv (a b : ℕ) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin (a + b) → Bool) where
  toFun s := Fin.append s.1 s.2
  invFun f := (fun i => f (Fin.castAdd b i), fun j => f (Fin.natAdd a j))
  left_inv s := by
    obtain ⟨s1, s2⟩ := s
    ext i
    · exact Fin.append_left s1 s2 i
    · exact Fin.append_right s1 s2 i
  right_inv f := Fin.append_castAdd_natAdd

''','')
rep('(rabin_appendEquiv _ _)','(Fin.appendEquiv _ _)',count=6)
rep('''/-- The coins of `A'` are the unit sampler's coins followed by the coins of `A`, with `ofFn (E (s, ρ)) = ofFn s ++ ofFn ρ`. -/''',
'''/-- The coins of `A'` are the unit sampler's coins followed by the coins of `A`, with
`ofFn (E (s, ρ)) = ofFn s ++ ofFn ρ` (Mathlib's `Fin.appendEquiv`, then the length cast). -/''')
rep('''/-- The coins of a Rabin generator are the two prime segments, with
`ofFn (E (s₁, s₂)) = ofFn s₁ ++ ofFn s₂`. -/''','''/-- The coins of a Rabin generator are the two prime segments, with
`ofFn (E (s₁, s₂)) = ofFn s₁ ++ ofFn s₂` (Mathlib's `Fin.appendEquiv`, then the length cast). -/''')
# ---- E2: rabin_pushesUniform_prod from the library's PushesUniform.prodMap
rep('''/-- A map pushing uniform to uniform on the first coordinate keeps the probability of an event
with independent coins (`uprob_prod`, the definition of `PushesUniform`). -/
private theorem rabin_pushesUniform_prod {Ω γ ρ : Type*} [Fintype Ω] [Fintype γ] [Fintype ρ]
    {π : Ω → γ} (h : HardcoreBit.PushesUniform π) (P : γ → ρ → Prop) :
    uprob (fun w : Ω × ρ => P (π w.1) w.2) = uprob (fun w : γ × ρ => P w.1 w.2) := by
  rw [uprob_prod, uprob_prod]
  exact (HardcoreBit.pushesUniform_iff π).1 h (fun a => uprob (fun b => P a b))''',
'''/-- A map pushing uniform to uniform on the first coordinate keeps the probability of an event
with independent coins: the library's `PushesUniform.prodMap` with `pushesUniform_id`, then
`PushesUniform.uprob_eq`. -/
private theorem rabin_pushesUniform_prod {Ω γ ρ : Type*} [Fintype Ω] [Fintype γ] [Fintype ρ]
    {π : Ω → γ} (h : HardcoreBit.PushesUniform π) (P : γ → ρ → Prop) :
    uprob (fun w : Ω × ρ => P (π w.1) w.2) = uprob (fun w : γ × ρ => P w.1 w.2) :=
  (h.prodMap HardcoreBit.pushesUniform_id).uprob_eq fun w => P w.1 w.2''')
# ---- E3: sketch refreshes (docstring only)
rep('''**Proof sketch.** As `polyTimeComputable_rsaGenRaw` without the exponent: the coins are cut
at `1^{4m³}` (`polyTimeComputable_pairTakePoly`/`_pairDropPoly rabinPrimeCoins`); each
prime is an `iterateFind` loop (`Complexity.polyTimeComputable_iterateFind`) whose test is
`H.prime` conjoined with the oddness test (the last bit, `polyTimeComputable_lenEq`-style
projection) and whose `none` branch is the constant fallback numeral; the validity test uses
`H.prime`, `polyTimeComputable_pairEq`, `H.le`; `N` by `H.mul`; the fallback pair is a
constant (`polyTimeComputable_ite`). -/''',
'''**Proof sketch.** The generator equals the string computation `rabin_genCore` with the test
`rabin_oddAcc` ("prime, and the residue modulo `2` (`H.divMod` by `⟦2⟧`) reads `≥ 1`", which
decides `p.Prime ∧ p ≠ 2` on every word, `Nat.Prime.eq_two_or_odd`) and the fallback words `⟦3⟧`,
`⟦5⟧` (`rabin_genCore_eq`). That computation is polynomial-time (`rabin_genCore_poly`):
`1^{max n 3}` by `polyTimeComputable_lenLe`/`_ite`; the coins are cut at `1^{4m³}`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly rabinPrimeCoins`); each prime is the block
loop over the repetition host `Complexity.polyTimeComputable_iterateFind` (`rabin_spOut_poly`),
its fallback zero-padded to `m` bits by `H.sub` and `H.add` (the width `m` varies, so it is not a
constant word); the validity test is `polyTimeComputable_pairEq` on the two numerals alone, since
both are always primes of the class below `2^m` (`rabin_samplePrimePL_spec`); `N` by `H.mul`. -/''')
rep('''`polyTimeComputable_oddGenRaw` with the test "`p ≡ 3 (mod 4)`" on the last two bits.''',
'''`polyTimeComputable_oddGenRaw` with the test "`p ≡ 3 (mod 4)`".''')
rep('''**Proof sketch.** As `rsaSampler_spec`: unfold the activation
(`NUPPT.runAtL_ofPolyTimeUniform`, `rabinSampleRaw`), case on `sampleUnitL`, discharge
`rabinDec`'s test by `length_natToList`, `listToNat_natToList`, `sampleUnitL_spec` /
`Nat.coprime_one_left`, and read the value back (`ZMod.coe_unitOfCoprime`, `ZMod.val_natCast`). -/''',
'''**Proof sketch.** Unfold the activation (`NUPPT.runAtL_ofPolyTimeUniform`, the P5 equations;
`rabin_sampler_runAt`) and the index (`oddGen_runAt`); at the index `⟦N⟧_{2m}` the sampler's
string is the numeral of the total S3 sampler's value (`unitSampleStr_eq`,
`listToNat_rabinIndexOf`); case on `sampleUnitL` (`sampleUnitL_spec`, or the fallback `1 % N`)
and discharge `rabinDec`'s test by `length_natToList` and `listToNat_natToList`. The decoded
unit's encoding is the sampler's string (canonical decoding, `rabin_enc_of_dec`:
`ZMod.coe_unitOfCoprime`, `natToList_val_natCast`), so `rabinEval_spec` gives the evaluator
clause. -/''')
rep('''**Proof sketch.** Unfold the activation (`NUPPT.runAtL_ofPolyTimeUniform`), then the
computation above with `blumDec`'s tests (`length_natToList`, `listToNat_natToList`,
`Nat.mod_lt`, `ZMod.coe_unitOfCoprime`, `ZMod.val_natCast`). -/''',
'''**Proof sketch.** Unfold the activation (`NUPPT.runAtL_ofPolyTimeUniform`,
`modExpStr_pairEncode`) and the index (`blumGen_runAt`), which is `BlumValid` with
`blumMod i = N`. Then the computation above with `blumDec`'s tests (`length_natToList`,
`listToNat_natToList`, `Nat.mod_lt`, coprimality by `Nat.Coprime.pow_left` and `Nat.gcd_rec`);
membership in `QR_N` is the square of `ZMod.unitOfCoprime v` (`mem_QR_iff`,
`ZMod.coe_unitOfCoprime`, `ZMod.natCast_mod`). The decoded residue's encoding is the sampler's
string (canonical decoding, `rabin_blumEnc_of_dec`), so `blumEval_spec` gives the evaluator
clause. -/''')
rep('''`Pr[E] ≥ Pr_{Π_n × Π_n}[p ≠ q ∧ E] ≥ Pr[E] − Pr[E ∧ p = q] ≥ (B/P)² − (1/P)(B/P) = B(B−1)/P²`''',
'''`Pr[E] ≥ Pr_{Π_n × Π_n}[p ≠ q ∧ E] ≥ Pr_{Π_n × Π_n}[E] − Pr_{Π_n × Π_n}[E ∧ p = q]
≥ (B/P)² − (1/P)(B/P) = B(B−1)/P²`''')
rep('''by `invProbAt (rabinBlumInverter H A) n + rabinErr n`, negligible by `h.hard`,''',
'''by `invProbAt (rabinBlumInverter H A) n + rabinErr n`, negligible by the `hard` clause of `h`
read through `TrapdoorCollection.oneWay_iff` (P2),''')
open(p,'w').write(s); print('ok')
