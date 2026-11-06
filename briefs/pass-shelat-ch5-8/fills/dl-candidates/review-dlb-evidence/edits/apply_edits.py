# usage: python3 -I apply_edits.py <head file> <out file>
# Applies the review's landing edits E1-E4 (E5, the headline docstring refresh, is a separate step).
import sys, textwrap
src = open(sys.argv[1]).read()

def rep(old, new, count=1):
    global src
    assert src.count(old) == count, (old[:80], src.count(old))
    src = src.replace(old, new)

# ---- E1: drop the copy `dlb_statClose_pi`; cite the public `OneWay.statClose_pi` (in the closure)
start = src.index("/-! ### Closeness of independent coordinates; the guess -/")
end = src.index("/-- Splitting an `n`-bit string at `κ ≤ n`")
src = src[:start] + "/-! ### The guess -/\n\n" + src[end:]
rep("have hXn := dlb_statClose_pi (dlb_statClose_pi hX1 ℓ) n",
    "have hXn := OneWay.statClose_pi (OneWay.statClose_pi hX1 ℓ) n")

# ---- E2: proof sketches for the twelve long private proofs (style_lint, policy §3)
S = {
"dlb_inner_eq": """The start state is `⟨1^{|bs|}, ⟨cs, []⟩⟩` (`dlb_iStart`, `hL`). After
`i ≤ |bs|` steps the state is `⟨1^{|bs|−i}, ⟨blocks(bs.drop i) ++ rest, votes(bs.take i)⟩⟩`
(`dlb_iStep_iterate`), and from `|bs|` steps on the counter is empty and the state is fixed
(`dlb_iStep_iterate_nil`). Every orbit state is within `3|Y| + 4` (`dlb_iB`), so the guard never
fires (`StateLoop.gstep_iterate_eq`, `dlb_orbit_eq`); the loop runs `|⟨Y, start Y⟩| ≥ |bs|`
rounds and ends in the state reached at `|bs|`.""",
"dlb_oStep_cons": """The trial loop on the round's root `rootF f y` (`dlb_oRoot_eq`)
returns the rest of the coins and the votes of the `ℓ` blocks, reversed (`dlb_inner_eq`);
reversal changes neither the length nor the count of `true`s (`List.length_reverse`,
`List.count_reverse`), so the majority bit is the displayed test. The parity bit is
`¬ qrF f y` (`dlb_oQr_eq`) and the counter loses one mark.""",
"dlb_oStep_shape": """Since `i < |rs₀|`, `rs = r :: rs'` with `|r| = ℓ`, and
`dlb_oStep_cons` performs the round. The new root is again an `n`-bit numeral: `rootF` ends in a
`modExpStr` with modulus `⟦p⟧_n` (`modExpStr_pairEncode`) and `p − root` is a `subStr` of the
same width (`subStr_pairEncode`). The parity bit extends `acc` by one, and `rs'` keeps the
invariants (its coin string is a suffix of that of `rs`).""",
"dlb_outer_eq": """By induction with `dlb_oStep_shape`, after `i ≤ |rs₀|` rounds the
state is `⟨⟦v⟧_n, ⟨acc, ⟨1^{|rs|}, rounds(rs) ++ rest⟩⟩⟩` with `|acc| = i`, never longer than the
initial state, and from `|rs₀|` rounds on it is fixed (`dlb_oStep_iterate_nil`). So every orbit
state fits `3|X| + 8` (`dlb_oB'`) and the guard never fires (`StateLoop.gstep_iterate_eq`,
`dlb_orbit_eq`); the loop runs `|⟨X, s₀⟩| ≥ |rs₀|` rounds and ends in the state reached at
`|rs₀|`.""",
"dlb_qrF_eq": """`powMod` on numerals is the numeral of `u^{(p−1)/2} mod p`
(`dlb_powMod_natToList`, `val_units_pow`), and the two comparisons with `⟦1⟧` (`leStr_pairEncode`)
say that this value is `1`. For odd `p`, `p / 2 = (p − 1)/2`, and Euler's criterion
(`ZMod.euler_criterion_units`, `mem_QR_iff`) makes that `u ∈ QR_p`.""",
"dlb_rootF_eq": """`qrF` decides `u ∈ QR_p` (`dlb_qrF_eq`), the test of `dlRoot`. On a
residue the root is `powMod ⟦u⟧ ⟦p/4 + 1⟧`, the numeral of `u^{p/4+1}` (`dlb_powMod_natToList`,
`val_units_pow`); otherwise the base is `mulMod ⟦u⟧ ⟦g⁻¹⟧`, the numeral of `u · g⁻¹`
(`dlb_mulMod_natToList`, `ZMod.val_mul`), raised to the same power.""",
"dlb_vote_eq": """The block decodes to `x₀`, so the sampler's output is the encoding
`⟦v⟧_n` of `v = (φ x₀).val` (`Collection.encD_decD`, `fullDLCollection_encD`, `expEnc_eq`), and
the machine computes the same string, the domain sampler being uniform
(`NUPPT.Uniform.runAt_eq`, `NUPPT.layout_eq`, `NUPPT.advInput_eq`). The query
`mulMod ⟦r⟧ (powMod ⟦g⟧ ⟦v⟧)` is the numeral of `r · g^v` (`dlb_powMod_natToList`,
`dlb_mulMod_natToList`, `val_units_pow`); the answer bit is `A.output` on its layout, which is
`dlb_Ai` (`NUPPT.distinguisherL_eq`, `NUPPT.runAt_eq`, `NUPPT.runAtL_eq_output_layout`); and
`halfStr ⟨i, ⟦v⟧_n⟩ = [2v + 2 ≤ p] = [2v < p − 1]`, which is `halfBit (p − 1)` of the exponent.""",
"dlb_oStep_round": """`dlb_oStep_cons` performs the round on strings; Euler's test is
`[y ∈ QR_p]` (`dlb_qrF_eq`) and the root is `⟦dlRoot g y⟧_n` (`dlb_rootF_eq`). Each vote is the
`majOracle` vote on the decoded coins (`dlb_vote_dec`), so the votes are `List.ofFn` of those
votes, whose count of `true`s is the cardinality of the agreeing trials (`dlb_count_ofFn`); with
`ℓ` odd the strict-majority test is `HardcoreBit.majority` (`dlb_majority_eq_of_odd`). In the
other branch `p − ⟦root⟧` is the numeral of `−root` (`subStr_pairEncode`,
`ZMod.val_neg_of_ne_zero`).""",
"dlb_loop_sem": """Induction on `k`; nothing runs at `k = 0`. At `k + 1` the round
coins are the first round's blocks followed by the others (`dlb_roundsL_succ`); one round
(`dlb_oStep_round`) moves to `±dlRoot g y` as `majOracle` decides and prepends the parity bit
`[y ∉ QR_p]` to `acc`. The induction hypothesis on the other `k` rounds, `dlLoop_succ` and
`⟦b :: acc⟧ = b · 2^{|acc|} + ⟦acc⟧` (`dlb_listToNat_cons`) give the claim.""",
"dlb_raw_sem": """Read the layout (`NUPPT.inParam_layout`, `inArg_layout`,
`inAdvice_layout`, `inCoins_layout`): `p` and `g` from the index, `⟦D⟧_n` and `1^κ` from the
advice, the guess block and the round coins from the coins. Each bundle operation is evaluated on
numerals (`subStr_pairEncode`, `dlb_quot_natToList`, `mulStr_pairEncode`,
`dlb_powMod_natToList`, `dlb_invMod_natToList`, `dlb_mulMod_natToList`): `s = ⌊(p − 1)/D⌋`,
`ts = t · s`, `y₀ = y · (g^{ts})⁻¹`, and the fixed data hold `g⁻¹`, `(p − 1)/2`, `p/4 + 1`, the
unary coin lengths and `1^ℓ` (`dlb_fix_proj`). The round loop runs exactly `n` rounds
(`dlb_outer_eq`) and its bits read `dlLoop g (majOracle g A_i ℓ) n y₀ c` (`dlb_loop_sem`); the
output `(bits + ts) mod (p − 1)` (`addStr_pairEncode`, `dlb_rem_natToList`) is the value of
`shiftInverter` (`ZMod.val_natCast`).""",
"dlb_instance": """At the index, `g = expUnit` generates `Z_p^*` (`dlb_isGenerator`) and
`A`'s success is `predProb (expo g) (halfBit (p − 1)) A_i` (`dlb_pred_eq`), so
`invProb_dlInverter_ge` bounds the success of `D := dlInverter g A_i s 2^κ ℓ n` below by
`(1 − n/(ε²ℓ))/2^κ`. Split `B`'s coins into the guess block and the `n·ℓ` trial blocks
(`dlb_split`, a bijection by `dlb_ofFn_split`). Let `P` be the event, read on the *decoded*
sampler outputs, that every block decodes and `D` inverts on the decoded coins; on `P`, `B`
outputs the numeral of `x` (`dlb_raw_sem`). The decoded outputs are `n·ℓ·δ`-close to `some` of
uniform domain elements (`StatClose.prod`, `OneWay.statClose_pi` twice,
`StatClose.abs_uprob_sub_le_prod`), and on uniform coordinates `P` is `D`'s inversion event,
carried to `D`'s coins by a map that pushes uniform to uniform (`dlb_guess_pushesUniform`,
`HardcoreBit.PushesUniform.prodMap`, `ZMod.ringEquivCongr`, `expo_injective`).""",
"dlb_reduction": """Take `n` past `G.n₀` and the thresholds where `δ(n) ≤ ε'/2` for
`ε' = 1/(2n^c)`, `δ_S(n) < n^{−(4c+3)}`, `n^{c+6} < 2^n` and `n ≥ 6000`. Move the average
success to `G.gen`'s coins (`fullDLCollection_index`, `fullDLCollection_coinsEquiv_uexp`); by
`good_instances` (with `2ε'`) and `hbig` (`ExpGroupGen.fullLengthExcept_iff`, `uprob_or_le`) the
coins with success `≥ 1/2 + ε'` and `p ≥ 2^{n−1}` have probability `≥ ε'/2`. On each of them
`16n^c ≤ p − 1`, so `dlb_window_params` gives the window, and `dlb_instance` with
`dlb_arith_success` (`2^κ ≤ 32n^c`, `dlb_two_pow_size_le`) bounds `B`'s success below by
`3/(128n^c) − n·ℓ·δ_S(n)`. `HardcoreBit.uprob_mul_le_uexp` averages over the good set, and
`dlb_arith_loss` with `dlb_arith_final` give `3/(1024 n^{2c})` (`ExpGroupGen.dlProb_eq`).""",
}
lines = src.split("\n")
for name, text in S.items():
    idx = [k for k, l in enumerate(lines) if l.startswith(f"private theorem {name} ")]
    assert len(idx) == 1, name
    j = idx[0] - 1
    while lines[j].startswith("omit"):
        j -= 1
    assert lines[j].rstrip().endswith("-/"), (name, lines[j])
    body = lines[j].rstrip()[:-2].rstrip()
    new = body + "\n\n**Proof sketch.** " + text + " -/"
    lines[j] = new
src = "\n".join(lines)

# ---- E3 (optional): silence the unused-variable warning of the frozen `hg`, proof only
rep("""    (1 - δ) / T ≤ invProb (expo g) (shiftInverter g B₀ s T) := by
  classical
  rw [invProb_def]""",
"""    (1 - δ) / T ≤ invProb (expo g) (shiftInverter g B₀ s T) := by
  classical
  -- the bound holds for every `g`; the frozen statement keeps `hg`, which the proof does not need
  have _ := hg
  rw [invProb_def]""")

open(sys.argv[2], "w").write(src)
