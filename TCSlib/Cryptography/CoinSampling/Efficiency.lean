/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.CoinSampling.Transfer
import TCSlib.Cryptography.CoinSampling.Buckets
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Complexity.ClassP.BinaryArith.Div
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform polynomial-time coin samplers in the Turing-machine model

The efficiency half of the coin-sampling bridge. A `UniformSampler` is **one** polynomial-time
string map `raw` that, on the NUPPT input layout `⟨⟨⟨1^κ, y⟩, α⟩, r⟩`, writes the encoded outcome
of a coin sampler of a finite type `Ω y` on the coins `r`. The parameter word `y` (for buckets,
the numeral of the modulus) is read from the machine's input: there is no κ-indexed family of
programs, no advice and no hard-wired modulus; `κ` only fixes the number of coins. Its machine
is `NUPPT.ofPolyTimeUniform`, a PPT (empty advice), whose output law is the coin draw's
(`expect_toNUPPT_runAt`), hence the exact law up to the failure term (`CoinSampling.Transfer`).

The instance `bucketSampler` reads the modulus `N` from the argument and the coins `x` (with
their number `s`) from the coin slot, tests `x < 2^s − (2^s mod N)`, and writes `true` followed
by `x mod N` as a numeral of the argument's width, or `[]` on rejection. Its polynomial-time
proof `polyTimeComputable_bucketRaw` is assembled only from proved tooling: the layout
projections, the MSB/LE adapters `Encoding.BinaryArith.toLE`/`fromLEPoly`, the zero word of
`EnsembleLemmas.polyTimeComputable_zeros`, the binary arithmetic `Complexity.BinArith.mod`,
`sub` and `lt`, and `polyTimeComputable_ite`. No host and no loop of its own.

## Main definitions

* `CoinSampling.encodeOption`: `[]` for `none`, `true :: enc a` for `some a`.
* `CoinSampling.UniformSampler`: the efficiency contract of a sampler (uniform, modulus as input).
* `CoinSampling.UniformSampler.toNUPPT`: its machine, `NUPPT.ofPolyTimeUniform`.
* `CoinSampling.bucketRaw`, `CoinSampling.bucketSampler`: the uniform bucket sampler.

## Main results

* `CoinSampling.UniformSampler.toNUPPT_uniform`: the machine has empty advice.
* `CoinSampling.UniformSampler.toNUPPT_runAt`, `.expect_toNUPPT_runAt`: the machine's run and
  output law are the coin sampler's.
* `CoinSampling.bucketRaw_layout`: the raw decoder computes the bucket sampler.
* `CoinSampling.polyTimeComputable_bucketRaw`: it is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 23.4 (probabilistic polynomial-time machines: one machine, uniform coins).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, §7.2 (the surrounding machine model of the binary-arithmetic machines).
* [Lem19] D. Lemire, *Fast Random Integer Generation in an Interval*, ACM Trans. Model. Comput.
  Simul. 29(1), 2019; arXiv:1805.10941v4, §3.2, Algorithm 4 (the bucket test and reduction).

**Readers of `Complexity.BinArith`.** `ClassP/BinaryArith` publishes no equation lemmas for
`lt`, `sub` and `mod` (only `beq_def`); the three private readers below
(`binArith_lt_pairEncode`, `binArith_sub_pairEncode`, `binArith_mod_pairEncode`) read the
definitions by `rfl` on encoded pairs. Publishing them beside the definitions is a follow-up.
-/

namespace TCSlib.Cryptography.CoinSampling

open Complexity Turing
open TCSlib.Cryptography.NumberTheory (listToNat)
open TCSlib.Cryptography.Games

/-- **Encoding an outcome or a failure**: `[]` for `none` (gave up), `true :: enc a` for
`some a` (the convention of the list-coin rejection samplers, where rejection is the empty
word). Glue. -/
def encodeOption {Ω : Type} (enc : Ω → List Bool) : Option Ω → List Bool
  | none => []
  | some a => true :: enc a

/-- `encodeOption enc none = []`. -/
theorem encodeOption_none {Ω : Type} (enc : Ω → List Bool) : encodeOption enc none = [] := rfl

/-- `encodeOption enc (some a) = true :: enc a`. -/
theorem encodeOption_some {Ω : Type} (enc : Ω → List Bool) (a : Ω) :
    encodeOption enc (some a) = true :: enc a := rfl

/-- **A uniform sampler** (the efficiency contract of a sampler): a family of finite types
`Ω y` indexed by the **parameter word** `y` that the machine reads from its input (for buckets,
the numeral of the modulus `N`), an encoding of their elements, for every coin count `s` a coin
sampler of `Ω y` reading exactly `s` coins, and **one** polynomial-time string map `raw` that,
on the NUPPT layout `⟨⟨⟨1^κ, y⟩, α⟩, r⟩`, writes the encoded decoded outcome of the coins `r`.
There is no κ-indexed family of programs and no hard-wired modulus: `κ` only fixes the number of
coins (`toNUPPT`), and the machine built from `raw` has empty advice [PS10, Definition 23.4]
(a PPT: one machine, uniform coins). -/
structure UniformSampler where
  /-- The finite type sampled at the parameter word `y`. -/
  Ω : List Bool → Type
  /-- Each sampled type is finite. -/
  [fintype : ∀ y, Fintype (Ω y)]
  /-- The encoding of a sampled element at the parameter `y`. -/
  enc : (y : List Bool) → Ω y → List Bool
  /-- The coin sampler of `Ω y` reading `s` coins. -/
  sampler : (y : List Bool) → (s : ℕ) → CoinSampler (Ω y) s
  /-- The string map computed by the machine. -/
  raw : List Bool → List Bool
  /-- On every layout, `raw` writes the encoded outcome of the coins (any advice slot). -/
  raw_layout : ∀ (κ : ℕ) (y α : List Bool) (s : ℕ) (c : Fin s → Bool),
    raw (NUPPT.layout (List.replicate κ true) y α (List.ofFn c)) =
      encodeOption (enc y) ((sampler y s).dec c)
  /-- The string map is polynomial-time (Turing-machine model). -/
  polyTime : PolyTimeComputable raw

attribute [instance] UniformSampler.fintype

namespace UniformSampler

/-- **The sampler's machine** with `coins(κ)` coins: `NUPPT.ofPolyTimeUniform`, a PPT (empty
advice) [PS10, Definition 23.4]. -/
noncomputable def toNUPPT (U : UniformSampler) (coins : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform U.polyTime coins

/-- `U.toNUPPT coins = NUPPT.ofPolyTimeUniform U.polyTime coins`. -/
theorem toNUPPT_eq (U : UniformSampler) (coins : PolyExpr) :
    U.toNUPPT coins = NUPPT.ofPolyTimeUniform U.polyTime coins := rfl

/-- The sampler's machine is uniform (`NUPPT.ofPolyTimeUniform_uniform`): no advice. -/
theorem toNUPPT_uniform (U : UniformSampler) (coins : PolyExpr) : (U.toNUPPT coins).Uniform :=
  NUPPT.ofPolyTimeUniform_uniform _ _

/-- The sampler's machine reads `coins(κ)` coins (`NUPPT.coins_ofPolyTimeUniform`). -/
theorem toNUPPT_coins (U : UniformSampler) (coins : PolyExpr) :
    (U.toNUPPT coins).coins = coins :=
  NUPPT.coins_ofPolyTimeUniform _ _

/-- **The run of the sampler's machine** on the parameter `y` at `κ` with coins `r` writes the
encoded outcome of the coin sampler `sampler y (coins κ)` on `r` (`NUPPT.runAt_eq`,
`runAtL_ofPolyTimeUniform`, `raw_layout`, `coinsEquiv_ofPolyTimeUniform_ofFn`). Glue. -/
theorem toNUPPT_runAt (U : UniformSampler) (coins : PolyExpr) (κ : ℕ) (y : List Bool)
    (r : (U.toNUPPT coins).Coins κ) :
    (U.toNUPPT coins).runAt κ y r =
      encodeOption (U.enc y) ((U.sampler y (coins.eval κ)).dec
        (NUPPT.coinsEquiv_ofPolyTimeUniform U.polyTime coins κ r)) := by
  rw [NUPPT.runAt_eq]
  refine (NUPPT.runAtL_ofPolyTimeUniform U.polyTime coins κ y (List.ofFn r)).trans ?_
  rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn U.polyTime coins κ r, NUPPT.advInput_eq,
    ← NUPPT.layout_eq]
  exact U.raw_layout κ y [] (coins.eval κ) _

/-- **The machine's output law is the coin draw's**: averaging any `g` over the machine's coins
is averaging `g ∘ encodeOption` over `(sampler y (coins κ)).draw`; with
`CoinSampler.expect_draw` it is the exact law up to the failure term (`toNUPPT_runAt`,
`ProbComp.expect_sample_equiv`). Glue. -/
theorem expect_toNUPPT_runAt (U : UniformSampler) (coins : PolyExpr) (κ : ℕ) (y : List Bool)
    (g : List Bool → ℝ) :
    ProbComp.expect (ProbComp.sample ((U.toNUPPT coins).Coins κ))
        (fun r => g ((U.toNUPPT coins).runAt κ y r)) =
      ProbComp.expect (U.sampler y (coins.eval κ)).draw
        (fun o => g (encodeOption (U.enc y) o)) := by
  simp_rw [U.toNUPPT_runAt coins κ y]
  rw [CoinSampler.draw_eq, ProbComp.expect_map]
  exact ProbComp.expect_sample_equiv (NUPPT.coinsEquiv_ofPolyTimeUniform U.polyTime coins κ)
    (fun c => g (encodeOption (U.enc y) ((U.sampler y (coins.eval κ)).dec c)))

end UniformSampler

/-- **The raw bucket decoder** on the layout `⟨⟨⟨1^κ, ⦃N⦄⟩, α⟩, r⟩`: with `N` the number read from
the argument (MSB first, `listToNat`), `s = |r|` and `x` the number read from the coins, accept
iff `x < ⌊2^s/N⌋·N` and write `true` followed by `x mod N` as a numeral of the argument's width;
write `[]` otherwise [Lem19, §3.2, Algorithm 4] (one round). The modulus is input, never
hard-wired. -/
def bucketRaw (z : List Bool) : List Bool :=
  if listToNat (NUPPT.inCoins z) <
      2 ^ (NUPPT.inCoins z).length / listToNat (NUPPT.inArg z) * listToNat (NUPPT.inArg z) then
    true :: Candidates.natToList (NUPPT.inArg z).length
      (listToNat (NUPPT.inCoins z) % listToNat (NUPPT.inArg z))
  else []

/-- The defining equation of `bucketRaw` (read through `NUPPT.inArg`, `NUPPT.inCoins`). -/
theorem bucketRaw_eq (z : List Bool) :
    bucketRaw z =
      if listToNat (NUPPT.inCoins z) <
          2 ^ (NUPPT.inCoins z).length / listToNat (NUPPT.inArg z) * listToNat (NUPPT.inArg z)
      then
        true :: Candidates.natToList (NUPPT.inArg z).length
          (listToNat (NUPPT.inCoins z) % listToNat (NUPPT.inArg z))
      else [] := rfl

/-- **The raw decoder computes the bucket sampler**: on the layout with argument `y` and coins
`c`, `bucketRaw` writes `encodeOption` of `(bucket ⟦y⟧ s).dec c`, elements written as numerals of
width `|y|` (`NUPPT.inArg_layout`, `NUPPT.inCoins_layout`, `NumberTheory.bitsToNat_eq_listToNat`,
`bucketDec_eq_some_iff`, `bucketDec_eq_none_iff`). Glue. -/
theorem bucketRaw_layout (κ : ℕ) (y α : List Bool) (s : ℕ) (c : Fin s → Bool) :
    bucketRaw (NUPPT.layout (List.replicate κ true) y α (List.ofFn c)) =
      encodeOption (fun a : Fin (listToNat y) => Candidates.natToList y.length a)
        ((bucket (listToNat y) s).dec c) := by
  rw [bucketRaw_eq, NUPPT.inArg_layout, NUPPT.inCoins_layout, List.length_ofFn,
    ← NumberTheory.bitsToNat_eq_listToNat, bucket_dec]
  by_cases h : bitsToNat c < 2 ^ s / listToNat y * listToNat y
  · have hN : 0 < listToNat y := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, Nat.mul_zero] at h
      exact Nat.not_lt_zero _ h
    rw [if_pos h, (bucketDec_eq_some_iff _ s c ⟨_, Nat.mod_lt _ hN⟩).2 ⟨h, rfl⟩,
      encodeOption_some]
  · rw [if_neg h, (bucketDec_eq_none_iff _ s c).2 (not_lt.1 h), encodeOption_none]

/-- `BinArith.lt` on an encoded pair compares the two little-endian values. Reader (`rfl`). -/
private theorem binArith_lt_pairEncode (a b : List Bool) :
    BinArith.lt (pairEncode a b) = decide (LogProg.bitsVal a < LogProg.bitsVal b) := by
  rw [show BinArith.lt (pairEncode a b) = decide (LogProg.bitsVal (pairFstD (pairEncode a b)) <
    LogProg.bitsVal (pairSndD (pairEncode a b))) from rfl, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- `BinArith.sub` on an encoded pair is the truncated difference. Reader (`rfl`). -/
private theorem binArith_sub_pairEncode (a b : List Bool) :
    BinArith.sub (pairEncode a b) = Nat.bits (LogProg.bitsVal a - LogProg.bitsVal b) := by
  rw [show BinArith.sub (pairEncode a b) = Nat.bits (LogProg.bitsVal (pairFstD (pairEncode a b)) -
    LogProg.bitsVal (pairSndD (pairEncode a b))) from rfl, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- `BinArith.mod` on an encoded pair is the remainder. Reader (`rfl`). -/
private theorem binArith_mod_pairEncode (a b : List Bool) :
    BinArith.mod (pairEncode a b) = Nat.bits (LogProg.bitsVal a % LogProg.bitsVal b) := by
  rw [show BinArith.mod (pairEncode a b) = Nat.bits (LogProg.bitsVal (pairFstD (pairEncode a b)) %
    LogProg.bitsVal (pairSndD (pairEncode a b))) from rfl, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- The little-endian word `0^s 1` has value `2^s` (`BinArith.bitsVal_append_singleton`,
`BinArith.bitsVal_eq_zero_iff`). Glue. -/
theorem bitsVal_replicate_false_append_true (s : ℕ) :
    LogProg.bitsVal (List.replicate s false ++ [true]) = 2 ^ s := by
  rw [BinArith.bitsVal_append_singleton, (BinArith.bitsVal_eq_zero_iff _).2 (by simp),
    List.length_replicate, Bool.toNat_true, one_mul, zero_add]

/-- `2^s − (2^s mod N) = ⌊2^s/N⌋ · N` (`Nat.div_add_mod'`), for every `N` (`N = 0` included).
Glue. -/
theorem two_pow_sub_mod_eq (s N : ℕ) : 2 ^ s - 2 ^ s % N = 2 ^ s / N * N := by
  have h := Nat.div_add_mod' (2 ^ s) N
  generalize 2 ^ s / N * N = q at h ⊢
  generalize 2 ^ s % N = r at h ⊢
  omega

/-- **The raw decoder in binary arithmetic**: with `X = toLE (coins)`, `A = toLE (argument)`,
`P = 0^s 1` (`2^s`, little-endian), the threshold `T = P − (P mod A)` and the residue
`R = X mod A`, `bucketRaw z = if lt ⟨X, T⟩ then true :: fromLEPoly var ⟨argument, R⟩ else []`.
Glue: the functional equation behind `polyTimeComputable_bucketRaw`.

**Proof sketch.** Read the binary-arithmetic words as numbers: the `toLE` words have the values
of the MSB words (`bitsVal_toLE`), `0^s 1` has value `2^s`, so the threshold is
`2^s − (2^s mod N) = ⌊2^s/N⌋·N` (`two_pow_sub_mod_eq`) and the residue is `x mod N`, written back
at the argument's width (`fromLEPoly_pairEncode`). The two branches then agree case by case on
`x < ⌊2^s/N⌋·N`. -/
theorem bucketRaw_eq_binArith (z : List Bool) :
    bucketRaw z =
      if BinArith.lt (pairEncode (Encoding.BinaryArith.toLE (NUPPT.inCoins z))
        (BinArith.sub (pairEncode
          (List.replicate (PolyExpr.var.eval (NUPPT.inCoins z).length) false ++ [true])
          (BinArith.mod (pairEncode
            (List.replicate (PolyExpr.var.eval (NUPPT.inCoins z).length) false ++ [true])
            (Encoding.BinaryArith.toLE (NUPPT.inArg z)))))))
      then true :: Encoding.BinaryArith.fromLEPoly .var (pairEncode (NUPPT.inArg z)
        (BinArith.mod (pairEncode (Encoding.BinaryArith.toLE (NUPPT.inCoins z))
          (Encoding.BinaryArith.toLE (NUPPT.inArg z)))))
      else [] := by
  rw [binArith_mod_pairEncode, binArith_mod_pairEncode, binArith_sub_pairEncode,
    binArith_lt_pairEncode, LogProg.bitsVal_bits, LogProg.bitsVal_bits,
    Encoding.BinaryArith.fromLEPoly_pairEncode, LogProg.bitsVal_bits,
    Encoding.BinaryArith.bitsVal_toLE, Encoding.BinaryArith.bitsVal_toLE,
    bitsVal_replicate_false_append_true, two_pow_sub_mod_eq, bucketRaw_eq]
  simp only [PolyExpr.eval_var]
  by_cases h : listToNat (NUPPT.inCoins z) <
      2 ^ (NUPPT.inCoins z).length / listToNat (NUPPT.inArg z) * listToNat (NUPPT.inArg z)
  · rw [if_pos h, if_pos (decide_eq_true h)]
  · rw [if_neg h, if_neg (by rw [decide_eq_false h]; exact Bool.false_ne_true)]

/-- **The bucket decoder is polynomial-time** in the Turing-machine model, from the proved
binary arithmetic of `Complexity.BinArith` [AB09, §7.2].

**Proof sketch.** By `bucketRaw_eq_binArith`, `bucketRaw` is a branch (`polyTimeComputable_ite`)
on a comparison (`BinArith.polyTimeComputable_lt`) of two words built from: the layout
projections (`NUPPT.polyTimeComputable_inArg`, `polyTimeComputable_inCoins`), the MSB-to-LE
adapter (`Encoding.BinaryArith.polyTimeComputable_toLE`), the word `0^s 1`
(`EnsembleLemmas.polyTimeComputable_zeros`, `PolyTimeComputable.append`), `BinArith.mod` and
`BinArith.sub`; the accepting branch prepends `true` (`BinArith.polyTimeComputable_cons`) to the
residue written back at the argument's width (`Encoding.BinaryArith.polyTimeComputable_fromLEPoly`),
the rejecting branch is constant. No host, no loop of its own. -/
theorem polyTimeComputable_bucketRaw : PolyTimeComputable bucketRaw := by
  have hX : PolyTimeComputable fun z => Encoding.BinaryArith.toLE (NUPPT.inCoins z) :=
    Encoding.BinaryArith.polyTimeComputable_toLE.comp NUPPT.polyTimeComputable_inCoins
  have hA : PolyTimeComputable fun z => Encoding.BinaryArith.toLE (NUPPT.inArg z) :=
    Encoding.BinaryArith.polyTimeComputable_toLE.comp NUPPT.polyTimeComputable_inArg
  have hP : PolyTimeComputable fun z =>
      List.replicate (PolyExpr.var.eval (NUPPT.inCoins z).length) false ++ [true] :=
    (EnsembleLemmas.polyTimeComputable_zeros .var NUPPT.polyTimeComputable_inCoins).append
      (polyTimeComputable_const [true])
  have hT := BinArith.polyTimeComputable_sub.comp
    (hP.pairEncode (BinArith.polyTimeComputable_mod.comp (hP.pairEncode hA)))
  have hlt := BinArith.polyTimeComputable_lt.comp (hX.pairEncode hT)
  have hR := BinArith.polyTimeComputable_mod.comp (hX.pairEncode hA)
  have hout := BinArith.polyTimeComputable_cons (p := fun _ => true)
    (polyTimeComputable_const [true])
    ((Encoding.BinaryArith.polyTimeComputable_fromLEPoly .var).comp
      (NUPPT.polyTimeComputable_inArg.pairEncode hR))
  exact (polyTimeComputable_ite hlt hout (polyTimeComputable_const [])).congr
    fun z => (bucketRaw_eq_binArith z).symm

/-- **The uniform bucket sampler**: parameter word `y` = the numeral of the modulus,
`Ω y = Fin ⟦y⟧`, elements written at width `|y|`, the bucket sampler at every coin count, and the
raw decoder `bucketRaw` [Lem19, §3.2, Algorithm 4] (one round). Its machine
`bucketSampler.toNUPPT coins` is one PPT for every modulus and every `κ`. -/
def bucketSampler : UniformSampler where
  Ω y := Fin (listToNat y)
  enc y a := Candidates.natToList y.length a
  sampler y s := bucket (listToNat y) s
  raw := bucketRaw
  raw_layout κ y α s c := bucketRaw_layout κ y α s c
  polyTime := polyTimeComputable_bucketRaw

/-- `bucketSampler.sampler y s = bucket ⟦y⟧ s`. -/
theorem bucketSampler_sampler (y : List Bool) (s : ℕ) :
    bucketSampler.sampler y s = bucket (listToNat y) s := rfl

/-- `bucketSampler.raw = bucketRaw`. -/
theorem bucketSampler_raw : bucketSampler.raw = bucketRaw := rfl

/-- `bucketSampler.enc y a = natToList |y| a`. -/
theorem bucketSampler_enc (y : List Bool) (a : Fin (listToNat y)) :
    bucketSampler.enc y a = Candidates.natToList y.length a := rfl

end TCSlib.Cryptography.CoinSampling
