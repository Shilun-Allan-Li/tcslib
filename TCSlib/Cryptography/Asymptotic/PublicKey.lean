/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Asymptotic.Ensembles
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.PublicKeyLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key encryption

The material of [PS10, §3.10]: public-key encryption schemes [PS10, Definition 102.1],
their security [PS10, Definition 102.2], multi-message security and the fact that for
public-key encryption it follows from single-message security (p. 103, "left as an
exercise"), single-bit security and the bitwise scheme (p. 103), and the construction of a
single-bit secure scheme from a collection of trapdoor permutations with a hard-core
predicate [PS10, Algorithm 104.3, Theorem 104.4].

Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). *Concrete* (one `n`,
samplers and adversaries as functions of uniform coins): the shared-public-key hybrid lemma
`distAdv_multi_le_sum` (the content of the single ⇒ multi-message argument; also the
multi-value hiding of commitments in chapter 4) and the signed predictor identities
`predProb_pkPredictor_false/true`, `exists_pkPredictor` (Lem-104.a: a distinguisher of
`(f(r), b(r))` from `(f(r), ¬b(r))` with advantage `ε` yields a predictor of `b` with success
exactly `1/2 + ε/2`, the indexed form of `owpPredictor`). *Asymptotic*: `PublicKeyScheme`
and `BitPublicKeyScheme` with their security notions, the bitwise scheme
`BitPublicKeyScheme.bitwise`, the scheme `TrapdoorCollection.tdpBitScheme` of Algorithm
104.3 and the three theorems.

The honest iterated machines (`blockEncFun`, `decListFun`) live in
`TCSlib.Cryptography.Asymptotic.BlockEncryptor`; with one-bit blocks they are the encryptor and
decryptor of the bitwise scheme, with `n`-bit blocks the sampling step of the hybrid reductions.
The proof infrastructure — the hybrid machine `exists_hybridMachine` with the hybrid index and
the messages in its advice, the single-machine hybrid bound `exists_hybridBound` on the
samplers `singleDist`/`multiDist`, and the predictor machine `tdpPredictor` of Theorem 104.4 —
lives in `TCSlib.Cryptography.Asymptotic.PublicKeyLemmas`.

**Deviation:** `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the
canonical message. **Deviation:** `Dec` is a deterministic polynomial-time string function
without the parameter `1^n` (the text's `Dec_sk(c)`); schemes that need `n` carry `1^n` in
the secret key. **Deviation:** the single-bit scheme of Algorithm 104.3 samples
`r ← D_i` with the collection's sampler (the text's `r ← {0,1}^n`), carries `⟨1^n, ⟨i, t⟩⟩`
as the secret key, runs the trapdoor inverter on the all-`true` coin string, and takes the
predicate evaluator `H` as explicit data (honest sampling is the field `Collection.sample_spec`,
run-3 audit P3-1).

## Main definitions

* `TCSlib.Cryptography.PublicKeyScheme` — [PS10, Definition 102.1]; `PublicKeyScheme.pkEncDist`
  — `{(pk, sk) ← Gen(1^n) : (pk, Enc_pk(m))}`; `PublicKeyScheme.Secure` —
  [PS10, Definition 102.2]; `PublicKeyScheme.pkMultiEncDist`, `PublicKeyScheme.MultiMessageSecure`
  — multi-message security (p. 103).
* `TCSlib.Cryptography.hybridPlant` — the `j`-th hybrid distinguisher with a shared public key.
* `TCSlib.Cryptography.BitPublicKeyScheme`, `BitPublicKeyScheme.pkEncDist`,
  `BitPublicKeyScheme.SingleBitSecure` — single-bit schemes and single-bit security (p. 103);
  `BitPublicKeyScheme.bitwise` — the bitwise scheme (p. 103).
* `TCSlib.Cryptography.Collection.PredEvaluator` — a polynomial-time evaluator of a predicate
  on a collection; `TCSlib.Cryptography.TrapdoorCollection.tdpGen`, `tdpEnc`, `tdpDec`,
  `tdpBitScheme` — [PS10, Algorithm 104.3].
* `TCSlib.Cryptography.pkPredictor` — the predictor `A'` of [PS10, Theorem 104.4, proof].

## Main results

* `TCSlib.Cryptography.distAdv_multi_le_sum` — the shared-key hybrid bound (Thm-103.d, concrete).
* `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` — single ⇒ multi-message
  security for public-key encryption [PS10, p. 103].
* `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` — bitwise encryption under a
  single-bit secure scheme is secure [PS10, p. 103].
* `TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAt`, `BitPublicKeyScheme.singleBitSecure_iff`
  — unfolding of the bitwise encryptor; the negligible-advantage form of single-bit security (proved).
* `TCSlib.Cryptography.predProb_pkPredictor_false`, `predProb_pkPredictor_true`,
  `exists_pkPredictor` — Lem-104.a (proved from [Gar26, Theorem 3.2]).
* `TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_singleBitSecure` — [PS10, Theorem 104.4];
  `TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure` — the text's hypothesis
  "trapdoor permutations exist" through Goldreich–Levin.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.10: Definitions 102.1, 102.2, p. 103, Algorithm 104.3, Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Theorem 3.2 (the predictor from a distinguisher).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset
open PrivateKeyScheme (encodeList)

/-! ## Public-key encryption schemes [PS10, Definition 102.1, 102.2] -/

/-- A **public-key encryption scheme** [PS10, Definition 102.1]: a PPT key generator
`Gen(1^n) = ⟨pk, sk⟩`, a PPT encryptor `Enc_pk(m)` for `m ∈ {0,1}^n` (activated on `⟨pk, m⟩`),
a deterministic polynomial-time decryptor `Dec_sk(c)` (applied to `⟨sk, c⟩`, output decoded as an
`n`-bit string, `⊥` = any other output), with perfect correctness (clause (5)) for every coin
string.

**Deviation:** `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the
canonical message. -/
structure PublicKeyScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(m)`, activated on `⟨pk, m⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness [PS10, Definition 102.1 (5)]. -/
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m

namespace PublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc_pk(m)⟩}` of [PS10, Definition 102.2] as a
sampler from the coins of `Gen` and `Enc`. -/
def pkEncDist (S : PublicKeyScheme) (n : ℕ) (m : Fin n → Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (List.ofFn m)) r.2)

/-- **Secure public-key encryption** [PS10, Definition 102.2]: for every non-uniform PPT `D`
there is a negligible `ε` such that for all `n` and `m₀, m₁ ∈ {0,1}^n`, `D` distinguishes
`⟨pk, Enc_pk(m₀)⟩` from `⟨pk, Enc_pk(m₁)⟩` with advantage at most `ε(n)`.

**Deviation:** `D` receives `1^n` with its sample (D5). -/
def Secure (S : PublicKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool),
    distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n

end PublicKeyScheme

namespace PublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, ⟨Enc_pk(m₀), …, Enc_pk(m_q)⟩⟩}` of the
multi-message security notion for public-key encryption [PS10, p. 103]: `q + 1` encryptions
under one public key with independent encryption coins. -/
def pkMultiEncDist (S : PublicKeyScheme) (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool) :
    S.gen.Coins n × (Fin (q + 1) → S.enc.Coins n) → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1)) (encodeList (List.ofFn fun i =>
    S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (List.ofFn (m i))) (r.2 i)))

/-- **Multi-message secure public-key encryption** [PS10, p. 103, "we can extend the
definition to multi-message security", i.e. Definition 93.1 with a public key]: for every
non-uniform PPT `D` and polynomial `q` there is a negligible `ε` such that for all `n` and all
message vectors `m, m' ∈ ({0,1}^n)^{q(n)+1}`, `D` distinguishes the encryptions of `m` from
those of `m'` under one key pair with advantage at most `ε(n)` (the public key is part of the
sample).

**Deviation:** `D` receives `1^n`; the ciphertexts are nested pairs. -/
def MultiMessageSecure (S : PublicKeyScheme) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
      distAdv (S.pkMultiEncDist n (q.eval n) m) (S.pkMultiEncDist n (q.eval n) m')
        (D.distinguisherL n) ≤ ε n

end PublicKeyScheme

/-! ## The shared-key hybrid lemma (Thm-103.d, concrete) -/

/-- The `j`-th hybrid distinguisher of the single ⇒ multi-message argument
[PS10, p. 103, "the key point here is that we can efficiently generate encryptions of any
message, without knowing the secret key"]: on a sample `⟨pk, c⟩` it encrypts `m'_0, …, m'_{j-1}`
and `m_{j+1}, …, m_q` itself under `pk` with its own coins `r.1`, plants `c` at position `j`
and runs `D` with coins `r.2`. -/
def hybridPlant {π μ γ ρ ρ' : Type*} {q : ℕ} (E : π → μ → ρ → γ) (m m' : Fin (q + 1) → μ)
    (j : Fin (q + 1)) (D : π × (Fin (q + 1) → γ) → ρ' → Bool) :
    π × γ → (Fin (q + 1) → ρ) × ρ' → Bool :=
  fun pc r => D (pc.1, fun i =>
    if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2 else E pc.1 (m i) (r.1 i)) r.2

/-- **The hybrid bound with a shared public parameter** (the concrete content of the single ⇒
multi-message theorem for public-key encryption [PS10, p. 103] and of the multi-value hiding of
commitments [PS10, Theorem 126.4, "show this!"]): for a parameter sampler `P` (the public key
from `Gen`'s coins), an encryptor `E pk m r`, message vectors `m, m'` and any `D`, the advantage
of `D` between the `q + 1` encryptions of `m` and of `m'` under one `pk` is at most the sum over
`j` of the advantages of `hybridPlant E m m' j D` between the single encryptions of `m_j` and
`m'_j`. (Unlike `exists_multicopyRed_ge` the copies share the parameter `pk` and the samplers
depend on the position.)

**Proof sketch.** Hybrids `H_j := ⟨pk, (E pk m'_i r_i)_{i<j}, (E pk m_i r_i)_{i≥j}⟩` on the seeds
`κ × (Fin (q+1) → ρ)`, `H_0` and `H_{q+1}` the two sides; `abs_sub_le_sum_hybrids` over
`j ∈ range (q+1)` (`Fin.sum_univ_eq_sum_range`). Each gap `|Pr[D(H_j)] − Pr[D(H_{j+1})]|` equals
the advantage of `hybridPlant E m m' j D` between `⟨pk, E pk m_j r⟩` and `⟨pk, E pk m'_j r⟩`:
`acceptProb (⟨pk, E pk m_j r⟩) (hybridPlant …)` is the probability over `(k, r), (v, r')` of
`D ⟨P k, plant_j (E (P k) m_j r) v⟩ r'`, in which the coordinate `v j` is unused; replacing
`v` by `update v j r` (`OneWay.uprob_update`, `[Nonempty ρ]`) and regrouping the seeds
(`uprob_comp_equiv`) gives `Pr[D(H_j)]`, and likewise `m'_j` gives `Pr[D(H_{j+1})]`
(`Function.update_apply`, the `if` cases `i < j`, `i = j`, `i > j`). -/
theorem distAdv_multi_le_sum {κ π μ γ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ']
    [Nonempty ρ] {q : ℕ} (P : κ → π) (E : π → μ → ρ → γ) (m m' : Fin (q + 1) → μ)
    (D : π × (Fin (q + 1) → γ) → ρ' → Bool) :
    distAdv (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D ≤
    ∑ j : Fin (q + 1), distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
      (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2)) (hybridPlant E m m' j D) :=
  distAdv_tuple_le_sum P E m m' D

/-! ## Single-bit schemes and the bitwise scheme [PS10, p. 103] -/

/-- A **single-bit public-key encryption scheme**: [PS10, Definition 102.1] with message space
`{0,1}` (the message `b` is the string `[b]`), as used in [PS10, p. 103 and Algorithm 104.3]. The
components and the conventions are those of `PublicKeyScheme`; correctness is `Dec_sk(Enc_pk(b)) = [b]`
for every coin string. -/
structure BitPublicKeyScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(b)`, activated on `⟨pk, [b]⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness on both bits, for every coin string. -/
  correct : ∀ n (b : Bool) (rg : gen.Coins n) (re : enc.Coins n),
    dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) [b]) re)) = [b]

namespace BitPublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc_pk(b)⟩}` of a single-bit scheme. -/
def pkEncDist (S : BitPublicKeyScheme) (n : ℕ) (b : Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) [b]) r.2)

/-- **Single-bit security** [PS10, p. 103, "we only require that encryptions of 0 and 1 are
indistinguishable"]: Definition 102.2 with message space `{0,1}`: for every non-uniform PPT `D`
there is a negligible `ε` with, for all `n` and `b₀, b₁ ∈ {0,1}`, advantage at most `ε(n)`
between `⟨pk, Enc_pk(b₀)⟩` and `⟨pk, Enc_pk(b₁)⟩`. -/
def SingleBitSecure (S : BitPublicKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (b₀ b₁ : Bool),
    distAdv (S.pkEncDist n b₀) (S.pkEncDist n b₁) (D.distinguisherL n) ≤ ε n

/-- **Single-bit security is the negligibility of the `0`-versus-`1` advantage** (the only
nontrivial pair of messages; sanity for the quantifier form of the definition).

**Proof sketch.** `→`: specialize to `(false, true)` and `Negligible.mono` (the advantage is
nonnegative). `←`: take `ε n` to be the `(false, true)` advantage itself; the pairs `(b, b)` have
advantage `0` and `(true, false)` the same advantage (`abs_sub_comm`). -/
theorem singleBitSecure_iff (S : BitPublicKeyScheme) : S.SingleBitSecure ↔
    ∀ D : NUPPT, Negligible fun n =>
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) := by
  constructor
  · intro h D
    obtain ⟨ε, hε, hle⟩ := h D
    refine hε.mono ⟨0, fun n _ => ?_⟩
    have h0 : 0 ≤ distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) :=
      abs_nonneg _
    rw [abs_of_nonneg h0]
    exact (hle n false true).trans (le_abs_self _)
  · intro h D
    refine ⟨_, h D, fun n b₀ b₁ => ?_⟩
    cases b₀ <;> cases b₁
    · simp only [distAdv, sub_self, abs_zero]; exact abs_nonneg _
    · exact le_rfl
    · exact (abs_sub_comm _ _).le
    · simp only [distAdv, sub_self, abs_zero]; exact abs_nonneg _

/-- The raw encryptor of the bitwise scheme on the layout `⟨⟨⟨1^n, ⟨pk, m⟩⟩, []⟩, r⟩`: the block
encryptor with one-bit blocks on the state `⟨1^n, ⟨pk, ⟨m, r⟩⟩⟩`. -/
def bitwiseEncFun (S : BitPublicKeyScheme) (z : List Bool) : List Bool :=
  blockEncFun S.enc.output (.const 1) S.enc.coins
    (blockState (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z))
      (NUPPT.inCoins z))

/-- The raw encryptor of the bitwise scheme is polynomial-time. -/
theorem bitwiseEncFun_poly (S : BitPublicKeyScheme) : PolyTimeComputable S.bitwiseEncFun :=
  (blockEncFun_poly S.enc.polyTimeComputable_output _ _).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins)))

/-- A string of the right length is the encoding of a typed string. -/
private theorem exists_ofFn_eq {ℓ : ℕ} (w : List Bool) (h : w.length = ℓ) :
    ∃ x : Fin ℓ → Bool, List.ofFn x = w := by
  subst h
  exact ⟨fun j => w.get j, List.ofFn_get w⟩

/-- A `flatMap` of singletons indexed by `Fin n` is the string. -/
private theorem flatMap_ofFn_singleton {n : ℕ} (f : Fin n → List Bool) (g : List Bool → List Bool)
    (m : Fin n → Bool) (h : ∀ i, g (f i) = [m i]) :
    (List.ofFn f).flatMap g = List.ofFn m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.flatMap_cons, h, ih (fun i => f i.succ) (fun i => m i.succ)
      (fun i => h i.succ)]
    rfl

/-- **Unfolding of the bitwise encryptor**: `Enc'(1^n, ⟨pk, m⟩; r)` is the tuple of the `n`
single-bit encryptions `Enc(1^n, ⟨pk, [m_i]⟩; r_i)` with the consecutive `B(n)`-coin segments
`r_i` of `r` (`blockEncFun_spec`, `blockList_ofFn`, `Uniform.runAtL_eq`). -/
theorem bitwise_enc_runAtL (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool) (m : Fin n → Bool)
    (r : List Bool) :
    (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAtL n
        (pairEncode pk (List.ofFn m)) r =
      encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i r)) := by
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [bitwiseEncFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput,
    pairFstD_pairEncode, pairSndD_pairEncode, blockEncFun]
  rw [blockEncFun_spec S.enc.output (.const 1) S.enc.coins (List.replicate n true) pk
    _ (List.ofFn m) r (by
      simp only [blockState, length_pairEncode, List.length_ofFn, PolyExpr.eval_const, mul_one]
      omega)]
  simp only [PolyExpr.eval_const, List.length_replicate]
  rw [blockList_ofFn S.enc.output _ _ _ n m r _ (by
    simp only [blockState, length_pairEncode, List.length_ofFn]; omega)]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [S.enc_uniform.runAtL_eq]
  rfl

/-- **Unfolding of the bitwise encryptor**, typed coins: `Enc'(1^n, ⟨pk, m⟩; r)` is the tuple of
the single-bit encryptions with the consecutive `B(n)`-coin segments of `List.ofFn r`. -/
theorem bitwise_enc_runAt (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool) (m : Fin n → Bool)
    (r : (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).Coins n) :
    (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAt n
        (pairEncode pk (List.ofFn m)) r =
      encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i (List.ofFn r))) := by
  rw [NUPPT.runAt_eq, bitwise_enc_runAtL]

/-- **The bitwise scheme** [PS10, p. 103, "simply encrypting each bit of the message using the
single-bit secure encryption"]: the same key generator, `Enc'_pk(m) = ⟨Enc_pk(m_1), …, Enc_pk(m_n)⟩`
with `n · B(n)` coins (`blockEncFun`, one-bit blocks), `Dec'_sk(c) = Dec_sk(c_1) ‖ ⋯ ‖ Dec_sk(c_n)`
(`decListFun`), decoded as an `n`-bit string.

**Deviation:** the text's "`Dec` returns `⊥` if any bit decrypts to `⊥`" is realised only up
to the output-length convention of D5 (an honest ciphertext decrypts correctly; a malformed one
decrypts to a wrong-length string or to an arbitrary `n`-bit string). -/
noncomputable def bitwise (S : BitPublicKeyScheme) : PublicKeyScheme where
  gen := S.gen
  enc := NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)
  dec := decListFun S.dec
  gen_uniform := S.gen_uniform
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := decListFun_poly S.dec_poly
  correct := by
    intro n m rg re
    rw [bitwise_enc_runAt, decListFun,
      decListFun_spec S.dec _ _ _ (by
        refine (length_le_length_encodeList _).trans ?_
        simp only [length_pairEncode]
        omega)]
    rw [flatMap_ofFn_singleton _ _ m (fun i => ?_)]
    · exact decodeFin_ofFn m
    · have hlen : (coinBlock (S.enc.coinLen n) i (List.ofFn re)).length = S.enc.coinLen n := by
        simp only [coinBlock, List.length_take, List.length_drop, List.length_ofFn, NUPPT.coinLen,
          NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_mul, PolyExpr.eval_var]
        have hi : (i : ℕ) + 1 ≤ n := i.isLt
        have := Nat.mul_le_mul_right (S.enc.coins.eval n) hi
        rw [Nat.add_mul, one_mul] at this
        omega
      obtain ⟨re', hre'⟩ := exists_ofFn_eq _ hlen
      have := S.correct n (m i) rg re'
      rw [NUPPT.runAt_eq (A := S.enc), hre'] at this
      exact this

/-- The single-bit sampler is `singleDist` on the one-bit message `[b]`. -/
private theorem pkEncDist_eq_singleDist (S : BitPublicKeyScheme) (n : ℕ) (b : Bool) :
    S.pkEncDist n b = singleDist S.gen S.enc n 1 (fun _ => b) := by
  funext r
  simp only [BitPublicKeyScheme.pkEncDist, singleDist, ofFn_fin_one]

/-- The ciphertext of the bitwise scheme on the coin blocks `v` is the tuple of the single-bit
encryptions with coins `v_i` (`bitwise_enc_runAt`, `coinBlock_ofFn_coinBlocks`): the sampler
`S.bitwise.pkEncDist n m` read through `coinBlocks` is `multiDist` with one-bit blocks. -/
private theorem bitwise_pkEncDist_coinBlocks (S : BitPublicKeyScheme) (n : ℕ) (m : Fin n → Bool)
    (r : S.gen.Coins n) (v : Fin n → S.enc.Coins n) :
    S.bitwise.pkEncDist n m (r, coinBlocks n (S.enc.coinLen n) v) =
      multiDist S.gen S.enc n n 1 (fun i _ => m i) (r, v) := by
  show pairEncode (pairFstD (S.gen.runAt n [] r))
      ((NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAt n
        (pairEncode (pairFstD (S.gen.runAt n [] r)) (List.ofFn m)) (coinBlocks n (S.enc.coinLen n) v)) =
    _
  rw [bitwise_enc_runAt]
  simp only [multiDist]
  refine congrArg _ (congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_))
  rw [coinBlock_ofFn_coinBlocks, ← NUPPT.runAt_eq, ofFn_fin_one]

/-- **The bitwise scheme's ciphertexts as a tuple of single-bit encryptions**: the acceptance
probability of any distinguisher on `S.bitwise.pkEncDist n m` is its acceptance probability on
`multiDist` with one-bit blocks (the coin bijection `coinBlocks`, `uprob_comp_equiv`). -/
private theorem acceptProb_bitwise_pkEncDist (S : BitPublicKeyScheme) (n : ℕ) (m : Fin n → Bool)
    {ρ : Type*} [Fintype ρ] (Dst : List Bool → ρ → Bool) :
    acceptProb (S.bitwise.pkEncDist n m) Dst =
      acceptProb (multiDist S.gen S.enc n n 1 (fun i _ => m i)) Dst := by
  unfold acceptProb
  rw [← uprob_comp_equiv
    (((Equiv.refl (S.gen.Coins n)).prodCongr (coinBlocks n (S.enc.coinLen n))).prodCongr
      (Equiv.refl ρ))]
  congr 1
  funext z
  obtain ⟨⟨r, v⟩, ρ'⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  rw [bitwise_pkEncDist_coinBlocks]

/-- **Bitwise encryption under a single-bit secure scheme is secure** [PS10, p. 103, "the security
of the new scheme follows directly from the multi-message security (which is equivalent to
traditional security) of the single-bit secure encryption scheme"].

**Proof sketch.** Fix a non-uniform PPT `D`. At each `n` choose `(m₀ⁿ, m₁ⁿ)` maximizing the
advantage of `D.distinguisherL n` between `pkEncDist n m₀` and `pkEncDist n m₁` of `S.bitwise`
(`Finset.exists_max_image`). By `bitwise_enc_runAtL` and the coin split
`(Fin (n · B n) → Bool) ≃ (Fin n → Fin (B n) → Bool)` (`FunFamily.blocks`, `coinBlock` of
`List.ofFn`; `acceptProb_comp_equiv`), the two samples are the shared-key tuples of
`distAdv_multi_le_sum` with `P := pk`, `E pk [b] r := Enc(1^n, ⟨pk, [b]⟩; r)`, `q := n − 1`
(for `n = 0` the advantage is `0`), after moving the string encoding into `D`
(`distAdv_comp`). Hence the advantage is at most `∑_{j<n}` of the advantages of
`hybridPlant E m₀ m₁ j D` between the single-bit encryptions of `m₀ⁿ_j` and `m₁ⁿ_j`, each at
most that of the machine `B_j`: advice `⟨⟨1^j, ⟨ofFn m₀ⁿ, ofFn m₁ⁿ⟩⟩, D.advice n⟩`
(`NUPPT.exists_withAdvice`), coins `var · S.enc.coins + D.coins` (`NUPPT.exists_split`), which
on `⟨pk, c⟩` encrypts the first `j` bits of `m₁ⁿ` and the last `n − j − 1` bits of `m₀ⁿ` with
`blockEncFun` (one-bit blocks, `blockEncFun_spec`), assembles the tuple
`encodeList l₁ ++ ⟨c, []⟩ ++ encodeList l₂` (`encodeList_eq_flatMap`, `pairEncode_nil_append`),
and runs `D` (`NUPPT.exists_comp`); by `singleBitSecure_iff` applied to `h` (and the `(b, b)` pairs
being `0`) each term is `≤ ε_j(n)`. Over a single machine `B` with the index `j` in the advice
(`Finset.exists_max_image` over `j`), the total is `≤ n · ε(n)`, negligible by
`Negligible.mul_pow`; the maximality of `(m₀ⁿ, m₁ⁿ)` gives the uniform bound. (Formally: `acceptProb_bitwise_pkEncDist`
reads the ciphertexts as `multiDist` with one-bit blocks, and `exists_hybridBound` with
`K := var`, `L := const 1` supplies the single machine `B` and the bound `n · ε(n)`.) -/
theorem SingleBitSecure.bitwise {S : BitPublicKeyScheme} (h : S.SingleBitSecure) :
    S.bitwise.Secure := by
  intro D
  -- the worst message pair at each parameter (hard-wired into the reduction)
  have hmax : ∀ n, ∃ p : (Fin n → Bool) × (Fin n → Bool), ∀ q : (Fin n → Bool) × (Fin n → Bool),
      distAdv (S.bitwise.pkEncDist n q.1) (S.bitwise.pkEncDist n q.2) (D.distinguisherL n) ≤
        distAdv (S.bitwise.pkEncDist n p.1) (S.bitwise.pkEncDist n p.2) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun q : (Fin n → Bool) × (Fin n → Bool) =>
        distAdv (S.bitwise.pkEncDist n q.1) (S.bitwise.pkEncDist n q.2) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun q => hp q (Finset.mem_univ q)⟩
  choose μ hμ using hmax
  -- the hybrid machine for the worst pairs: `n` positions, one-bit blocks
  obtain ⟨B, hB⟩ := exists_hybridBound S.gen S.enc D S.enc_uniform .var (.const 1)
    (fun n i _ => (μ n).1 i) (fun n i _ => (μ n).2 i)
  obtain ⟨ε, hε, hBε⟩ := h B
  refine ⟨fun n => (n : ℝ) * ε n, EnsembleLemmas.negligible_polyExpr_mul .var hε, fun n m₀ m₁ => ?_⟩
  refine (hμ n (m₀, m₁)).trans ?_
  have hε0 : 0 ≤ ε n := (abs_nonneg _).trans (hBε n false false)
  have hsingle : ∀ msg msg' : Fin 1 → Bool,
      distAdv (singleDist S.gen S.enc n 1 msg) (singleDist S.gen S.enc n 1 msg')
        (B.distinguisherL n) ≤ ε n := by
    intro msg msg'
    have h1 : msg = fun _ => msg 0 := funext fun i => congrArg msg (Subsingleton.elim i 0)
    have h2 : msg' = fun _ => msg' 0 := funext fun i => congrArg msg' (Subsingleton.elim i 0)
    rw [h1, h2, ← S.pkEncDist_eq_singleDist, ← S.pkEncDist_eq_singleDist]
    exact hBε n _ _
  have hn := hB n (ε n) hε0 hsingle
  unfold distAdv at hn ⊢
  rw [acceptProb_bitwise_pkEncDist, acceptProb_bitwise_pkEncDist]
  exact hn

end BitPublicKeyScheme

/-! ## Single ⇒ multi-message security for public-key encryption [PS10, p. 103] -/

/-- **For public-key encryption, single-message security implies multi-message security**
[PS10, p. 103, "multi-message security is equivalent to single-message security … We leave it as
an exercise to the reader"].

**Proof sketch.** Fix `D` and `q`. At each `n` choose `(mⁿ, m'ⁿ)` maximizing the advantage of
`D.distinguisherL n` between `pkMultiEncDist n (q n) m` and `pkMultiEncDist n (q n) m'`
(`Finset.exists_max_image`). The samples are the shared-key tuples of `distAdv_multi_le_sum`
with `P := pk ∘ Gen`, `E pk m r := Enc(1^n, ⟨pk, m⟩; r)` after moving the tuple encoding into `D`
(`distAdv_comp`), so the advantage is at most `∑_{j ≤ q n}` of the advantages of
`hybridPlant E mⁿ m'ⁿ j D` between `pkEncDist n (mⁿ_j)` and `pkEncDist n (m'ⁿ_j)`. Each is the
advantage of the machine `B_j`: advice `⟨⟨1^j, ⟨ofFn mⁿ, ofFn m'ⁿ⟩⟩, D.advice n⟩`
(`NUPPT.exists_withAdvice`, bound `2(q+1)·var + …`), coins `q · S.enc.coins + D.coins`
(`NUPPT.exists_split`), which on `⟨pk, c⟩` encrypts the other `q n` messages with
`blockEncFun` (`n`-bit blocks, `blockEncFun_spec`), plants `c` at position `j`
(`encodeList_eq_flatMap`, `pairEncode_nil_append`) and runs `D` (`NUPPT.exists_comp`); by `h`
each term is `≤ ε(n)` for the single machine `B` with the index `j` in its advice (take the
maximizing `j` per `n`), so the total is `≤ (q n + 1) ε(n)`, negligible by `Negligible.mul_pow`
and `PolyExpr.eval_le`; maximality of `(mⁿ, m'ⁿ)` gives the uniform bound. (Formally:
`exists_hybridBound` with `K := q + 1`, `L := var` on the samplers `singleDist`/`multiDist`,
which are `pkEncDist`/`pkMultiEncDist` definitionally.) -/
theorem PublicKeyScheme.Secure.multiMessageSecure {S : PublicKeyScheme} (h : S.Secure) :
    S.MultiMessageSecure := by
  intro D q
  -- the worst pair of message vectors at each parameter (hard-wired into the reduction)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
      ∀ p' : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
        distAdv (S.pkMultiEncDist n (q.eval n) p'.1) (S.pkMultiEncDist n (q.eval n) p'.2)
            (D.distinguisherL n) ≤
          distAdv (S.pkMultiEncDist n (q.eval n) p.1) (S.pkMultiEncDist n (q.eval n) p.2)
            (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun p' : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
        distAdv (S.pkMultiEncDist n (q.eval n) p'.1) (S.pkMultiEncDist n (q.eval n) p'.2)
          (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun p' => hp p' (Finset.mem_univ p')⟩
  choose μ hμ using hmax
  -- the hybrid machine for the worst pairs: `q + 1` positions, `n`-bit blocks
  obtain ⟨B, hB⟩ := exists_hybridBound S.gen S.enc D S.enc_uniform (.add q (.const 1)) .var
    (fun n => (μ n).1) (fun n => (μ n).2)
  obtain ⟨ε, hε, hBε⟩ := h B
  refine ⟨fun n => (((PolyExpr.add q (.const 1)).eval n : ℕ) : ℝ) * ε n,
    EnsembleLemmas.negligible_polyExpr_mul _ hε, fun n m m' => ?_⟩
  refine (hμ n (m, m')).trans ?_
  have hε0 : 0 ≤ ε n := (abs_nonneg _).trans (hBε n (fun _ => false) (fun _ => false))
  exact hB n (ε n) hε0 fun msg msg' => hBε n msg msg'

/-! ## Algorithm 104.3: a single-bit scheme from a trapdoor permutation with a hard-core bit -/

/-- A **polynomial-time evaluator of a predicate on a collection**: `H ⟨i, w⟩ = [h_i(x)]` for
every string `w` that decodes to `x ∈ D_i` (the efficiency clause of `Collection.HardCore`
strengthened from canonical encodings to all decodable strings, since the outputs of the
sampler and of the trapdoor inverter need not be canonical; the field `Collection.sample_spec`
plays the same role for `eval`). -/
structure Collection.PredEvaluator (F : Collection) (h : ∀ i, F.D i → Bool) where
  /-- The evaluator. -/
  H : List Bool → List Bool
  /-- The evaluator is polynomial-time. -/
  poly : PolyTimeComputable H
  /-- `H ⟨i, w⟩ = [h_i x]` whenever `w` decodes to `x`. -/
  spec : ∀ i w x, F.decD i w = some x → H (pairEncode i w) = [h i x]

namespace TrapdoorCollection

variable (T : TrapdoorCollection)

/-- The raw key generator of [PS10, Algorithm 104.3] on `⟨⟨⟨1^n, []⟩, []⟩, r⟩`: run `Gen_T(1^n; r) = ⟨i, t⟩`
and output `⟨pk, sk⟩ = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩`. -/
def tdpGenFun (z : List Bool) : List Bool :=
  pairEncode (pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))
    (pairEncode (NUPPT.inParam z)
      (pairEncode (pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))
        (pairSndD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))))

/-- The raw key generator is polynomial-time. -/
theorem tdpGenFun_poly : PolyTimeComputable T.tdpGenFun :=
  have ho : PolyTimeComputable fun z =>
      T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z)) :=
    T.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
      NUPPT.polyTimeComputable_inCoins)
  (polyTimeComputable_pairFstD.comp ho).pairEncode (NUPPT.polyTimeComputable_inParam.pairEncode
    ((polyTimeComputable_pairFstD.comp ho).pairEncode (polyTimeComputable_pairSndD.comp ho)))

/-- The raw encryptor of [PS10, Algorithm 104.3] on `⟨⟨⟨1^n, ⟨i, [m]⟩⟩, []⟩, s⟩`: sample
`w ← Sample(1^n, i; s)` and output `⟨eval ⟨i, w⟩, H ⟨i, w⟩ ⊕ [m]⟩ = ⟨f_i(r), b_i(r) ⊕ m⟩`. -/
def tdpEncFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode
    (T.eval (pairEncode (pairFstD (NUPPT.inArg z))
      (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) [] (NUPPT.inCoins z)))))
    (List.zipWith xor
      (H (pairEncode (pairFstD (NUPPT.inArg z))
        (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) [] (NUPPT.inCoins z)))))
      (pairSndD (NUPPT.inArg z)))

/-- The raw encryptor is polynomial-time (`polyTimeComputable_pairXor` for the mask). -/
theorem tdpEncFun_poly {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (T.tdpEncFun H) := by
  have hi := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hiw := hi.pairEncode (T.sample.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hi
      (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins))
  have h := (T.eval_poly.comp hiw).pairEncode (polyTimeComputable_pairXor.comp
    ((hH.comp hiw).pairEncode (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg)))
  convert h using 1
  funext z
  simp only [tdpEncFun, Function.comp, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The raw decryptor of [PS10, Algorithm 104.3] on `⟨⟨u, ⟨i, t⟩⟩, ⟨c₁, c₂⟩⟩`: run the trapdoor
inverter `Inv(u, ⟨t, c₁⟩)` on the all-`true` coin string of length `coins(|u|)` and output
`H ⟨i, Inv(…)⟩ ⊕ c₂ = b_i(f_i^{-1}(c₁)) ⊕ c₂`. -/
def tdpDecFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor
    (H (pairEncode (pairFstD (pairSndD (pairFstD z)))
      (T.inv.output (NUPPT.layout (pairFstD (pairFstD z))
        (pairEncode (pairSndD (pairSndD (pairFstD z))) (pairFstD (pairSndD z))) []
        (List.replicate (T.inv.coins.eval (pairFstD (pairFstD z)).length) true)))))
    (pairSndD (pairSndD z))

/-- The raw decryptor is polynomial-time (`polyTimeComputable_unaryPoly` for the coin string). -/
theorem tdpDecFun_poly {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (T.tdpDecFun H) := by
  have hsk := polyTimeComputable_pairFstD
  have hu := polyTimeComputable_pairFstD.comp hsk
  have hi := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hsk)
  have ht := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hsk)
  have hc₁ := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hc₂ := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hw := T.inv.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout hu
    (ht.pairEncode hc₁) (polyTimeComputable_const [])
    ((polyTimeComputable_unaryPoly T.inv.coins).comp hu))
  have h := polyTimeComputable_pairXor.comp ((hH.comp (hi.pairEncode hw)).pairEncode hc₂)
  convert h using 1
  funext z
  simp only [tdpDecFun, Function.comp, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The key generator of [PS10, Algorithm 104.3]: `Gen_T`'s coins, output `⟨i, ⟨1^n, ⟨i, t⟩⟩⟩`. -/
noncomputable def tdpGen : NUPPT := NUPPT.ofPolyTimeUniform T.tdpGenFun_poly T.gen.coins

/-- The encryptor of [PS10, Algorithm 104.3] with the predicate evaluator `H`: the sampler's coins. -/
noncomputable def tdpEnc {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) : NUPPT :=
  NUPPT.ofPolyTimeUniform (T.tdpEncFun_poly E.poly) T.sample.coins

/-- Unfolding: `Gen(1^n; r) = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩` with `⟨i, t⟩ = Gen_T(1^n; r)`. -/
theorem tdpGen_runAt (n : ℕ) (r : T.gen.Coins n) :
    T.tdpGen.runAt n [] r =
      pairEncode (T.index n r) (pairEncode (List.replicate n true) (pairEncode (T.index n r) (T.trap n r))) := by
  rw [NUPPT.runAt_eq]
  unfold tdpGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [tdpGenFun, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput, pairFstD_pairEncode,
    pairSndD_pairEncode, Collection.index, Collection.trap, T.gen_uniform.runAt_eq]
  rfl

/-- Unfolding: `Enc(1^n, ⟨i, [b]⟩; s) = ⟨eval ⟨i, w⟩, H ⟨i, w⟩ ⊕ [b]⟩` with `w = Sample(1^n, i; s)`. -/
theorem tdpEnc_runAt {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) (n : ℕ)
    (i : List Bool) (b : Bool) (s : T.sample.Coins n) :
    (T.tdpEnc E).runAt n (pairEncode i [b]) s =
      pairEncode (T.eval (pairEncode i (T.sample.runAt n i s)))
        (List.zipWith xor (E.H (pairEncode i (T.sample.runAt n i s))) [b]) := by
  rw [NUPPT.runAt_eq]
  unfold tdpEnc
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [tdpEncFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput,
    pairFstD_pairEncode, pairSndD_pairEncode, T.sample_uniform.runAt_eq]
  rfl

/-- Unfolding: `Dec(⟨⟨1^n, ⟨i, t⟩⟩, ⟨c₁, c₂⟩⟩) = H ⟨i, Inv(1^n, ⟨t, c₁⟩; 1^{coins n})⟩ ⊕ c₂`. -/
theorem tdpDecFun_apply (H : List Bool → List Bool) (n : ℕ) (i t c₁ c₂ : List Bool) :
    T.tdpDecFun H (pairEncode (pairEncode (List.replicate n true) (pairEncode i t)) (pairEncode c₁ c₂)) =
      List.zipWith xor (H (pairEncode i (T.inv.runAt n (pairEncode t c₁) fun _ => true))) c₂ := by
  simp only [tdpDecFun, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    T.inv_uniform.runAt_eq, List.ofFn_const, NUPPT.coinLen]
  rfl

/-- **The single-bit scheme of [PS10, Algorithm 104.3]** from a collection of trapdoor
permutations `T` with a predicate `h` (its hard-core bit), given a polynomial-time evaluator `E`
of `h`: `Gen(1^n) = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩` with `⟨i, t⟩ ← Gen_T(1^n)`,
`Enc_i(m) = ⟨f_i(r), h_i(r) ⊕ m⟩` for `r ← Sample(1^n, i)`, `Dec(c₁, c₂) = h_i(f_i^{-1}(c₁)) ⊕ c₂`.

**Deviation:** `r ← D_i` through the collection's sampler (the text's `r ← {0,1}^n`); the secret
key carries `1^n` and `i` (the text's `f_i^{-1}` "knows" `i`); the inverter runs on the all-`true`
coin string (`inv_spec` holds for every coin string); `E` is explicit data. Repair (run-3 audit
P3-1): the former hypothesis `hS : T.toCollection.EvalSampled` is dropped, being
`T.toCollection.evalSampled` (the field `Collection.sample_spec`).

**Proof sketch** (of correctness). `tdpGen_runAt`, `tdpEnc_runAt`, `tdpDecFun_apply`;
`T.toCollection.evalSampled` gives `x` with `decD i w = some x` and
`eval ⟨i, w⟩ = f_i x = encD i (perm i x)` (`f_perm`);
`inv_spec` at `perm i x` decodes the inverter's answer to `x` (`Equiv.symm_apply_apply`); `E.spec`
twice gives `H = [h_i x]` on both strings, and `a ⊕ (a ⊕ b) = b`. -/
noncomputable def tdpBitScheme {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) :
    BitPublicKeyScheme where
  gen := T.tdpGen
  enc := T.tdpEnc E
  dec := T.tdpDecFun E.H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := T.tdpDecFun_poly E.poly
  correct := by
    intro n b rg re
    rw [tdpGen_runAt]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [tdpEnc_runAt, tdpDecFun_apply]
    obtain ⟨x, hx, hev⟩ := T.toCollection.evalSampled n rg re
    rw [hev, T.f_perm]
    have hinv : T.decD (T.index n rg) (T.inv.runAt n
        (pairEncode (T.trap n rg) (T.encD (T.index n rg) (T.perm (T.index n rg) x))) fun _ => true) =
        some x := by
      have := T.inv_spec n rg (T.perm _ x) (fun _ => true)
      rw [Equiv.symm_apply_apply] at this
      exact this
    rw [E.spec _ _ _ hinv, E.spec _ _ _ hx]
    cases h (T.index n rg) x <;> cases b <;> rfl

end TrapdoorCollection

/-! ## Lem-104.a: from a ciphertext distinguisher to a predictor of the hard-core bit -/

/-- The predictor `A'` of [PS10, Theorem 104.4, proof] built from a distinguisher `D` of
`(f(r), b(r))` versus `(f(r), ¬b(r))` (the encryptions of `0` and `1`): on input `y = f(r)`, draw
`c ← {0,1}` and coins for `D`, output `c` if `D(y, c)` accepts and `1 − c` otherwise (negated when
`flip`); this is `owpPredictor` with the pass-through component removed. -/
def pkPredictor {α ρ : Type*} (D : α × Bool → ρ → Bool) (flip : Bool) : α → Bool × ρ → Bool :=
  fun y c => xor (if D (y, c.1) c.2 then c.1 else !c.1) flip

/-- The predictor is `owpPredictor` on `α × Unit`. -/
private theorem predProb_pkPredictor_eq {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) (flip : Bool) :
    predProb f B (pkPredictor D flip) =
      predProb (owpPair (β := Unit) f) (fun w => B w.1)
        (owpPredictor (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) flip) := by
  unfold predProb
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).symm.prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- `acceptProb` of the generator `owpGen` on `α × Unit` is that of `(f(x), B(x))`. -/
private theorem acceptProb_owpGen_unit {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) :
    acceptProb (owpGen (β := Unit) f fun w => B w.1) (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) =
      acceptProb (fun x => (f x, B x)) D := by
  unfold acceptProb
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- `acceptProb` of `owpGenNot` on `α × Unit` is that of `(f(x), ¬B(x))`. -/
private theorem acceptProb_owpGenNot_unit {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) :
    acceptProb (owpGenNot (β := Unit) f fun w => B w.1) (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) =
      acceptProb (fun x => (f x, !B x)) D := by
  unfold acceptProb
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- **The predictor `pkPredictor D false` predicts `B` from `f(x)` with probability exactly
`1/2 + (Pr[D(f(x), B(x)) = 1] − Pr[D(f(x), ¬B(x)) = 1]) / 2`** (Lem-104.a, signed form; the
identity behind [PS10, Theorem 104.4, proof] and [Gar26, Theorem 3.2]). The sign is uniform over
the index in the collection setting, so the forms with a fixed `flip` average over `Gen`'s coins.

**Proof sketch.** `predProb_owpPredictor_false` on `α × Unit` (`predProb_pkPredictor_eq`,
`acceptProb_owpGen_unit`, `acceptProb_owpGenNot_unit`). -/
theorem predProb_pkPredictor_false {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    predProb f B (pkPredictor D false) =
      1 / 2 + (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) / 2 := by
  rw [predProb_pkPredictor_eq, predProb_owpPredictor_false, acceptProb_owpGen_unit,
    acceptProb_owpGenNot_unit]

/-- **The flipped predictor `pkPredictor D true` predicts `B` with probability exactly
`1/2 − (Pr[D(f(x), B(x)) = 1] − Pr[D(f(x), ¬B(x)) = 1]) / 2`** (Lem-104.a, the other sign). -/
theorem predProb_pkPredictor_true {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    predProb f B (pkPredictor D true) =
      1 / 2 - (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) / 2 := by
  rw [predProb_pkPredictor_eq, predProb_owpPredictor_true, acceptProb_owpGen_unit,
    acceptProb_owpGenNot_unit]

/-- **Lem-104.a**: a distinguisher `D` of `(f(r), b(r))` versus `(f(r), ¬b(r))` with advantage `ε`
yields, for one choice of `flip`, a predictor of `b` from `f(r)` with success exactly `1/2 + ε/2`
([PS10, Theorem 104.4, proof: "we can now use `A` to construct a machine `A'` that predicts the
hard-core predicate"]; [Gar26, Theorem 3.2]). -/
theorem exists_pkPredictor {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    ∃ flip : Bool, predProb f B (pkPredictor D flip) =
      1 / 2 + distAdv (fun x => (f x, B x)) (fun x => (f x, !B x)) D / 2 := by
  unfold distAdv
  rcases le_total 0 (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) with
    h | h
  · exact ⟨false, by rw [predProb_pkPredictor_false, abs_of_nonneg h]⟩
  · exact ⟨true, by rw [predProb_pkPredictor_true, abs_of_nonpos h]; ring⟩

/-! ## Theorem 104.4 -/

/-- The sampled element of `D_i` behind the honest ciphertext: the decoding of
`Sample(1^n, i; s)` (always `some`, by `Collection.sample_spec`), with the default as fallback. -/
private def tdpSampled (T : TrapdoorCollection) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) :
    T.D (T.index n r) :=
  (T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default

/-- **The honest ciphertext of Algorithm 104.3** is `⟨i, ⟨f_i(x), [h_i(x) ⊕ b]⟩⟩` for the sampled
element `x` (`tdpGen_runAt`, `tdpEnc_runAt`, `Collection.evalSampled`, `E.spec`, `f_perm`). -/
private theorem tdpBitScheme_pkEncDist (T : TrapdoorCollection) {h : ∀ i, T.D i → Bool}
    (E : T.toCollection.PredEvaluator h) (n : ℕ) (b : Bool) (r : T.gen.Coins n)
    (s : T.sample.Coins n) :
    (T.tdpBitScheme E).pkEncDist n b (r, s) =
      pairEncode (T.index n r) (pairEncode (T.encD _ (T.perm _ (tdpSampled T n r s)))
        [xor (h _ (tdpSampled T n r s)) b]) := by
  obtain ⟨x, hx, hev⟩ := T.toCollection.evalSampled n r s
  show pairEncode (pairFstD (T.tdpGen.runAt n [] r))
      ((T.tdpEnc E).runAt n (pairEncode (pairFstD (T.tdpGen.runAt n [] r)) [b]) s) = _
  rw [TrapdoorCollection.tdpGen_runAt]
  simp only [pairFstD_pairEncode]
  rw [TrapdoorCollection.tdpEnc_runAt, hev, T.f_perm, E.spec _ _ _ hx]
  simp only [tdpSampled, hx, Option.getD_some]
  rfl

/-- **[PS10, Theorem 104.4]: the scheme of Algorithm 104.3 is a secure single-bit public-key
encryption scheme** when `T` is a collection of one-way trapdoor permutations and `h` is a
hard-core predicate for it.

**Deviation:** the hypothesis includes the hard-core predicate `hHC` (the text's "if trapdoor
permutations exist" omits it; `TrapdoorCollection.OneWay.glPad_hardCore` supplies one from
trapdoor permutations alone, see `OneWay.glPad_tdpBitScheme_singleBitSecure`); the proof's "`D`"
in the display after the prediction lemma is the predictor `A`.

**Proof sketch.** Fix a non-uniform PPT `D`; let `μ n` be its advantage between
`pkEncDist n false` and `pkEncDist n true` (by `singleBitSecure_iff` it suffices to bound `μ`).
For `flip ∈ {false, true}` build the machine `A_flip` with coins `const 1 + D.coins` and advice
`D.advice`: on `⟨1^n, ⟨i, y⟩⟩` it reads the coin `c`, runs `D` on `⟨1^n, ⟨i, ⟨y, [c]⟩⟩⟩` with the
remaining coins (`NUPPT.exists_split (const 1)`, `NUPPT.exists_comp` with `pre` the re-pairing),
and outputs `[c ⊕ verdict ⊕ flip]` (`polyTimeComputable_pairEq` for the verdict `= [true]`,
`polyTimeComputable_pairXor`) — the text's `A'` composed with the prediction lemma's sign choice.
`hHC.2 A_flip` gives a negligible `ε_flip` with, for all `n`,
`E_r[Pr_{x, c, ρ}[A_flip(1^n, ⟨i, f_i x⟩) = h_i x]] ≤ 1/2 + ε_flip n`. For a fixed `r` (index
`i = index n r`), the inner probability is `predProb (perm i) (h i) (pkPredictor D_i flip)` with
`D_i (y, c) ρ := D.distinguisherL n ⟨i, ⟨encD i y, [c]⟩⟩ ρ` (`f_perm`, `uprob_comp_equiv` on the
coin split), which `predProb_pkPredictor_false/true` evaluates as
`1/2 ± (Pr[D_i(f_i x, h_i x)] − Pr[D_i(f_i x, ¬h_i x)])/2` over the ideal uniform `x ∈ D_i`.
Averaging over `r` (`OneWay.uexp_add`, `uexp_const`) gives
`1/2 ± (P₀ − P₁)/2 ≤ 1/2 + ε_flip n` where `P_b` is `D`'s acceptance of `⟨i, ⟨f_i x, [h_i x ⊕ b]⟩⟩`
with ideal `x`. By `tdpGen_runAt`/`tdpEnc_runAt` the honest sample `pkEncDist n b` is the same
string with `x` replaced by the sampler's output `decD i (Sample(1^n, i; s))`
(`T.toCollection.evalSampled`, `E.spec`), so `|acceptProb (pkEncDist n b) D − P_b| ≤ δ n` by
`hT.sampleClose = ⟨δ, hδ, hS'⟩` and `StatClose.abs_uprob_sub_le_prod` averaged over `r`
(`OneWay.uexp_mono`). Hence `μ n ≤ 2 (ε_false n + ε_true n) + 2 δ n` for every `n` (the sign of
`P₀ − P₁` selects the flip), negligible by `Negligible.add`, `Negligible.const_mul`,
`Negligible.mono`. (Formally: the machines are `tdpPredictor D flip`, the coin split is
`predCoins`, the per-index identity is `uprob_tdpPredictor`, the honest ciphertext is
`tdpBitScheme_pkEncDist` and the bound is `2 δ(n) + 2 (|ε_false(n)| + |ε_true(n)|)`.) -/
theorem TrapdoorCollection.tdpBitScheme_singleBitSecure (T : TrapdoorCollection)
    {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h)
    (hT : T.OneWay) (hHC : T.toCollection.HardCore h) : (T.tdpBitScheme E).SingleBitSecure := by
  rw [BitPublicKeyScheme.singleBitSecure_iff]
  intro D
  obtain ⟨δ, hδ, hδS⟩ := hT.sampleClose
  obtain ⟨εf, hεf, hAf⟩ := hHC.2 (tdpPredictor D false)
  obtain ⟨εt, hεt, hAt⟩ := hHC.2 (tdpPredictor D true)
  -- the concrete distinguisher of `(f_i(x), c)` at the index `i = index n r`
  let Di : ∀ n (r : T.gen.Coins n), T.D (T.index n r) × Bool → D.Coins n → Bool :=
    fun n r yc ρ =>
      D.distinguisherL n (pairEncode (T.index n r) (pairEncode (T.encD _ yc.1) [yc.2])) ρ
  -- the honest acceptance probability is within `δ n` of the ideal one
  have hclose : ∀ n (b : Bool),
      |acceptProb ((T.tdpBitScheme E).pkEncDist n b) (D.distinguisherL n) -
        uexp (fun r : T.gen.Coins n =>
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, xor (h _ x) b)) (Di n r))| ≤ δ n := by
    intro n b
    have e1 : acceptProb ((T.tdpBitScheme E).pkEncDist n b) (D.distinguisherL n) =
        uexp fun r : T.gen.Coins n => uprob fun w : T.sample.Coins n × D.Coins n =>
          D.distinguisherL n (pairEncode (T.index n r)
            (pairEncode (T.encD _ (T.perm _ (tdpSampled T n r w.1)))
              [xor (h _ (tdpSampled T n r w.1)) b])) w.2 = true := by
      unfold acceptProb
      rw [← uprob_comp_equiv (Equiv.prodAssoc (T.gen.Coins n) (T.sample.Coins n) (D.Coins n)).symm,
        uprob_prod]
      congr 1
      funext r
      congr 1
      funext w
      obtain ⟨s, ρ⟩ := w
      simp only [Equiv.prodAssoc_symm_apply]
      rw [tdpBitScheme_pkEncDist]
    rw [e1]
    refine abs_uexp_sub_le (hδS n (fun _ => false)).nonneg fun r => ?_
    have hs := (hδS n r).abs_uprob_sub_le_prod
      fun (o : Option (T.D (T.index n r))) (ρ : D.Coins n) =>
        D.distinguisherL n (pairEncode (T.index n r)
          (pairEncode (T.encD _ (T.perm _ (o.getD default))) [xor (h _ (o.getD default)) b])) ρ = true
    simp only [Option.getD_some] at hs
    exact hs
  -- the prediction experiments of the two predictor machines
  have key : ∀ n (flip : Bool) (r : T.gen.Coins n),
      uprob (fun z : T.D (T.index n r) × (tdpPredictor D flip).Coins n =>
        (tdpPredictor D flip).distinguisherL n (pairEncode (T.index n r) (T.f _ z.1)) z.2 =
          h (T.index n r) z.1) =
      predProb (T.perm (T.index n r)) (h (T.index n r)) (pkPredictor (Di n r) flip) := by
    intro n flip r
    simp only [T.f_perm]
    exact uprob_tdpPredictor D flip n (T.index n r) (T.perm _) (h _) (T.encD _)
  have hf : ∀ n, uexp (fun r : T.gen.Coins n =>
      acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) -
      uexp (fun r : T.gen.Coins n =>
        acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) ≤ 2 * εf n := by
    intro n
    have := hAf n
    have e : uexp (fun r : T.gen.Coins n => 1 / 2 +
        (acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r) -
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) / 2) ≤
        1 / 2 + εf n := by
      refine le_of_eq_of_le ?_ this
      congr 1
      funext r
      rw [← predProb_pkPredictor_false (T.perm _) (h _) (Di n r), ← key n false r]
    rw [uexp_half_add] at e
    linarith
  have ht : ∀ n, uexp (fun r : T.gen.Coins n =>
      acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) -
      uexp (fun r : T.gen.Coins n =>
        acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) ≤ 2 * εt n := by
    intro n
    have := hAt n
    have e : uexp (fun r : T.gen.Coins n => 1 / 2 -
        (acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r) -
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) / 2) ≤
        1 / 2 + εt n := by
      refine le_of_eq_of_le ?_ this
      congr 1
      funext r
      rw [← predProb_pkPredictor_true (T.perm _) (h _) (Di n r), ← key n true r]
    rw [uexp_half_sub] at e
    linarith
  -- the negligible bound `2 δ + 2 (|ε_false| + |ε_true|)`
  refine ((hδ.const_mul 2).add (((hεf.mono ⟨0, fun n _ => (abs_abs _).le⟩).add
    (hεt.mono ⟨0, fun n _ => (abs_abs _).le⟩)).const_mul 2)).mono ⟨0, fun n _ => ?_⟩
  have hc0 := hclose n false
  have hc1 := hclose n true
  simp only [Bool.xor_false, Bool.xor_true] at hc0 hc1
  set A₀ := acceptProb ((T.tdpBitScheme E).pkEncDist n false) (D.distinguisherL n) with hA₀
  set A₁ := acceptProb ((T.tdpBitScheme E).pkEncDist n true) (D.distinguisherL n) with hA₁
  set Qa := uexp (fun r : T.gen.Coins n =>
    acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) with hQa
  set Qb := uexp (fun r : T.gen.Coins n =>
    acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) with hQb
  have hmid : |Qa - Qb| ≤ 2 * (|εf n| + |εt n|) := by
    have h1 := hf n
    have h2 := ht n
    have h3 := le_abs_self (εf n)
    have h4 := le_abs_self (εt n)
    have h5 := abs_nonneg (εf n)
    have h6 := abs_nonneg (εt n)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hδ0 : 0 ≤ δ n := (hδS n (fun _ => false)).nonneg
  have htri1 := abs_sub_le A₀ Qa A₁
  have htri2 := abs_sub_le Qa Qb A₁
  have hpos : 0 ≤ 2 * δ n + 2 * (|εf n| + |εt n|) := by positivity
  rw [abs_of_nonneg hpos]
  show |(|A₀ - A₁|)| ≤ _
  rw [abs_abs, abs_sub_comm A₁ Qb] at *
  linarith

/-- **Trapdoor permutations give a secure single-bit public-key encryption scheme** — the text's
reading of [PS10, Theorem 104.4] with the hard-core bit supplied by Goldreich–Levin
([PS10, Theorem 87.3], collection form): for a collection of one-way trapdoor permutations `T`
with encoding length `m(n)` at generated indices, the scheme of Algorithm 104.3 for the padded
collection `T.glPad m` with the predicate `⟨x, r⟩` is single-bit secure (given its predicate
evaluator). -/
theorem TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure {T : TrapdoorCollection}
    (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (hT : T.OneWay) (E : (T.glPad m henc).toCollection.PredEvaluator T.glBit) :
    ((T.glPad m henc).tdpBitScheme E).SingleBitSecure :=
  (T.glPad m henc).tdpBitScheme_singleBitSecure E (hT.glPad m henc) (hT.glPad_hardCore m henc)

end TCSlib.Cryptography
