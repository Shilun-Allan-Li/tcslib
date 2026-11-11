/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Encryption.PublicKey.Scheme
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Ensemble security for public-key encryption

The experiments expose the public key with the ciphertexts. In the fixed-vector
experiment, all encryptions share one key and use independent encryption coins.

The scheme interface gives decryption the secret key and ciphertext. A scheme
that needs `1^n` for decryption includes it in the secret key.

## Main definitions

* `TCSlib.Cryptography.PublicKeyScheme.pkEncDist` and `PublicKeyScheme.Secure` give the
  single-message experiment and security predicate.
* `TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist` and
  `PublicKeyScheme.MultiMessageSecure` give the fixed-vector experiment and security predicate.
* `TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist` and `BitPublicKeyScheme.SingleBitSecure`
  specialize the experiment to one bit. `BitPublicKeyScheme.bitwise` encrypts a string bit by bit.
* `TCSlib.Cryptography.hybridPlant` inserts a challenge ciphertext at the selected position
  and encrypts the other messages with the public key.

## Main results

* `TCSlib.Cryptography.distAdv_multi_le_sum` bounds the fixed-vector advantage by the sum
  of the single-position advantages.
* `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` lifts single-message
  security to fixed-vector security.
* `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` proves security of
  the bitwise scheme. `BitPublicKeyScheme.singleBitSecure_iff` characterizes single-bit
  security by the negligible advantage between the two possible messages.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 102.2 and p. 103.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset
open PrivateKeyScheme (encodeList)

/-! ## Ensemble security [PS10, Definition 102.2] -/

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

/-! ## Single-bit security and the bitwise scheme [PS10, p. 103] -/

namespace BitPublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc_pk(b)⟩}` of a single-bit scheme. -/
def pkEncDist (S : BitPublicKeyScheme) (n : ℕ) (b : Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) [b]) r.2)

/-- The single-bit sampler returns the public key and the encryption of `[b]`
on the supplied key-generation and encryption coins. -/
theorem pkEncDist_eq (S : BitPublicKeyScheme) (n : ℕ) (b : Bool)
    (r : S.gen.Coins n × S.enc.Coins n) :
    S.pkEncDist n b r = pairEncode (pairFstD (S.gen.runAt n [] r.1))
      (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) [b]) r.2) := rfl

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
    · simp only [distAdv_def, sub_self, abs_zero]; exact abs_nonneg _
    · exact le_rfl
    · exact (abs_sub_comm _ _).le
    · simp only [distAdv_def, sub_self, abs_zero]; exact abs_nonneg _

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
  simp only [bitwiseEncFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, blockEncFun_eq]
  rw [blockEncFun_spec S.enc.output (.const 1) S.enc.coins (List.replicate n true) pk
    _ (List.ofFn m) r (by
      simp only [blockState_eq, length_pairEncode, List.length_ofFn, PolyExpr.eval_const, mul_one]
      omega)]
  simp only [PolyExpr.eval_const, List.length_replicate]
  rw [blockList_ofFn S.enc.output _ _ _ n m r _ (by
    simp only [blockState_eq, length_pairEncode, List.length_ofFn]; omega)]
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
    rw [bitwise_enc_runAt, decListFun_eq,
      decListFun_spec S.dec _ _ _ (by
        refine (length_le_length_encodeList _).trans ?_
        simp only [length_pairEncode]
        omega)]
    rw [flatMap_ofFn_singleton _ _ m (fun i => ?_)]
    · exact decodeFin_ofFn m
    · have hre : (List.ofFn re).length = n * S.enc.coins.eval n := by
        rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn S.bitwiseEncFun_poly (.mul .var S.enc.coins)
          n re, List.length_ofFn, PolyExpr.eval_mul, PolyExpr.eval_var]
      have hlen : (coinBlock (S.enc.coinLen n) i (List.ofFn re)).length = S.enc.coinLen n := by
        simp only [coinBlock_eq, List.length_take, List.length_drop]
        rw [hre, NUPPT.coinLen_eq]
        have hi : (i : ℕ) + 1 ≤ n := i.isLt
        have := Nat.mul_le_mul_right (S.enc.coins.eval n) hi
        rw [Nat.add_mul, one_mul] at this
        omega
      obtain ⟨re', hre'⟩ := exists_ofFn_eq _ hlen
      have := S.correct n (m i) rg re'
      rw [NUPPT.runAt_eq (A := S.enc), hre'] at this
      exact this

/-- The bitwise scheme keeps the key generator: `S.bitwise.gen = S.gen`. -/
theorem bitwise_gen (S : BitPublicKeyScheme) : S.bitwise.gen = S.gen := rfl

/-- The bitwise encryptor is the uniform machine of `bitwiseEncFun` with `n · B(n)` coins:
`S.bitwise.enc = NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)`. -/
theorem bitwise_enc (S : BitPublicKeyScheme) :
    S.bitwise.enc = NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins) := rfl

/-- The bitwise decryptor decrypts block by block: `S.bitwise.dec = decListFun S.dec`. -/
theorem bitwise_dec (S : BitPublicKeyScheme) : S.bitwise.dec = decListFun S.dec := rfl

/-- The coin count of the bitwise encryptor: `n · B(n)`. -/
theorem bitwise_enc_coinLen (S : BitPublicKeyScheme) (n : ℕ) :
    n * S.enc.coinLen n = (PolyExpr.mul .var S.enc.coins).eval n := by
  rw [NUPPT.coinLen_eq, PolyExpr.eval_mul, PolyExpr.eval_var]

/-- **The coins of the bitwise encryptor are `n` single-bit coin blocks**: the published
equivalence `(Fin n → {0,1}^{B(n)}) ≃ S.bitwise.enc.Coins n` (`coinBlocks`, then `finCongr` along
`bitwise_enc_coinLen` and the coin equivalence of `ofPolyTimeUniform`). -/
noncomputable def bitwiseEncCoins (S : BitPublicKeyScheme) (n : ℕ) :
    (Fin n → S.enc.Coins n) ≃ S.bitwise.enc.Coins n :=
  (coinBlocks n (S.enc.coinLen n)).trans
    ((Equiv.arrowCongr (finCongr (S.bitwise_enc_coinLen n)) (Equiv.refl Bool)).trans
      (NUPPT.coinsEquiv_ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins) n).symm)

/-- The bitwise encryptor's coin string on the blocks `v` is that of `coinBlocks n B v`. -/
theorem bitwiseEncCoins_ofFn (S : BitPublicKeyScheme) (n : ℕ) (v : Fin n → S.enc.Coins n) :
    List.ofFn (S.bitwiseEncCoins n v) = List.ofFn (coinBlocks n (S.enc.coinLen n) v) := by
  have key : ∀ w, List.ofFn ((NUPPT.coinsEquiv_ofPolyTimeUniform S.bitwiseEncFun_poly
      (.mul .var S.enc.coins) n).symm w) = List.ofFn w := fun w => by
    rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, Equiv.apply_symm_apply]
  unfold bitwiseEncCoins
  rw [Equiv.trans_apply, Equiv.trans_apply]
  exact (key _).trans (List.ofFn_congr (S.bitwise_enc_coinLen n) _).symm

/-- The single-bit sampler is `singleDist` on the one-bit message `[b]`. -/
private theorem pkEncDist_eq_singleDist (S : BitPublicKeyScheme) (n : ℕ) (b : Bool) :
    S.pkEncDist n b = singleDist S.gen S.enc n 1 (fun _ => b) := by
  funext r
  simp only [BitPublicKeyScheme.pkEncDist, singleDist_def, ofFn_fin_one]

/-- The ciphertext of the bitwise scheme on the coin blocks `v` is the tuple of the single-bit
encryptions with coins `v_i` (`bitwise_enc_runAt`, `coinBlock_ofFn_coinBlocks`): the sampler
`S.bitwise.pkEncDist n m` read through `bitwiseEncCoins` is `multiDist` with one-bit blocks. -/
private theorem bitwise_pkEncDist_coinBlocks (S : BitPublicKeyScheme) (n : ℕ) (m : Fin n → Bool)
    (r : S.gen.Coins n) (v : Fin n → S.enc.Coins n) :
    S.bitwise.pkEncDist n m (r, S.bitwiseEncCoins n v) =
      multiDist S.gen S.enc n n 1 (fun i _ => m i) (r, v) := by
  show pairEncode (pairFstD (S.gen.runAt n [] r))
      ((NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAt n
        (pairEncode (pairFstD (S.gen.runAt n [] r)) (List.ofFn m)) (S.bitwiseEncCoins n v)) =
    _
  rw [bitwise_enc_runAt]
  simp only [multiDist_eq]
  refine congrArg _ (congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_))
  rw [bitwiseEncCoins_ofFn, coinBlock_ofFn_coinBlocks, ← NUPPT.runAt_eq, ofFn_fin_one]

/-- **The bitwise scheme's ciphertexts as a tuple of single-bit encryptions**: the acceptance
probability of any distinguisher on `S.bitwise.pkEncDist n m` is its acceptance probability on
`multiDist` with one-bit blocks (the coin bijection `coinBlocks`, `uprob_comp_equiv`). -/
private theorem acceptProb_bitwise_pkEncDist (S : BitPublicKeyScheme) (n : ℕ) (m : Fin n → Bool)
    {ρ : Type*} [Fintype ρ] (Dst : List Bool → ρ → Bool) :
    acceptProb (S.bitwise.pkEncDist n m) Dst =
      acceptProb (multiDist S.gen S.enc n n 1 (fun i _ => m i)) Dst := by
  rw [acceptProb_def, acceptProb_def]
  rw [← uprob_comp_equiv
    (((Equiv.refl (S.gen.Coins n)).prodCongr (S.bitwiseEncCoins n)).prodCongr
      (Equiv.refl ρ))]
  congr 1
  funext z
  obtain ⟨⟨r, v⟩, ρ'⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
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
  have hε0 : 0 ≤ ε n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.trans_le (hBε n false false))
  have hsingle : ∀ msg msg' : Fin 1 → Bool,
      distAdv (singleDist S.gen S.enc n 1 msg) (singleDist S.gen S.enc n 1 msg')
        (B.distinguisherL n) ≤ ε n := by
    intro msg msg'
    have h1 : msg = fun _ => msg 0 := funext fun i => congrArg msg (Subsingleton.elim i 0)
    have h2 : msg' = fun _ => msg' 0 := funext fun i => congrArg msg' (Subsingleton.elim i 0)
    rw [h1, h2, ← S.pkEncDist_eq_singleDist, ← S.pkEncDist_eq_singleDist]
    exact hBε n _ _
  have hn := hB n (ε n) hε0 hsingle
  rw [distAdv_def] at hn ⊢
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

end TCSlib.Cryptography
