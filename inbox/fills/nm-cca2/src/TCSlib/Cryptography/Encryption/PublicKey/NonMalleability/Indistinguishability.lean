/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Readers
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Non-malleable encryption (statement phase)

[PS10, Definition 172.6] and Theorem 175.9, over the public-key experiment of Definition 171.5
(`Encryption/PublicKey/OracleSecurity.lean`).

**The experiment** `NM_b(Π, A, n)`: `(pk, sk) ← Gen(1^n)`; `(m₀, m₁, state) ← A^{O₁}(1^n, pk)`;
`c ← Enc_pk(m_b)`; `(c'₁, …, c'_ℓ) ← A^{O₂}(c, state)`; output `(m'₁, …, m'_ℓ)` with
`m'_i = ⊥` if `c'_i = c` and `m'_i = Dec_sk(c'_i)` otherwise. The scheme is non-malleable when,
for every adversary `A` and distinguisher `D`, `D` tells `NM_0` from `NM_1` with negligible
advantage.

**Its encoding.** The oracles and the phases are those of Definition 171.5 (`indImpl`). The
adversary's final output is `ℓ(n)` ciphertexts of `ctLen(n)` bits. Each decryption is encoded as
`Dec`'s oracle answers are (`decAnswer`): a validity flag and the message, all-`false` for `⊥`.
`D` receives their concatenation.

**Source notes.**
- The definition writes private-key notation (`k ← Gen(1^n)`, `Dec_k`) for a public-key scheme;
  the public-key reading is taken (inventory Def-172.6).
- The source leaves the oracles `O₁, O₂` open; they are parametrized by the attack, as in
  Definition 171.5. Theorem 175.9's "CCA2 non-malleability" is the CCA2 instance.
- The adversary chooses `m₀, m₁`, so the definition's closing "for all `m₀, m₁ ∈ {0,1}^n`" is
  dropped. At CPA this is [PSV06, Definition 3], by the source's authors (ruling of 2026-11-05):
  the adversary picks `m₀, m₁` after seeing `pk`, `D` sees only the decryptions, and a copy of
  the challenge and an invalid ciphertext both decrypt to `⊥`.
- [PSV07, Definition 3] (IND-NME′) allows many challenges and distinguishes `COPY` from
  an invalid ciphertext's `⊥`; it is not literally the many-message form of this encoding.
  For the one-challenge security comparison, the complementary-pair copy-flag export argument
  is in the maintainer's sketch of `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa`
  (`SimNonMalleable.lean`). It separates `L = msgLen(n) = 0`, when the two experiments
  coincide, from `L > 0`, when the complementary plaintexts differ and their encrypted pair
  exports each copy flag. This is a security comparison of the one-challenge conventions;
  no many-challenge bridge is claimed here.
- Definition 173.7 and Theorem 174.8 follow [PSV07] (same ruling), in
  `Encryption/PublicKey/NonMalleability/Simulation.lean`.

## Contents

* `NonMalleability.Indistinguishability.Readers`: the two decryption-oracle readers requested for
  `PublicKey/OracleSecurity.lean` (the fill's escalation).
* `NonMalleability.Indistinguishability.Forward`: the forwarding handler and the log readers.
* `NonMalleability.Indistinguishability.Decrypt`: the reduction (⇒), whose finalization decrypts
  the adversary's ciphertexts and runs the distinguisher.

## Main definitions

* `FixedLengthPKScheme.nmGame`, `FixedLengthPKScheme.NMSecure`: [PS10, Definition 172.6].

## Main results

* `FixedLengthPKScheme.nmSecure_cca2_of_indSecure_cca2`: (⇒) of Thm 175.9.
* `FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2` (Thm 175.9, stated; a `sorry` under the
  source's sketch; (⇒) is proved).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.5 and §7.1.7, Definition 172.6 and Theorem 175.9 (book pp. 172–175).
* [PSV06] R. Pass, a. shelat, V. Vaikuntanathan, *Construction of a non-malleable encryption
  scheme from any semantically secure one*, CRYPTO 2006, LNCS 4117, pp. 271–289: Definition 3.
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 3.
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-- The codec of the adversary: the oracles of Definition 171.5, and a final output of `ℓ`
ciphertexts. -/
def nmCodec (n ℓ : ℕ) : MachineCodec (S.indSpec n) (Fin (ℓ * S.ctLen.eval n) → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n)

/-- The non-malleability codec uses `decodeBitMove` with the scheme's oracle lengths and an
output of `ℓ * ctLen(n)` bits. -/
theorem nmCodec_decodeMove (n ℓ : ℕ) (w : List Bool) :
    (S.nmCodec n ℓ).decodeMove w =
      decodeBitMove (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) w

/-- The non-malleability codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem nmCodec_encodeEntry (n ℓ : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.nmCodec n ℓ).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) e

/-- When its query budget expires, the non-malleability codec returns `zeroBits (ℓ * ctLen(n))`.
-/
theorem nmCodec_timeout (n ℓ : ℕ) :
    (S.nmCodec n ℓ).timeout = zeroBits (ℓ * S.ctLen.eval n) :=
  bitCodec_timeout (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n)

/-- The `i`-th of the `ℓ` ciphertexts in the adversary's output. -/
def nthCt {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    Fin (S.ctLen.eval n) → Bool :=
  fun j => w (finProdFinEquiv (i, j))

/-- Ciphertext `i` is the block whose bit `j` is output bit `finProdFinEquiv (i, j)`. -/
theorem nthCt_eq {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    S.nthCt w i = fun j => w (finProdFinEquiv (i, j)) := rfl

/-- The decryption `m'` of an output ciphertext `c'` against the recorded challenge `s`: `⊥` if
`c'` is the challenge, and `Dec_sk(c')` otherwise, encoded as `Dec`'s oracle answers are. -/
def nmDecrypt {n : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (c' : Fin (S.ctLen.eval n) → Bool) : Fin (S.msgLen.eval n + 1) → Bool :=
  if s = some c' then zeroBits _
  else FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c'))))

/-- An output ciphertext decrypts to all-false bits when it copies the challenge, and to the
encoded decryption answer otherwise [PS10, Definition 172.6]. -/
theorem nmDecrypt_eq {n : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (c' : Fin (S.ctLen.eval n) → Bool) :
    S.nmDecrypt sk s c' =
      if s = some c' then zeroBits (S.msgLen.eval n + 1)
      else FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c')))) := rfl

/-- The output of `NM_b`: the concatenated decryptions of the adversary's `ℓ` ciphertexts. -/
def nmOutput {n ℓ : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (w : Fin (ℓ * S.ctLen.eval n) → Bool) : List Bool :=
  (List.ofFn fun i : Fin ℓ => List.ofFn (S.nmDecrypt sk s (S.nthCt w i))).flatten

/-- The non-malleability output flattens the encoded decryptions of all `ℓ` output blocks. -/
theorem nmOutput_eq {n ℓ : ℕ} (sk : List Bool)
    (s : Option (Fin (S.ctLen.eval n) → Bool)) (w : Fin (ℓ * S.ctLen.eval n) → Bool) :
    S.nmOutput sk s w =
      (List.ofFn fun i : Fin ℓ => List.ofFn (S.nmDecrypt sk s (S.nthCt w i))).flatten := rfl

/-- **The experiment `NM_b(Π, A, n)`** [PS10, Definition 172.6] for the attack `atk`, with query
budget `q` and `ℓ` output ciphertexts, followed by the distinguisher `D`: sample the keys and the
coins, run `A` on `pk` against the oracles of Definition 171.5, decrypt its output (`⊥` on a copy
of the challenge), and output `D`'s verdict on the decryptions. -/
noncomputable def nmGame (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (b : Bool) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (ProbComp.sample (D.Coins n)).bind fun ρ =>
  (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
      (A.toCompOn (S.nmCodec n ℓ) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
    fun res =>
      .pure (D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)

/-- The non-malleability experiment samples keys and both machines' coins, runs the adversary
against the IND oracles, and applies the distinguisher to its decrypted output
[PS10, Definition 172.6]. -/
theorem nmGame_eq (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (b : Bool) (n : ℕ) :
    S.nmGame atk A q ℓ D b n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (ProbComp.sample (D.Coins n)).bind fun ρ =>
      (simulate
          (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
          (A.toCompOn (S.nmCodec n ℓ) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
        fun res =>
          .pure (D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) :=
  rfl

/-- **Non-malleability** [PS10, Definition 172.6] under the attack `atk`: for every non-uniform
PPT adversary `A`, every polynomial query budget `q` and number `ℓ` of output ciphertexts, and
every non-uniform PPT distinguisher `D`, `D`'s advantage between `NM_0` and `NM_1` is
negligible. -/
def NMSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q ℓ : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.nmGame atk A (q.eval n) (ℓ.eval n) D false n)
      (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) ≤ ε n

/-- Non-malleability holds exactly when every adversary, polynomial query and output budgets,
and distinguisher have a negligible bound on the two games' advantage
[PS10, Definition 172.6]. -/
theorem NMSecure_iff (atk : Attack) :
    S.NMSecure atk ↔
      ∀ (A : NUPPT) (q ℓ : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n, advantage (S.nmGame atk A (q.eval n) (ℓ.eval n) D false n)
          (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) ≤ ε n := Iff.rfl

/-- A copy of the challenge decrypts to `⊥`. -/
theorem nmDecrypt_challenge {n : ℕ} (sk : List Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.nmDecrypt sk (some c) c = zeroBits _ := by
  simp [nmDecrypt]

/-! ### Proof of Theorem 175.9 -/

section Proof

open AdaptiveCPA NMCCA2 ProbComp ChallengeSim

/-- The non-malleability codec is the bit codec of the oracles of Definition 171.5 with
`ℓ · ctLen(n)` output bits: `S.nmCodec n ℓ = bitCodec (S.inLens n) (S.outLens n) (ℓ · ctLen(n))`. -/
theorem nmCodec_eq_bitCodec (n ℓ : ℕ) :
    S.nmCodec n ℓ = bitCodec (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) := rfl

/-- Ciphertext `i` of an output string is its `i`-th block of `ctLen(n)` bits:
`⟦S.nthCt w i⟧ = (⟦w⟧.drop (i · ctLen(n))).take ctLen(n)`. -/
theorem ofFn_nthCt {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    List.ofFn (S.nthCt w i) =
      ((List.ofFn w).drop (i * S.ctLen.eval n)).take (S.ctLen.eval n) := by
  have hle : (i : ℕ) * S.ctLen.eval n + S.ctLen.eval n ≤ ℓ * S.ctLen.eval n := by
    have := Nat.mul_le_mul_right (S.ctLen.eval n) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine congrArg w (Fin.ext ?_)
    rw [finProdFinEquiv_apply_val]
    show j + S.ctLen.eval n * i = i * S.ctLen.eval n + j
    rw [Nat.mul_comm]
    omega

/-! ### (⇒) The CCA2 adversary built from a non-malleability adversary -/

/-- **The CCA2 decryption oracle on T2's codec answers as the experiment decrypts:** a query `x`
in state `st` is answered `⟦S.nmDecrypt sk st c⟧`, `c` the query read as a ciphertext, and the
state is kept.

**Proof sketch.** `castImpl_eq` and the decryption reader with its answer cast
(`indImpl_dec_onSpec_cast`); under CCA2 `Dec` is open (`decOpen_cca2`), so it refuses exactly
the recorded challenge with `⊥ = 0`, as `nmDecrypt` does (`nmDecrypt_eq`); the casts keep the
strings (`ofFn_cast`, `ofFn_zeroBits`, `outLens_zero`). -/
private theorem castImpl_indImpl_dec (b : Bool) (n : ℕ) (pk sk : List Bool)
    (x : Fin ((acDin S 0).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
      (S.indImpl .cca2 b n pk sk) 0 x st =
      .pure (padFin ((acDout S 0).eval n) (List.ofFn (S.nmDecrypt sk st
        (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x))))), st) := by
  rw [castImpl_eq, indImpl_dec_onSpec_cast, FixedLengthScheme.decOpen_cca2, Bool.true_and,
    S.nmDecrypt_eq]
  by_cases hs : st = some (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)))
  · rw [if_neg (by rw [decide_eq_true hs, Bool.not_true]; exact Bool.false_ne_true), if_pos hs,
      OracleComp.pure_bind]
    dsimp only
    rw [ofFn_zeroBits, ofFn_zeroBits, S.outLens_zero]
  · rw [if_pos (by rw [decide_eq_false hs, Bool.not_false]), if_neg hs, OracleComp.pure_bind]
    dsimp only
    rw [ofFn_cast (S.outLens_zero n).symm]

/-- **The reduction's queries are the experiment's ciphertexts:** block `i < ℓ(n)` of the
adversary's output `a`, read as a decryption query, is ciphertext `i` of `a`.

**Proof sketch.** Both are the bits `[i · ctLen(n), (i + 1) · ctLen(n))` of `⟦a⟧`
(`ofFn_nthCt`, `ofFn_padFin_eq_take`, `ofFn_cast`); they are equal as strings
(`List.ofFn_injective`). -/
private theorem decBlock_eq_nthCt (ℓ : PolyExpr) (n : ℕ)
    (a : Fin ((ℓ.mul S.ctLen).eval n) → Bool) (i : ℕ) (hi : i < ℓ.eval n) :
    cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn (decBlock S n a i))) =
      S.nthCt (padFin (ℓ.eval n * S.ctLen.eval n) (List.ofFn a)) ⟨i, hi⟩ := by
  have hct : (acDin S 0).eval n = S.ctLen.eval n := by rw [acDin_zero]
  have hin : S.inLens n 0 = S.ctLen.eval n := S.inLens_zero n
  have ha : (List.ofFn a).length = ℓ.eval n * S.ctLen.eval n := by
    rw [List.length_ofFn, PolyExpr.eval_mul]
  have hle : i * S.ctLen.eval n + S.ctLen.eval n ≤ ℓ.eval n * S.ctLen.eval n := by
    have := Nat.mul_le_mul_right (S.ctLen.eval n) (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this
    exact this
  have hblk : List.ofFn (decBlock S n a i) =
      ((List.ofFn a).drop (i * S.ctLen.eval n)).take (S.ctLen.eval n) := by
    rw [decBlock_eq, ofFn_padFin_eq_take, hct,
      List.take_append_of_le_length (by rw [List.length_drop, ha]; omega)]
  apply List.ofFn_injective
  rw [ofFn_cast hin, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hct, hin]), hblk,
    ofFn_nthCt, GGMRed.ofFn_padFin_of_length ha]

/-- **The reduction's collected answers are the experiment's output:** the concatenated answers
of the CCA2 decryption oracle on the `ℓ(n)` blocks of `a`, in state `st`, are
`S.nmOutput sk st a`.

**Proof sketch.** Answer `i` is `⟦nmDecrypt sk st (block i)⟧` (`castImpl_indImpl_dec`, read at
its width by `acDout_zero`), and block `i` is ciphertext `i` (`decBlock_eq_nthCt`); compare the
two lists entrywise (`nmOutput_eq`). -/
private theorem decAnswers_eq_nmOutput (ℓ : PolyExpr) (n : ℕ) (sk : List Bool)
    (a : Fin ((ℓ.mul S.ctLen).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    ((List.range (ℓ.eval n)).map fun i => List.ofFn (padFin ((acDout S 0).eval n) (List.ofFn
        (S.nmDecrypt sk st (cast (S.indSpec_decDom n) (padFin (S.inLens n 0)
          (List.ofFn (decBlock S n a i)))))))).flatten =
      S.nmOutput sk st (padFin (ℓ.eval n * S.ctLen.eval n) (List.ofFn a)) := by
  have hout : (acDout S 0).eval n = S.msgLen.eval n + 1 := by
    rw [acDout_zero, PolyExpr.eval_add, PolyExpr.eval_const]
  rw [nmOutput_eq]
  congr 1
  refine List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn])
    fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hout]),
    decBlock_eq_nthCt S ℓ n a i (by rw [List.length_map, List.length_range] at h₁; exact h₁)]


/-- **The reduction's game is the non-malleability experiment.** Let `B` be T2's machine for the
handler `decHandler S ℓ D` (with its coin bijection `φ` at `n`) and `B'` the machine `B` with
`D`'s advice hard-wired (`hB'`, coins identified by `hc`). Then `B'`'s CCA2 game `Ind_b` and the
experiment `NM_b` for `A` and `D` accept with the same probability.

**Proof sketch.** Fix the keys. `B'`'s coins are the handler's seed (`D`'s coins, `e`) and `A`'s
coins (`φ`, `expect_sample_equiv`, `expect_sample_prod`, `expect_sample_comm`). For fixed coins,
transport `B`'s run to T2's codec (`indCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`) and
replace it by the reduction (T2's equation `hφ`). The handler forwards (`simulate_decHandler_impl`),
so the run is `A`'s run against the CCA2 oracles followed by the finalization in the final
state (`simulate_bind`), which decrypts the `ℓ` ciphertexts with the state kept
(`simulate_decHandler_finish`, `castImpl_indImpl_dec`) and outputs `D`'s verdict on
`S.nmOutput sk st a` (`decAnswers_eq_nmOutput`). That is `NM_b`'s output, after transporting
`A`'s run back to the experiment's codec (`nmCodec_eq_bitCodec`). -/
private theorem accept_indGame_decRed (A D B B' : NUPPT) (q ℓ : PolyExpr) (n : ℕ)
    (φ : (Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((decHandler S ℓ D).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((ℓ.mul S.ctLen).eval n)) n (q.eval n) ((decHandler S ℓ D).advInput n z ω) r)
          ((decHandler S ℓ D).init n)).bind
          (fun res => (decHandler S ℓ D).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((decHandler S ℓ D).outLen.eval n)) n
          (q.eval n * (decHandler S ℓ D).perCall.eval n + (decHandler S ℓ D).finCall.eval n)
          z (φ (ω, r)))
    (hc : B.coins = B'.coins)
    (hB' : ∀ (Q : ℕ) (x : List Bool) (r : B.Coins n),
      B'.toCompOn (S.indCodec n) n Q x (NUPPT.coinsCongr hc n r) =
        B.toCompOn (S.indCodec n) n Q (pairEncode x (D.advice n)) r)
    (b : Bool) :
    accept (S.indGame .cca2 B'
        (q.eval n * (decHandler S ℓ D).perCall.eval n + (decHandler S ℓ D).finCall.eval n) b n) =
      accept (S.nmGame .cca2 A (q.eval n) (ℓ.eval n) D b n) := by
  have hd1 : (decHandler S ℓ D).outLen.eval n = 1 := by
    rw [decHandler_outLen, PolyExpr.eval_const]
  have hdα : (ℓ.mul S.ctLen).eval n = ℓ.eval n * S.ctLen.eval n := PolyExpr.eval_mul _ _ _
  let e : D.Coins n ≃ (Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) :=
    NUPPT.coinsEquivPoly (decHandler_seedLen S ℓ D).symm n
  rw [accept_eq, accept_eq, S.indGame_eq, S.nmGame_eq, prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  conv_lhs => rw [prob_bind, ← expect_sample_equiv (φ.trans (NUPPT.coinsCongr hc n)),
    expect_sample_prod, expect_sample_comm]
  conv_rhs => rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  conv_lhs => rw [← expect_sample_equiv e]
  conv_rhs => rw [prob_bind]
  refine congrArg _ (funext fun ρ => ?_)
  -- The reduction's side: transport to T2's codec and unfold the reduction.
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if p.1.headD false = true then (1 : ℝ) else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [headD_ofFn_one]
  rw [Equiv.trans_apply, hB', prob_bind, indCodec_eq_bitCodec, h1]
  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _ B n _ _ _
    none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if p.1.headD false = true then (1 : ℝ) else 0)).symm.trans ?_
  rw [← hφ, decHandler_advInput, pairFstD_pairEncode, simulate_decHandler_impl,
    OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]
  rw [simulate_bind, expect_bind]
  simp only [simulate_decHandler_finish S ℓ D n _ _ _ _ _ _ (castImpl_indImpl_dec S b n _ _),
    expect_pure]
  -- The experiment's side: transport `A`'s run to T2's codec.
  have h2 : (fun res : (Fin (ℓ.eval n * S.ctLen.eval n) → Bool) ×
      Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (D.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin (ℓ.eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ) else 0)
        (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, nmCodec_eq_bitCodec, h2]
  refine Eq.trans ?_ (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hdα _
    A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin (ℓ.eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ) else 0))
  refine congrArg _ (funext fun p => ?_)
  -- Pointwise: the verdict on the collected answers is `D`'s verdict on `NM_b`'s output.
  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_singleton, hd1]), List.headD_cons,
    pairSndD_pairEncode, decAnswers_eq_nmOutput, NUPPT.coinsEquivPoly_ofFn,
    ← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]

/-- **(⇒) of Theorem 175.9: CCA2 security implies CCA2 non-malleability** [PS10, Theorem 175.9].

**Proof sketch.** Given `A` (budget `q`, `ℓ` ciphertexts) and `D`, T2
(`Games.exists_interactiveHandlerMachine`) makes the handler `decHandler S ℓ D` a machine `B`, and
`exists_withAdviceOn` hard-wires `D`'s advice into it (`B'`). `B'`'s budget is
`q · 1 + ℓ`, a polynomial; CCA2 security gives a negligible bound on `B'`'s advantage, which at
every `n` equals the advantage of `D` between `NM_0` and `NM_1` (`accept_indGame_decRed`). -/
theorem nmSecure_cca2_of_indSecure_cca2 (h : S.INDSecure .cca2) : S.NMSecure .cca2 := by
  rw [NMSecure_iff]
  intro A q ℓ D
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (acDin S) (acDout S) (acDin S)
    (acDout S) (ℓ.mul S.ctLen) (decHandler S ℓ D)
  obtain ⟨B', hc, hB'⟩ := exists_withAdviceOn B D.advice D.adv D.advice_length
  obtain ⟨ε, hε, hbound⟩ := (S.INDSecure_iff .cca2).1 h B'
    ((q.mul (decHandler S ℓ D).perCall).add (decHandler S ℓ D).finCall)
  refine ⟨ε, hε, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  have key := fun b => accept_indGame_decRed S A D B B' q ℓ n φ hφ hc
    (fun Q x r => hB' n (S.indCodec n) Q x r) b
  have hn := hbound n
  rw [PolyExpr.eval_add, PolyExpr.eval_mul] at hn
  rw [advantage_eq, ← key false, ← key true, ← advantage_eq]
  exact hn

end Proof

/-- **Theorem 175.9: under CCA2, secrecy and non-malleability coincide** [PS10, Theorem 175.9].

**Proof sketch** (the source's, made explicit).
1. (⇒) Given an NM adversary `A` with `ℓ` ciphertexts and a distinguisher `D`, the IND
   adversary runs `A`, then asks CCA2's `Dec` for each of `A`'s ciphertexts. `Dec` refuses the
   challenge with the same `⊥` that `NM` assigns to its copies (`indImpl_dec_cca2_challenge`,
   `nmDecrypt_challenge`), so the answers are exactly `NM_b`'s output. It runs `D` on them and
   outputs `D`'s verdict. T2 (`Games.exists_interactiveHandlerMachine`) supplies
   `advIn = pk`, forwards decryption queries, and uses `finCall = ℓ` in finalization before
   running `D`, for total budget `q + ℓ`. Advice is carried through `z` and the public
   `exists_withAdvice`/`exists_comp` closure lemmas. The advantage is unchanged.
2. (⇐) Given an IND adversary `A` with guess `g`, the NM adversary runs `A` and outputs fresh
   encryptions of `g^{msgLen}` and `(¬g)^{msgLen}` (it holds `pk`). The two plaintexts differ, so
   by correctness at most one of the two ciphertexts is the challenge. The distinguisher reads
   `g` from the first if it decrypts, and from the second otherwise. Same advantage; at
   `msgLen(n) = 0` there is nothing to distinguish.

The source's sketch argues the contrapositives: an NM break yields a related ciphertext that
`Dec` decrypts, and an IND break lets the adversary decrypt and re-encrypt a related message. -/
theorem indSecure_cca2_iff_nmSecure_cca2 : S.INDSecure .cca2 ↔ S.NMSecure .cca2 := by
  sorry

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability
