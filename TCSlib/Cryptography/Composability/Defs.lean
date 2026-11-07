/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Asymptotic.Encryption

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of private-key encryption (definitions)

[PS10, Definition 168.1], the first definition of ch. 7 (prong C of the ch. 5–8 campaign), stated
as a game of the `Games` framework over the ch. 2–4 layer's `PrivateKeyScheme`.

**The experiment** `IND_b^{O₁,O₂}(Π, A, n)`: `k ← Gen(1^n)`; `(m₀, m₁, state) ← A^{O₁(k)}(1^n)`;
`c ← Enc_k(m_b)`; output `A^{O₂(k)}(c, state)`. The oracle pairs are `[Enc; Enc]` (CPA),
`[Enc, Dec; Enc]` (CCA1) and `[Enc, Dec; Enc, Dec]` (CCA2). Under CCA2, `Dec` returns `⊥` on the
challenge `c`.

**Its encoding.** One machine plays both phases against three bit-string oracles:
- `Enc` (`n`-bit messages, `ct(n)`-bit ciphertexts);
- `Dec` (`ct(n)`-bit ciphertexts; an `(n + 1)`-bit answer, a validity flag followed by the message);
- `Challenge`, which takes `⟨m₀, m₁⟩` and returns `c ← Enc_k(m_b)`.

The oracles' state remembers the challenge, once asked. That state decides the phase: `Dec` answers
never (CPA), before the challenge only (CCA1), or always, except on `c` itself (CCA2). A refused
`Dec` query, or a repeated challenge, gets a fixed answer. The machine's final output is one bit.

**Deviations, declared once here.**
- **One machine for both phases.** The source's two-phase adversary passes `state` from phase 1
  to phase 2. Here a single next-move machine plays both phases, and its query log (which includes
  the challenge `c`) is that state. Either form simulates the other, at polynomial cost.
- **Fixed-length ciphertexts.** The scheme's ciphertexts at parameter `n` have exactly `ct(n)`
  bits (`FixedLengthScheme`), as the oracle codec needs.
- **Query budgets.** The adversary's number of oracle queries is an explicit polynomial `q`,
  universally quantified, as in the ch. 2–4 layer's `OracleEnsemble.Indist`.
- **Indistinguishability** of the two one-bit outputs is a negligible distinguishing advantage
  between the games for `b = 0` and `b = 1`.

## Main definitions

* `Composability.Attack`: CPA, CCA1, CCA2.
* `Composability.FixedLengthScheme`: a `PrivateKeyScheme` with fixed-length ciphertexts.
* `FixedLengthScheme.indImpl`, `FixedLengthScheme.indGame`: the oracles and the experiment
  `IND_b`.
* `FixedLengthScheme.INDSecure`: [PS10, Definition 168.1].

## Main results

* `indImpl_dec_cpa`, `indImpl_dec_cca2_challenge`, `indImpl_challenge_repeat`: sanity checks of
  the oracles (CPA's `Dec` is closed; CCA2's `Dec` refuses the challenge; a challenge is asked
  once).

The theorems on these notions (Thms 168.2 and 170.4, Claim 169.a) are stated in the statement
phase of prong C, in their own modules.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.1, Definition 168.1 (book p. 168).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The three attacks of [PS10, Definition 168.1]. -/
inductive Attack : Type where
  /-- Chosen-plaintext: `[Enc; Enc]`. -/
  | cpa
  /-- Non-adaptive chosen-ciphertext: `[Enc, Dec; Enc]`. -/
  | cca1
  /-- Adaptive chosen-ciphertext: `[Enc, Dec; Enc, Dec]`, `Dec` refusing the challenge. -/
  | cca2
  deriving DecidableEq

/-- A **private-key encryption scheme with fixed-length ciphertexts**: every encryption of an
`n`-bit message under a generated key has exactly `ct(n)` bits. -/
structure FixedLengthScheme extends PrivateKeyScheme where
  /-- The ciphertext length `ct(n)`. -/
  ctLen : PolyExpr
  /-- Ciphertexts of `n`-bit messages under generated keys have `ct(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin n → Bool) (r : enc.Coins n),
    (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) r).length = ctLen.eval n

namespace FixedLengthScheme

variable (S : FixedLengthScheme)

/-- The query lengths of the three oracles `Enc`, `Dec`, `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 3 → ℕ
  | 0 => n
  | 1 => S.ctLen.eval n
  | 2 => n + n

/-- The encryption oracle accepts `n`-bit messages. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = n := rfl

/-- The decryption oracle accepts ciphertexts of the fixed ciphertext length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.ctLen.eval n := rfl

/-- The challenge oracle accepts a pair of `n`-bit messages. -/
theorem inLens_two (n : ℕ) : S.inLens n 2 = n + n := rfl

/-- The answer lengths of the three oracles at parameter `n`; `Dec`'s answer is a validity flag
followed by the message. -/
def outLens (n : ℕ) : Fin 3 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => n + 1
  | 2 => S.ctLen.eval n

/-- Encryption returns the fixed ciphertext length. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.ctLen.eval n := rfl

/-- Decryption returns a validity bit followed by an `n`-bit message. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = n + 1 := rfl

/-- The challenge returns the fixed ciphertext length. -/
theorem outLens_two (n : ℕ) : S.outLens n 2 = S.ctLen.eval n := rfl

/-- The three oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens n) (S.outLens n)

/-- The IND oracle specification has the published input and output lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Whether `Dec` answers, given the attack and whether the challenge has been asked. -/
def decOpen : Attack → Bool → Bool
  | .cpa, _ => false
  | .cca1, challenged => !challenged
  | .cca2, _ => true

/-- CPA never opens the decryption oracle. -/
theorem decOpen_cpa (challenged : Bool) : decOpen .cpa challenged = false := rfl

/-- CCA1 opens decryption exactly before the challenge. -/
theorem decOpen_cca1 (challenged : Bool) : decOpen .cca1 challenged = !challenged := rfl

/-- CCA2 always opens decryption, with the challenge refusal checked separately. -/
theorem decOpen_cca2 (challenged : Bool) : decOpen .cca2 challenged = true := rfl

/-- The ciphertext `Enc_k(m)` with coins `r`, read at `ct(n)` bits. -/
def encryptAt (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode k (List.ofFn m)) r)

/-- Encryption is the padded reading of the underlying encryption machine's output. -/
theorem encryptAt_eq (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    S.encryptAt n k m r = padFin (S.ctLen.eval n)
      (S.enc.runAt n (pairEncode k (List.ofFn m)) r) := rfl

/-- `Dec`'s answer `⟨1, m⟩` on a valid decryption `m`, and the all-`false` `⊥` otherwise. -/
def decAnswer {n : ℕ} : Option (Fin n → Bool) → (Fin (n + 1) → Bool)
  | some m => Fin.cons (α := fun _ => Bool) true m
  | none => zeroBits _

/-- A successful decryption is prefixed by its `true` validity bit. -/
theorem decAnswer_some {n : ℕ} (m : Fin n → Bool) :
    decAnswer (some m) = Fin.cons (α := fun _ => Bool) true m := rfl

/-- Failed decryption is the all-false answer. -/
theorem decAnswer_none (n : ℕ) : decAnswer (n := n) none = zeroBits (n + 1) := rfl

/-- The first and the second `n` bits of a `2n`-bit query: the challenge messages `m₀, m₁`. -/
def splitHalf {n : ℕ} (x : Fin (n + n) → Bool) : (Fin n → Bool) × (Fin n → Bool) :=
  (fun i => x (Fin.castAdd n i), fun j => x (Fin.natAdd n j))

/-- The first half of a challenge query consists of its first `n` bits. -/
theorem splitHalf_fst {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).1 = fun i => x (Fin.castAdd n i) := rfl

/-- The second half of a challenge query consists of its final `n` bits. -/
theorem splitHalf_snd {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).2 = fun j => x (Fin.natAdd n j) := rfl

/-- **The oracles of `IND_b`** at parameter `n`, for the key `k`; the state is the challenge,
once asked.
- `Enc` answers `Enc_k(m)` with fresh coins.
- `Dec` answers `⟨1, Dec_k(c)⟩` with fresh coins when it is open (`decOpen`) and `c` is not the
  challenge, and `⊥` (all `false`) otherwise; a ciphertext that fails to decrypt is `⊥` as well.
- `Challenge` answers `Enc_k(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, m, s => (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, s)
  | 1, c, s =>
    if decOpen atk s.isSome && !decide (s = some c) then
      (ProbComp.sample (S.dec.Coins n)).bind fun r =>
        .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), s)
    else .pure (zeroBits _, s)
  | 2, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c)

/-- An encryption query samples fresh encryption coins and preserves the challenge state. -/
theorem indImpl_enc (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (m : Fin n → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 0 m st =
      (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, st) := rfl

/-- Decryption queries test oracle availability and refuse the recorded challenge before
running the decryption machine. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some c) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), st)
      else .pure (zeroBits _, st) := rfl

/-- A first challenge query encrypts the selected half and records that ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c) := rfl

/-- Under CPA, `Dec` never answers: every decryption query gets `⊥`. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n k 1 c s = .pure (zeroBits _, s) := by
  simp [indImpl, decOpen]

/-- Under CCA2, `Dec` refuses the challenge: on the recorded challenge `c` it answers `⊥`. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n k 1 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, decOpen]

/-- A repeated challenge query returns the recorded challenge and changes nothing. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n k 2 mm (some c) = .pure (c, some c) := rfl

/-- The codec of the adversary: the three oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The IND codec decodes a move using the bit-string decoder at its oracle lengths. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The IND codec records a log entry as the oracle index paired with its query and answer. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The IND codec returns the false verdict when its budget expires. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- **The experiment `IND_b^{O₁,O₂}(Π, A, n)`** [PS10, Definition 168.1] for the attack `atk`, with
query budget `q`: sample `k ← Gen(1^n)` and `A`'s coins, run `A` against the oracles of `IND_b`
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (S.gen.runAt n [] rg)) (A.toComp (S.indCodec n) n q r) none).bind
    fun res => .pure (res.1 0)

/-- The IND experiment samples keys and adversary coins, simulates the recorded oracle
interaction from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (S.gen.runAt n [] rg))
        (A.toComp (S.indCodec n) n q r) none).bind fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security** [PS10, Definition 168.1]: for every non-uniform PPT `A` and
every polynomial query budget, `IND_0` and `IND_1` are indistinguishable: `A`'s advantage between
them is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- IND security is exactly negligible advantage for every PPT adversary and polynomial
query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthScheme

end TCSlib.Cryptography.Composability
