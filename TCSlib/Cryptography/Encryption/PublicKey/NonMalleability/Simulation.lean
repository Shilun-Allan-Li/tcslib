/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation-based non-malleability (statement phase)

[PS10, Definition 173.7 and Theorem 174.8], in the form of [PSV07] (ruling of 2026-11-05: the
non-malleability notions of §7.1.5–7.1.6 follow Pass, shelat and Vaikuntanathan).

**Why not the source's form.** As written, Theorem 174.8 is false (inventory Thm-174.8).
- Definition 173.7's simulator `S(1^n, z)` gets no public key. An adversary that outputs a fresh
  `Enc_pk(0^n)` hits the relation `R(m) = {0^n}` with probability 1, while a simulator without
  `pk` produces a ciphertext that decrypts to `0^n` under a fresh key only with the probability
  of guessing one.
- The quantifiers of Definitions 172.6 and 173.7 do not line up: adaptive `m₀, m₁` in one, a
  fixed `m` in the other.

**The form taken: SIM-NME′ at one message** [PSV07, Definition 1, with `ℓ = 1`; "single-message
security" there].
- *Real.* `(pk, sk) ← Gen(1^n)`; `(M, s) ← A₁^{O₁}(pk)`; `m ← M`; `y ← Enc_pk(m)`;
  `((c₁, …, c_r), σ) ← A₂^{O₂}(y, h(m), s)`; output `(M, m, (d₁, …, d_r), σ)` with
  `d_i = COPY` if `c_i = y` and `d_i = Dec_sk(c_i)` otherwise (possibly `⊥`: invalid ciphertexts
  are allowed, the "′" of [PSV07]).
- *Ideal.* `(pk, sk) ← Gen(1^n)`; `(M, s) ← S₁(pk)`; `m ← M`; `((c₁, …, c_r), σ) ← S₂(h(m), s)`;
  output `(M, m, (d₁, …, d_r), σ)` with `d_i = COPY` if `c_i = COPY` and `Dec_sk(c_i)` otherwise.
- *Security.* For every history function `h`, every adversary `A` and all polynomials `r`, there
  is a simulator `S` whose experiment no distinguisher tells from `A`'s. [PSV07] replaces the
  relations `R` of [PS10] and [DDN00] by distinguishers ("any p.p.t. distinguisher can be
  described as a p.p.t. relation and vice versa", remarks after Definition 2).

**The encoding.**
- *Phases and oracles* are those of Definition 171.5: the challenge query separates `A₁` from
  `A₂`, and `Dec` answers per the attack (`decOpen`), refusing the challenge.
- *The sampler.* [PSV07]'s `A₁` outputs a machine `M`. Here a sampler `M` (a machine with a
  history function, `MsgSampler`) is quantified together with `A`, and `A₁` outputs a parameter
  `a`, with `m = M(a)` read at `msgLen(n)` bits. The output carries `a` in place of `M`'s
  description. With `M` a universal clocked machine this is [PSV07]'s form, and the fixed
  lengths make every sampler valid in [PSV07]'s sense.
- *The simulator* is one oracle machine on `pk`. Its single query `a` is answered by `h(m)`,
  where `m = M(a)` is drawn by the experiment: `S₁` is its run up to the query, `S₂` the rest. It
  has no `Dec` oracle under any attack, as in [PSV07]. Each of its `r` outputs is a `COPY` flag
  and a ciphertext.
- *No challenge.* If the machine never queries, its parameter is `0^{pl(n)}` and `m = M(0^{pl(n)})`
  (in both experiments).

**Theorem 174.8.** [PSV07] proves that SIM-NME′ and IND-NME′ (Definition 172.6 at many messages)
coincide **under CPA** (its Theorem 3), and that SIM-NME′ is **strictly stronger under CCA1 and
CCA2**, even at one message (its Theorem 4). It always implies IND-NME′ (its Corollary 1). So
Theorem 174.8 is stated under CPA, with the implication SIM ⇒ IND for every attack. [PSV07]
defers both proofs to its full version; the sketches below are the maintainer's.

## Main definitions

* `MsgSampler`: a message sampler with a history function.
* `FixedLengthPKScheme.snmReal`, `FixedLengthPKScheme.snmIdeal`: the two experiments.
* `FixedLengthPKScheme.SimNMSecure`: [PS10, Definition 173.7] as [PSV07, Definition 1].

## Main results

* `FixedLengthPKScheme.nmSecure_of_simNMSecure` (stated; a `sorry` under its sketch):
  SIM ⇒ IND for every attack [PSV07, Corollary 1].
* `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa` (stated; a `sorry` under its sketch):
  IND ⇒ SIM under CPA [PSV07, Theorem 3].
* `FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa`: Theorem 174.8 under CPA, from the two.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.6, Definition 173.7 and Theorem 174.8 (book pp. 173–174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definitions 1–4, Theorems 3 and 4,
  Corollary 1.
* [PSV06] R. Pass, a. shelat, V. Vaikuntanathan, *Construction of a non-malleable encryption
  scheme from any semantically secure one*, CRYPTO 2006, LNCS 4117, pp. 271–289: Definition 3.
* [DDN00] D. Dolev, C. Dwork, M. Naor, *Nonmalleable cryptography*, SIAM J. Comput. 30(2), 2000
  (cited through [PSV07]).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- **A message sampler with a history function** [PSV07, Definition 1]: a machine `M` activated
on a `paramLen(n)`-bit parameter, whose output is the message, and a polynomial-time history
function `h`, read at `histLen(n)` bits. -/
structure MsgSampler where
  /-- The sampler, activated on the adversary's parameter. -/
  samp : NUPPT
  /-- The length of the parameter. -/
  paramLen : PolyExpr
  /-- The history function `h`. -/
  hist : List Bool → List Bool
  /-- The length at which `h(m)` is read. -/
  histLen : PolyExpr
  /-- `h` is polynomial-time. -/
  hist_poly : PolyTimeComputable hist

namespace MsgSampler

variable (M : MsgSampler)

/-- The message `m = M(a)` with the sampler's coins `ρ`, read at `ℓ` bits. -/
def draw (ℓ n : ℕ) (a : Fin (M.paramLen.eval n) → Bool) (ρ : M.samp.Coins n) : Fin ℓ → Bool :=
  padFin ℓ (M.samp.runAt n (List.ofFn a) ρ)

/-- Drawing a message pads the sampler's output on parameter `a` and coins `ρ` to `ℓ` bits. -/
theorem draw_eq (ℓ n : ℕ) (a : Fin (M.paramLen.eval n) → Bool) (ρ : M.samp.Coins n) :
    M.draw ℓ n a ρ = padFin ℓ (M.samp.runAt n (List.ofFn a) ρ) := rfl

/-- The history `h(m)`, read at `histLen(n)` bits. -/
def histAt {ℓ : ℕ} (n : ℕ) (m : Fin ℓ → Bool) : Fin (M.histLen.eval n) → Bool :=
  padFin _ (M.hist (List.ofFn m))

/-- The sampled message's history is `M.hist (List.ofFn m)`, padded to `histLen(n)` bits. -/
theorem histAt_eq {ℓ : ℕ} (n : ℕ) (m : Fin ℓ → Bool) :
    M.histAt n m = padFin (M.histLen.eval n) (M.hist (List.ofFn m)) := rfl

/-- The simulator's oracle at parameter `n`: the parameter in, the history out. -/
abbrev simSpec (n : ℕ) : OracleSpec (Fin 1) :=
  bitSpec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)

/-- The simulator's oracle is `bitSpec` with parameter-length queries and history-length
answers. -/
theorem simSpec_eq (n : ℕ) :
    M.simSpec n = bitSpec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n) := rfl

end MsgSampler

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-! ### The real experiment -/

/-- The query lengths of the real experiment's oracles `Dec` and `Challenge`. -/
def snmInLens (M : MsgSampler) (n : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => M.paramLen.eval n

/-- A real-experiment decryption query has `ctLen(n)` bits. -/
theorem snmInLens_zero (M : MsgSampler) (n : ℕ) :
    S.snmInLens M n 0 = S.ctLen.eval n := rfl

/-- A real-experiment challenge query has `paramLen(n)` bits. -/
theorem snmInLens_one (M : MsgSampler) (n : ℕ) :
    S.snmInLens M n 1 = M.paramLen.eval n := rfl

/-- The answer lengths: `Dec` answers a validity flag and a message; `Challenge` the challenge
ciphertext and the history. -/
def snmOutLens (M : MsgSampler) (n : ℕ) : Fin 2 → ℕ
  | 0 => S.msgLen.eval n + 1
  | 1 => S.ctLen.eval n + M.histLen.eval n

/-- A real-experiment decryption answer has one validity bit followed by `msgLen(n)` bits. -/
theorem snmOutLens_zero (M : MsgSampler) (n : ℕ) :
    S.snmOutLens M n 0 = S.msgLen.eval n + 1 := rfl

/-- A real-experiment challenge answer has `ctLen(n) + histLen(n)` bits. -/
theorem snmOutLens_one (M : MsgSampler) (n : ℕ) :
    S.snmOutLens M n 1 = S.ctLen.eval n + M.histLen.eval n := rfl

/-- The two oracles of the real experiment at parameter `n`. -/
abbrev snmSpec (M : MsgSampler) (n : ℕ) : OracleSpec (Fin 2) :=
  bitSpec (S.snmInLens M n) (S.snmOutLens M n)

/-- The real experiment's oracle specification is `bitSpec` at its published query and
answer lengths. -/
theorem snmSpec_eq (M : MsgSampler) (n : ℕ) :
    S.snmSpec M n = bitSpec (S.snmInLens M n) (S.snmOutLens M n) := rfl

/-- The state of the real experiment's oracles: the challenge, with the parameter it was asked
on, once asked. -/
abbrev SnmState (M : MsgSampler) (n : ℕ) : Type :=
  Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (M.paramLen.eval n) → Bool))

/-- The real oracle state is an optional pair of a `ctLen(n)`-bit ciphertext and a
`paramLen(n)`-bit sampler parameter. -/
theorem SnmState_eq (M : MsgSampler) (n : ℕ) :
    S.SnmState M n =
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (M.paramLen.eval n) → Bool)) := rfl

/-- **The oracles of the real experiment** at parameter `n`, for the keys `pk`, `sk` and the
sampler's coins `ρ`.
- `Dec` answers as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is
  not the challenge, and `⊥` (all `false`) otherwise.
- `Challenge` on the parameter `a`, the first time: `m = M(a; ρ)`, `y ← Enc_pk(m)`; it answers
  `⟨y, h(m)⟩` and records `(y, a)`. Later it repeats the recorded answer. -/
noncomputable def snmImpl (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) : QueryImpl (S.snmSpec M n) (S.SnmState M n) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome && !decide (s.map Prod.fst = some c) then
      .pure (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
    else .pure (zeroBits _, s)
  | 1, a, s =>
    match s with
    | some (y, a₀) => .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a₀ ρ)), s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        let y : Fin (S.ctLen.eval n) → Bool :=
          padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn (M.draw (S.msgLen.eval n) n a ρ))) re)
        .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a ρ)), some (y, a))

/-- A real-experiment decryption query returns the encoded decryption exactly when the oracle
is open and the ciphertext is not the recorded challenge; otherwise it returns all-false bits. -/
theorem snmImpl_dec (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) (c : Fin (S.ctLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl atk M n pk sk ρ 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s.map Prod.fst = some c) then
        .pure (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))), s)
      else .pure (zeroBits (S.msgLen.eval n + 1), s) := rfl

/-- A real-experiment challenge query repeats the recorded ciphertext and history when a
challenge exists; otherwise it encrypts the sampled message and records the ciphertext and
parameter [PSV07, Definition 1]. -/
theorem snmImpl_challenge (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) (a : Fin (M.paramLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl atk M n pk sk ρ 1 a s =
      match s with
      | some (y, a₀) => .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a₀ ρ)), s)
      | none =>
        (ProbComp.sample (S.enc.Coins n)).bind fun re =>
          let y : Fin (S.ctLen.eval n) → Bool :=
            padFin (S.ctLen.eval n)
              (S.enc.runAt n (pairEncode pk (List.ofFn (M.draw (S.msgLen.eval n) n a ρ))) re)
          .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a ρ)), some (y, a)) := rfl

/-- Under CPA, `Dec` never answers. -/
theorem snmImpl_dec_cpa (M : MsgSampler) (n : ℕ) (pk sk : List Bool) (ρ : M.samp.Coins n)
    (c : Fin (S.ctLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl .cpa M n pk sk ρ 0 c s = .pure (zeroBits _, s) := by
  simp [snmImpl, FixedLengthScheme.decOpen_cpa]

/-- The codec of the adversary: the two oracles, and a final output of `r` ciphertexts followed by
an `sl`-bit `σ`. -/
def snmCodec (M : MsgSampler) (n r sl : ℕ) :
    MachineCodec (S.snmSpec M n) (Fin (r * S.ctLen.eval n + sl) → Bool) :=
  bitCodec (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl)

/-- The real-experiment codec uses `decodeBitMove` with `r * ctLen(n) + sl` output bits. -/
theorem snmCodec_decodeMove (M : MsgSampler) (n r sl : ℕ) (w : List Bool) :
    (S.snmCodec M n r sl).decodeMove w =
      decodeBitMove (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) w :=
  bitCodec_decodeMove (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) w

/-- The real-experiment codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem snmCodec_encodeEntry (M : MsgSampler) (n r sl : ℕ)
    (e : Σ i, (S.snmSpec M n).dom i × (S.snmSpec M n).rng i) :
    (S.snmCodec M n r sl).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) e

/-- When its query budget expires, the real-experiment codec returns
`zeroBits (r * ctLen(n) + sl)`. -/
theorem snmCodec_timeout (M : MsgSampler) (n r sl : ℕ) :
    (S.snmCodec M n r sl).timeout = zeroBits (r * S.ctLen.eval n + sl) :=
  bitCodec_timeout (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl)

/-- The `i`-th of the `r` ciphertexts in an adversary's output. -/
def snmCt {n r sl : ℕ} (w : Fin (r * S.ctLen.eval n + sl) → Bool) (i : Fin r) :
    Fin (S.ctLen.eval n) → Bool :=
  fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j)))

/-- Real output ciphertext `i` has bit `j` at `Fin.castAdd sl (finProdFinEquiv (i, j))`. -/
theorem snmCt_eq {n r sl : ℕ} (w : Fin (r * S.ctLen.eval n + sl) → Bool) (i : Fin r) :
    S.snmCt w i = fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j))) := rfl

/-- The final `σ`: the last `sl` bits of an output. -/
def snmSigma {k sl : ℕ} (w : Fin (k + sl) → Bool) : Fin sl → Bool :=
  fun j => w (Fin.natAdd k j)

/-- The final output string's bit `j` is input bit `Fin.natAdd k j`. -/
theorem snmSigma_eq {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    snmSigma w = fun j => w (Fin.natAdd k j) := rfl

/-- **The entry `d_i`** [PSV07, Definition 1]: `COPY` if `copy`, and `Dec_sk(c)` otherwise.
Encoded as a `COPY` flag followed by `Dec`'s answer (a validity flag and the message; all `false`
for `⊥`). -/
def snmEntry {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    Fin (S.msgLen.eval n + 1 + 1) → Bool :=
  if copy then Fin.cons (α := fun _ => Bool) true (zeroBits _)
  else Fin.cons (α := fun _ => Bool) false
    (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))))

/-- An entry begins with its COPY flag; a copy has an all-false payload, and every other entry
has the encoded decryption as payload [PSV07, Definition 1]. -/
theorem snmEntry_eq {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.snmEntry sk copy c =
      if copy then Fin.cons (α := fun _ => Bool) true (zeroBits (S.msgLen.eval n + 1))
      else Fin.cons (α := fun _ => Bool) false
        (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c))))) := rfl

/-- **The output `(M, m, (d₁, …, d_r), σ)`** handed to the distinguisher, with the parameter `a`
in place of `M`: the concatenation of its fixed-length parts. -/
def snmView {n pl r sl : ℕ} (a : Fin pl → Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (d : Fin r → Fin (S.msgLen.eval n + 1 + 1) → Bool) (σ : Fin sl → Bool) : List Bool :=
  List.ofFn a ++ List.ofFn m ++ (List.ofFn fun i => List.ofFn (d i)).flatten ++ List.ofFn σ

/-- The distinguisher's view concatenates the parameter, sampled message, flattened entries,
and final `σ` [PSV07, Definition 1]. -/
theorem snmView_eq {n pl r sl : ℕ} (a : Fin pl → Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (d : Fin r → Fin (S.msgLen.eval n + 1 + 1) → Bool) (σ : Fin sl → Bool) :
    S.snmView a m d σ =
      List.ofFn a ++ List.ofFn m ++ (List.ofFn fun i => List.ofFn (d i)).flatten ++ List.ofFn σ :=
  rfl

/-- **The real experiment** `SIM-NME′(Π, A, n)` [PSV07, Definition 1, `ℓ = 1`] for the attack
`atk`, the sampler `M`, query budget `q`, `r` output ciphertexts and an `sl`-bit `σ`, followed
by the distinguisher `D`: sample the keys and the coins, run `A` on `pk` against the oracles, and
output `D`'s verdict on `(a, m, (d_i)_i, σ)`, where `d_i` is `COPY` on a copy of the challenge. -/
noncomputable def snmReal (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl : ℕ) (D : NUPPT)
    (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
  (ProbComp.sample (A.Coins n)).bind fun rA =>
  (ProbComp.sample (D.Coins n)).bind fun rD =>
  (simulate
      (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ)
      (A.toCompOn (S.snmCodec M n r sl) n q (pairFstD (S.gen.runAt n [] rg)) rA) none).bind
    fun res =>
      let a := (res.2.map Prod.snd).getD (zeroBits _)
      .pure (D.distinguisherL n
        (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
          (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg))
            (decide (res.2.map Prod.fst = some (S.snmCt res.1 i))) (S.snmCt res.1 i))
          (snmSigma res.1)) rD)

/-- The real simulation experiment samples all coins, runs the adversary against its oracles,
and applies the distinguisher to the resulting parameter, message, entries, and final output
[PSV07, Definition 1]. -/
theorem snmReal_eq (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl : ℕ) (D : NUPPT)
    (n : ℕ) :
    S.snmReal atk M A q r sl D n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
      (ProbComp.sample (A.Coins n)).bind fun rA =>
      (ProbComp.sample (D.Coins n)).bind fun rD =>
      (simulate
          (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ)
          (A.toCompOn (S.snmCodec M n r sl) n q (pairFstD (S.gen.runAt n [] rg)) rA) none).bind
        fun res =>
          let a := (res.2.map Prod.snd).getD (zeroBits (M.paramLen.eval n))
          .pure (D.distinguisherL n
            (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
              (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg))
                (decide (res.2.map Prod.fst = some (S.snmCt res.1 i))) (S.snmCt res.1 i))
              (snmSigma res.1)) rD)) := rfl

/-! ### The ideal experiment -/

/-- **The oracle of the ideal experiment**: on the parameter `a` (the first one asked, recorded),
the history `h(m)` of `m = M(a; ρ)`. -/
noncomputable def simImpl (M : MsgSampler) (n : ℕ) (ρ : M.samp.Coins n) :
    QueryImpl (M.simSpec n) (Option (Fin (M.paramLen.eval n) → Bool)) unifSpec :=
  fun _ a s => .pure (M.histAt n (M.draw (S.msgLen.eval n) n (s.getD a) ρ), some (s.getD a))

/-- The ideal oracle returns the history of the sampled message at the recorded parameter,
or at the current query if no parameter has been recorded, and records that parameter. -/
theorem simImpl_eq (M : MsgSampler) (n : ℕ) (ρ : M.samp.Coins n) :
    S.simImpl M n ρ =
      fun _ a s => .pure
        (M.histAt n (M.draw (S.msgLen.eval n) n (s.getD a) ρ), some (s.getD a)) := rfl

/-- The codec of the simulator: its one oracle, and a final output of `r` entries, each a `COPY`
flag and a ciphertext, followed by an `sl`-bit `σ`. -/
def simCodec (M : MsgSampler) (n r sl : ℕ) :
    MachineCodec (M.simSpec n) (Fin (r * (S.ctLen.eval n + 1) + sl) → Bool) :=
  bitCodec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl)

/-- The ideal-experiment codec uses `decodeBitMove` with parameter and history lengths and
`r * (ctLen(n) + 1) + sl` output bits. -/
theorem simCodec_decodeMove (M : MsgSampler) (n r sl : ℕ) (w : List Bool) :
    (S.simCodec M n r sl).decodeMove w =
      decodeBitMove (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
        (r * (S.ctLen.eval n + 1) + sl) w :=
  bitCodec_decodeMove (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl) w

/-- The ideal-experiment codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem simCodec_encodeEntry (M : MsgSampler) (n r sl : ℕ)
    (e : Σ i, (M.simSpec n).dom i × (M.simSpec n).rng i) :
    (S.simCodec M n r sl).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl) e

/-- When its query budget expires, the ideal-experiment codec returns
`zeroBits (r * (ctLen(n) + 1) + sl)`. -/
theorem simCodec_timeout (M : MsgSampler) (n r sl : ℕ) :
    (S.simCodec M n r sl).timeout = zeroBits (r * (S.ctLen.eval n + 1) + sl) :=
  bitCodec_timeout (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl)

/-- The `i`-th entry of the simulator's output: its `COPY` flag and its ciphertext. -/
def simEntry {n r sl : ℕ} (w : Fin (r * (S.ctLen.eval n + 1) + sl) → Bool) (i : Fin r) :
    Bool × (Fin (S.ctLen.eval n) → Bool) :=
  (w (Fin.castAdd sl (finProdFinEquiv (i, 0))),
    fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j.succ))))

attribute [simps (config := { isSimp := false }) fst snd] simEntry

/-- **The ideal experiment** `SIM-NME′‾(Π, S, n)` [PSV07, Definition 1, `ℓ = 1`] for the sampler
`M`, `r` output entries and an `sl`-bit `σ`, followed by the distinguisher `D`: sample the keys
and the coins, run the simulator on `pk` against the history oracle with one query, and output
`D`'s verdict on `(a, m, (d_i)_i, σ)`, where `d_i` is `COPY` on a flagged entry and `Dec_sk(c_i)`
otherwise. -/
noncomputable def snmIdeal (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (D : NUPPT) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
  (ProbComp.sample (Sim.Coins n)).bind fun rS =>
  (ProbComp.sample (D.Coins n)).bind fun rD =>
  (simulate (S.simImpl M n ρ)
      (Sim.toCompOn (S.simCodec M n r sl) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none).bind
    fun res =>
      let a := res.2.getD (zeroBits _)
      .pure (D.distinguisherL n
        (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
          (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg)) (S.simEntry res.1 i).1
            (S.simEntry res.1 i).2)
          (snmSigma res.1)) rD)

/-- The ideal simulation experiment samples all coins, runs the simulator against the history
oracle, and applies the distinguisher to the parameter, message, decoded entries, and final
output [PSV07, Definition 1]. -/
theorem snmIdeal_eq (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (D : NUPPT) (n : ℕ) :
    S.snmIdeal M Sim r sl D n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
      (ProbComp.sample (Sim.Coins n)).bind fun rS =>
      (ProbComp.sample (D.Coins n)).bind fun rD =>
      (simulate (S.simImpl M n ρ)
          (Sim.toCompOn (S.simCodec M n r sl) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none).bind
        fun res =>
          let a := res.2.getD (zeroBits (M.paramLen.eval n))
          .pure (D.distinguisherL n
            (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
              (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg)) (S.simEntry res.1 i).1
                (S.simEntry res.1 i).2)
              (snmSigma res.1)) rD)) := rfl

/-! ### Definition 173.7 and Theorem 174.8 -/

/-- **Simulation-based non-malleability** [PS10, Definition 173.7], in the form SIM-NME′ of
[PSV07, Definition 1] at one message, under the attack `atk`: for every sampler `M` (with its
history function), every non-uniform PPT adversary `A`, every polynomial query budget `q`,
number `r` of output ciphertexts and length `sl` of `σ`, there is a non-uniform PPT simulator
whose ideal experiment every non-uniform PPT distinguisher tells from `A`'s real one with
negligible advantage. -/
def SimNMSecure (atk : Attack) : Prop :=
  ∀ (M : MsgSampler) (A : NUPPT) (q r sl : PolyExpr), ∃ Sim : NUPPT,
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      advantage (S.snmReal atk M A (q.eval n) (r.eval n) (sl.eval n) D n)
        (S.snmIdeal M Sim (r.eval n) (sl.eval n) D n) ≤ ε n

/-- Simulation-based non-malleability holds exactly when, for every sampler, adversary and
polynomial budgets, one simulator makes every distinguisher's real/ideal advantage negligible
[PS10, Definition 173.7; PSV07, Definition 1]. -/
theorem SimNMSecure_iff (atk : Attack) :
    S.SimNMSecure atk ↔
      ∀ (M : MsgSampler) (A : NUPPT) (q r sl : PolyExpr), ∃ Sim : NUPPT,
        ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
          advantage (S.snmReal atk M A (q.eval n) (r.eval n) (sl.eval n) D n)
            (S.snmIdeal M Sim (r.eval n) (sl.eval n) D n) ≤ ε n := Iff.rfl

/-- **Theorem 174.8, (relation-based ⇒ indistinguishability-based), for every attack**
[PSV07, Corollary 1, at one message]: SIM-NME′ implies Definition 172.6.

**Proof sketch** (the maintainer's; [PSV07] defers its proof).
1. Fix an NM adversary `A` (budget `q`, `ℓ` ciphertexts) and a distinguisher `D`. Take the
   sampler `M` with parameter `⟨m₀, m₁⟩` that outputs `m_β` for a uniform coin `β`, and the
   constant history. The adversary `A'` runs `A`, forwarding `Dec`; on `A`'s challenge
   `⟨m₀, m₁⟩` it asks its own challenge with that parameter and passes `y` on. It outputs `A`'s
   ciphertexts, with `sl = 0`.
2. In the real experiment `m = m_β`, `y ← Enc_pk(m_β)`, and the entries `d_i` are `NM_β`'s
   output once `COPY` is read as `⊥`. Let `D'` read `m₀, m₁, m` from the view, output `0` when
   `m₀ = m₁`, and otherwise output whether `D`'s verdict on the converted entries equals `β`.
   Then `Pr[D' = 1] = ½ + ½ (Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1])` on the event `m₀ ≠ m₁`
   (when `m₀ = m₁`, `NM_0` and `NM_1` coincide).
3. In the ideal experiment the simulator's entries depend on `pk`, its coins and the constant
   history, so they are independent of `β` given the parameter; `D'` accepts with probability
   `½` on the event `m₀ ≠ m₁`. The distinguisher `D''` that tests `m₀ ≠ m₁` bounds the
   difference of that event's probabilities. So `NM`'s advantage is at most twice the sum of
   `D'`'s and `D''`'s, both negligible. -/
theorem nmSecure_of_simNMSecure (atk : Attack) (h : S.SimNMSecure atk) : S.NMSecure atk := by
  sorry

/-- **Theorem 174.8, (indistinguishability-based ⇒ relation-based), under CPA** [PSV07,
Theorem 3, at one message]: Definition 172.6 implies SIM-NME′ under a chosen-plaintext attack.
(Under CCA1 and CCA2 it does not, [PSV07, Theorem 4].)

**Proof sketch** (the maintainer's; [PSV07] defers its proof). Fix `M`, `A`, `q`, `r`, `sl`.
1. **The simulator** runs `A` on `pk`, answering `Dec` with `⊥` (CPA, `snmImpl_dec_cpa`). On
   `A`'s challenge `a` it asks its own query `a`, gets `h(m)`, draws a dummy `m̃ ← M(a)` with its
   own coins (it can run `M`), and answers `A` with `⟨Enc_pk(m̃), h(m)⟩`. It outputs `A`'s
   ciphertexts, flagging those equal to its dummy challenge, and `σ`. If `A` never asks, it
   never queries and outputs `A`'s output unflagged. At `msgLen(n) = 0` the two experiments
   coincide.
2. **The two experiments differ only in the challenge**: `Enc_pk(m)` in the real one,
   `Enc_pk(m̃)` in the ideal one, with `m, m̃` independent draws from `M(a)`, and the same `h(m)`.
3. **The NM adversary** `B` runs `A`; at `a` it draws `m, m̃ ← M(a)`, asks its challenge on
   `⟨m, m̃⟩`, receives `y = Enc_pk(m_b)`, and answers `A` with `⟨y, h(m)⟩`. It outputs `A`'s
   ciphertexts, then for each bit `x` of `a`, `m`, `σ` and the copy flags `[c_i = y]`, the pair
   `Enc_pk(x^{msgLen})`, `Enc_pk((¬x)^{msgLen})`. The two plaintexts differ, so by correctness at
   most one of the pair is the challenge, and the NM view yields `x` (as in the sketch of
   Theorem 175.9).
4. From `NM_b`'s view, the distinguisher reconstructs `(a, m, (d_i)_i, σ)`: the real experiment's
   output for `b = 0`, and the ideal one's (with the simulator of step 1) for `b = 1`. So `D`'s
   advantage is `B`'s NM advantage, negligible. -/
theorem simNMSecure_of_nmSecure_cpa (h : S.NMSecure .cpa) : S.SimNMSecure .cpa := by
  sorry

/-- **Theorem 174.8 under CPA** [PS10, Theorem 174.8; PSV07, Theorem 3, at one message]:
non-malleability (Definition 172.6) and simulation-based non-malleability (Definition 173.7, as
SIM-NME′) coincide under a chosen-plaintext attack. -/
theorem simNMSecure_cpa_iff_nmSecure_cpa : S.SimNMSecure .cpa ↔ S.NMSecure .cpa :=
  ⟨S.nmSecure_of_simNMSecure .cpa, S.simNMSecure_of_nmSecure_cpa⟩

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability
