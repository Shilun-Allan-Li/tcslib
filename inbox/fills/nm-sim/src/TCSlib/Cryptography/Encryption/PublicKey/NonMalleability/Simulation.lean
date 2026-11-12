/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimINDGap
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Rounds
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.IndSim
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation-based non-malleability

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

* `FixedLengthPKScheme.nmSecure_of_simNMSecure`: SIM ⇒ IND for every attack [PSV07, Corollary 1].
* `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa`: IND ⇒ SIM under CPA [PSV07, Theorem 3].
* `FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa`: Theorem 174.8 under CPA, from the two.
* `FixedLengthPKScheme.accept_snmReal_eq`, `FixedLengthPKScheme.accept_snmIdeal_eq`: both
  experiments on T2's lengths (`NMSim.realAcc`, `NMSim.idealAcc`).

## Contents

The proofs use the helper modules under `NonMalleability/Simulation/` (namespace
`TCSlib.Cryptography.Composability.NMSim`):
* `Generic`: budget reduction, coins drawn in advance, equal until bad, chunk maps;
* `Hybrid`: the hybrid oracle `rImpl` (an encryption of `M(a; ρ)` or of an independent draw), the
  history oracle, the views as strings and the acceptance rates `realAcc`, `idealAcc`, `hybAcc`;
* `SimIND`, `SimINDGap`: SIM ⇒ IND (the sampler `⟨m₀, m₁⟩ ↦ m_β`, the SIM adversary, `D'`, `D''`,
  and the real and ideal gaps);
* `Rounds`, `Challenge`: rounds of T2's handlers and the challenge handler shared by the two
  machines of IND ⇒ SIM;
* `Simulator`: the simulator (the ideal experiment is the hybrid `H_true`);
* `Reduction`, `Recover`, `IndSim`: the NM adversary, the NM distinguisher, and `NM_b = H_b`.

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

/-! ### The experiments on T2's lengths -/

section Transport

open NMSim
open AdaptiveCPA (castImpl castImpl_eq expect_simulate_castImpl_toCompOn padFin_ofFn_zeroBits)

/-- **The real experiment's oracles on T2's lengths are the hybrid oracle with `b = false`:**
read along `snmDin`, `snmDout`, `snmImpl` is `NMSim.rImpl … false … ρ ρ' none` (for every `ρ'`).

**Proof sketch.** Query by query (`snmImpl_dec`, `snmImpl_challenge`, `rImpl_dec`, `rImpl_some`,
`rImpl_none_lazy`, `rImpl_none_eager`): the casts keep the strings (`ofFn_padFin_of_length`), and
`M.draw`, `M.histAt` are `drawWith`, `histWith`. -/
theorem castImpl_snmImpl (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ ρ' : M.samp.Coins n) :
    castImpl (ins := fun i => (snmDin S M.paramLen i).eval n)
        (outs := fun i => (snmDout S M.histLen i).eval n) (S.snmImpl atk M n pk sk ρ) =
      rImpl S atk false M.samp M.paramLen M.histLen M.hist n pk sk ρ ρ' none := by
  funext i x s
  rw [castImpl_eq]
  match i, s with
  | 0, s =>
    have hx : List.ofFn (padFin (S.ctLen.eval n) (List.ofFn x)) = List.ofFn x :=
      GGMRed.ofFn_padFin_of_length (by
        rw [List.length_ofFn]; show (snmDin S M.paramLen 0).eval n = _; rw [snmDin_zero])
    erw [S.snmImpl_dec atk M n pk sk ρ (padFin (S.ctLen.eval n) (List.ofFn x)) s]
    rw [rImpl_dec, hx]
    by_cases hc : (FixedLengthScheme.decOpen atk s.isSome &&
        !decide (s.map Prod.fst = some (padFin (S.ctLen.eval n) (List.ofFn x)))) = true
    · rw [if_pos hc, if_pos hc, OracleComp.pure_bind]
    · rw [if_neg hc, if_neg hc, OracleComp.pure_bind]
      dsimp only
      erw [padFin_ofFn_zeroBits]
  | 1, some (y, a) =>
    erw [S.snmImpl_challenge atk M n pk sk ρ (padFin (M.paramLen.eval n) (List.ofFn x))
      (some (y, a))]
    dsimp only
    rw [OracleComp.pure_bind, rImpl_some]
    dsimp only
    erw [List.ofFn_fin_append]
    simp only [M.histAt_eq, M.draw_eq, histWith_eq, drawWith_eq]
  | 1, none =>
    erw [S.snmImpl_challenge atk M n pk sk ρ (padFin (M.paramLen.eval n) (List.ofFn x)) none]
    dsimp only
    rw [rImpl_none_lazy, OracleComp.bind_assoc]
    refine congrArg _ (funext fun re => ?_)
    rw [OracleComp.pure_bind, rImpl_none_eager, if_neg Bool.false_ne_true, encWith_eq]
    dsimp only
    erw [List.ofFn_fin_append]
    simp only [M.histAt_eq, M.draw_eq, histWith_eq, drawWith_eq]

/-- An entry as a string: `⟦snmEntry sk copy c⟧ = entryL S n sk copy ⟦c⟧`. -/
theorem ofFn_snmEntry {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    List.ofFn (S.snmEntry sk copy c) = entryL S n sk copy (List.ofFn c) := by
  rw [snmEntry_eq, entryL_eq]
  cases copy
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  · rw [if_pos rfl, if_pos rfl, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, ofFn_zeroBits]

/-- **The real experiment's view is `realView`:** for an output `w` and a final state `s`,
`snmView a (M.draw … a ρ) (d_i)_i (snmSigma w) = realView … ⟦w⟧ s`, with `a` the recorded parameter.

**Proof sketch.** Block by block: `ofFn_block` for the ciphertexts, `decide_map_ofFn` for the
copy test, `ofFn_snmEntry` for the entries and `ofFn_natAdd_eq_drop` for `σ`. -/
theorem snmView_realView (M : MsgSampler) (n r sl : ℕ) (sk : List Bool) (ρ : M.samp.Coins n)
    (w : Fin (r * S.ctLen.eval n + sl) → Bool) (s : S.SnmState M n) :
    S.snmView ((s.map Prod.snd).getD (zeroBits (M.paramLen.eval n)))
        (M.draw (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits (M.paramLen.eval n))) ρ)
        (fun i => S.snmEntry sk (decide (s.map Prod.fst = some (S.snmCt w i))) (S.snmCt w i))
        (snmSigma w) =
      realView S M.samp M.paramLen n r sk ρ (List.ofFn w) s := by
  rw [snmView_eq, realView_eq, M.draw_eq, drawWith_eq, snmSigma_eq, ofFn_natAdd_eq_drop]
  congr 3
  refine ofFn_eq_map_range _ _ fun i => ?_
  have hc : chunkAt (S.ctLen.eval n) i (List.ofFn w) = List.ofFn (S.snmCt w i) := by
    rw [snmCt_eq, ofFn_block]
  rw [hc, decide_map_ofFn, ofFn_snmEntry]

/-- **The ideal experiment's view is `idealView`:** for an output `w` and the oracle's final state
`sa`, `snmView a (M.draw … a ρ) (d_i)_i (snmSigma w) = idealView … ⟦w⟧ sa`.

**Proof sketch.** Entry `i` of `w` is the block `chunkAt (ctLen(n) + 1) i ⟦w⟧` (`ofFn_block`),
whose head is the `COPY` flag and whose tail is the ciphertext (`simEntry_fst`, `simEntry_snd`). -/
theorem snmView_idealView (M : MsgSampler) (n r sl : ℕ) (sk : List Bool) (ρ : M.samp.Coins n)
    (w : Fin (r * (S.ctLen.eval n + 1) + sl) → Bool) (sa : Option (Fin (M.paramLen.eval n) → Bool)) :
    S.snmView (sa.getD (zeroBits (M.paramLen.eval n)))
        (M.draw (S.msgLen.eval n) n (sa.getD (zeroBits (M.paramLen.eval n))) ρ)
        (fun i => S.snmEntry sk (S.simEntry w i).1 (S.simEntry w i).2) (snmSigma w) =
      idealView S M.samp M.paramLen n r sk ρ (List.ofFn w) sa := by
  rw [snmView_eq, idealView_eq, M.draw_eq, drawWith_eq, snmSigma_eq, ofFn_natAdd_eq_drop]
  congr 3
  refine ofFn_eq_map_range _ _ fun i => ?_
  have hc : chunkAt (S.ctLen.eval n + 1) i (List.ofFn w) =
      (S.simEntry w i).1 :: List.ofFn (S.simEntry w i).2 := by
    rw [← ofFn_block, List.ofFn_succ, simEntry_fst]
    exact congrArg _ (congrArg List.ofFn (funext fun j => (simEntry_snd S w i j).symm))
  rw [hc, List.headD_cons, List.tail_cons, ofFn_snmEntry]

/-- The ideal experiment's oracle is `NMSim.histImpl` of the sampler. -/
theorem simImpl_eq_histImpl (M : MsgSampler) (n : ℕ) (ρ : M.samp.Coins n) :
    S.simImpl M n ρ = histImpl S M.samp M.paramLen M.histLen M.hist n ρ := by
  funext i a s
  rw [simImpl_eq, histImpl_eq]
  dsimp only
  rw [M.histAt_eq, M.draw_eq, histWith_eq, drawWith_eq]

/-- `T2`'s query lengths at `pl = M.paramLen` are the real experiment's. -/
private theorem snmDin_eval (M : MsgSampler) (n : ℕ) :
    (fun i => (snmDin S M.paramLen i).eval n) = S.snmInLens M n := by
  funext i
  match i with
  | 0 => rw [snmDin_zero, snmInLens_zero]
  | 1 => rw [snmDin_one, snmInLens_one]

/-- `T2`'s answer lengths at `hl = M.histLen` are the real experiment's. -/
private theorem snmDout_eval (M : MsgSampler) (n : ℕ) :
    (fun i => (snmDout S M.histLen i).eval n) = S.snmOutLens M n := by
  funext i
  match i with
  | 0 => rw [snmDout_zero, snmOutLens_zero, PolyExpr.eval_add, PolyExpr.eval_const]
  | 1 => rw [snmDout_one, snmOutLens_one, PolyExpr.eval_add]

/-- **The real experiment's acceptance rate on T2's lengths:**
`accept (snmReal atk M A q r sl X n) = NMSim.realAcc S atk M.samp M.paramLen M.histLen M.hist A q r sl X n`.

**Proof sketch.** Transport `A`'s run (`expect_simulate_castImpl_toCompOn`, `castImpl_snmImpl`)
and read the view (`snmView_realView`). -/
theorem accept_snmReal_eq (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl : ℕ) (X : NUPPT)
    (n : ℕ) :
    accept (S.snmReal atk M A q r sl X n) =
      realAcc S atk M.samp M.paramLen M.histLen M.hist A q r sl X n := by
  rw [accept_eq, snmReal_eq, realAcc_eq, ProbComp.prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun ρ => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun rA => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun rX => ?_)
  rw [ProbComp.prob_bind, ← castImpl_snmImpl S atk M n _ _ ρ ρ]
  have hG : (fun res : (Fin (r * S.ctLen.eval n + sl) → Bool) × S.SnmState M n =>
      ProbComp.prob (.pure (X.distinguisherL n
        (S.snmView ((res.2.map Prod.snd).getD (zeroBits (M.paramLen.eval n)))
          (M.draw (S.msgLen.eval n) n ((res.2.map Prod.snd).getD (zeroBits (M.paramLen.eval n))) ρ)
          (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg))
            (decide (res.2.map Prod.fst = some (S.snmCt res.1 i))) (S.snmCt res.1 i))
          (snmSigma res.1)) rX)) (· = true)) =
      fun res => (fun p : List Bool × S.SnmState M n =>
        if X.distinguisherL n (realView S M.samp M.paramLen n r (pairSndD (S.gen.runAt n [] rg)) ρ
          p.1 p.2) rX = true then (1 : ℝ) else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [ProbComp.prob_pure, snmView_realView]
  exact (congrArg (ProbComp.expect _) hG).trans
    (expect_simulate_castImpl_toCompOn (snmDin_eval S M n) (snmDout_eval S M n)
      (rfl : r * S.ctLen.eval n + sl = r * S.ctLen.eval n + sl)
      (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ) A n q
      (pairFstD (S.gen.runAt n [] rg)) rA none fun p : List Bool × S.SnmState M n =>
        if X.distinguisherL n (realView S M.samp M.paramLen n r (pairSndD (S.gen.runAt n [] rg)) ρ
          p.1 p.2) rX = true then (1 : ℝ) else 0).symm

/-- **The ideal experiment's acceptance rate on T2's lengths:**
`accept (snmIdeal M Sim r sl X n) = NMSim.idealAcc S M.samp M.paramLen M.histLen M.hist Sim r sl X n`.

**Proof sketch.** `simImpl_eq_histImpl`, and read the view (`snmView_idealView`). -/
theorem accept_snmIdeal_eq (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (X : NUPPT) (n : ℕ) :
    accept (S.snmIdeal M Sim r sl X n) =
      idealAcc S M.samp M.paramLen M.histLen M.hist Sim r sl X n := by
  rw [accept_eq, snmIdeal_eq, idealAcc_eq, ProbComp.prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun ρ => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun rS => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun rX => ?_)
  rw [ProbComp.prob_bind, simImpl_eq_histImpl]
  refine congrArg (ProbComp.expect _) (funext fun res => ?_)
  rw [ProbComp.prob_pure]
  dsimp only
  rw [snmView_idealView]

end Transport

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

/-- The bound of SIM ⇒ IND: if `2·R₁ − R₂ = a − b`, `2·I₁ = I₂`, `|R₁ − I₁| ≤ e₁` and
`|R₂ − I₂| ≤ e₂`, then `|b − a| ≤ 2·e₁ + e₂`. -/
private theorem abs_le_of_gap {a b R₁ I₁ R₂ I₂ e₁ e₂ : ℝ} (hr : 2 * R₁ - R₂ = a - b)
    (hi : 2 * I₁ = I₂) (h₁ : |R₁ - I₁| ≤ e₁) (h₂ : |R₂ - I₂| ≤ e₂) : |b - a| ≤ 2 * e₁ + e₂ := by
  have hab : b - a = -(2 * (R₁ - I₁) - (R₂ - I₂)) := by linarith
  rw [hab, abs_neg]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_two]
  linarith

/-- **Theorem 174.8, (relation-based ⇒ indistinguishability-based), for every attack**
[PSV07, Corollary 1, at one message]: SIM-NME′ implies Definition 172.6.

**Proof sketch** (the maintainer's route; [PSV07] defers its proof).
1. Fix an NM adversary `A` (budget `q`, `ℓ` ciphertexts) and a distinguisher `D`. Take the
   sampler `M = NMSim.halfSamp S`: its parameter is `⟨m₀, m₁⟩` (`paramLen = msgLen + msgLen`), it
   outputs `m_β` for its single coin `β`, and its history is empty (`histLen = 0`). The SIM
   adversary `A'` is T2's machine of `NMSim.simHandler S ℓ`: it forwards `A`'s `Dec` and challenge
   queries and outputs `A`'s ciphertexts (`r = ℓ`, `sl = 0`). Take `Sim` from `h M A' Q ℓ 0`, with
   `Q = q·perCall + finCall` T2's budget.
2. `D' = NMSim.tailDist S D` outputs `0` when `m₀ = m₁`, and otherwise whether `D`'s verdict on the
   entries without their `COPY` flags (so a copy reads as `nmDecrypt`'s `⊥`) equals `[m = m₁]`;
   `D'' = NMSim.halfDist S` tests `m₀ ≠ m₁`.
3. **Real** (`NMSim.real_gap`). With the coin `β` fixed, the real experiment's oracles are those of
   `NM_β` (`castImpl_snmImpl`, `NMSim.castImpl_indImpl_abs`), and the unflagged entries are
   `NM_β`'s output. While `m₀ = m₁` the two coins give the same run (`NMSim.expect_runB_good`). So
   `2·Pr_real[D' = 1] − Pr_real[D'' = 1] = Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1]`.
4. **Ideal** (`NMSim.ideal_gap`). With the empty history the simulator's oracle ignores `β`
   (`NMSim.histImpl_coins`), and `m = m_β` makes exactly one coin satisfy `D'` when `m₀ ≠ m₁`:
   `2·Pr_ideal[D' = 1] = Pr_ideal[D'' = 1]`.
5. Hence `NM`'s advantage is at most `2·adv(D') + adv(D'')`, negligible (`accept_snmReal_eq`,
   `accept_snmIdeal_eq` read both experiments on T2's lengths). -/
theorem nmSecure_of_simNMSecure (atk : Attack) (h : S.SimNMSecure atk) : S.NMSecure atk := by
  rw [S.NMSecure_iff]
  intro A q ℓ D
  obtain ⟨A', hA'⟩ := exists_interactiveHandlerMachine A q (NMSim.snmDin S (S.msgLen.add S.msgLen))
    (NMSim.snmDout S (.const 0)) (NMSim.snmDin S (S.msgLen.add S.msgLen))
    (NMSim.snmDout S (.const 0)) (ℓ.mul S.ctLen) (NMSim.simHandler S ℓ)
  obtain ⟨Sim, hSim⟩ := h ⟨NMSim.halfSamp S, S.msgLen.add S.msgLen, fun _ => [], .const 0,
      polyTimeComputable_const []⟩ A'
    ((q.mul (NMSim.simHandler S ℓ).perCall).add (NMSim.simHandler S ℓ).finCall) ℓ (.const 0)
  obtain ⟨ε₁, hε₁, h₁⟩ := hSim (NMSim.tailDist S D)
  obtain ⟨ε₂, hε₂, h₂⟩ := hSim (NMSim.halfDist S)
  refine ⟨fun n => 2 * ε₁ n + ε₂ n, (hε₁.const_mul 2).add hε₂, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hA' n
  have hK : ((q.mul (NMSim.simHandler S ℓ).perCall).add (NMSim.simHandler S ℓ).finCall).eval n =
      q.eval n * (NMSim.simHandler S ℓ).perCall.eval n + (NMSim.simHandler S ℓ).finCall.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have e₁ := h₁ n
  have e₂ := h₂ n
  rw [advantage_eq, accept_snmReal_eq, accept_snmIdeal_eq] at e₁ e₂
  rw [advantage_eq]
  exact abs_le_of_gap (NMSim.real_gap S atk A A' q ℓ _ D n hK φ hφ)
    (NMSim.ideal_gap S Sim D (ℓ.eval n) n) e₁ e₂

/-- **Theorem 174.8, (indistinguishability-based ⇒ relation-based), under CPA** [PSV07,
Theorem 3, at one message]: Definition 172.6 implies SIM-NME′ under a chosen-plaintext attack.
(Under CCA1 and CCA2 it does not, [PSV07, Theorem 4].)

**Proof sketch** (the maintainer's route; [PSV07] defers its proof). Fix `M`, `A`, `q`, `r`, `sl`.
1. **The hybrids.** `H_b` (`NMSim.hybAcc`) runs `A` against the oracle `NMSim.rImpl … b …` (under
   CPA `Dec` answers `⊥`, `snmImpl_dec_cpa`): on the first challenge `a` it answers
   `⟨Enc_pk(M(a; ρ_b)), h(M(a; ρ))⟩` for the sampler's coins `ρ₀ = ρ` and an independent `ρ₁`, and
   the view is `(a, M(a; ρ), (d_i)_i, σ)` with `d_i = COPY` iff `c_i` is the challenge. `H_false` is
   the real experiment (`castImpl_snmImpl`, `NMSim.realAcc_eq_hybAcc`).
2. **The simulator** (`NMSim.exists_simulator`) runs `A` on `pk`, answering `Dec` with `⊥`. On `A`'s
   first challenge `a` it makes its only query `a`, gets `h(m)`, draws `m̃ = M(a; ρ̃)` with its own
   coins and `M`'s advice (hard-wired, `exists_withAdviceOn`), and answers `⟨Enc_pk(m̃), h(m)⟩`;
   repeated challenges get the recorded answer. It outputs `A`'s ciphertexts, each flagged `COPY`
   iff it equals its dummy challenge, and `σ`; if `A` never asks it never queries. Its run at
   budget `1` is its run at T2's budget (`NMSim.toCompOn_budget_eq`; it asks at most one query,
   `NMSim.chalHandler_costBoundedBy`), and against the history oracle it is `H_true`.
3. **The NM adversary** `B` (`NMSim.exists_nmAdversary`) runs `A`; on `a` it draws `m, m̃ ← M(a)`,
   asks its challenge on `⟨m, m̃⟩`, receives `y = Enc_pk(m_b)` and answers `A` with `⟨y, h(m)⟩`. It
   outputs each of `A`'s ciphertexts followed by the pair `Enc_pk(f^{msgLen})`, `Enc_pk((¬f)^{msgLen})`
   for its copy flag `f = [c_i = y]`, then the same pair for each bit `x` of `a`, `m` and `σ`. By
   correctness the two plaintexts of a pair differ, so at most one of the pair is the challenge,
   and the distinguisher `NMSim.recDist` reads `x` back (`NMCCA2.guessBit`) and runs `D` on the
   view. When `msgLen(n) > 0`, `NM_b` accepts with the probability of `H_b`.
4. Hence at every `n` the SIM advantage is `B`'s NM advantage, or `0` when `msgLen(n) = 0` (the two
   hybrids coincide, `NMSim.hybAcc_true_eq_false`): it is negligible. -/
theorem simNMSecure_of_nmSecure_cpa (h : S.NMSecure .cpa) : S.SimNMSecure .cpa := by
  intro M A q r sl
  obtain ⟨Sim, hSim⟩ := NMSim.exists_simulator S M.samp M.paramLen M.histLen M.hist A q r sl
  obtain ⟨B, qB, hB⟩ := NMSim.exists_nmAdversary S M.samp M.paramLen M.histLen M.hist
    M.hist_poly r sl A q
  refine ⟨Sim, fun D => ?_⟩
  obtain ⟨ε, hε, hεn⟩ := (S.NMSecure_iff .cpa).1 h B qB (NMSim.nmLen S M.paramLen r sl)
    (NMSim.recDist S M.paramLen r D)
  refine ⟨ε, hε, fun n => ?_⟩
  have h₀ := hεn n
  rw [advantage_eq] at h₀
  rw [advantage_eq, accept_snmReal_eq, accept_snmIdeal_eq, hSim, NMSim.realAcc_eq_hybAcc]
  by_cases hL : S.msgLen.eval n = 0
  · rw [NMSim.hybAcc_true_eq_false S .cpa M.samp M.paramLen M.histLen M.hist A (q.eval n) (r.eval n)
      (sl.eval n) D n hL, sub_self, abs_zero]
    exact (abs_nonneg _).trans h₀
  · rwa [← hB D n false (Nat.pos_of_ne_zero hL), ← hB D n true (Nat.pos_of_ne_zero hL)]

/-- **Theorem 174.8 under CPA** [PS10, Theorem 174.8; PSV07, Theorem 3, at one message]:
non-malleability (Definition 172.6) and simulation-based non-malleability (Definition 173.7, as
SIM-NME′) coincide under a chosen-plaintext attack. -/
theorem simNMSecure_cpa_iff_nmSecure_cpa : S.SimNMSecure .cpa ↔ S.NMSecure .cpa :=
  ⟨S.nmSecure_of_simNMSecure .cpa, S.simNMSecure_of_nmSecure_cpa⟩

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability
