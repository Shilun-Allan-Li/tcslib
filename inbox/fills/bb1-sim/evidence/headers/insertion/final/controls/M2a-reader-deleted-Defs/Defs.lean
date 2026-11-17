/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Identity-based encryption and selective-identity security

An *identity-based encryption* (IBE) system [BB04, §2.1] consists of four algorithms: `Setup`
generates the system parameters `params` and a master key; `KeyGen` uses the master key to
generate the private key `d_ID` of an identity `ID`; `Encrypt` encrypts a message for an identity
using the parameters; `Decrypt` decrypts with a private key.

*Selective-identity chosen-plaintext security* (IND-sID-CPA, [BB04, §2.1, the game and
Definition 2.2]): the adversary first commits to the identity `ID*` it will attack (**Init**);
the challenger runs `Setup` and gives it `params` (**Setup**); the adversary adaptively asks for
the private keys of identities `ID ≠ ID*` (**Phase 1**); it outputs two messages `M₀, M₁` of the
message space and receives `Encrypt(params, ID*, M_b)` (**Challenge**); it asks more private-key
queries (**Phase 2**) and outputs a guess `b'` (**Guess**). There are no decryption queries.

**The scheme interface.** The algorithms are probabilistic computations of the `Games` framework
over typed parameters, keys and ciphertexts (`IBEScheme`). Identities are `idLen(κ)`-bit strings
and messages arrive as `msgLen(κ)`-bit strings; a scheme declares which strings are messages for
given parameters (`MsgSpace`, the paper's message space `M`). For the adversary, parameters,
private keys and ciphertexts are written as fixed-width strings (`encPP`, `encSK`, `encCT`),
injective on the objects the algorithms can output (`encPP_inj`, `encSK_inj`, `encCT_inj`).

**The game's encoding.** As in the public-key games (`Encryption.PublicKey.OracleSecurity`), one
non-uniform PPT machine plays every phase against bit-string oracles (`Games.bitCodec`):
* `Init` (oracle 0) takes `ID*` and answers `params`. The first query fixes `ID*`; later queries
  repeat `params` and leave `ID*` unchanged.
* `KeyGen` (oracle 1) takes `ID` and answers `⟨1, d_ID⟩` with fresh `KeyGen` coins when `ID*` is
  fixed and `ID ≠ ID*`, and `⊥` (all `false`) otherwise.
* `Challenge` (oracle 2) takes `⟨M₀, M₁⟩` and answers `Encrypt(params, ID*, M_b)` the first time
  it is asked with `ID*` fixed and `M₀, M₁ ∈ M`, recording it; later it repeats the recorded
  challenge; it answers `⊥` before `Init` and on messages outside `M`.
The machine starts with input `1^κ` only, so the only information it has before committing is
its coins. `Setup` is run before the machine starts; since nothing about `params` reaches the
machine before its `Init` query, this is the order of [BB04, §2.1] in distribution.

**Deviation:** [BB04, Definition 2.2] is concrete (`(t, q_ID, ε)`) and measures
`|Pr[b = b'] − 1/2|`; here security is asymptotic, for every non-uniform PPT and every polynomial
query budget, and the advantage is `|Pr[b' = 1 | b = 0] − Pr[b' = 1 | b = 1]|`, twice the
paper's (`Games.guessAdv_eq_half_advantage`). Queries to `KeyGen` for `ID*` and challenges outside
`M` are answered `⊥` instead of being forbidden. The algorithms are typed probabilistic
computations; their efficiency is not part of the interface (per-scheme contracts).

## Main definitions

* `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme` — an IBE system [BB04, §2.1].
* `IBEScheme.Correct` — perfect correctness on the message space.
* `IBEScheme.sidSpec`, `IBEScheme.sidImpl`, `IBEScheme.sidGame`, `IBEScheme.SIDSecure` — the
  IND-sID-CPA game and security [BB04, §2.1 and Definition 2.2].
* `IBEScheme.oracleImpl` — the three oracles from typed handlers (for simulators).

## Main results

* `IBEScheme.sidImpl_init_none`, `sidImpl_init_some`, `sidImpl_keyGen_none`,
  `sidImpl_keyGen_target`, `sidImpl_keyGen_ne`, `sidImpl_challenge_none`,
  `sidImpl_challenge_repeat`, `sidImpl_challenge_fresh`, `sidImpl_challenge_invalid` — the
  oracles case by case; `oracleImpl_zero`, `oracleImpl_one`, `oracleImpl_two`.
* `IBEScheme.honestRun_eq`, `correct_iff`, `sidGame_eq`, `sidSecure_iff` — the experiments and
  predicates through their published equations.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.1 (pp. 2–4): IBE systems, the
  selective identity game, Definitions 2.1 and 2.2.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; the one-machine encoding of the games of §7.1.4.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Composability

/-- An **identity-based encryption system** [BB04, §2.1]: at each security parameter `κ`, types of
system parameters `PP κ`, master keys `MSK κ`, private keys `SK κ` and ciphertexts `CT κ`, and
* `setup κ`, a probabilistic computation of `(params, master-key)`;
* `keyGen κ msk ID`, a probabilistic computation of the private key `d_ID` of the `idLen(κ)`-bit
  identity `ID`;
* `enc κ params ID M`, a probabilistic computation of a ciphertext of the `msgLen(κ)`-bit message
  `M` for `ID`;
* `dec κ d_ID C`, the deterministic decryption, `none` for `⊥`;
* the message space `MsgSpace κ params` (the paper's `M`), and fixed-width encodings of
  parameters, private keys and ciphertexts for the adversary, which lose no information on the
  objects the algorithms can output (`encPP_inj`, `encSK_inj`, `encCT_inj`).

**Deviation:** messages are strings with a parameter-dependent message space (as for El Gamal,
`Candidates.GroupPKScheme`); the algorithms are typed probabilistic computations, without an
efficiency requirement in the interface. The adversary sees parameters, private keys and
ciphertexts only through their encodings; their fidelity is injectivity on reachable objects
(possible outputs of `setup`, and keys and ciphertexts under one possible output of `setup`), not
efficient decoding, and not injectivity on all of `PP κ`, `SK κ`, `CT κ` (an encoding may omit
data that the parameters fix). The efficiency of the encodings is deferred with that of the
algorithms (ruling Q5 of `PairingCryptographyPlan.md`). -/
structure IBEScheme where
  /-- The identity length. -/
  idLen : PolyExpr
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The width of encoded parameters. -/
  ppLen : PolyExpr
  /-- The width of encoded private keys. -/
  skLen : PolyExpr
  /-- The width of encoded ciphertexts. -/
  ctLen : PolyExpr
  /-- System parameters. -/
  PP : ℕ → Type
  /-- Master keys. -/
  MSK : ℕ → Type
  /-- Private keys. -/
  SK : ℕ → Type
  /-- Ciphertexts. -/
  CT : ℕ → Type
  /-- `Setup`: system parameters and a master key. -/
  setup : (κ : ℕ) → ProbComp (PP κ × MSK κ)
  /-- `KeyGen`: the private key of an identity. -/
  keyGen : (κ : ℕ) → MSK κ → (Fin (idLen.eval κ) → Bool) → ProbComp (SK κ)
  /-- `Encrypt`: a ciphertext of a message for an identity. -/
  enc : (κ : ℕ) → PP κ → (Fin (idLen.eval κ) → Bool) → (Fin (msgLen.eval κ) → Bool) →
    ProbComp (CT κ)
  /-- `Decrypt`: the message of a ciphertext under a private key, or `⊥`. -/
  dec : (κ : ℕ) → SK κ → CT κ → Option (Fin (msgLen.eval κ) → Bool)
  /-- The message space for given parameters. -/
  MsgSpace : (κ : ℕ) → PP κ → (Fin (msgLen.eval κ) → Bool) → Prop
  /-- The encoding of parameters. -/
  encPP : (κ : ℕ) → PP κ → Fin (ppLen.eval κ) → Bool
  /-- The encoding of private keys. -/
  encSK : (κ : ℕ) → SK κ → Fin (skLen.eval κ) → Bool
  /-- The encoding of ciphertexts. -/
  encCT : (κ : ℕ) → CT κ → Fin (ctLen.eval κ) → Bool
  /-- **The parameter encoding is injective on reachable parameters**: two parameters output by
  `setup κ` with equal encodings are equal. With `encSK_inj` and `encCT_inj`, the adversary's
  wire view loses no information about the objects it is given [BB04, §2.1: the adversary
  receives `params`, the private keys `d_i` and the challenge ciphertext `C`]. -/
  encPP_inj : ∀ κ, (setup κ).AllOutputs fun k => (setup κ).AllOutputs fun k' =>
    encPP κ k.1 = encPP κ k'.1 → k.1 = k'.1
  /-- **The private-key encoding is injective on reachable keys**: for every possible output
  `(params, master-key)` of `setup κ`, two private keys output by `keyGen` with that master key,
  for any identities, with equal encodings are equal [BB04, §2.1, the adversary's view]. -/
  encSK_inj : ∀ κ, (setup κ).AllOutputs fun k => ∀ id id',
    (keyGen κ k.2 id).AllOutputs fun d => (keyGen κ k.2 id').AllOutputs fun d' =>
      encSK κ d = encSK κ d' → d = d'
  /-- **The ciphertext encoding is injective on reachable ciphertexts**: for every possible output
  of `setup κ`, two ciphertexts output by `enc` with its parameters, for any identities and
  messages, with equal encodings are equal [BB04, §2.1, the adversary's view]. -/
  encCT_inj : ∀ κ, (setup κ).AllOutputs fun k => ∀ id id' m m',
    (enc κ k.1 id m).AllOutputs fun c => (enc κ k.1 id' m').AllOutputs fun c' =>
      encCT κ c = encCT κ c' → c = c'

namespace IBEScheme

variable (S : IBEScheme)

/-- One honest run for the identity `ID` and the message `M`: `Setup`, then `KeyGen` for `ID`
and `Encrypt(params, ID, M)`, returning the parameters, the private key and the ciphertext. -/
noncomputable def honestRun (κ : ℕ) (id : Fin (S.idLen.eval κ) → Bool)
    (m : Fin (S.msgLen.eval κ) → Bool) : ProbComp (S.PP κ × S.SK κ × S.CT κ) :=
  (S.setup κ).bind fun k =>
  (S.keyGen κ k.2 id).bind fun sk =>
  (S.enc κ k.1 id m).bind fun c => .pure (k.1, sk, c)

/-- `S.honestRun κ id m` runs `Setup`, `KeyGen` for `id` and `Encrypt` of `m` for `id`, and
returns `(params, d_id, C)`. -/
theorem honestRun_eq (κ : ℕ) (id : Fin (S.idLen.eval κ) → Bool)
    (m : Fin (S.msgLen.eval κ) → Bool) :
    S.honestRun κ id m =
      (S.setup κ).bind fun k =>
      (S.keyGen κ k.2 id).bind fun sk =>
      (S.enc κ k.1 id m).bind fun c => .pure (k.1, sk, c) := rfl

/-- **Perfect correctness** [BB04, §2.1, "the decryption algorithm decrypts ciphertexts using the
private key"; §4.1's verification for BB1]: for every identity `ID` and every message `M`, every
possible outcome `(params, d_ID, C)` of an honest run with `M` in the message space of `params`
has `Decrypt(d_ID, C) = M`. -/
def Correct : Prop :=
  ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),
    (S.honestRun κ id m).AllOutputs fun x => S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m

/-- `S.Correct` iff every possible outcome of every honest run with a message of the message
space decrypts to that message. -/
theorem correct_iff :
    S.Correct ↔ ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),
      (S.honestRun κ id m).AllOutputs fun x =>
        S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m := Iff.rfl

/-! ### The selective-identity game -/

/-- The query lengths of the three oracles: `Init` and `KeyGen` take an identity, `Challenge`
takes two messages. -/
def inLens (κ : ℕ) : Fin 3 → ℕ
  | 0 => S.idLen.eval κ
  | 1 => S.idLen.eval κ
  | 2 => S.msgLen.eval κ + S.msgLen.eval κ

/-- `Init` queries are identities: `S.inLens κ 0 = S.idLen.eval κ`. -/
theorem inLens_zero (κ : ℕ) : S.inLens κ 0 = S.idLen.eval κ := rfl

/-- `KeyGen` queries are identities: `S.inLens κ 1 = S.idLen.eval κ`. -/
theorem inLens_one (κ : ℕ) : S.inLens κ 1 = S.idLen.eval κ := rfl

/-- `Challenge` queries are two messages: `S.inLens κ 2 = S.msgLen.eval κ + S.msgLen.eval κ`. -/
theorem inLens_two (κ : ℕ) : S.inLens κ 2 = S.msgLen.eval κ + S.msgLen.eval κ := rfl

/-- The answer lengths of the three oracles: `Init` answers the parameters, `KeyGen` a validity
bit and a private key, `Challenge` a ciphertext. -/
def outLens (κ : ℕ) : Fin 3 → ℕ
  | 0 => S.ppLen.eval κ
  | 1 => S.skLen.eval κ + 1
  | 2 => S.ctLen.eval κ

/-- `Init` answers parameters: `S.outLens κ 0 = S.ppLen.eval κ`. -/
theorem outLens_zero (κ : ℕ) : S.outLens κ 0 = S.ppLen.eval κ := rfl

/-- `KeyGen` answers a validity bit and a key: `S.outLens κ 1 = S.skLen.eval κ + 1`. -/
theorem outLens_one (κ : ℕ) : S.outLens κ 1 = S.skLen.eval κ + 1 := rfl

/-- `Challenge` answers a ciphertext: `S.outLens κ 2 = S.ctLen.eval κ`. -/
theorem outLens_two (κ : ℕ) : S.outLens κ 2 = S.ctLen.eval κ := rfl

/-- The three oracles of the IND-sID-CPA game at parameter `κ`. -/
abbrev sidSpec (κ : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens κ) (S.outLens κ)

/-- The IND-sID-CPA oracle specification is the bit specification at the scheme's query and
answer lengths: `S.sidSpec κ = bitSpec (S.inLens κ) (S.outLens κ)`. -/
theorem sidSpec_eq (κ : ℕ) : S.sidSpec κ = bitSpec (S.inLens κ) (S.outLens κ) := rfl

/-- The state of the IND-sID-CPA game: the committed identity `ID*` (once `Init` is asked) and
the challenge ciphertext (once issued). -/
abbrev SidState (κ : ℕ) : Type :=
  Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)

/-- The game state is the optional committed identity and the optional encoded challenge:
`S.SidState κ = Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)`. -/
theorem sidState_eq (κ : ℕ) :
    S.SidState κ =
      (Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)) := rfl

open Classical in
/-- **The oracles of the IND-sID-CPA game** [BB04, §2.1] with hidden bit `b`, at parameter `κ`,
for the parameters `pp` and the master key `msk`:
- `Init` on `ID`: answers `params`; records `ID*` = `ID` if none is recorded yet.
- `KeyGen` on `ID`: when `ID*` is recorded and `ID ≠ ID*`, answers `⟨1, d_ID⟩` with
  `d_ID ← KeyGen(msk, ID)`; otherwise `⊥`.
- `Challenge` on `⟨M₀, M₁⟩`: with `ID*` recorded and no challenge yet, if `M₀, M₁ ∈ M`, answers
  and records `C ← Encrypt(params, ID*, M_b)`, and otherwise `⊥`; once a challenge is recorded,
  repeats it; before `Init`, `⊥`. -/
noncomputable def sidImpl (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ) :
    QueryImpl (S.sidSpec κ) (S.SidState κ) unifSpec
  | 0, id, s =>
    match s.1 with
    | none => .pure (S.encPP κ pp, (some id, s.2))
    | some _ => .pure (S.encPP κ pp, s)
  | 1, id, s =>
    match s.1 with
    | some t =>
      if id = t then .pure (zeroBits _, s)
      else (S.keyGen κ msk id).bind fun sk =>
        .pure (FixedLengthScheme.decAnswer (some (S.encSK κ sk)), s)
    | none => .pure (zeroBits _, s)
  | 2, mm, s =>
    match s.1, s.2 with
    | some _, some c => .pure (c, s)
    | some t, none =>
      if S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
          S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2 then
        (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1)).bind fun c =>
          .pure (S.encCT κ c, (some t, some (S.encCT κ c)))
      else .pure (zeroBits _, s)
    | none, _ => .pure (zeroBits _, s)

/-- `Init` before any commitment answers the parameters and records the identity. -/
theorem sidImpl_init_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 0 id (none, c) = .pure (S.encPP κ pp, (some id, c)) := rfl

/-- `Init` after a commitment answers the parameters and keeps the state. -/
theorem sidImpl_init_some (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 0 id (some t, c) = .pure (S.encPP κ pp, (some t, c)) := rfl

/-- `KeyGen` before `Init` answers `⊥`. -/
theorem sidImpl_keyGen_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 1 id (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `KeyGen` for the committed identity answers `⊥`. -/
theorem sidImpl_keyGen_target (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 1 t (some t, c) = .pure (zeroBits _, (some t, c)) := by
  simp [sidImpl]

/-- `KeyGen` for an identity other than the committed one answers `⟨1, d_ID⟩` with
`d_ID ← KeyGen(msk, ID)` and keeps the state. -/
theorem sidImpl_keyGen_ne (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool))
    (h : id ≠ t) :
    S.sidImpl b κ pp msk 1 id (some t, c) =
      (S.keyGen κ msk id).bind fun sk =>
        .pure (FixedLengthScheme.decAnswer (some (S.encSK κ sk)), (some t, c)) := by
  simp [sidImpl, h]

/-- `Challenge` before `Init` answers `⊥`. -/
theorem sidImpl_challenge_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 2 mm (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `Challenge` after a recorded challenge repeats it. -/
theorem sidImpl_challenge_repeat (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Fin (S.ctLen.eval κ) → Bool) :
    S.sidImpl b κ pp msk 2 mm (some t, some c) = .pure (c, (some t, some c)) := rfl

/-- The first `Challenge` with both messages in the message space answers and records
`C ← Encrypt(params, ID*, M_b)`. -/
theorem sidImpl_challenge_fresh (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2) :
    S.sidImpl b κ pp msk 2 mm (some t, none) =
      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf mm).2
        else (FixedLengthScheme.splitHalf mm).1)).bind fun c =>
        .pure (S.encCT κ c, (some t, some (S.encCT κ c))) := by
  simp only [sidImpl]
  rw [if_pos h]

/-- The first `Challenge` with a message outside the message space answers `⊥`. -/
theorem sidImpl_challenge_invalid (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (h : ¬ (S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2)) :
    S.sidImpl b κ pp msk 2 mm (some t, none) = .pure (zeroBits _, (some t, none)) := by
  simp only [sidImpl]
  rw [if_neg h]

/-- **The three oracles from typed handlers**: an implementation of `S.sidSpec κ` whose `Init`,
`KeyGen` and `Challenge` oracles are the handlers `init`, `key` and `chal`, which take and return
strings of the scheme's lengths. Simulators and reductions describe their oracles this way, so
that they never read the oracle lengths `inLens`, `outLens` through their bodies. -/
def oracleImpl {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ)) :
    QueryImpl (S.sidSpec κ) σ unifSpec
  | 0, x, s => init x s
  | 1, x, s => key x s
  | 2, x, s => chal x s

/-- Oracle `0` of `S.oracleImpl κ init key chal` is the handler `init`. -/
theorem oracleImpl_zero {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.idLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 0 x s = init x s := rfl

/-- Oracle `1` of `S.oracleImpl κ init key chal` is the handler `key`. -/
theorem oracleImpl_one {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.idLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 1 x s = key x s := rfl

/-- Oracle `2` of `S.oracleImpl κ init key chal` is the handler `chal`. -/
theorem oracleImpl_two {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 2 x s = chal x s := rfl

/-- **Oracle `0` of `oracleImpl` on the game's query type**: the handler `init` on the query read
as an identity, its answer read back on the game's answer type. -/
theorem oracleImpl_zero_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 0) (s : σ) :
    S.oracleImpl κ init key chal 0 x s =
      (init (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `1` of `oracleImpl` on the game's query type**: the handler `key` on the query read
as an identity, its answer read back on the game's answer type. -/
theorem oracleImpl_one_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 1) (s : σ) :
    S.oracleImpl κ init key chal 1 x s =
      (key (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `2` of `oracleImpl` on the game's query type**: the handler `chal` on the query read
as two messages, its answer read back on the game's answer type. -/
theorem oracleImpl_two_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 2) (s : σ) :
    S.oracleImpl κ init key chal 2 x s =
      (chal (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
        from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `0` of the game on the game's query type**: `Init` on the query read as an identity,
its answer read back on the game's answer type:
`S.sidImpl b κ pp msk 0 x s =
(S.sidImpl b κ pp msk 0 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
theorem sidImpl_zero_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 0) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 0 x s =
      (S.sidImpl b κ pp msk 0
        (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
          Fin (S.idLen.eval κ) → Bool) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `2` of the game on the game's query type**: `Challenge` on the query read as two
messages, its answer read back on the game's answer type:
`S.sidImpl b κ pp msk 2 x s =
(S.sidImpl b κ pp msk 2 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
theorem sidImpl_two_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 2 x s =
      (S.sidImpl b κ pp msk 2
        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `1` of the game, its query read as an identity**: the call on the game's query
type is the call on the query read as an `idLen(κ)`-bit identity, with the answer kept on the
game's answer type (the form for the `⊥` answers):
`S.sidImpl b κ pp msk 1 x s = S.sidImpl b κ pp msk 1 (cast x) s`. -/
theorem sidImpl_one_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 1) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 1 x s =
      S.sidImpl b κ pp msk 1
        (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
          Fin (S.idLen.eval κ) → Bool) s := rfl

/-- **`KeyGen` for another identity, on the game's types**: with `ID*` recorded and the query
`x`, read as an identity, different from it, the answer is `⟨1, d_ID⟩` with
`d_ID ← KeyGen(msk, ID)`, read back on the game's answer type: for `cast x ≠ t`,
`S.sidImpl b κ pp msk 1 x (some t, c) =
(S.keyGen κ msk (cast x)).bind fun sk => pure (cast (decAnswer (some (encSK sk))), (some t, c))`. -/
theorem sidImpl_keyGen_ne_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 1) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool))
    (h : (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
      Fin (S.idLen.eval κ) → Bool) ≠ t) :
    S.sidImpl b κ pp msk 1 x (some t, c) =
      (S.keyGen κ msk (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl)
        x)).bind fun sk =>
        .pure (cast (show (Fin (S.skLen.eval κ + 1) → Bool) = (S.sidSpec κ).rng 1 from rfl)
          (FixedLengthScheme.decAnswer (some (S.encSK κ sk))), (some t, c)) :=
  S.sidImpl_keyGen_ne b κ pp msk _ t c h

/-- **The first valid `Challenge`, on the game's types**: with `ID*` recorded, no challenge yet,
and both messages of the query `x`, read as two messages, in the message space, the answer is
`C ← Encrypt(params, ID*, M_b)`, read back on the game's answer type, and `C` is recorded: for
`(M₀, M₁) = splitHalf (cast x)` with `M₀, M₁ ∈ M`, `S.sidImpl b κ pp msk 2 x (some t, none) =
(S.enc κ pp t M_b).bind fun C => pure (cast (encCT C), (some t, some (encCT C)))`. -/
theorem sidImpl_challenge_fresh_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (t : Fin (S.idLen.eval κ) → Bool)
    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2) :
    S.sidImpl b κ pp msk 2 x (some t, none) =
      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2
        else (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1)).bind fun c =>
        .pure (cast (show (Fin (S.ctLen.eval κ) → Bool) = (S.sidSpec κ).rng 2 from rfl)
          (S.encCT κ c), (some t, some (S.encCT κ c))) :=
  S.sidImpl_challenge_fresh b κ pp msk _ t h

/-- The codec of the adversary: the three oracles and a one-bit guess. -/
def sidCodec (κ : ℕ) : MachineCodec (S.sidSpec κ) (Fin 1 → Bool) :=
  bitCodec (S.inLens κ) (S.outLens κ) 1

/-- The adversary codec is a bit codec: `S.sidCodec κ = bitCodec (S.inLens κ) (S.outLens κ) 1`. -/
theorem sidCodec_eq (κ : ℕ) : S.sidCodec κ = bitCodec (S.inLens κ) (S.outLens κ) 1 := rfl

/-- **The experiment `IND-sID-CPA_b(A, κ)`** [BB04, §2.1] with query budget `q`: run `Setup`,
draw `A`'s coins, run `A(1^κ)` against the three oracles from the empty state (no identity
committed, no challenge), and return its one-bit guess. -/
noncomputable def sidGame (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) : ProbComp Bool :=
  (S.setup κ).bind fun k =>
  (ProbComp.sample (A.Coins κ)).bind fun r =>
  (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind
    fun res => .pure (res.1 0)

/-- The IND-sID-CPA experiment runs `Setup`, samples the adversary's coins, simulates the
oracles from the empty state, and returns the guess bit. -/
theorem sidGame_eq (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    S.sidGame A q b κ =
      (S.setup κ).bind fun k =>
      (ProbComp.sample (A.Coins κ)).bind fun r =>
      (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind
        fun res => .pure (res.1 0) := rfl

/-- **IND-sID-CPA security** [BB04, §2.1 and Definition 2.2]: for every non-uniform PPT `A` and
every polynomial query budget `q`, `A`'s advantage between the experiments with `b = 0` and
`b = 1` is negligible.

**Deviation:** asymptotic, with a polynomial budget `q(κ)` on all queries (the paper's `q_ID`
bounds private-key queries); the advantage is twice the paper's (module docstring). -/
def SIDSecure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ κ, advantage (S.sidGame A (q.eval κ) false κ) (S.sidGame A (q.eval κ) true κ) ≤ ε κ

/-- IND-sID-CPA security is negligible advantage, uniformly in `κ`, for every non-uniform PPT
adversary and polynomial query budget. -/
theorem sidSecure_iff :
    S.SIDSecure ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ κ, advantage (S.sidGame A (q.eval κ) false κ) (S.sidGame A (q.eval κ) true κ) ≤ ε κ :=
  Iff.rfl

end IBEScheme

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
