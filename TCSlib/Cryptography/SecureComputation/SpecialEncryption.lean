/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Primitives
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The special encryption scheme of Yao's protocol: the algorithms (statement phase)

[PS10, Algorithm 157.2]: for a length-doubling pseudorandom function family
`{f_s : {0,1}^{|s|} → {0,1}^{2|s|}}`:
- `Gen(1^n)` outputs `k ← U_n`;
- `Enc_k(m)` outputs `(r, 0^n ‖ m ⊕ f_k(r))` for `r ← U_n`;
- `Dec_k(c₁, c₂)` computes `m₀ ‖ m₁ = c₂ ⊕ f_k(c₁)` with `|m₀| = n`, and outputs `m₁` if
  `m₀ = 0^n`, and `⊥` otherwise.

This module has the algorithms, on strings and as machines, with their correctness. The scheme
as a `PrivateKeyScheme` and Claim 157.a are in `SpecialEncryptionSecurity.lean`. The garbling of
Yao's protocol nests two encryptions (`GarblingSpecial.lean`), so the string-level scheme
(`spEncStr`, `spDecStr`) takes any message length `ℓ`, with a pad of `n + ℓ` bits.

**Deviations.**
- `x` for `m`: a source typo, read as `m`.
- `(0^n ‖ m) ⊕ p` is computed as `p_{<n} ‖ (m ⊕ p_{≥n})` for the pad `p = f_k(r)`. The test
  "`m₀ = 0^n`" is computed as `c₂,_{<n} = p_{<n}`. Both are equalities of strings.
- `Dec` checks the key, nonce-component and body-component lengths before evaluating `E`,
  then checks the pad prefix. It uses total pair projections and does not separately require
  successful pair parsing. At `n = ℓ = 0`, the malformed empty ciphertext with an empty key
  therefore returns `some []`. The length checks protect the stated `n`-bit evaluator domain;
  universal malformed-input rejection is not claimed.
- `⊥` of the machine `Dec` is the `(n + 1)`-bit string `1^{n+1}`, which decodes to no message.

## Main definitions

* `SecureComputation.spEncStr`, `spDecStr`: Algorithm 157.2 on strings, for any message length.
* `SecureComputation.spEncFun`, `spDecFun`: the algorithms on the machine layout (`n`-bit
  messages).

## Main results

* `SecureComputation.spDecStr_spEncStr`, `length_spEncStr`: decryption inverts encryption, and the
  ciphertext length.
* `SecureComputation.polyTimeComputable_spEncFun`, `polyTimeComputable_spDecFun`, `runAt_spEnc`,
  `runAt_spDec`: the machines.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Algorithm 157.2 (book pp. 156–157).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-! ### The scheme on strings -/

/-- **`Enc_k(m)` with coins `r`** [PS10, Algorithm 157.2], `n = |r|`: the pad `p = E(⟨k, r⟩)`
and the ciphertext `⟨r, p_{<n} ‖ (m ⊕ p_{≥n})⟩`, that is `⟨r, (0^n ‖ m) ⊕ p⟩`. -/
def spEncStr (E : List Bool → List Bool) (k m r : List Bool) : List Bool :=
  pairEncode r ((E (pairEncode k r)).take r.length ++
    List.zipWith xor m ((E (pairEncode k r)).drop r.length))

/-- Encryption pairs the nonce with a pad prefix and the XOR-masked message. -/
theorem spEncStr_eq (E : List Bool → List Bool) (k m r : List Bool) :
    spEncStr E k m r = pairEncode r ((E (pairEncode k r)).take r.length ++
      List.zipWith xor m ((E (pairEncode k r)).drop r.length)) := rfl

/-- **`Dec_k(c)`** [PS10, Algorithm 157.2] at parameter `n` for `ℓ`-bit messages: `none` (`⊥`)
unless `k` and `r` have `n` bits and `c₂` has `n + ℓ`; then, with the pad `p = E(⟨k, r⟩)`, the
message `c₂,_{≥n} ⊕ p_{≥n}` if `c₂,_{<n} = p_{<n}` ("`m₀ = 0^n`"), and `⊥` otherwise.
Here `r` and `c₂` are the total pair projections; successful parsing is not an additional
test. In particular `n = ℓ = 0`, `k = c = []` returns `some []`. -/
def spDecStr (E : List Bool → List Bool) (n ℓ : ℕ) (k c : List Bool) : Option (List Bool) :=
  if k.length = n ∧ (pairFstD c).length = n ∧ (pairSndD c).length = n + ℓ then
    if (pairSndD c).take n = (E (pairEncode k (pairFstD c))).take n then
      some (List.zipWith xor ((pairSndD c).drop n) ((E (pairEncode k (pairFstD c))).drop n))
    else none
  else none

/-- Decryption checks the key, nonce and ciphertext lengths and the pad prefix, returning
only the unmasked suffix when every check succeeds. -/
theorem spDecStr_eq (E : List Bool → List Bool) (n ℓ : ℕ) (k c : List Bool) :
    spDecStr E n ℓ k c =
      if k.length = n ∧ (pairFstD c).length = n ∧ (pairSndD c).length = n + ℓ then
        if (pairSndD c).take n = (E (pairEncode k (pairFstD c))).take n then
          some (List.zipWith xor ((pairSndD c).drop n)
            ((E (pairEncode k (pairFstD c))).drop n))
        else none
      else none := rfl

/-- XOR-ing twice with the same pad, at least as long as the message, is the identity. -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **Decryption inverts encryption**: for an `n`-bit key and coins, an `ℓ`-bit message, and a
pad of `n + ℓ` bits, `Dec_k(Enc_k(m; r)) = m`. -/
theorem spDecStr_spEncStr (E : List Bool → List Bool) {n ℓ : ℕ} {k m r : List Bool}
    (hk : k.length = n) (hm : m.length = ℓ) (hr : r.length = n)
    (hp : (E (pairEncode k r)).length = n + ℓ) :
    spDecStr E n ℓ k (spEncStr E k m r) = some m := by
  subst hr
  have h1 : ((E (pairEncode k r)).take r.length).length = r.length := by
    rw [List.length_take, hp]; omega
  have h2 : ((E (pairEncode k r)).drop r.length).length = ℓ := by
    rw [List.length_drop, hp]; omega
  have hz : (List.zipWith xor m ((E (pairEncode k r)).drop r.length)).length = ℓ := by
    rw [List.length_zipWith, hm, h2]; omega
  unfold spDecStr spEncStr
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [if_pos ⟨hk, trivial, by rw [List.length_append, h1, hz]⟩, List.take_left' h1, if_pos rfl,
    List.drop_left' h1, zipWith_xor_xor_self _ _ (by rw [hm, h2])]

/-! ### The scheme as a `PrivateKeyScheme` -/

/-- `Enc` on the machine layout `⟨⟨⟨1^n, ⟨k, m⟩⟩, α⟩, r⟩`: `spEncStr` with the coin string as
`r`. -/
def spEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  spEncStr E (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z)) (NUPPT.inCoins z)

/-- The encryption adapter reads the key and message from its argument and its nonce from
its machine coin word. -/
theorem spEncFun_eq (E : List Bool → List Bool) (z : List Bool) :
    spEncFun E z = spEncStr E (pairFstD (NUPPT.inArg z))
      (pairSndD (NUPPT.inArg z)) (NUPPT.inCoins z) := rfl

/-- `Dec` on the layout `⟨⟨⟨1^n, ⟨k, c⟩⟩, α⟩, r'⟩` for `n`-bit messages: the message, or `⊥` as
the `(n + 1)`-bit string `1^{n+1}`. -/
def spDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  (spDecStr E (NUPPT.inParam z).length (NUPPT.inParam z).length (pairFstD (NUPPT.inArg z))
    (pairSndD (NUPPT.inArg z))).getD (true :: NUPPT.inParam z)

/-- The decryption adapter reads both lengths from the unary parameter and returns the
specified overlong failure word if string decryption fails. -/
theorem spDecFun_eq (E : List Bool → List Bool) (z : List Bool) :
    spDecFun E z = (spDecStr E (NUPPT.inParam z).length (NUPPT.inParam z).length
      (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z))).getD
        (true :: NUPPT.inParam z) := rfl

/-- The string-level `Enc` is polynomial-time on the layout when `E` is. -/
theorem polyTimeComputable_spEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (spEncFun E) := by
  have hk := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hm := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hr := NUPPT.polyTimeComputable_inCoins
  have hp := hE.comp (hk.pairEncode hr)
  have ht := (polyTimeComputable_pairTakePoly .var).comp (hr.pairEncode hp)
  have hd := (polyTimeComputable_pairDropPoly .var).comp (hr.pairEncode hp)
  have hx := polyTimeComputable_pairXor.comp (hm.pairEncode hd)
  have h := hr.pairEncode (ht.append hx)
  refine (congrArg PolyTimeComputable (?_ : spEncFun E = _)).mpr h
  funext z
  simp only [spEncFun, spEncStr, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- The guard of `Dec` (`n`-bit key and `r`, `2n`-bit `c₂`) is polynomial-time.

**Proof sketch.** Obtain the key, nonce, ciphertext body and unary parameter by polynomial-time
projections. Compare the key and nonce lengths with the parameter length. Compare the body's
length with twice that length, represented by appending the parameter word to itself. Each
comparison is a polynomial-time length test, and two Boolean conjunctions combine the three
tests into the guard. -/
private theorem polyTimeComputable_spDecGuard :
    PolyTimeComputable fun z =>
      [decide ((pairFstD (NUPPT.inArg z)).length = (NUPPT.inParam z).length ∧
        (pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length ∧
        (pairSndD (pairSndD (NUPPT.inArg z))).length =
          (NUPPT.inParam z).length + (NUPPT.inParam z).length)] := by
  have hP := NUPPT.polyTimeComputable_inParam
  have hl : ∀ g h : List Bool → List Bool, PolyTimeComputable g → PolyTimeComputable h →
      PolyTimeComputable (fun z => [decide ((g z).length = (h z).length)]) := by
    intro g h hg hh
    have h' := polyTimeComputable_lenEq.comp (hg.pairEncode hh)
    refine (congrArg PolyTimeComputable
      (?_ : (fun z => [decide ((g z).length = (h z).length)]) = _)).mpr h'
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hArg := NUPPT.polyTimeComputable_inArg
  have h1 := hl _ _ (polyTimeComputable_pairFstD.comp hArg) hP
  have h2 := hl _ _ ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp hArg) hP
  have h3 := hl _ _ ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp hArg)
    (hP.append hP)
  have h := polyTimeComputable_and h1 (polyTimeComputable_and h2 h3)
  refine (congrArg PolyTimeComputable (?_ : (fun z =>
    [decide ((pairFstD (NUPPT.inArg z)).length = (NUPPT.inParam z).length ∧
      (pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length ∧
      (pairSndD (pairSndD (NUPPT.inArg z))).length =
        (NUPPT.inParam z).length + (NUPPT.inParam z).length)]) = _)).mpr h
  funext z
  simp only [Function.comp_apply, List.length_append, Bool.decide_and]

/-- The string-level `Dec` is polynomial-time on the layout when `E` is: the guard, the
comparison of the first `n` bits (`polyTimeComputable_pairEq`), and the masked tail.

**Proof sketch.** Compute the pad by applying the polynomial-time evaluator to the key and
nonce. Polynomial-time prefix and suffix operations split both the pad and ciphertext body
after `n` bits. Compare their prefixes, and XOR their suffixes to recover the candidate message.
Use the shape guard and prefix comparison to select this message when both tests pass;
otherwise return a `true` bit followed by the unary parameter, the designated failure word.
Composition and conditional selection preserve polynomial time. -/
theorem polyTimeComputable_spDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (spDecFun E) := by
  have hP := NUPPT.polyTimeComputable_inParam
  have hArg := NUPPT.polyTimeComputable_inArg
  have hk := polyTimeComputable_pairFstD.comp hArg
  have hr := (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp hArg
  have hc := (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp hArg
  have hp := hE.comp (hk.pairEncode hr)
  have hct := (polyTimeComputable_pairTakePoly .var).comp (hP.pairEncode hc)
  have hpt := (polyTimeComputable_pairTakePoly .var).comp (hP.pairEncode hp)
  have hcd := (polyTimeComputable_pairDropPoly .var).comp (hP.pairEncode hc)
  have hpd := (polyTimeComputable_pairDropPoly .var).comp (hP.pairEncode hp)
  have heq := polyTimeComputable_pairEq.comp (hct.pairEncode hpt)
  have hx := polyTimeComputable_pairXor.comp (hcd.pairEncode hpd)
  have hbot := (polyTimeComputable_const [true]).append hP
  have h := polyTimeComputable_ite polyTimeComputable_spDecGuard
    (polyTimeComputable_ite heq hx hbot) hbot
  refine (congrArg PolyTimeComputable (?_ : spDecFun E = _)).mpr h
  funext z
  simp only [spDecFun, spDecStr, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var, decide_eq_true_eq]
  split_ifs <;> rfl

/-- The activation of the encryption machine on `⟨k, m⟩` with coins `r` is `spEncStr`. -/
theorem runAt_spEnc {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k m : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_spEncFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_spEncFun hE) coins).runAt n (pairEncode k m) r =
      spEncStr E k m (List.ofFn r) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [spEncFun, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- The activation of the decryption machine on `⟨k, c⟩` is `spDecStr` at `ℓ = n`, with `⊥` as
`1^{n+1}`. -/
theorem runAt_spDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k c : List Bool)
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_spDecFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_spDecFun hE) coins).runAt n (pairEncode k c) r' =
      (spDecStr E n n k c).getD (true :: List.replicate n true) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [spDecFun, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]

/-- The length of a special ciphertext: `2|r| + 2` for `r`, then `|r| + |m|` when the pad has at
least `|r| + |m|` bits. -/
theorem length_spEncStr (E : List Bool → List Bool) {k m r : List Bool}
    (hp : r.length + m.length ≤ (E (pairEncode k r)).length) :
    (spEncStr E k m r).length = 2 * r.length + 2 + (r.length + m.length) := by
  unfold spEncStr
  rw [length_pairEncode, List.length_append, List.length_take, List.length_zipWith,
    List.length_drop]
  omega

end TCSlib.Cryptography.SecureComputation
