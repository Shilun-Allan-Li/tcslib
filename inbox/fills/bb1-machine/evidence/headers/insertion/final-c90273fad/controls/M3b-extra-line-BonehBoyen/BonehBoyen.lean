/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Boneh–Boyen selective-identity IBE (BB1)

[BB04, §4.1] with depth `ℓ = 1` (an IBE system is an HIBE whose identities have depth 1,
[BB04, §2.1]). In a bilinear group `G` of prime order `p` with pairing `e`:
* **Setup**: a random generator `g ∈ G^*`, `α ∈ Z_p`, `g_1 = g^α`, random `h, g_2 ∈ G`;
  `params = (g, g_1, g_2, h)`, `master-key = g_2^α`; `F(x) = g_1^x h`.
* **KeyGen**(`ID ∈ Z_p`): a random `r ∈ Z_p`, `d_ID = (g_2^α · F(ID)^r, g^r)`.
* **Encrypt**(`params`, `ID`, `M ∈ G_1`): a random `s ∈ Z_p`,
  `C = (e(g_1, g_2)^s · M, g^s, F(ID)^s)`.
* **Decrypt**(`d_ID = (d_0, d_1)`, `C = (A, B, C_1)`): `A · e(C_1, d_1) / e(B, d_0)`.

It is IND-sID-CPA secure under Decision BDH [BB04, Theorem 4.1], without random oracles; the
security statement and its simulation are in `AdvancedEncryption.IdentityBased.BonehBoyenSecurity`.

**Identities and messages.** The generic interface (`IBEScheme`) has `ℓ(κ)`-bit identities.
BB1 reads an identity as the residue of its binary value in `Z_p` (`idToZ`), the injective
"hash" `{0,1}^ℓ → {0, …, 2^ℓ − 1}` of [BB04, §4.4] ("a collision resistant hash function
`H : {0,1}^* → {1, …, 2^b}` where `2^b < p` is sufficient"); distinct identities stay distinct in
`Z_p` when `2^ℓ ≤ p`, which the security theorem assumes except with negligible probability.
Messages are elements of `G_T` (the paper's `G_1`), sent as their `wT(κ)`-bit encodings; the
message space is the set of encodings, and `Encrypt` reads a string through `decodeT` (strings
outside the message space read as `1`, a choice that is never exercised by the game, which
refuses them).

**Groups from the generator.** Parameters, keys and ciphertexts carry the description `d` of the
group they live in (a dependent pair), since the group is drawn by `Setup` from the generator
(`Pairing.BilinearGen`). Decryption of a ciphertext whose description differs from the key's is
`⊥`.

**Deviation:** abstract bilinear groups drawn by a generator; depth-1 identities given as
`ℓ(κ)`-bit strings and embedded into `Z_p` by their binary value; messages as encodings of `G_T`;
parameters, keys and ciphertexts tagged with the group's description.

## Main definitions

* `BB1.Params`, `BB1.Key`, `BB1.Ciphertext` — `params`, `d_ID` and `C`.
* `BB1.F`, `BB1.setup`, `BB1.keyGen`, `BB1.encrypt`, `BB1.decrypt` — the
  algorithms of [BB04, §4.1] over one bilinear group.
* `BB1.idToZ`, `BB1.decodeT` — identities in `Z_p` and messages in `G_T`.
* `bb1Scheme` — BB1 as an `IBEScheme` over a generator.
* `BB1SimState`, `bb1SimParams`, `bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`,
  `bb1SimCt`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame` — the simulator of
  [BB04, proof of Theorem 4.1] and its game, with ideal exponents.

## Main results

* `BB1.decrypt_encrypt` — decryption inverts encryption [BB04, §4.1, "for a valid
  ciphertext"].
* `bb1_correct` — BB1 is perfectly correct.
* `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj` — BB1's encodings are injective on
  parameters of the advertised description length and on keys and ciphertexts in one group.
* `bb1SimInit_none`, …, `bb1SimChal_invalid` — the simulator's handlers case by case.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.1 (pp. 2–4), §4.1 (pp. 5–6:
  the construction), §4.2 (pp. 6–8: the simulator in the proof of Theorem 4.1), §4.4 (p. 8:
  arbitrary identities).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **System parameters** `params = (g, g_1, g_2, h)` of BB1 [BB04, §4.1, `Setup` at depth 1]. -/
structure Params where
  /-- The generator `g ∈ G^*`. -/
  g : B.G
  /-- `g_1 = g^α`. -/
  g1 : B.G
  /-- The random element `g_2`. -/
  g2 : B.G
  /-- The random element `h = h_1`. -/
  h : B.G

/-- **A private key** `d_ID = (d_0, d_1)` of BB1 [BB04, §4.1, `KeyGen` at depth 1]. -/
structure Key where
  /-- `d_0 = g_2^α · F(ID)^r`. -/
  d0 : B.G
  /-- `d_1 = g^r`. -/
  d1 : B.G

/-- **A ciphertext** `C = (A, B, C_1)` of BB1 [BB04, §4.1, `Encrypt` at depth 1]. -/
structure Ciphertext where
  /-- `A = e(g_1, g_2)^s · M`. -/
  a : B.GT
  /-- `B = g^s`. -/
  b : B.G
  /-- `C_1 = F(ID)^s`. -/
  c : B.G

variable {B}

/-- **The function** `F(x) = g_1^x h` [BB04, §4.1, `F_1 : Z_p → G`]. -/
def F (pp : Params B) (x : ZMod B.order) : B.G := pp.g1 ^ x.val * pp.h

/-- `F pp x = pp.g1 ^ x.val * pp.h`. -/
theorem F_eq (pp : Params B) (x : ZMod B.order) : F pp x = pp.g1 ^ x.val * pp.h := rfl

variable (B)

/-- **Setup** [BB04, §4.1, depth 1]: a uniform generator `g ∈ G^*`, a uniform `α ∈ Z_p`, uniform
`h, g_2 ∈ G`; returns `params = (g, g^α, g_2, h)` and `master-key = g_2^α`. -/
noncomputable def setup : ProbComp (Params B × B.G) :=
  (ProbComp.sample {x : B.G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod B.order)).bind fun α =>
  (ProbComp.sample B.G).bind fun h =>
  (ProbComp.sample B.G).bind fun g2 =>
    .pure (⟨g.1, g.1 ^ α.val, g2, h⟩, g2 ^ α.val)

/-- `setup B` draws `g ∈ G^*`, `α ∈ Z_p`, `h, g_2 ∈ G` and returns
`((g, g^α, g_2, h), g_2^α)`. -/
theorem setup_eq :
    setup B =
      (ProbComp.sample {x : B.G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod B.order)).bind fun α =>
      (ProbComp.sample B.G).bind fun h =>
      (ProbComp.sample B.G).bind fun g2 =>
        .pure (⟨g.1, g.1 ^ α.val, g2, h⟩, g2 ^ α.val) := rfl

variable {B}

/-- **KeyGen** [BB04, §4.1, depth 1]: from the parameters, the master key `mk = g_2^α` and an
identity `ID ∈ Z_p`, a uniform `r ∈ Z_p` and `d_ID = (mk · F(ID)^r, g^r)`. -/
noncomputable def keyGen (pp : Params B) (mk : B.G) (id : ZMod B.order) : ProbComp (Key B) :=
  (ProbComp.sample (ZMod B.order)).bind fun r => .pure ⟨mk * F pp id ^ r.val, pp.g ^ r.val⟩

/-- `keyGen pp mk id` draws `r ∈ Z_p` and returns `(mk · F(id)^r, g^r)`. -/
theorem keyGen_eq (pp : Params B) (mk : B.G) (id : ZMod B.order) :
    keyGen pp mk id =
      (ProbComp.sample (ZMod B.order)).bind fun r => .pure ⟨mk * F pp id ^ r.val, pp.g ^ r.val⟩ :=
  rfl

/-- **Encrypt** [BB04, §4.1, depth 1]: for an identity `ID ∈ Z_p` and a message `M ∈ G_T`, a
uniform `s ∈ Z_p` and `C = (e(g_1, g_2)^s · M, g^s, F(ID)^s)`. -/
noncomputable def encrypt (pp : Params B) (id : ZMod B.order) (M : B.GT) :
    ProbComp (Ciphertext B) :=
  (ProbComp.sample (ZMod B.order)).bind fun s =>
    .pure ⟨B.pair pp.g1 pp.g2 ^ s.val * M, pp.g ^ s.val, F pp id ^ s.val⟩

/-- `encrypt pp id M` draws `s ∈ Z_p` and returns `(e(g_1, g_2)^s · M, g^s, F(id)^s)`. -/
theorem encrypt_eq (pp : Params B) (id : ZMod B.order) (M : B.GT) :
    encrypt pp id M =
      (ProbComp.sample (ZMod B.order)).bind fun s =>
        .pure ⟨B.pair pp.g1 pp.g2 ^ s.val * M, pp.g ^ s.val, F pp id ^ s.val⟩ := rfl

/-- **Decrypt** [BB04, §4.1, depth 1]: `A · e(C_1, d_1) / e(B, d_0)` for `d_ID = (d_0, d_1)` and
`C = (A, B, C_1)`. -/
def decrypt (d : Key B) (C : Ciphertext B) : B.GT := C.a * B.pair C.c d.d1 / B.pair C.b d.d0

/-- `decrypt d C = C.a * e(C.c, d.d1) / e(C.b, d.d0)`. -/
theorem decrypt_eq (d : Key B) (C : Ciphertext B) :
    decrypt d C = C.a * B.pair C.c d.d1 / B.pair C.b d.d0 := rfl

/-- **Decryption inverts encryption** [BB04, §4.1, "for a valid ciphertext, we have
`e(C_1, d_1) / e(B, d_0) = 1 / e(g_1, g_2)^s`"]: for the parameters `(g, g^α, g_2, h)`, the
master key `g_2^α`, the private key with exponent `r` and the ciphertext with exponent `s` of
`M` for the same identity, `Decrypt(d_ID, C) = M`.

**Proof sketch.** The proof is the paper's computation:
`e(F(ID)^s, g^r) = e(g, F(ID))^{sr}` (bilinearity and symmetry) and
`e(g^s, g_2^α F(ID)^r) = e(g, g_2)^{αs} · e(g, F(ID))^{sr}`, while the mask of `A`
is `e(g^α, g_2)^s = e(g, g_2)^{αs}`. -/
theorem decrypt_encrypt (g g2 h : B.G) (α r s id : ZMod B.order) (M : B.GT) :
    decrypt (⟨g2 ^ α.val * F ⟨g, g ^ α.val, g2, h⟩ id ^ r.val, g ^ r.val⟩ : Key B)
      ⟨B.pair (g ^ α.val) g2 ^ s.val * M, g ^ s.val, F ⟨g, g ^ α.val, g2, h⟩ id ^ s.val⟩ = M := by
  rw [decrypt_eq]
  dsimp only
  have h1 : B.pair (g ^ α.val) g2 ^ s.val = B.pair g g2 ^ (α.val * s.val) := by
    rw [B.pair_pow_left, ← pow_mul]
  have h2 : B.pair (F ⟨g, g ^ α.val, g2, h⟩ id ^ s.val) (g ^ r.val) =
      B.pair g (F ⟨g, g ^ α.val, g2, h⟩ id) ^ (s.val * r.val) := by
    rw [B.bilinear_pow, B.pair_comm (F ⟨g, g ^ α.val, g2, h⟩ id) g]
  have h3 : B.pair (g ^ s.val) (g2 ^ α.val * F ⟨g, g ^ α.val, g2, h⟩ id ^ r.val) =
      B.pair g g2 ^ (α.val * s.val) * B.pair g (F ⟨g, g ^ α.val, g2, h⟩ id) ^ (s.val * r.val) := by
    rw [map_mul (B.pair (g ^ s.val)), B.bilinear_pow, B.bilinear_pow, mul_comm s.val α.val]
  rw [h1, h2, h3, mul_right_comm]
  exact mul_div_cancel_left _ _

variable (B)

/-- **An identity as an element of `Z_p`**: the residue of the binary value of an `ℓ`-bit string,
the injective encoding `{0,1}^ℓ → {0, …, 2^ℓ − 1}` of [BB04, §4.4] read in `Z_p`. -/
def idToZ {ℓ : ℕ} (id : Fin ℓ → Bool) : ZMod B.order := (bitsToNat id : ZMod B.order)

/-- `idToZ id` is the cast of `bitsToNat id` into `Z_p`. -/
theorem idToZ_eq {ℓ : ℕ} (id : Fin ℓ → Bool) :
    idToZ B id = (bitsToNat id : ZMod B.order) := rfl

/-- **A message from its encoding**: the element of `G_T` with encoding `w`, and `1` when `w`
encodes none. -/
noncomputable def decodeT (w : Fin wT → Bool) : B.GT := (Function.partialInv B.encT w).getD 1

/-- `decodeT B w = (Function.partialInv B.encT w).getD 1`. -/
theorem decodeT_eq (w : Fin wT → Bool) : decodeT B w = (Function.partialInv B.encT w).getD 1 :=
  rfl

/-- Decoding an encoding returns the element: `decodeT B (B.encT u) = u`. -/
theorem decodeT_encT (u : B.GT) : decodeT B (B.encT u) = u := by
  rw [decodeT_eq, Function.partialInv_left B.encT_injective, Option.getD_some]

end BB1

/-! ### The encodings of BB1 lose no information

The wire formats of `bb1Scheme` below, before the scheme is assembled: each is injective on the
objects it is used for, which gives the fields `encPP_inj`, `encSK_inj` and `encCT_inj`. -/

section Encodings

variable (G : BilinearGen)

/-- **Parameters with a description of the advertised length are determined by their
encoding** (the encoding of `bb1Scheme`'s parameters): for `pp, pp'` whose descriptions have
`descLen(κ)` bits, equal padded words `d ‖ g ‖ g_1 ‖ g_2 ‖ h` give `pp = pp'`.

**Proof sketch.** Both words have exactly `descLen(κ) + 4 · wG(κ)` bits, so they are equal before
padding (`ofFn_padFin_of_length`). Splitting off the last four blocks of `wG(κ)` bits
(`List.append_inj'`) leaves equal descriptions; in the one group they describe, the four element
encodings are equal, so the elements are (`List.ofFn_inj`, `encG_injective`). -/
theorem bb1_encPP_inj {κ : ℕ} {pp pp' : Σ d : List Bool, BB1.Params (G.group κ d)}
    (h : padFin ((PolyExpr.add G.descLen (.mul (.const 4) G.wG)).eval κ)
        (pp.1 ++ List.ofFn ((G.group κ pp.1).encG pp.2.g) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.g1) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.g2) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.h)) =
      padFin ((PolyExpr.add G.descLen (.mul (.const 4) G.wG)).eval κ)
        (pp'.1 ++ List.ofFn ((G.group κ pp'.1).encG pp'.2.g) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.g1) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.g2) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.h)))
    (hl : pp.1.length = G.descLen.eval κ) (hl' : pp'.1.length = G.descLen.eval κ) :
    pp = pp' := by
  obtain ⟨d, ⟨g, g1, g2, x⟩⟩ := pp
  obtain ⟨d', ⟨g', g1', g2', x'⟩⟩ := pp'
  dsimp only at hl hl' h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn, hl,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn, hl',
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨hw, hx⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨hw, hg2⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨hw, hg1⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨rfl, hg⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (BilinearGroup.encG_injective _).eq_iff] at hx hg2 hg1 hg
  rw [hx, hg2, hg1, hg]

/-- **Two keys in one group with equal encodings are equal** (the encoding of `bb1Scheme`'s
private keys, which omits the description).

**Proof sketch.** Both words `d_0 ‖ d_1` have exactly `2 · wG(κ)` bits, so they are equal
before padding (`ofFn_padFin_of_length`); splitting at `wG(κ)` (`List.append_inj'`) gives equal
encodings of `d_0` and of `d_1`, hence equal elements (`List.ofFn_inj`, `encG_injective`). -/
theorem bb1_encSK_inj {κ : ℕ} {d : List Bool} {k k' : BB1.Key (G.group κ d)}
    (h : padFin ((PolyExpr.mul (.const 2) G.wG).eval κ)
        (List.ofFn ((G.group κ d).encG k.d0) ++ List.ofFn ((G.group κ d).encG k.d1)) =
      padFin ((PolyExpr.mul (.const 2) G.wG).eval κ)
        (List.ofFn ((G.group κ d).encG k'.d0) ++ List.ofFn ((G.group κ d).encG k'.d1))) :
    k = k' := by
  obtain ⟨a, b⟩ := k
  obtain ⟨a', b'⟩ := k'
  dsimp only at h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨ha, hb⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (G.group κ d).encG_injective.eq_iff] at ha hb
  rw [ha, hb]

/-- **Two ciphertexts in one group with equal encodings are equal** (the encoding of
`bb1Scheme`'s ciphertexts, which omits the description).

**Proof sketch.** Both words `A ‖ B ‖ C_1` have exactly `wT(κ) + 2 · wG(κ)` bits, so they are
equal before padding (`ofFn_padFin_of_length`); splitting off the last two blocks of `wG(κ)` bits
(`List.append_inj'`) gives equal encodings of the three components, hence equal components
(`List.ofFn_inj`, `encT_injective`, `encG_injective`). -/
theorem bb1_encCT_inj {κ : ℕ} {d : List Bool} {c c' : BB1.Ciphertext (G.group κ d)}
    (h : padFin ((PolyExpr.add G.wT (.mul (.const 2) G.wG)).eval κ)
        (List.ofFn ((G.group κ d).encT c.a) ++ List.ofFn ((G.group κ d).encG c.b) ++
          List.ofFn ((G.group κ d).encG c.c)) =
      padFin ((PolyExpr.add G.wT (.mul (.const 2) G.wG)).eval κ)
        (List.ofFn ((G.group κ d).encT c'.a) ++ List.ofFn ((G.group κ d).encG c'.b) ++
          List.ofFn ((G.group κ d).encG c'.c))) :
    c = c' := by
  obtain ⟨a, b, x⟩ := c
  obtain ⟨a', b', x'⟩ := c'
  dsimp only at h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨hw, hx⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨ha, hb⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (G.group κ d).encG_injective.eq_iff] at hx hb
  rw [List.ofFn_inj, (G.group κ d).encT_injective.eq_iff] at ha
  rw [ha, hb, hx]

end Encodings

/-- **The BB1 IBE system** over the bilinear group generator `G`, for `ℓ(κ)`-bit identities
[BB04, §4.1 at depth 1, with the identity encoding of §4.4]: `Setup` runs the generator and BB1's
`Setup` in the group it describes; the parameters are `⟨d, (g, g_1, g_2, h)⟩`, the master key
also carries the parameters; `KeyGen` and `Encrypt` read the identity through `idToZ` and the
message through `decodeT`; `Decrypt` returns the encoding of BB1's decryption, or `⊥` if the key
and the ciphertext name different descriptions. The message space at `⟨d, params⟩` is the set
of encodings of `G_T` of the group `d` describes. Parameters are encoded as `d` followed by the
four elements, keys as two elements, ciphertexts as `A, B, C_1`.

The encodings are injective where the interface asks: generated descriptions have `descLen(κ)`
bits (`BilinearGen.length_desc`, `bb1_encPP_inj`), and the keys and ciphertexts of one possible
output of `Setup` carry its description, in whose group the element encodings are injective
(`bb1_encSK_inj`, `bb1_encCT_inj`). -/
noncomputable def bb1Scheme (G : BilinearGen) (ℓ : PolyExpr) : IBEScheme where
  idLen := ℓ
  msgLen := G.wT
  ppLen := .add G.descLen (.mul (.const 4) G.wG)
  skLen := .mul (.const 2) G.wG
  ctLen := .add G.wT (.mul (.const 2) G.wG)
  PP κ := Σ d : List Bool, BB1.Params (G.group κ d)
  MSK κ := Σ d : List Bool, BB1.Params (G.group κ d) × (G.group κ d).G
  SK κ := Σ d : List Bool, BB1.Key (G.group κ d)
  CT κ := Σ d : List Bool, BB1.Ciphertext (G.group κ d)
  setup κ :=
    (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
    (BB1.setup (G.group κ (G.desc κ r))).bind fun k =>
      .pure (⟨G.desc κ r, k.1⟩, ⟨G.desc κ r, k⟩)
  keyGen _ msk id :=
    (BB1.keyGen msk.2.1 msk.2.2 (BB1.idToZ _ id)).bind fun d => .pure ⟨msk.1, d⟩
  enc _ pp id m :=
    (BB1.encrypt pp.2 (BB1.idToZ _ id) (BB1.decodeT _ m)).bind fun c => .pure ⟨pp.1, c⟩
  dec κ sk c :=
    if h : c.1 = sk.1 then
      some ((G.group κ sk.1).encT (BB1.decrypt sk.2 (h ▸ c.2)))
    else none
  MsgSpace κ pp m := ∃ u, (G.group κ pp.1).encT u = m
  encPP κ pp := padFin _ (pp.1 ++ List.ofFn ((G.group κ pp.1).encG pp.2.g) ++
    List.ofFn ((G.group κ pp.1).encG pp.2.g1) ++ List.ofFn ((G.group κ pp.1).encG pp.2.g2) ++
    List.ofFn ((G.group κ pp.1).encG pp.2.h))
  encSK κ sk := padFin _ (List.ofFn ((G.group κ sk.1).encG sk.2.d0) ++
    List.ofFn ((G.group κ sk.1).encG sk.2.d1))
  encCT κ c := padFin _ (List.ofFn ((G.group κ c.1).encT c.2.a) ++
    List.ofFn ((G.group κ c.1).encG c.2.b) ++ List.ofFn ((G.group κ c.1).encG c.2.c))
  encPP_inj κ := by
    refine (OracleComp.allOutputs_true _).bind fun r _ =>
      (OracleComp.allOutputs_true _).bind fun k _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun r' _ =>
      (OracleComp.allOutputs_true _).bind fun k' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => bb1_encPP_inj G h (G.length_desc κ r) (G.length_desc κ r')
  encSK_inj κ := by
    refine (OracleComp.allOutputs_true _).mono fun k _ id id' => ?_
    refine (OracleComp.allOutputs_true _).bind fun a _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun a' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => congrArg (Sigma.mk k.2.1) (bb1_encSK_inj G h)
  encCT_inj κ := by
    refine (OracleComp.allOutputs_true _).mono fun k _ id id' m m' => ?_
    refine (OracleComp.allOutputs_true _).bind fun a _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun a' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => congrArg (Sigma.mk k.1.1) (bb1_encCT_inj G h)

attribute [simps (config := { isSimp := false }) idLen msgLen ppLen skLen ctLen PP MSK SK CT
  setup keyGen enc dec MsgSpace encPP encSK encCT] bb1Scheme

/-- **The parameter encoding as a word**: `⟦encPP ⟨d, pp⟩⟧` is the padded word
`d ‖ g ‖ g_1 ‖ g_2 ‖ h` (`ppLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encPP (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encPP κ ⟨d, pp⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ppLen.eval κ) (d ++ List.ofFn ((G.group κ d).encG pp.g) ++
        List.ofFn ((G.group κ d).encG pp.g1) ++ List.ofFn ((G.group κ d).encG pp.g2) ++
        List.ofFn ((G.group κ d).encG pp.h))) := rfl

/-- **The key encoding as a word**: `⟦encSK ⟨d, k⟩⟧` is the padded word `d_0 ‖ d_1`
(`skLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encSK (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (k : BB1.Key (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encSK κ ⟨d, k⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).skLen.eval κ) (List.ofFn ((G.group κ d).encG k.d0) ++
        List.ofFn ((G.group κ d).encG k.d1))) := rfl

/-- **The message space as words**: a `msgLen(κ)`-bit message is in the message space of
`⟨d, pp⟩` iff its word is the word of the encoding of an element of `G_T`. -/
theorem bb1Scheme_msgSpace_iff (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    (bb1Scheme G ℓ).MsgSpace κ ⟨d, pp⟩ m ↔
      ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn m :=
  exists_congr fun _ => List.ofFn_inj.symm

/-- **BB1 is perfectly correct** [BB04, §4.1, "Indeed, for a valid ciphertext …"]: every
honest run with a message of the message space decrypts to that message.

**Proof sketch.** Every possible outcome of an honest run has parameters
`⟨d, (g, g^α, g_2, h)⟩`, key `⟨d, (g_2^α F(ID)^r, g^r)⟩` and ciphertext
`⟨d, (e(g^α, g_2)^s · M', g^s, F(ID)^s)⟩` with the same description `d` and
`M' = decodeT M`, so `Decrypt` takes its first branch and returns the encoding of `M'` by
`BB1.decrypt_encrypt`. A message of the message space is an encoding `encT u`, so
`M' = u` (`decodeT_encT`) and its encoding is `M`. -/
theorem bb1_correct (G : BilinearGen) (ℓ : PolyExpr) : (bb1Scheme G ℓ).Correct := by
  rw [IBEScheme.correct_iff]
  intro κ id m
  rw [IBEScheme.honestRun_eq, bb1Scheme_setup]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, BB1.setup_eq, bb1Scheme_keyGen,
    bb1Scheme_enc, BB1.keyGen_eq, BB1.encrypt_eq]
  refine (OracleComp.allOutputs_true _).bind fun r _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun g _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun α _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun h _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun g2 _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun ρ _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun σ _ => ?_
  refine OracleComp.allOutputs_pure.2 fun hm => ?_
  obtain ⟨u, hu⟩ := hm
  rw [bb1Scheme_dec, dif_pos rfl]
  dsimp only
  rw [← hu, BB1.decodeT_encT, BB1.decrypt_encrypt]

/-! ### The simulator of [BB04, proof of Theorem 4.1]

The Decision BDH algorithm `B` of the proof, as typed oracle handlers over the parameters of
`bb1Scheme`, with ideal uniform exponents; `bb1SimGame` runs the adversary against them. The
security argument is in `AdvancedEncryption.IdentityBased.BonehBoyenSecurity`. -/

section Simulator


variable (G : BilinearGen) (ℓ : PolyExpr)

/-- The simulator's state at parameter `κ` in the group described by `d`: the committed identity
with the simulator's exponent `α_1` (once `Init` is asked), and the issued challenge. -/
abbrev BB1SimState (κ : ℕ) (d : List Bool) : Type :=
  Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) ×
    Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)

/-- `BB1SimState G ℓ κ d` is the optional pair of the committed identity and `α_1`, with the
optional encoded challenge. -/
theorem bb1SimState_eq (κ : ℕ) (d : List Bool) :
    BB1SimState G ℓ κ d =
      (Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) ×
        Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) := rfl

/-- The simulated parameters `(g, X, Y, X^{−ID*} g^{α_1})` for the committed identity `ID*` and
the exponent `α_1` [BB04, proof of Theorem 4.1, *Setup*]. -/
noncomputable def bb1SimParams {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order) :
    BB1.Params (G.group κ d) :=
  ⟨g, X, Y, X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val⟩

/-- `bb1SimParams G ℓ g X Y t α₁ = (g, X, Y, X ^ (−idToZ t).val · g ^ α₁.val)`. -/
theorem bb1SimParams_eq {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order) :
    bb1SimParams G ℓ g X Y t α₁ =
      ⟨g, X, Y, X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val⟩ := rfl

/-- The simulated private key of `ID ≠ ID*` with exponent `r` [BB04, proof of Theorem 4.1,
*Phase 1*]: `(Y^{−α_1/(ID − ID*)} F(ID)^r, Y^{−1/(ID − ID*)} g^r)`, with `F` of the simulated
parameters and the identities read in `Z_p`. -/
noncomputable def bb1SimKey {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (r : ZMod (G.group κ d).order) :
    BB1.Key (G.group κ d) :=
  ⟨Y ^ (-α₁ / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val *
      BB1.F (bb1SimParams G ℓ g X Y t α₁) (BB1.idToZ (G.group κ d) id) ^ r.val,
    Y ^ (-1 / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val * g ^ r.val⟩

/-- `bb1SimKey G ℓ g X Y t α₁ id r` is
`(Y^{(−α₁/(id − t)).val} · F(id)^{r.val}, Y^{(−1/(id − t)).val} · g^{r.val})`. -/
theorem bb1SimKey_eq {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (r : ZMod (G.group κ d).order) :
    bb1SimKey G ℓ g X Y t α₁ id r =
      ⟨Y ^ (-α₁ / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val *
          BB1.F (bb1SimParams G ℓ g X Y t α₁) (BB1.idToZ (G.group κ d) id) ^ r.val,
        Y ^ (-1 / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val * g ^ r.val⟩ :=
  rfl

/-- **The simulator's `Init`** [BB04, proof of Theorem 4.1, *Initialization* and *Setup*] on the
description `d` and `g, X = g^a, Y = g^{b'}`: before any commitment, draw `α_1 ∈ Z_p`, record
`(ID, α_1)` and answer the simulated parameters; afterwards answer the recorded identity's. -/
noncomputable def bb1SimInit (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ppLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1 with
  | none => (ProbComp.sample (ZMod (G.group κ d).order)).bind fun α₁ =>
      .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y id α₁⟩, (some (id, α₁), s.2))
  | some (t, α₁) => .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩, s)

/-- `Init` before any commitment draws `α_1` and answers the simulated parameters. -/
theorem bb1SimInit_none (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimInit G ℓ κ d g X Y id (none, c) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun α₁ =>
        .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y id α₁⟩, (some (id, α₁), c)) :=
  rfl

/-- `Init` after a commitment answers the recorded identity's simulated parameters. -/
theorem bb1SimInit_some (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimInit G ℓ κ d g X Y id (some (t, α₁), c) =
      .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩, (some (t, α₁), c)) :=
  rfl

/-- **The simulator's `KeyGen`** [BB04, proof of Theorem 4.1, *Phase 1*]: when `ID*` is recorded
and `ID ≠ ID*`, draw `r ∈ Z_p` and answer `⟨1, bb1SimKey … ID r⟩`; otherwise `⊥`. -/
noncomputable def bb1SimKeyQ (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).skLen.eval κ + 1) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1 with
  | some (t, α₁) =>
    if id = t then .pure (zeroBits _, s)
    else (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
      .pure (FixedLengthScheme.decAnswer
        (some ((bb1Scheme G ℓ).encSK κ ⟨d, bb1SimKey G ℓ g X Y t α₁ id r⟩)), s)
  | none => .pure (zeroBits _, s)

/-- `KeyGen` before `Init` answers `⊥`. -/
theorem bb1SimKeyQ_none (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimKeyQ G ℓ κ d g X Y id (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `KeyGen` for the committed identity answers `⊥`. -/
theorem bb1SimKeyQ_target (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimKeyQ G ℓ κ d g X Y t (some (t, α₁), c) = .pure (zeroBits _, (some (t, α₁), c)) := by
  simp [bb1SimKeyQ]

/-- `KeyGen` for `ID ≠ ID*` draws `r` and answers the simulated key. -/
theorem bb1SimKeyQ_ne (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (h : id ≠ t) :
    bb1SimKeyQ G ℓ κ d g X Y id (some (t, α₁), c) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
        .pure (FixedLengthScheme.decAnswer
          (some ((bb1Scheme G ℓ).encSK κ ⟨d, bb1SimKey G ℓ g X Y t α₁ id r⟩)),
          (some (t, α₁), c)) := by
  simp [bb1SimKeyQ, h]

/-- The simulated challenge `(M · T, Z, Z^{α_1})` [BB04, proof of Theorem 4.1, *Challenge*] of the
message string `m`, encoded. -/
noncomputable def bb1SimCt (κ : ℕ) (d : List Bool) (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (α₁ : ZMod (G.group κ d).order) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool :=
  (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩

/-- `bb1SimCt G ℓ κ d Z T α₁ m` is the encoding of `(decodeT m · T, Z, Z ^ α₁.val)`. -/
theorem bb1SimCt_eq (κ : ℕ) (d : List Bool) (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (α₁ : ZMod (G.group κ d).order) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    bb1SimCt G ℓ κ d Z T α₁ m =
      (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩ := rfl

/-- **The simulated challenge as a word**: `⟦bb1SimCt … m⟧` is the padded word
`decodeT(m) · T ‖ Z ‖ Z^{α_1.val}` (`ctLen(κ)` bits), the message read at the width of `G_T`. -/
theorem ofFn_bb1SimCt (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (Z : (G.group κ d).G) (T : (G.group κ d).GT) (α₁ : ZMod (G.group κ d).order)
    (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    List.ofFn (bb1SimCt G ℓ κ d Z T α₁ m) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ctLen.eval κ)
        (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)) * T)) ++
          List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val)))) := by
  rw [padFin_ofFn]
  rfl

open Classical in
/-- **The simulator's `Challenge`** [BB04, proof of Theorem 4.1, *Challenge*] with challenge bit
`b`, on `Z = g^c` and `T`: with `ID*` recorded and no challenge yet, if `M₀, M₁` are in the
message space, answer and record `(M_b · T, Z, Z^{α_1})`, and otherwise `⊥`; once a challenge is
recorded, repeat it; before `Init`, `⊥`. -/
noncomputable def bb1SimChal (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1, s.2 with
  | some _, some c => .pure (c, s)
  | some (t, α₁), none =>
    if (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2 then
      .pure (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1),
        (s.1, some (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1))))
    else .pure (zeroBits _, s)
  | none, _ => .pure (zeroBits _, s)

/-- `Challenge` before `Init` answers `⊥`. -/
theorem bb1SimChal_none (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `Challenge` after a recorded challenge repeats it. -/
theorem bb1SimChal_repeat (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : (Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order)
    (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some t, some w) = .pure (w, (some t, some w)) := rfl

/-- The first `Challenge` with both messages in the message space answers and records
`(M_b · T, Z, Z^{α_1})`. -/
theorem bb1SimChal_fresh (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (h : (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some (t, α₁), none) =
      .pure (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1),
        (some (t, α₁), some (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1)))) := by
  simp only [bb1SimChal]
  rw [if_pos h]

/-- The first `Challenge` with a message outside the message space answers `⊥`. -/
theorem bb1SimChal_invalid (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (h : ¬ ((bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2)) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some (t, α₁), none) =
      .pure (zeroBits _, (some (t, α₁), none)) := by
  simp only [bb1SimChal]
  rw [if_neg h]

/-- **The simulator's oracles** [BB04, proof of Theorem 4.1] with challenge bit `b`, at
parameter `κ`, on the description `d` and the Decision BDH tuple `(g, X, Y, Z, T)`: the three
handlers `bb1SimInit`, `bb1SimKeyQ`, `bb1SimChal` as an implementation of the game's oracles. -/
noncomputable def bb1SimImpl (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec :=
  (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
    (bb1SimChal G ℓ b κ d g X Y Z T)

/-- `bb1SimImpl` is `oracleImpl` of the three simulator handlers. -/
theorem bb1SimImpl_eq (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    bb1SimImpl G ℓ b κ d g X Y Z T =
      (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
        (bb1SimChal G ℓ b κ d g X Y Z T) := rfl

/-- **The simulation game** [BB04, proof of Theorem 4.1] for the adversary `A` with budget `q`,
challenge bit `b`, on `P_BDH` (`real`) or `R_BDH`: draw the generator's coins `r`, `g ∈ G^*`,
`a, b', c ∈ Z_p`, `T ∈ G_T` and `A`'s coins, run `A(1^κ)` against the simulator's oracles on
`(g, g^a, g^{b'}, g^c, T')` with `T' = e(g, g)^{ab'c}` if `real` and `T` otherwise, and return
`A`'s guess. -/
noncomputable def bb1SimGame (A : NUPPT) (q : ℕ) (b real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order ×
    ZMod (G.group κ (G.desc κ r)).order)).bind fun abc =>
  (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
  (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
      (g.1 ^ abc.2.2.val)
      (if real then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
        else t))
    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind fun res => .pure (res.1 0)

/-- The simulation game draws the generator's coins, `g ∈ G^*`, `(a, b', c)`, `T` and `A`'s
coins, and simulates `A` against `bb1SimImpl` on the Decision BDH tuple. -/
theorem bb1SimGame_eq (A : NUPPT) (q : ℕ) (b real : Bool) (κ : ℕ) :
    bb1SimGame G ℓ A q b real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order ×
        ZMod (G.group κ (G.desc κ r)).order)).bind fun abc =>
      (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
      (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
          (g.1 ^ abc.2.2.val)
          (if real then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
            else t))
        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
        fun res => .pure (res.1 0) := rfl

end Simulator

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
