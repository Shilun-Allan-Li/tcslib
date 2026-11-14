/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hash-and-sign

[PS10, Protocol 144.2]: from a family of collision-resistant hash functions `{h_i}` and a
signature scheme `(Gen, Sign, Ver)` for the hash values,
- `Gen′(1^n)` runs `(pk, sk) ← Gen(1^n)` and `i ← Gen_CRH(1^n)`, and outputs
  `pk′ = (pk, i)` and `sk′ = (sk, i)`;
- `Sign′_{sk′}(m) = Sign_sk(h_i(m))`;
- `Ver′_{pk′}(m, σ) = Ver_pk(h_i(m), σ)`.

Theorem 144.1: if the hash family is collision resistant and the signature scheme is one-time
secure, so is the new scheme.

**Message lengths (decision D-3).** The source hashes `{0,1}^*`. Here, per D-3, the CRH has
`d(n)`-bit inputs, and the new scheme signs `d(n)`-bit messages. Messages of any length up to
`p(n)` embed injectively into `p(n) + 1` bits: append `1`, then pad with `0`s. So the fixed-length
form covers them with `d = p + 1`. The unbounded form (with Merkle–Damgård) is optional.

**Hypotheses on the CRH.**
- **The domain is full:** `D_i` is every `d(n)`-bit string (`hdom` of the theorem), as for the
  source's `{0,1}^*`. Without it the theorem is false. Take a CRH whose `h_i` is constant off a
  small `D_i`: it is collision resistant, since its game counts only collisions inside `D_i`. But
  a forger queries some `m ∉ D_i` and outputs another `m′ ∉ D_i` with the same signature.
- **The hash values fit the signature scheme:** `r(n) = ℓ(n)`, the message length of
  `(Gen, Sign, Ver)` (`hlen`). It is a pointwise equation of lengths, used only inside the
  correctness proof, so the statements carry no casts.

The hash value is `h_i(m)` read at `r(n)` bits (`CRH.hash`, `padFin`), the very string whose
collisions the CRH game counts.

## Main definitions

* `Authentication.hsHashList`, `hsGenFun`, `hsSignFun`, `hsVerFun`: the hash and the three
  algorithms as string functions.
* `Authentication.hashAndSign`: Protocol 144.2 as a `SignatureScheme`, with correctness proved.

## Main results

* The `hsHashList_eq`, key/index and algorithm equations expose the string computations.
* `Authentication.hashAndSign_msgLen`, `hashAndSign_sigLen`, `hashAndSign_gen`,
  `hashAndSign_sign`, `hashAndSign_ver`: the signature-scheme data fields.
* `Authentication.hashAndSign_oneTimeSecure` (Thm 144.1): one-time security from collision
  resistance and one-time security of the original scheme, proved by the two reductions.
* `Authentication.exists_oneTimeSecure_of_crh_owf`: the source's existential form, with
  Lamport's scheme (proved from Theorems 137.2 and 144.1).

## Contents

* `HashAndSign.CodecReaders`: canonical forger codecs and split-word readers.
* `HashAndSign.OneQuery`: zero/one-query computation normal forms.
* `HashAndSign.OneQuerySampling`: drawing one signing tape in advance.
* `HashAndSign.ForwardHandler`: the efficient hashing/forwarding handler.
* `HashAndSign.FixedGame`: the common fixed-tape transcript.
* `HashAndSign.CollisionHandler`: the efficient collision finder and its soundness.
* `HashAndSign.CollisionGame`: the collision-finding probability bound.
* `HashAndSign.ForwardGame`: the original-scheme forgery probability equality.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §5.6, Theorem 144.1 and Protocol 144.2 (book pp. 144–145).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### The string functions -/

/-- The hash value `h_i(m)` at `r(n)` bits, with `n = |u|` read off `u = 1^n`: `H.eval` on
`⟨1^n, ⟨i, m⟩⟩`, padded or truncated (`padStr`, the string form of `CRH.hash`). -/
def hsHashList (H : CRH) (u i m : List Bool) : List Bool :=
  padStr H.rangeLen u (H.eval (pairEncode u (pairEncode i m)))

/-- The hash word is the evaluator output padded or truncated to the hash range length. -/
theorem hsHashList_eq (H : CRH) (u i m : List Bool) :
    hsHashList H u i m = padStr H.rangeLen u (H.eval (pairEncode u (pairEncode i m))) := rfl

/-- The key `⟨pk, sk⟩ = Gen(1^n)` of the signature scheme, from the first `coins_Gen(n)` coins of
the layout `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩`. -/
def hsSigKey (S : SignatureScheme) (z : List Bool) : List Bool :=
  S.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    ((NUPPT.inCoins z).take (S.gen.coins.eval (NUPPT.inParam z).length)))

/-- The signature-key word runs the original generator with empty argument and advice on
the first generator-sized segment of the tape. -/
theorem hsSigKey_eq (S : SignatureScheme) (z : List Bool) :
    hsSigKey S z =
      S.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (S.gen.coins.eval (NUPPT.inParam z).length))) := rfl

/-- The index `i = Gen_CRH(1^n)`, from the remaining coins. -/
def hsIdx (S : SignatureScheme) (H : CRH) (z : List Bool) : List Bool :=
  H.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    ((NUPPT.inCoins z).drop (S.gen.coins.eval (NUPPT.inParam z).length)))

/-- The hash-index word runs the hash generator with empty argument and advice on the tape
after the original generator's coin segment. -/
theorem hsIdx_eq (S : SignatureScheme) (H : CRH) (z : List Bool) :
    hsIdx S H z =
      H.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).drop (S.gen.coins.eval (NUPPT.inParam z).length))) := rfl

/-- `Gen′`: the key `⟨pk′, sk′⟩ = ⟨⟨pk, i⟩, ⟨sk, i⟩⟩`. -/
def hsGenFun (S : SignatureScheme) (H : CRH) (z : List Bool) : List Bool :=
  pairEncode (pairEncode (pairFstD (hsSigKey S z)) (hsIdx S H z))
    (pairEncode (pairSndD (hsSigKey S z)) (hsIdx S H z))

/-- The new key word pairs the public key with the hash index and the secret key with that
same index. -/
theorem hsGenFun_eq (S : SignatureScheme) (H : CRH) (z : List Bool) :
    hsGenFun S H z =
      pairEncode (pairEncode (pairFstD (hsSigKey S z)) (hsIdx S H z))
        (pairEncode (pairSndD (hsSigKey S z)) (hsIdx S H z)) := rfl

/-- `Sign′` on the layout `⟨⟨⟨1^n, ⟨⟨sk, i⟩, m⟩⟩, α⟩, ρ⟩`: `Sign` on `⟨sk, h_i(m)⟩` with the same
coins. -/
def hsSignFun (S : SignatureScheme) (H : CRH) (z : List Bool) : List Bool :=
  S.sign.output (NUPPT.layout (NUPPT.inParam z)
    (pairEncode (pairFstD (pairFstD (NUPPT.inArg z)))
      (hsHashList H (NUPPT.inParam z) (pairSndD (pairFstD (NUPPT.inArg z)))
        (pairSndD (NUPPT.inArg z))))
    [] (NUPPT.inCoins z))

/-- The signing word runs the original signer on the secret key paired with the hash word,
retaining the parameter and coins and using empty advice. -/
theorem hsSignFun_eq (S : SignatureScheme) (H : CRH) (z : List Bool) :
    hsSignFun S H z =
      S.sign.output (NUPPT.layout (NUPPT.inParam z)
        (pairEncode (pairFstD (pairFstD (NUPPT.inArg z)))
          (hsHashList H (NUPPT.inParam z) (pairSndD (pairFstD (NUPPT.inArg z)))
            (pairSndD (NUPPT.inArg z))))
        [] (NUPPT.inCoins z)) := rfl

/-- `Ver′` on `⟨1^n, ⟨⟨pk, i⟩, ⟨m, σ⟩⟩⟩`: `Ver` on `⟨1^n, ⟨pk, ⟨h_i(m), σ⟩⟩⟩`. -/
def hsVerFun (S : SignatureScheme) (H : CRH) (w : List Bool) : List Bool :=
  S.ver (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
    (pairEncode (hsHashList H (pairFstD w) (pairSndD (pairFstD (pairSndD w)))
        (pairFstD (pairSndD (pairSndD w))))
      (pairSndD (pairSndD (pairSndD w))))))

/-- The verification word passes the original public key, hashed message and signature to
the original verifier at the same parameter. -/
theorem hsVerFun_eq (S : SignatureScheme) (H : CRH) (w : List Bool) :
    hsVerFun S H w =
      S.ver (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
        (pairEncode (hsHashList H (pairFstD w) (pairSndD (pairFstD (pairSndD w)))
            (pairFstD (pairSndD (pairSndD w))))
          (pairSndD (pairSndD (pairSndD w)))))) := rfl

/-! ### Efficiency -/

/-- The hash value is polynomial-time on any polynomial-time choice of `u`, `i` and `m`. -/
theorem polyTimeComputable_hsHashList (H : CRH) {u i m : List Bool → List Bool}
    (hu : PolyTimeComputable u) (hi : PolyTimeComputable i) (hm : PolyTimeComputable m) :
    PolyTimeComputable fun z => hsHashList H (u z) (i z) (m z) := by
  have h := (polyTimeComputable_padStr H.rangeLen).comp
    (hu.pairEncode (H.eval_poly.comp (hu.pairEncode (hi.pairEncode hm))))
  refine (congrArg PolyTimeComputable (?_ : (fun z => hsHashList H (u z) (i z) (m z)) = _)).mpr h
  funext z
  simp only [hsHashList, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The signature key of `Gen′` is polynomial-time. -/
theorem polyTimeComputable_hsSigKey (S : SignatureScheme) : PolyTimeComputable (hsSigKey S) := by
  have ht := (polyTimeComputable_pairTakePoly S.gen.coins).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
  have h := S.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
    ht)
  refine (congrArg PolyTimeComputable (?_ : hsSigKey S = _)).mpr h
  funext z
  simp only [hsSigKey, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The index of `Gen′` is polynomial-time. -/
theorem polyTimeComputable_hsIdx (S : SignatureScheme) (H : CRH) :
    PolyTimeComputable (hsIdx S H) := by
  have hd := (polyTimeComputable_pairDropPoly S.gen.coins).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
  have h := H.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
    hd)
  refine (congrArg PolyTimeComputable (?_ : hsIdx S H = _)).mpr h
  funext z
  simp only [hsIdx, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `Gen′` is polynomial-time. -/
theorem polyTimeComputable_hsGenFun (S : SignatureScheme) (H : CRH) :
    PolyTimeComputable (hsGenFun S H) := by
  have hk := polyTimeComputable_hsSigKey S
  have hi := polyTimeComputable_hsIdx S H
  exact ((polyTimeComputable_pairFstD.comp hk).pairEncode hi).pairEncode
    ((polyTimeComputable_pairSndD.comp hk).pairEncode hi)

/-- `Sign′` is polynomial-time. -/
theorem polyTimeComputable_hsSignFun (S : SignatureScheme) (H : CRH) :
    PolyTimeComputable (hsSignFun S H) := by
  have hA := NUPPT.polyTimeComputable_inArg
  have hl := polyTimeComputable_hsHashList H NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hA)
    (polyTimeComputable_pairSndD.comp hA)
  have h := S.sign.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam
    (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp hA).pairEncode hl)
    (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)
  refine (congrArg PolyTimeComputable (?_ : hsSignFun S H = _)).mpr h
  funext z
  simp only [hsSignFun, Function.comp_apply]

/-- `Ver′` is polynomial-time. -/
theorem polyTimeComputable_hsVerFun (S : SignatureScheme) (H : CRH) :
    PolyTimeComputable (hsVerFun S H) := by
  have hT := polyTimeComputable_pairSndD
  have hl := polyTimeComputable_hsHashList H polyTimeComputable_pairFstD
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hT)
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp hT)
  have h := S.ver_poly.comp (polyTimeComputable_pairFstD.pairEncode
    (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp hT).pairEncode
      (hl.pairEncode ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp hT))))
  refine (congrArg PolyTimeComputable (?_ : hsVerFun S H = _)).mpr h
  funext z
  simp only [hsVerFun, Function.comp_apply]

/-! ### The machines -/

/-- The machine `Gen′`, with the coins of `Gen` followed by those of `Gen_CRH`. -/
noncomputable abbrev hsGen (S : SignatureScheme) (H : CRH) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_hsGenFun S H) (.add S.gen.coins H.gen.coins)

/-- The hash-and-sign generator uses `S.gen.coinLen n + H.gen.coinLen n` coins at parameter
`n`, with the signature-generator segment first and the hash-index segment second. -/
theorem hsGen_coinLen (S : SignatureScheme) (H : CRH) (n : ℕ) :
    (hsGen S H).coinLen n = S.gen.coinLen n + H.gen.coinLen n :=
  (NUPPT.coinLen_eq (hsGen S H) n).trans
    ((congrArg (fun p : PolyExpr => p.eval n)
      (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsGenFun S H)
        (.add S.gen.coins H.gen.coins))).trans
      ((PolyExpr.eval_add S.gen.coins H.gen.coins n).trans
        (congrArg₂ Nat.add (NUPPT.coinLen_eq S.gen n).symm
          (NUPPT.coinLen_eq H.gen n).symm)))

/-- The machine `Sign′`, with the coins of `Sign`. -/
noncomputable abbrev hsSign (S : SignatureScheme) (H : CRH) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_hsSignFun S H) S.sign.coins

/-- The coins of `Gen′` split as those of `Gen`, then those of `Gen_CRH`. -/
theorem ofFn_coins_split {a b : ℕ} (ρ : Fin (a + b) → Bool) :
    (List.ofFn ρ).take a = List.ofFn (fun j : Fin a => ρ (Fin.castAdd b j)) ∧
      (List.ofFn ρ).drop a = List.ofFn (fun j : Fin b => ρ (Fin.natAdd a j)) := by
  rw [List.ofFn_add]
  constructor
  · exact List.take_left' (by simp)
  · exact List.drop_left' (by simp)

/-- `Gen′` outputs `⟨⟨pk, i⟩, ⟨sk, i⟩⟩` with `⟨pk, sk⟩ = Gen(1^n)` on the first coins and
`i = Gen_CRH(1^n)` on the rest. -/
theorem runAt_hsGen (S : SignatureScheme) (H : CRH) (n : ℕ) (ρ : (hsGen S H).Coins n) :
    (hsGen S H).runAt n [] ρ =
      let σ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
        fun j => ρ (Fin.cast (hsGen_coinLen S H n).symm j)
      pairEncode
        (pairEncode (pairFstD (S.gen.runAt n [] fun j => σ (Fin.castAdd (H.gen.coinLen n) j)))
          (H.gen.runAt n [] fun j => σ (Fin.natAdd (S.gen.coinLen n) j)))
        (pairEncode (pairSndD (S.gen.runAt n [] fun j => σ (Fin.castAdd (H.gen.coinLen n) j)))
          (H.gen.runAt n [] fun j => σ (Fin.natAdd (S.gen.coinLen n) j))) := by
  let σ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
    fun j => ρ (Fin.cast (hsGen_coinLen S H n).symm j)
  have hρ : List.ofFn ρ = List.ofFn σ := List.ofFn_congr (hsGen_coinLen S H n) ρ
  obtain ⟨h₁, h₂⟩ := ofFn_coins_split σ
  simp only [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform,
    S.gen_uniform.runAtL_eq, H.gen_uniform.runAtL_eq,
    hsGenFun_eq, hsSigKey_eq, hsIdx_eq, NUPPT.inParam_eq, NUPPT.inCoins_eq,
    NUPPT.advInput_eq, NUPPT.layout_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, ← NUPPT.coinLen_eq S.gen n, hρ, h₁, h₂]
  rfl

/-- `Sign′` on `⟨⟨sk, i⟩, m⟩` is `Sign` on `⟨sk, h_i(m)⟩` with the same coins. -/
theorem runAt_hsSign (S : SignatureScheme) (H : CRH) (n : ℕ) (sk i m : List Bool)
    (r : S.sign.Coins n) :
    (hsSign S H).runAt n (pairEncode (pairEncode sk i) m)
        (NUPPT.coinsCongr (A := S.sign) (B := hsSign S H)
          (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsSignFun S H)
            S.sign.coins).symm n r) =
      S.sign.runAt n (pairEncode sk (hsHashList H (List.replicate n true) i m)) r := by
  rw [NUPPT.runAt_coinsCongr, NUPPT.runAtL_ofPolyTimeUniform, S.sign_uniform.runAt_eq]
  simp only [hsSignFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.advInput_eq, NUPPT.layout_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-! ### The scheme -/

/-- **Protocol 144.2** [PS10]: hash with `H`, then sign the hash with `S`. Messages have the
CRH's input length `d(n)`; signatures are `S`'s. `hlen` says that the hash values have `S`'s
message length.

**Proof sketch.** The generator's published coin-length equation splits its tape into the
original signature-generator and hash-index tapes. The signer wrapper's published coin
equivalence carries its tape back to the original signer. The two run equations reduce
verification to `S`'s verifier on the hash word; `hlen` and `List.ofFn_congr` encode that word at
`S`'s message length. Original-scheme correctness applies to these same keys and coin tapes. -/
noncomputable def hashAndSign (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) : SignatureScheme where
  msgLen := H.domLen
  sigLen := S.sigLen
  gen := hsGen S H
  sign := hsSign S H
  ver := hsVerFun S H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sign_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  ver_poly := polyTimeComputable_hsVerFun S H
  correct := by
    intro n m rg rs
    let ρ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
      fun j => rg (Fin.cast (hsGen_coinLen S H n).symm j)
    let rg₁ : S.gen.Coins n := fun j => ρ (Fin.castAdd (H.gen.coinLen n) j)
    let ri : H.gen.Coins n := fun j => ρ (Fin.natAdd (S.gen.coinLen n) j)
    let i : List Bool := H.gen.runAt n [] ri
    let e : S.sign.Coins n ≃ (hsSign S H).Coins n :=
      NUPPT.coinsCongr (A := S.sign) (B := hsSign S H)
        (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsSignFun S H)
          S.sign.coins).symm n
    have hgen : (hsGen S H).runAt n [] rg =
        pairEncode
          (pairEncode (pairFstD (S.gen.runAt n [] rg₁)) i)
          (pairEncode (pairSndD (S.gen.runAt n [] rg₁)) i) :=
      runAt_hsGen S H n rg
    simp only [hgen, pairFstD_pairEncode, pairSndD_pairEncode]
    rw [← e.apply_symm_apply rs, runAt_hsSign]
    simp only [hsVerFun_eq, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode]
    let w : List Bool := H.eval (pairEncode (List.replicate n true)
      (pairEncode i (List.ofFn m)))
    have hl : H.rangeLen.eval (List.replicate n true).length = S.msgLen.eval n :=
      (congrArg (fun k : ℕ => H.rangeLen.eval k)
        (List.length_replicate (n := n) (a := true))).trans (hlen n)
    let mh : Fin (S.msgLen.eval n) → Bool := fun j =>
      padFin (H.rangeLen.eval (List.replicate n true).length) w (Fin.cast hl.symm j)
    have hm₀ : List.ofFn mh = hsHashList H (List.replicate n true) i (List.ofFn m) :=
      (List.ofFn_congr hl
        (padFin (H.rangeLen.eval (List.replicate n true).length) w)).symm.trans
          ((ofFn_padFin_eq_padStr H.rangeLen (List.replicate n true) w).trans
            (hsHashList_eq H (List.replicate n true) i (List.ofFn m)).symm)
    simpa only [atParam_eq, hm₀] using S.correct n mh rg₁ (e.symm rs)

/-- Hash-and-sign uses the hash family's domain length as its message length. -/
theorem hashAndSign_msgLen (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).msgLen = H.domLen := rfl

/-- Hash-and-sign retains the original signature length. -/
theorem hashAndSign_sigLen (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).sigLen = S.sigLen := rfl

/-- Hash-and-sign uses the combined signature-key and hash-index generator. -/
theorem hashAndSign_gen (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).gen = hsGen S H := rfl

/-- Hash-and-sign uses the signer that hashes its message before calling the original signer. -/
theorem hashAndSign_sign (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).sign = hsSign S H := rfl

/-- Hash-and-sign uses the verifier that hashes its message before calling the original verifier. -/
theorem hashAndSign_ver (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) :
    (hashAndSign H S hlen).ver = hsVerFun S H := rfl

/-! ### Theorem 144.1 -/

/-- When hash and signature message widths agree, the hash-and-sign hash word equals the
word used by the two reduction handlers, including on arbitrary list inputs. -/
theorem hsHashList_eq_hashWord (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (i m : List Bool) :
    hsHashList H (List.replicate n true) i m =
      HashSignForward.hashWord H S (List.replicate n true) i m := by
  simp only [hsHashList_eq, HashSignForward.hashWord_eq, padStr_eq,
    List.length_replicate, hlen n]

/-- For a computation making at most one signing query, the hash-and-sign signing oracle
has the same expected logged payoff as sampling one original signing tape before the run.

**Proof sketch.** First move the wrapper signer's randomness outside the simulation using
the one-query sampling law. Its coin bijection with the original signer preserves uniform
sampling. The published wrapper run equation and the hash-width equation identify each
fixed-tape answer with the common experiment's answer. -/
theorem expect_hashAndSign_sign (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (sk i : List Bool)
    (c : OracleComp (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
      (fun _ => S.sigLen.eval n)) (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool))
    (hc : c.CostBoundedBy (fun _ => 1) 1)
    (g : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))) → ℝ) :
    ProbComp.expect
        (simulate ((hashAndSign H S hlen).signImpl n (pairEncode sk i)).withLog c ((), [])) g =
      ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
        ProbComp.expect (simulate (HashSignFill.fixedSign H S n sk i rs).withLog c ((), [])) g) := by
  have hraw := HashSignFill.expect_simulate_sample_once
    (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (rs : (hsSign S H).Coins n) =>
      padFin (S.sigLen.eval n)
        ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) rs)) c hc g
  have hfirst : ProbComp.expect
      (simulate ((hashAndSign H S hlen).signImpl n (pairEncode sk i)).withLog c ((), [])) g =
      ProbComp.expect (ProbComp.sample ((hsSign S H).Coins n)) (fun rs =>
        ProbComp.expect
          (simulate (QueryImpl.withLog (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool)
            (_ : Unit) => (OracleComp.pure
              (padFin (S.sigLen.eval n)
                ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) rs), ()) :
              ProbComp ((Fin (S.sigLen.eval n) → Bool) × Unit)))) c ((), [])) g) := by
    simpa only [SignatureScheme.signImpl_eq, hashAndSign_sign, hashAndSign_sigLen] using hraw
  rw [hfirst]
  let e : S.sign.Coins n ≃ (hsSign S H).Coins n :=
    NUPPT.coinsCongr (A := S.sign) (B := hsSign S H)
      (NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsSignFun S H) S.sign.coins).symm n
  rw [← ProbComp.expect_sample_equiv e]
  apply congrArg (ProbComp.expect (ProbComp.sample (S.sign.Coins n)))
  funext rs
  have hi : (fun (_ : Fin 1) (m : Fin (H.domLen.eval n) → Bool) (_ : Unit) =>
      (OracleComp.pure (padFin (S.sigLen.eval n)
        ((hsSign S H).runAt n (pairEncode (pairEncode sk i) (List.ofFn m)) (e rs)), ()) :
        ProbComp ((Fin (S.sigLen.eval n) → Bool) × Unit))) =
      HashSignFill.fixedSign H S n sk i rs := by
    funext j m s
    rw [HashSignFill.fixedSign_apply, HashSignFill.hashedReply_eq,
      runAt_hsSign, hsHashList_eq_hashWord H S hlen]
  rw [hi]

/-- Hash-and-sign accepts a message/signature pair exactly when the original scheme accepts
the padded hash of that message with the same signature. -/
theorem hashAndSign_accepts_iff (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (pk i : List Bool)
    (m : Fin (H.domLen.eval n) → Bool) (σ : Fin (S.sigLen.eval n) → Bool) :
    (hashAndSign H S hlen).Accepts n (pairEncode pk i) m σ ↔
      S.Accepts n pk (padFin (S.msgLen.eval n)
        (H.eval (atParam n (pairEncode i (List.ofFn m))))) σ := by
  simp only [SignatureScheme.accepts_iff, hashAndSign_ver, hsVerFun_eq, atParam_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, hsHashList_eq_hashWord H S hlen,
    HashSignForward.hashWord_unary]

/-- On concatenated original-generator and hash-generator tapes, the combined generator
returns the original public and secret keys each paired with the same generated hash index.

**Proof sketch.** The published coin-splitting bijection has the concatenated encoding.
Transporting to the combined width preserves that encoding, so its two projections are
the original tapes. The combined generator's run equation then gives the paired keys. -/
theorem runAt_hsGen_split (S : SignatureScheme) (H : CRH) (n : ℕ)
    (rg : S.gen.Coins n) (ri : H.gen.Coins n) :
    (hsGen S H).runAt n []
        (EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n) (rg, ri)) =
      pairEncode
        (pairEncode (pairFstD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri))
        (pairEncode (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri)) := by
  let ρ := EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n) (rg, ri)
  let σ : Fin (S.gen.coinLen n + H.gen.coinLen n) → Bool :=
    fun j => ρ (Fin.cast (hsGen_coinLen S H n).symm j)
  have hσ : σ = Fin.append rg ri := by
    apply List.ofFn_injective
    exact (List.ofFn_congr (hsGen_coinLen S H n) ρ).symm.trans
      ((EnsembleLemmas.ofFn_coinsEquiv (hsGen_coinLen S H n) (rg, ri)).trans
        (List.ofFn_fin_append rg ri).symm)
  rw [runAt_hsGen]
  change pairEncode
    (pairEncode (pairFstD (S.gen.runAt n [] (fun j => σ (Fin.castAdd (H.gen.coinLen n) j))))
      (H.gen.runAt n [] (fun j => σ (Fin.natAdd (S.gen.coinLen n) j))))
    (pairEncode (pairSndD (S.gen.runAt n [] (fun j => σ (Fin.castAdd (H.gen.coinLen n) j))))
      (H.gen.runAt n [] (fun j => σ (Fin.natAdd (S.gen.coinLen n) j)))) = _
  simp only [hσ, Fin.append_left, Fin.append_right]

/-- The hash-and-sign forgery probability equals the common transcript's success
probability averaged over independent original key, hash-index, adversary and signing tapes.

**Proof sketch.** Read the forgery experiment through its published equation. Reindex the
combined generator tape by the product of the original generator tapes and use its run
equation. Finally move the single signing tape outside the logged simulation and identify
verification with original-scheme verification on the hash. -/
theorem hashAndSign_forge_eq_common (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (A : NUPPT) (n : ℕ) :
    accept ((hashAndSign H S hlen).forgeGame A 1 n) =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
              ProbComp.prob
                (HashSignFill.transcript H S A n (pairFstD (S.gen.runAt n [] rg))
                  (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri) rs rA)
                (HashSignFill.Success H S n (pairFstD (S.gen.runAt n [] rg))
                  (H.gen.runAt n [] ri)))))) := by
  classical
  rw [SignatureScheme.forgeGame_eq, accept_eq, ProbComp.prob_eq_expect]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure, decide_eq_true_eq,
    hashAndSign_gen]
  rw [← ProbComp.expect_sample_equiv (EnsembleLemmas.coinsEquiv (hsGen_coinLen S H n))]
  rw [← Bridge.expect_sample_pair]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  apply congrArg (ProbComp.expect (ProbComp.sample (S.gen.Coins n)))
  funext rg
  apply congrArg (ProbComp.expect (ProbComp.sample (H.gen.Coins n)))
  funext ri
  simp only [runAt_hsGen_split, pairFstD_pairEncode, pairSndD_pairEncode,
    SignatureScheme.forgerCodec_eq_bitCodec, hashAndSign_msgLen, hashAndSign_sigLen]
  apply congrArg (ProbComp.expect (ProbComp.sample (A.Coins n)))
  funext rA
  rw [expect_hashAndSign_sign H S hlen n _ _ _ (A.toCompOn_costBoundedBy _ n 1 _ rA)]
  apply congrArg (ProbComp.expect (ProbComp.sample (S.sign.Coins n)))
  funext rs
  simp only [HashSignFill.transcript_eq, ProbComp.prob_eq_expect,
    HashSignFill.success_iff, hashAndSign_accepts_iff]
  apply congrArg (ProbComp.expect _)
  funext res
  split <;> rfl

/-- Every successful common transcript either gives a fresh-message hash collision or
is a successful forgery after forwarding hashes to the original signing oracle.

**Proof sketch.** If a queried message has the final message's hash, use source freshness
for the collision case. Otherwise the final hash is fresh among forwarded queries.
The range-width equation transports equality of the forwarded hash vectors back to
equality of CRH hash vectors, including at width zero. -/
theorem hashAndSign_success_cases (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (n : ℕ) (pk i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n))))
    (h : HashSignFill.Success H S n pk i res) :
    HashSignFill.CollisionCase H S n i res ∨
      HashSignFill.ForwardSuccess H S n pk i res := by
  classical
  obtain ⟨haccept, hfresh⟩ := (HashSignFill.success_iff H S n pk i res).mp h
  by_cases heq : ∃ e ∈ res.2.2,
      H.hash n i e.2.1 = H.hash n i (splitBits res.1).1
  · exact Or.inl ((HashSignFill.collisionCase_iff H S n i res).mpr ⟨hfresh, heq⟩)
  · apply Or.inr
    apply (HashSignFill.forwardSuccess_iff H S n pk i res).mpr
    constructor
    · simpa only [HashSignFill.queryHash_eq] using haccept
    · intro e hem hsame
      apply heq
      refine ⟨e, hem, ?_⟩
      funext j
      have hv := congrFun hsame (Fin.cast (hlen n) j)
      simpa only [HashSignFill.queryHash_eq, CRH.hash_eq, padFin_apply, Fin.coe_cast] using hv

/-- **Theorem 144.1: hash-and-sign is one-time secure** [PS10, Theorem 144.1] when the hash
family is collision resistant on its full domain and the signature scheme is one-time secure.

**Proof sketch.** The source's two reductions are implemented with independent key,
hash-index, adversary and signing tapes; a one-query sampling law couples their common
logged transcript, including no-query and codec-timeout outputs.
1. Let `A` be a one-time forger against `hashAndSign`, querying `m` (or nothing) and outputting
   `(m′, σ′)` with `m′ ≠ m` and `Ver_pk(h_i(m′), σ′)` accepting.
2. *Case `h_i(m′) = h_i(m)`.* The collision finder `B(1^n, i)` samples `(pk, sk) ← Gen(1^n)`,
   runs `A` on `⟨pk, i⟩` answering its query with `Sign_sk(h_i(m))`, and outputs `(m, m′)`
   (using the initial zero word if no query was made). For the queried case, freshness and
   `hdom` give a collision. `B` answers `A`'s queries itself, so it is a machine by T1
   (`Games.exists_handlerMachine`), with `advIn` supplying `⟨pk, i⟩`, `out` returning `(m, m′)`,
   and the seed holding the coins of `Gen` and `Sign`.
3. *Case `A` made no query or `h_i(m′) ≠ h_i(m)`.* The forger `C^{Sign_sk}(1^n, pk)` samples
   `i ← Gen_CRH(1^n)`, runs `A` on `⟨pk, i⟩` forwarding its query `m` as `h_i(m)`, and outputs
   `(h_i(m′), σ′)`. That is a one-time forgery against `S`: `C` makes at most one query, and
   `h_i(m′)` was not queried. T2 (`Games.exists_interactiveHandlerMachine`) uses
   `advIn = ⟨pk, i⟩`, forwards each query as `h_i(m)` (`perCall = 1`), and finishes without
   another oracle query (`finCall = 0`).
4. `A`'s success probability is at most `B`'s plus `C`'s, both negligible. -/
theorem hashAndSign_oneTimeSecure (H : CRH) (S : SignatureScheme)
    (hlen : ∀ n, H.rangeLen.eval n = S.msgLen.eval n) (hdom : ∀ n i x, H.inDom n i x = true)
    (hH : H.CollisionResistant) (hS : S.OneTimeSecure) :
    (hashAndSign H S hlen).OneTimeSecure := by
  classical
  apply (SignatureScheme.oneTimeSecure_iff _).mpr
  intro A
  obtain ⟨B, hB⟩ := HashSignFill.exists_collisionGame_bound H S A hdom
  obtain ⟨C, hC⟩ := HashSignFill.exists_forwardGame H S A
  obtain ⟨εB, hεB, hboundB⟩ := (CRH.collisionResistant_iff H).mp hH B
  obtain ⟨εC, hεC, hboundC⟩ := (SignatureScheme.oneTimeSecure_iff S).mp hS C
  refine ⟨fun n => εB n + εC n, hεB.add hεC, fun n => ?_⟩
  rw [hashAndSign_forge_eq_common H S hlen A n]
  refine le_trans ?_ (add_le_add (hboundB n) (hboundC n))
  refine le_trans ?_ (add_le_add (hB n) (le_of_eq (hC n).symm))
  -- Bound the success event by the union before averaging the independent tapes.
  rw [← ProbComp.expect_add]
  apply ProbComp.expect_mono
  intro rg
  rw [← ProbComp.expect_add]
  apply ProbComp.expect_mono
  intro ri
  rw [← ProbComp.expect_add]
  apply ProbComp.expect_mono
  intro rA
  rw [← ProbComp.expect_add]
  apply ProbComp.expect_mono
  intro rs
  exact (ProbComp.prob_mono _ (fun res hs =>
    hashAndSign_success_cases H S hlen n _ _ res hs)).trans (ProbComp.prob_or_le _ _ _)

/-- **The existential form of Theorem 144.1** [PS10]: a collision-resistant hash family
`{0,1}^{d(n)} → {0,1}^n` on its full domain, and a one-way function, give a one-time secure
signature scheme for `d(n)`-bit messages: hash-and-sign over Lamport's scheme
(`lamport_oneTimeSecure`). Lamport signs `n`-bit messages, so the hash values have `n` bits. -/
theorem exists_oneTimeSecure_of_crh_owf (H : CRH) (hn : ∀ n, H.rangeLen.eval n = n)
    (hdom : ∀ n i x, H.inDom n i x = true) (hH : H.CollisionResistant)
    (L : PolyExpr) (f : ∀ n, (Fin n → Bool) → (Fin (L.eval n) → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hfE : ∀ n (x : Fin n → Bool), E (NUPPT.advInput n (List.ofFn x)) = List.ofFn (f n x))
    (hf : (lamportOWF L f).StrongOneWay) :
    ∃ S : SignatureScheme, S.msgLen = H.domLen ∧ S.OneTimeSecure :=
  let hlen : ∀ n, H.rangeLen.eval n = (lamport L f E hE hfE).msgLen.eval n :=
    fun n => (hn n).trans
      ((congrArg (fun p : PolyExpr => p.eval n)
        (lamport_msgLen L f E hE hfE)).trans (PolyExpr.eval_var n)).symm
  ⟨hashAndSign H (lamport L f E hE hfE) hlen,
    hashAndSign_msgLen H (lamport L f E hE hfE) hlen,
    hashAndSign_oneTimeSecure H (lamport L f E hE hfE) hlen hdom hH
      (lamport_oneTimeSecure L f E hE hfE hf)⟩

end TCSlib.Cryptography.Authentication
