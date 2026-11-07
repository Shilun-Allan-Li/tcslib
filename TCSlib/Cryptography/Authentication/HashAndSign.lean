/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Lamport
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hash-and-sign (statement phase)

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
* `Authentication.hashAndSign_oneTimeSecure` (Thm 144.1, stated; a `sorry` under the source's
  sketch).
* `Authentication.exists_oneTimeSecure_of_crh_owf`: the source's existential form, with
  Lamport's scheme (proved from Theorems 137.2 and 144.1).

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
      pairEncode
        (pairEncode (pairFstD (S.gen.runAt n [] fun j => ρ (Fin.castAdd _ j)))
          (H.gen.runAt n [] fun j => ρ (Fin.natAdd _ j)))
        (pairEncode (pairSndD (S.gen.runAt n [] fun j => ρ (Fin.castAdd _ j)))
          (H.gen.runAt n [] fun j => ρ (Fin.natAdd _ j))) := by
  obtain ⟨h₁, h₂⟩ := ofFn_coins_split (a := S.gen.coins.eval n) (b := H.gen.coins.eval n) ρ
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, S.gen_uniform.runAt_eq,
    H.gen_uniform.runAt_eq]
  simp only [hsGenFun, hsSigKey, hsIdx, NUPPT.inParam_eq, NUPPT.inCoins_eq,
    NUPPT.advInput_eq, NUPPT.layout_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  rw [h₁, h₂]
  rfl

/-- `Sign′` on `⟨⟨sk, i⟩, m⟩` is `Sign` on `⟨sk, h_i(m)⟩` with the same coins. -/
theorem runAt_hsSign (S : SignatureScheme) (H : CRH) (n : ℕ) (sk i m : List Bool)
    (r : S.sign.Coins n) :
    (hsSign S H).runAt n (pairEncode (pairEncode sk i) m) r =
      S.sign.runAt n (pairEncode sk (hsHashList H (List.replicate n true) i m)) r := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, S.sign_uniform.runAt_eq]
  simp only [hsSignFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.advInput_eq, NUPPT.layout_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-! ### The scheme -/

/-- **Protocol 144.2** [PS10]: hash with `H`, then sign the hash with `S`. Messages have the
CRH's input length `d(n)`; signatures are `S`'s. `hlen` says that the hash values have `S`'s
message length. -/
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
    rw [runAt_hsGen]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [runAt_hsSign]
    simp only [hsVerFun, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode]
    set rg₁ : S.gen.Coins n := fun j => rg (Fin.castAdd _ j)
    set w := H.eval (pairEncode (List.replicate n true)
      (pairEncode (H.gen.runAt n [] fun j => rg (Fin.natAdd _ j)) (List.ofFn m)))
    have hl : H.rangeLen.eval (List.replicate n true).length = S.msgLen.eval n := by
      rw [List.length_replicate, hlen]
    have hm₀ : List.ofFn (fun j : Fin (S.msgLen.eval n) =>
        padFin (H.rangeLen.eval (List.replicate n true).length) w (Fin.cast hl.symm j)) =
        padStr H.rangeLen (List.replicate n true) w := by
      rw [← List.ofFn_congr hl, ofFn_padFin_eq_padStr]
    simp only [hsHashList]
    rw [← hm₀]
    simpa only [atParam_eq] using S.correct n _ rg₁ rs

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

/-- **Theorem 144.1: hash-and-sign is one-time secure** [PS10, Theorem 144.1] when the hash
family is collision resistant on its full domain and the signature scheme is one-time secure.

**Proof sketch** (the source's).
1. Let `A` be a one-time forger against `hashAndSign`, querying `m` (or nothing) and outputting
   `(m′, σ′)` with `m′ ≠ m` and `Ver_pk(h_i(m′), σ′)` accepting.
2. *Case `h_i(m′) = h_i(m)`.* The collision finder `B(1^n, i)` samples `(pk, sk) ← Gen(1^n)`,
   runs `A` on `⟨pk, i⟩` answering its query with `Sign_sk(h_i(m))`, and outputs `(m, m′)`
   (aborting if `A` made no query). Since `m′ ≠ m` and both lie in `D_i` (`hdom`), this is a
   collision. `B` answers `A`'s queries itself, so it is a machine by T1
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
  sorry

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
  ⟨hashAndSign H (lamport L f E hE hfE) hn, rfl,
    hashAndSign_oneTimeSecure H (lamport L f E hE hfE) hn hdom hH
      (lamport_oneTimeSecure L f E hE hfE hf)⟩

end TCSlib.Cryptography.Authentication
