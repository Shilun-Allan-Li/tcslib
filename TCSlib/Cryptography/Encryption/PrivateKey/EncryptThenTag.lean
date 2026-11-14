/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Reduction
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Transfer
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Forgery
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A CCA2-secure private-key scheme (statement phase)

[PS10, Algorithm 169.3] and Theorem 170.4. For a PRF family `{f_k}`:
- `Gen′(1^n)` samples keys `k₁ ← U_n` and `k₂ ← U_{2n}`;
- `Enc′_{k₁,k₂}(m)` samples `r ← U_n`, sets `c₁ = m ⊕ f_{k₁}(r)`, and outputs
  `(r, c₁, f_{k₂}(r ‖ c₁))`;
- `Dec′_{k₁,k₂}(r, c₁, t)` outputs `⊥` unless `f_{k₂}(r ‖ c₁) = t`, and `c₁ ⊕ f_{k₁}(r)` otherwise.

It is the §3.9 scheme with its whole ciphertext `(r, c₁)` tagged under a second key: encrypt, then
authenticate. The tag defeats the mauling attack on the §3.9 scheme (Claim 169.a).

**Source notes: what the tag covers.**
- The algorithm box outputs `(r, c₁, f_{k₂}(c))`, with `c` undefined, while `Dec′` tests
  `f_{k₂}(c₁)`. The proof tags `c₁ ← Enc_{s₁}(m)`, which there names the whole §3.9 ciphertext.
  So the tag covers `(r, c₁)`.
- **Tagging `c₁` alone would not be CCA2-secure.** For positive `n`, choose challenge messages
  `0^n` and `1^n`, obtain `(r*, c₁*, t*)`, and obtain an encryption
  `(r₁, f_{k₁}(r₁), t₁)` of `0^n`. In this short-tag variant the query
  `(r*, f_{k₁}(r₁), t₁)` has a valid tag. If it equals the challenge, do not query it and count
  that branch as attack failure; otherwise its answer `f_{k₁}(r₁) ⊕ f_{k₁}(r*)` reveals the pad
  `f_{k₁}(r*)` and hence `m_b`. Equality can occur, in particular when `r₁ = r*` and `m_b = 0^n`.
  In the random-pad hybrid, nonce equality and accidental masked-message equality have total
  probability at most `2 / 2^n`; the real PRF setting adds a negligible reduction error.
  The attack is therefore overwhelmingly successful, rather than unconditionally query-distinct.
- The input `r ‖ c₁` has `2n` bits. The source's families are length-preserving on `|s|`-bit
  keys, so the tag key `k₂` has `2n` bits and the tag `2n` bits. One family `F` serves both keys,
  at parameters `n` and `2n` (the source names two families, `f` and `g`).
- `Dec′` is specified on well-formed triples. Here total pair projections and the two length
  guards enforce malformed rejection for generated keys when `n > 0`: both ciphertext pair layers
  must parse, and evaluator agreement then forces the valid tag to have `2n` bits. The evaluator
  `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`. At `n = 0`, failed projections can all be
  empty: the malformed four-bit word `0000`, for example, decrypts to the valid empty message.
  This finite-prefix behavior is retained; the malformed-rejection claim is only for positive
  parameters. There is only one plaintext at zero, so this does not change the security statement.

**The encoding.** The key is `⟨k₁, k₂⟩`; `Gen′` reads its `3n` coins as `k₁` (the first `n`)
followed by `k₂`. A ciphertext is `⟨r, ⟨c₁, t⟩⟩`, of `6n + 4` bits.

## Main definitions

* `Composability.ccaGenFun`, `ccaEncFun`, `ccaDecFun`: the three algorithms as string functions.
* `Composability.ccaScheme`: Algorithm 169.3 as a `FixedLengthScheme`, with correctness and the
  ciphertext length proved.

## Main results

* `Composability.ccaScheme_cca2` (Thm 170.4, stated; a `sorry` under the source's sketch).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.3, Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### The algorithms as string functions -/

/-- `Gen′` on the layout `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with `3n` coins `ρ`: the key `⟨k₁, k₂⟩`, where
`k₁` is the first `n` coins and `k₂` the rest. -/
def ccaGenFun (z : List Bool) : List Bool :=
  pairEncode ((NUPPT.inCoins z).take (NUPPT.inParam z).length)
    ((NUPPT.inCoins z).drop (NUPPT.inParam z).length)

/-- The raw generator pairs the input coins before and after the parameter length:
`⟨ρ.take n, ρ.drop n⟩`. -/
theorem ccaGenFun_eq (z : List Bool) :
    ccaGenFun z =
      pairEncode ((NUPPT.inCoins z).take (NUPPT.inParam z).length)
        ((NUPPT.inCoins z).drop (NUPPT.inParam z).length) := rfl

/-- The first ciphertext part `c₁ = m ⊕ E(⟨k₁, r⟩)` of `Enc′`, on the layout
`⟨⟨⟨1^n, ⟨⟨k₁, k₂⟩, m⟩⟩, α⟩, r⟩`. -/
def ccaMaskFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor (pairSndD (NUPPT.inArg z))
    (E (pairEncode (pairFstD (pairFstD (NUPPT.inArg z))) (NUPPT.inCoins z)))

/-- The raw ciphertext mask is the decoded message XOR the evaluator's output on the first
key and the input coins [PS10, Algorithm 169.3]. -/
theorem ccaMaskFun_eq (E : List Bool → List Bool) (z : List Bool) :
    ccaMaskFun E z =
      List.zipWith xor (pairSndD (NUPPT.inArg z))
        (E (pairEncode (pairFstD (pairFstD (NUPPT.inArg z))) (NUPPT.inCoins z))) := rfl

/-- `Enc′` on the layout `⟨⟨⟨1^n, ⟨⟨k₁, k₂⟩, m⟩⟩, α⟩, r⟩`: the ciphertext
`⟨r, ⟨c₁, E(⟨k₂, r ++ c₁⟩)⟩⟩` with `c₁ = m ⊕ E(⟨k₁, r⟩)`. -/
def ccaEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (NUPPT.inCoins z)
    (pairEncode (ccaMaskFun E z)
      (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
        (NUPPT.inCoins z ++ ccaMaskFun E z))))

/-- Raw encryption returns the nonce, the masked message, and the tag of their concatenation
under the second key [PS10, Algorithm 169.3]. -/
theorem ccaEncFun_eq (E : List Bool → List Bool) (z : List Bool) :
    ccaEncFun E z =
      pairEncode (NUPPT.inCoins z)
        (pairEncode (ccaMaskFun E z)
          (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
            (NUPPT.inCoins z ++ ccaMaskFun E z)))) := rfl

/-- The test of `Dec′` on the layout `⟨⟨⟨1^n, ⟨⟨k₁, k₂⟩, ⟨r, ⟨c₁, t⟩⟩⟩⟩, α⟩, r'⟩`: `r` and `c₁`
have `n` bits, and the tag is valid, `E(⟨k₂, r ++ c₁⟩) = t`. -/
def ccaDecOK (E : List Bool → List Bool) (z : List Bool) : Bool :=
  decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
    decide ((pairFstD (pairSndD (pairSndD (NUPPT.inArg z)))).length =
      (NUPPT.inParam z).length) &&
    decide (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
        (pairFstD (pairSndD (NUPPT.inArg z)) ++ pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) =
      pairSndD (pairSndD (pairSndD (NUPPT.inArg z))))

/-- The raw decryption guard conjoins the two parameter-length checks with equality of the
computed and supplied tags [PS10, Algorithm 169.3]. -/
theorem ccaDecOK_eq (E : List Bool → List Bool) (z : List Bool) :
    ccaDecOK E z = (
      decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
        decide ((pairFstD (pairSndD (pairSndD (NUPPT.inArg z)))).length =
          (NUPPT.inParam z).length) &&
        decide (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
            (pairFstD (pairSndD (NUPPT.inArg z)) ++
              pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) =
          pairSndD (pairSndD (pairSndD (NUPPT.inArg z))))) := rfl

/-- `Dec′` on the layout `⟨⟨⟨1^n, ⟨⟨k₁, k₂⟩, ⟨r, ⟨c₁, t⟩⟩⟩⟩, α⟩, r'⟩`: `c₁ ⊕ E(⟨k₁, r⟩)` when
the test passes, and otherwise `⊥`, here `1^{n+1}`, which decodes to no `n`-bit message. -/
def ccaDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  if ccaDecOK E z then
    List.zipWith xor (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
      (E (pairEncode (pairFstD (pairFstD (NUPPT.inArg z))) (pairFstD (pairSndD (NUPPT.inArg z)))))
  else true :: NUPPT.inParam z

/-- Raw decryption XORs the first ciphertext component with the first-key pad when
`ccaDecOK` holds, and returns `true :: NUPPT.inParam z` otherwise [PS10, Algorithm 169.3]. -/
theorem ccaDecFun_eq (E : List Bool → List Bool) (z : List Bool) :
    ccaDecFun E z =
      if ccaDecOK E z then
        List.zipWith xor (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
          (E (pairEncode (pairFstD (pairFstD (NUPPT.inArg z)))
            (pairFstD (pairSndD (NUPPT.inArg z)))))
      else true :: NUPPT.inParam z := rfl

/-! ### Efficiency -/

/-- `Gen′` is polynomial-time: a split of the coins at `n` (`polyTimeComputable_pairTakePoly`). -/
theorem polyTimeComputable_ccaGenFun : PolyTimeComputable ccaGenFun := by
  have hp := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  convert ((polyTimeComputable_pairTakePoly .var).comp hp).pairEncode
    ((polyTimeComputable_pairDropPoly .var).comp hp) using 1
  funext z
  simp [ccaGenFun, Function.comp_apply]

/-- The mask `c₁` is polynomial-time when `E` is. -/
theorem polyTimeComputable_ccaMaskFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ccaMaskFun E) := by
  have h := polyTimeComputable_pairXor.comp
    ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      (hE.comp (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp
        NUPPT.polyTimeComputable_inArg).pairEncode NUPPT.polyTimeComputable_inCoins)))
  convert h using 1
  funext z
  simp [ccaMaskFun, Function.comp_apply]

/-- `Enc′` is polynomial-time when `E` is. -/
theorem polyTimeComputable_ccaEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ccaEncFun E) := by
  have hm := polyTimeComputable_ccaMaskFun hE
  have h := NUPPT.polyTimeComputable_inCoins.pairEncode (hm.pairEncode
    (hE.comp (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp
      NUPPT.polyTimeComputable_inArg).pairEncode (NUPPT.polyTimeComputable_inCoins.append hm))))
  convert h using 1

/-- The test of `Dec′` is polynomial-time when `E` is: two length comparisons and one equality
(`polyTimeComputable_lenEq`, `polyTimeComputable_pairEq`).

**Proof sketch.** Project the nonce, encrypted message, tag and second key from the layout.
Two polynomial-time length comparisons check that the nonce and encrypted message each have
`n` bits. Append these two words and evaluate the tag under the second key, using composition
with the polynomial-time evaluator. A word-equality test compares this result with the supplied
tag; Boolean conjunction combines that test with the two length checks. -/
theorem polyTimeComputable_ccaDecOK {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (fun z => [ccaDecOK E z]) := by
  have hl : ∀ g : List Bool → List Bool, PolyTimeComputable g →
      PolyTimeComputable (fun z => [decide ((g z).length = (NUPPT.inParam z).length)]) := by
    intro g hg
    convert polyTimeComputable_lenEq.comp (hg.pairEncode NUPPT.polyTimeComputable_inParam)
      using 1
    funext z
    simp [Function.comp_apply]
  have hArg := NUPPT.polyTimeComputable_inArg
  have hc₁ : PolyTimeComputable fun z => pairFstD (pairSndD (pairSndD (NUPPT.inArg z))) :=
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      polyTimeComputable_pairSndD).comp hArg
  have hc₂ : PolyTimeComputable fun z => pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) :=
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
      polyTimeComputable_pairSndD).comp hArg
  have hr : PolyTimeComputable fun z => pairFstD (pairSndD (NUPPT.inArg z)) :=
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp hArg
  have htag : PolyTimeComputable fun z =>
      [decide (E (pairEncode (pairSndD (pairFstD (NUPPT.inArg z)))
          (pairFstD (pairSndD (NUPPT.inArg z)) ++
            pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) =
        pairSndD (pairSndD (pairSndD (NUPPT.inArg z))))] := by
    convert polyTimeComputable_pairEq.comp ((hE.comp
      (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hArg).pairEncode
        (hr.append hc₁))).pairEncode hc₂) using 1
    funext z
    simp [Function.comp_apply]
  exact polyTimeComputable_and (polyTimeComputable_and (hl _ hr) (hl _ hc₁)) htag

/-- `Dec′` is polynomial-time when `E` is. -/
theorem polyTimeComputable_ccaDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ccaDecFun E) := by
  refine polyTimeComputable_ite (polyTimeComputable_ccaDecOK hE) ?_
    ((polyTimeComputable_const [true]).append NUPPT.polyTimeComputable_inParam)
  have hArg := NUPPT.polyTimeComputable_inArg
  have h := polyTimeComputable_pairXor.comp
    ((((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      polyTimeComputable_pairSndD).comp hArg).pairEncode
      (hE.comp (((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp
        hArg).pairEncode ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
          hArg))))
  convert h using 1
  funext z
  simp [Function.comp_apply]

/-! ### The machines -/

section Machines

variable {E : List Bool → List Bool} (hE : PolyTimeComputable E)

/-- The machine `Gen′`, with `3n` coins. -/
noncomputable abbrev ccaGen : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_ccaGenFun (.mul (.const 3) .var)

/-- The machine `Enc′`, with `n` coins. -/
noncomputable abbrev ccaEnc : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_ccaEncFun hE) .var

/-- The machine `Dec′`, deterministic. -/
noncomputable abbrev ccaDec : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_ccaDecFun hE) (.const 0)

/-- `Gen′` splits its `3n` coins at `n`. -/
theorem runAt_ccaGen (n : ℕ) (ρ : ccaGen.Coins n) :
    ccaGen.runAt n [] ρ = pairEncode ((List.ofFn ρ).take n) ((List.ofFn ρ).drop n) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [ccaGenFun, NUPPT.inCoins_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]

/-- `Enc′` on `⟨⟨k₁, k₂⟩, m⟩` with coins `r` is `⟨r, ⟨c₁, E(⟨k₂, r ++ c₁⟩)⟩⟩`,
`c₁ = m ⊕ E(⟨k₁, r⟩)`. -/
theorem runAt_ccaEnc (n : ℕ) (k₁ k₂ m : List Bool) (r : (ccaEnc hE).Coins n) :
    (ccaEnc hE).runAt n (pairEncode (pairEncode k₁ k₂) m) r =
      pairEncode (List.ofFn r)
        (pairEncode (List.zipWith xor m (E (pairEncode k₁ (List.ofFn r))))
          (E (pairEncode k₂
            (List.ofFn r ++ List.zipWith xor m (E (pairEncode k₁ (List.ofFn r))))))) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [ccaEncFun, ccaMaskFun, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- `Dec′` on `⟨⟨k₁, k₂⟩, ⟨r, ⟨c₁, t⟩⟩⟩` with `n`-bit `r` and `c₁` and a valid tag is
`c₁ ⊕ E(⟨k₁, r⟩)`. -/
theorem runAt_ccaDec (n : ℕ) (k₁ k₂ r c₁ t : List Bool) (hr : r.length = n)
    (hc₁ : c₁.length = n) (htag : E (pairEncode k₂ (r ++ c₁)) = t) (r' : (ccaDec hE).Coins n) :
    (ccaDec hE).runAt n (pairEncode (pairEncode k₁ k₂) (pairEncode r (pairEncode c₁ t))) r' =
      List.zipWith xor c₁ (E (pairEncode k₁ r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [ccaDecFun, ccaDecOK, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq,
    hr, hc₁, htag]

end Machines

/-! ### The scheme -/

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))

include hFE in
/-- On two `n`-bit strings, `E` returns `n` bits (it agrees with `F`). -/
theorem length_eval_of_length {n : ℕ} {a b : List Bool} (ha : a.length = n)
    (hb : b.length = n) : (E (pairEncode a b)).length = n := by
  have hA : List.ofFn (padFin n a) = a := by
    simpa only [ha, Nat.sub_self, List.replicate_zero, List.append_nil] using
      (Collection.ofFn_padFin_of_le (ℓ := n) ha.le)
  have hB : List.ofFn (padFin n b) = b := by
    simpa only [hb, Nat.sub_self, List.replicate_zero, List.append_nil] using
      (Collection.ofFn_padFin_of_le (ℓ := n) hb.le)
  rw [← hA, ← hB, hFE, List.length_ofFn]

/-- XOR-ing twice with the same pad, at least as long as the message, is the identity. -/
private theorem zipWith_xor_xor_self' : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self' m p (by simpa using h)⟩

/-- **`π′`** [PS10, Algorithm 169.3], for a family `F` with evaluator `E`: the §3.9 scheme under
the `n`-bit key `k₁`, its ciphertext `(r, c₁)` tagged with `f_{k₂}(r ‖ c₁)` under the `2n`-bit key
`k₂`. Ciphertexts have `6n + 4` bits. -/
noncomputable def ccaScheme : FixedLengthScheme where
  gen := ccaGen
  enc := ccaEnc hE
  dec := ccaDec hE
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    have hρ : (List.ofFn rg).length = 3 * n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have hk₁ : ((List.ofFn rg).take n).length = n := by simp [hρ]; omega
    have hr : (List.ofFn re).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hp := length_eval_of_length F E hFE hk₁ hr
    have hc₁ : (List.zipWith xor (List.ofFn m) (E (pairEncode ((List.ofFn rg).take n)
        (List.ofFn re)))).length = n := by simp [hp]
    rw [runAt_ccaGen, runAt_ccaEnc, runAt_ccaDec hE n _ _ _ _ _ hr hc₁ rfl,
      zipWith_xor_xor_self' _ _ (by simp [hp]), decodeFin_ofFn]
  ctLen := .add (.mul (.const 6) .var) (.const 4)
  enc_length := by
    intro n rg m r
    show ((ccaEnc hE).runAt n (pairEncode (ccaGen.runAt n [] rg) (List.ofFn m)) r).length = _
    have hρ : (List.ofFn rg).length = 3 * n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have hk₁ : ((List.ofFn rg).take n).length = n := by simp [hρ]; omega
    have hk₂ : ((List.ofFn rg).drop n).length = 2 * n := by simp [hρ]; omega
    have hr : (List.ofFn r).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hp := length_eval_of_length F E hFE hk₁ hr
    have hc₁ : (List.zipWith xor (List.ofFn m) (E (pairEncode ((List.ofFn rg).take n)
        (List.ofFn r)))).length = n := by simp [hp]
    have hrc : (List.ofFn r ++ List.zipWith xor (List.ofFn m) (E (pairEncode
        ((List.ofFn rg).take n) (List.ofFn r)))).length = 2 * n := by
      rw [List.length_append, hr, hc₁]; ring
    have ht := length_eval_of_length F E hFE hk₂ hrc
    rw [runAt_ccaGen, runAt_ccaEnc]
    simp only [length_pairEncode, hr, hc₁, ht, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega

attribute [simps (config := { isSimp := false }) gen enc dec ctLen] ccaScheme

/-! ### The proof of Theorem 170.4 -/

section Proof

open ETTGame ProbComp

/-- The ciphertext length is `6n + 4` (`ccaScheme_ctLen`). -/
private theorem cca_ctLen_eval (n : ℕ) : (ccaScheme F E hE hFE).ctLen.eval n = 6 * n + 4 := by
  rw [ccaScheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_const, PolyExpr.eval_var]

/-- The scheme's query lengths are the reduction's: `inLens n = fun i => (ettDin i).eval n`. -/
private theorem cca_inLens (n : ℕ) :
    (ccaScheme F E hE hFE).inLens n = fun i => (ettDin i).eval n := by
  funext i
  match i with
  | 0 => rw [FixedLengthScheme.inLens_zero, ettDin_zero, PolyExpr.eval_var]
  | 1 => rw [FixedLengthScheme.inLens_one, ettDin_one, cca_ctLen_eval, ettCt_eval]
  | 2 => rw [FixedLengthScheme.inLens_two, ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]

/-- The scheme's answer lengths are the reduction's: `outLens n = fun i => (ettDout i).eval n`. -/
private theorem cca_outLens (n : ℕ) :
    (ccaScheme F E hE hFE).outLens n = fun i => (ettDout i).eval n := by
  funext i
  match i with
  | 0 => rw [FixedLengthScheme.outLens_zero, ettDout_zero, cca_ctLen_eval, ettCt_eval]
  | 1 =>
    rw [FixedLengthScheme.outLens_one, ettDout_one, PolyExpr.eval_add, PolyExpr.eval_var,
      PolyExpr.eval_const]
  | 2 => rw [FixedLengthScheme.outLens_two, ettDout_two, cca_ctLen_eval, ettCt_eval]

/-- `Gen′` has `3n` coins. -/
private theorem cca_gen_coins : (ccaScheme F E hE hFE).gen.coins = .mul (.const 3) .var := by
  rw [ccaScheme_gen, NUPPT.coins_ofPolyTimeUniform]

/-- `Enc′` has `n` coins. -/
private theorem cca_enc_coins : (ccaScheme F E hE hFE).enc.coins = .var := by
  rw [ccaScheme_enc, NUPPT.coins_ofPolyTimeUniform]

/-- `3n = n + 2n`, for the key coins. -/
private theorem cca_gen_len (n : ℕ) : (PolyExpr.mul (.const 3) .var).eval n = n + 2 * n := by
  rw [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  ring

/-- The `3n` key coins as the keys `k₁` (`n` bits) and `k₂` (`2n` bits). -/
private noncomputable def ccaKeyEq (n : ℕ) :
    (ccaScheme F E hE hFE).gen.Coins n ≃ (Fin n → Bool) × (Fin (2 * n) → Bool) :=
  (NUPPT.coinsEquivPoly (cca_gen_coins F E hE hFE) n).trans
    (EnsembleLemmas.coinsEquiv (cca_gen_len n)).symm

/-- `⟦rg⟧ = ⟦k₁⟧ ++ ⟦k₂⟧` for `(k₁, k₂) = ccaKeyEq rg`. -/
private theorem ofFn_ccaKeyEq (n : ℕ) (rg : (ccaScheme F E hE hFE).gen.Coins n) :
    List.ofFn rg = List.ofFn (ccaKeyEq F E hE hFE n rg).1 ++
      List.ofFn (ccaKeyEq F E hE hFE n rg).2 := by
  rw [← EnsembleLemmas.ofFn_coinsEquiv (cca_gen_len n), ccaKeyEq, Equiv.trans_apply,
    Equiv.apply_symm_apply, NUPPT.coinsEquivPoly_ofFn]

/-- **`Gen′` outputs the pair of the two keys:** `Gen′(1^n; rg) = ⟨⟦k₁⟧, ⟦k₂⟧⟩` for
`(k₁, k₂) = ccaKeyEq rg` (`runAt_ccaGen`). -/
private theorem cca_gen_runAt (n : ℕ) (rg : (ccaScheme F E hE hFE).gen.Coins n) :
    (ccaScheme F E hE hFE).gen.runAt n [] rg =
      pairEncode (List.ofFn (ccaKeyEq F E hE hFE n rg).1)
        (List.ofFn (ccaKeyEq F E hE hFE n rg).2) := by
  have h := ofFn_ccaKeyEq F E hE hFE n rg
  generalize ccaKeyEq F E hE hFE n rg = kk at h
  revert rg
  rw [ccaScheme_gen]
  intro rg h
  rw [runAt_ccaGen, h, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]

/-- The encryption coins as an `n`-bit nonce, keeping the string. -/
private noncomputable def ccaNonceEq (n : ℕ) : (ccaScheme F E hE hFE).enc.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsEquivPoly (cca_enc_coins F E hE hFE) n).trans
    (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))

/-- `⟦ccaNonceEq n re⟧ = ⟦re⟧`. -/
private theorem ofFn_ccaNonceEq (n : ℕ) (re : (ccaScheme F E hE hFE).enc.Coins n) :
    List.ofFn (ccaNonceEq F E hE hFE n re) = List.ofFn re := by
  rw [ccaNonceEq, Equiv.trans_apply, ofFn_arrowCongr_finCongr, NUPPT.coinsEquivPoly_ofFn]

/-- **`Enc′` with the keys `k₁`, `k₂` and the coins `re`** is `encW (F n k₁) (F (2n) k₂)` with the
nonce `ccaNonceEq re` (`runAt_ccaEnc`, `hFE` at `n` and at `2n`). -/
private theorem ofFn_cca_encryptAt (n : ℕ) (k₁ : Fin n → Bool) (k₂ : Fin (2 * n) → Bool)
    (m : Fin n → Bool) (re : (ccaScheme F E hE hFE).enc.Coins n) :
    List.ofFn ((ccaScheme F E hE hFE).encryptAt n (pairEncode (List.ofFn k₁) (List.ofFn k₂)) m re) =
      encW (F n k₁) (F (2 * n) k₂) (ccaNonceEq F E hE hFE n re) (List.ofFn m) := by
  have hx : List.ofFn re = List.ofFn (ccaNonceEq F E hE hFE n re) :=
    (ofFn_ccaNonceEq F E hE hFE n re).symm
  generalize ccaNonceEq F E hE hFE n re = r at hx
  revert re
  simp only [FixedLengthScheme.encryptAt_eq]
  rw [ccaScheme_enc]
  intro re hx
  have hm : (List.ofFn m).length = n := List.length_ofFn
  have hc := length_maskL (F n k₁) r hm
  have hp : List.ofFn r ++ maskL (F n k₁) r (List.ofFn m) =
      List.ofFn (pairV n (List.ofFn r) (maskL (F n k₁) r (List.ofFn m))) := by
    rw [pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, List.length_ofFn, hc]; omega)]
  rw [runAt_ccaEnc, hx, hFE, ← maskL_eq, hp, hFE, ← tagL_eq, ← ctW_eq, ← encW_eq,
    ofFn_padFin_of_length (by rw [length_encW _ _ _ hm, cca_ctLen_eval])]

/-- **`Dec′` with the keys `k₁`, `k₂`** on a word `w`: `⟨1, wC w ⊕ ⟦F n k₁ (wR w)⟧⟩` if `w` is valid
for the tag function `F (2n) k₂`, and `⊥` otherwise (`ccaDecFun_eq`, `ccaDecOK_eq`, `hFE`). The
zero-parameter malformed words are read alike: their total projections are empty. -/
private theorem ofFn_cca_decAnswer (n : ℕ) (k₁ : Fin n → Bool) (k₂ : Fin (2 * n) → Bool)
    (w : List Bool) (rd : (ccaScheme F E hE hFE).dec.Coins n) :
    List.ofFn (FixedLengthScheme.decAnswer (decodeFin n ((ccaScheme F E hE hFE).dec.runAt n
        (pairEncode (pairEncode (List.ofFn k₁) (List.ofFn k₂)) w) rd))) =
      if validW (F (2 * n) k₂) w = true then decL (F n k₁) w
      else List.replicate (n + 1) false := by
  revert rd
  rw [ccaScheme_dec]
  intro rd
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, ccaDecFun_eq, ccaDecOK_eq]
  simp only [NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate]
  have htag : ∀ (hr : (pairFstD w).length = n) (hc : (pairFstD (pairSndD w)).length = n),
      E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
        tagL (F (2 * n) k₂) (wR w) (wC w) := by
    intro hr hc
    have he : pairFstD w ++ pairFstD (pairSndD w) =
        List.ofFn (pairV n (pairFstD w) (pairFstD (pairSndD w))) := by
      rw [pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, hr, hc]; omega)]
    rw [he, hFE, tagL_eq, wR_eq, wC_eq]
  by_cases hv : validW (F (2 * n) k₂) w = true
  · rw [if_pos hv]
    have hv' := hv
    rw [validW_eq, Bool.and_eq_true, wfW_eq, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq, decide_eq_true_eq] at hv'
    obtain ⟨⟨hr, hc⟩, ht⟩ := hv'
    rw [wR_eq] at hr
    rw [wC_eq] at hc
    have hok : (decide ((pairFstD w).length = n) && decide ((pairFstD (pairSndD w)).length = n) &&
        decide (E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
          pairSndD (pairSndD w))) = true := by
      rw [htag hr hc, ← wT_eq, ← ht]
      simp [hr, hc]
    rw [if_pos hok]
    have hk : pairFstD w = List.ofFn (padFin n (pairFstD w)) := (ofFn_padFin_of_length hr).symm
    have hlen : (List.zipWith xor (pairFstD (pairSndD w))
        (List.ofFn (F n k₁ (padFin n (pairFstD w))))).length = n := by
      rw [List.length_zipWith, List.length_ofFn, hc, Nat.min_self]
    have hdec : List.zipWith xor (pairFstD (pairSndD w))
        (List.ofFn (F n k₁ (padFin n (pairFstD w)))) =
        List.ofFn (padFin n (List.zipWith xor (pairFstD (pairSndD w))
          (List.ofFn (F n k₁ (padFin n (pairFstD w)))))) := (ofFn_padFin_of_length hlen).symm
    conv_lhs => rw [hk, hFE, hdec, decodeFin_ofFn, FixedLengthScheme.decAnswer_some]
    rw [List.ofFn_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [← hdec, decL_eq, wC_eq, wR_eq]
  · rw [if_neg hv]
    have hnok : (decide ((pairFstD w).length = n) && decide ((pairFstD (pairSndD w)).length = n) &&
        decide (E (pairEncode (List.ofFn k₂) (pairFstD w ++ pairFstD (pairSndD w))) =
          pairSndD (pairSndD w))) = false := by
      by_contra hc'
      rw [Bool.not_eq_false, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        decide_eq_true_eq, decide_eq_true_eq] at hc'
      obtain ⟨⟨hr, hc⟩, ht⟩ := hc'
      apply hv
      rw [validW_eq, wfW_eq, wR_eq, wC_eq, hr, hc, wT_eq, ← ht, htag hr hc, wR_eq, wC_eq]
      simp
    rw [if_neg (by rw [hnok]; exact Bool.false_ne_true), decodeFin_eq,
      dif_neg (by rw [List.length_cons, List.length_replicate]; omega),
      FixedLengthScheme.decAnswer_none, ofFn_zeroBits]

/-- **The CCA2 experiment of `π′` is the experiment with `f_{k₁}` and `f_{k₂}`:**
`Pr[IND_b = 1] = 𝔼_{k₁} 𝔼_{k₂} ettAcc (F n k₁) (F (2n) k₂) false b A Q`, on the reduction's lengths.

**Proof sketch.** `ETTGame.accept_indGame_eq` with the key split (`ccaKeyEq`, `cca_gen_runAt`), the
nonce (`ccaNonceEq`) and the readers `ofFn_cca_encryptAt`, `ofFn_cca_decAnswer`; the key coins are
uniform pairs (`expect_sample_equiv`, `expect_sample_prod`), and the lengths are the reduction's
(`cca_inLens`, `cca_outLens`, `cca_ctLen_eval`, `expect_ettImpl_transport`). -/
private theorem accept_cca_indGame (A : NUPPT) (Q : ℕ) (b : Bool) (n : ℕ) :
    accept ((ccaScheme F E hE hFE).indGame .cca2 A Q b n) =
      expect (sample (Fin n → Bool)) fun k₁ => expect (sample (Fin (2 * n) → Bool)) fun k₂ =>
        ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
          (F n k₁) (F (2 * n) k₂) false b A Q := by
  rw [accept_indGame_eq (ccaScheme F E hE hFE) b n A Q (cca_ctLen_eval F E hE hFE n)
      (fun rg => F n (ccaKeyEq F E hE hFE n rg).1)
      (fun rg => F (2 * n) (ccaKeyEq F E hE hFE n rg).2) (ccaNonceEq F E hE hFE n)
      (fun rg m re => by rw [cca_gen_runAt]; exact ofFn_cca_encryptAt F E hE hFE n _ _ m re)
      (fun rg w rd => by rw [cca_gen_runAt]; exact ofFn_cca_decAnswer F E hE hFE n _ _ w rd),
    ← expect_sample_equiv (ccaKeyEq F E hE hFE n).symm, ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun k₁ => congrArg _ (funext fun k₂ => ?_))
  simp only [Equiv.apply_symm_apply]
  rw [ettAcc_eq]
  refine congrArg _ (funext fun r => ?_)
  exact expect_ettImpl_transport n _ _ false b (cca_inLens F E hE hFE n)
    (cca_outLens F E hE hFE n) (by rw [cca_ctLen_eval, ettCt_eval]) A Q r

/-- **Step 1: the tag key becomes a random function** [PS10, Thm 170.4, proof]. For a machine
adversary `A` with budget `q` and a bit `b`, there is a PRF distinguisher `D` such that at every
`n`, `|Pr[IND_b = 1] − 𝔼_{k₁} 𝔼_R ettAcc (F n k₁) R false b A (q n)|` is the PRF advantage of `D`
at parameter `2n` with budget `q(2n)`.

**Proof sketch.** `accept_cca_indGame` and `ETTGame.exists_tagStep`. -/
private theorem cca_tag_step (A : NUPPT) (q : PolyExpr) (b : Bool) :
    ∃ D : NUPPT, ∀ n : ℕ,
      |accept ((ccaScheme F E hE hFE).indGame .cca2 A (q.eval n) b n) -
          expect (sample (Fin n → Bool)) (fun k₁ =>
            expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
              ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
                (F n k₁) R false b A (q.eval n))| =
        prfAdv (F (2 * n)) (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) := by
  obtain ⟨D, hD⟩ := exists_tagStep F E hE hFE A q b
  exact ⟨D, fun n => by rw [accept_cca_indGame, hD n]⟩

/-- **Step 2: fresh decryption queries are rejected** [PS10, Thm 170.4, proof]. For `n > 0`, the
experiments with a random tag function without and with the rejection of fresh pairs, averaged
over the key `k₁`, differ by at most `q(n) / 2^{2n}`.

**Proof sketch.** `ETTGame.abs_ettAcc_rej_sub_le` for each `k₁` (the ciphertexts have
`6n + 4 = ettCt(n)` bits and the challenge queries `2n`), averaged over `k₁`
(`abs_expect_sub_le`). -/
private theorem cca_rej_step (A : NUPPT) (Q : ℕ) (b : Bool) (n : ℕ) (hn : 0 < n) :
    |expect (sample (Fin n → Bool)) (fun k₁ =>
          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
              (F n k₁) R false b A Q) -
        expect (sample (Fin n → Bool)) (fun k₁ =>
          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
              (F n k₁) R true b A Q)| ≤ Q * ((2 : ℝ) ^ (2 * n))⁻¹ :=
  abs_expect_sub_le _ fun k₁ => abs_ettAcc_rej_sub_le _ _ _ n (F n k₁) b hn (ettCt_eval n)
    (by show (ettDin 2).eval n = n + n; rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
    A Q

end Proof

/-- **Theorem 170.4: `π′` is CCA2-secure** [PS10, Theorem 170.4] when `F` is a pseudorandom
function family.

**Proof sketch** (the source's, made explicit).
1. Replace `f_{k₂}` by a random function `RF` on `2n` bits: by PRF security at parameter `2n`,
   the advantage changes by a negligible amount. The reduction samples `k₁` itself and answers
   `Enc′` and `Dec′` with its oracle in place of `f_{k₂}`. T2
   (`Games.exists_interactiveHandlerMachine`) implements the forwarding handler with `k₁`
   in its seed, the input-free companion supplies its machine input, and T4
   (`Games.exists_toOracleAdversary_of_bitCodec`) provides the oracle adversary at length
   `2n`.
2. For positive `n`, call a `Dec′` query `(r, c₁, t)` *fresh* if `(r, c₁)` is not the
   ciphertext part of an earlier `Enc′` or challenge answer. Compare with a game that always
   rejects fresh-pair queries. Couple both games with the same tapes and `RF`: they agree until
   the first fresh-pair query with a valid tag. In the always-reject game, prior rejected guesses
   reveal no value of `RF` at such a pair. Each guess therefore hits that unrevealed uniform
   `2n`-bit value with probability at most `2^{-2n}`, even if the pair was queried before. The union bound
   gives a first-discrepancy probability at most `q(n)/2^{2n}` in each bit-game. This does not
   assert the same conditional probability after failed guesses in the original game.
   A nonfresh valid-tag query is an earlier answer itself: canonical parsing and the tag's
   dependence on `(r, c₁)` make it the refused challenge or an encryption of a chosen message.
3. The always-reject game is simulated by a CPA adversary against the §3.9 scheme under `k₁`:
   `Enc′` answers come from the CPA encryption oracle, tagged by a lazily sampled `RF`; `Dec′`
   answers come from the table of earlier answers, or are `⊥`. Up to fixed constant factors
   when combining the two bit-games, the advantage is bounded by the CPA advantage
   (`prfFixedScheme_cpa`), the first-discrepancy term `q(n)/2^{2n}`, and the PRF advantage.
   Each is negligible; the zero-parameter behavior described above changes no asymptotic claim.

The source's simulator tags with fresh uniform strings rather than a lazily sampled `RF`. The two
differ only when two answers share `(r, c₁)`, a collision of the `n`-bit `r`, of probability at
most `q(n)²/2^n`. -/
theorem ccaScheme_cca2 (hF : PRF F) : (ccaScheme F E hE hFE).INDSecure .cca2 := by
  sorry

end TCSlib.Cryptography.Composability
