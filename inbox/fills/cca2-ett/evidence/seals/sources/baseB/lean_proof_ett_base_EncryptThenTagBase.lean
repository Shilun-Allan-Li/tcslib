/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import Mathlib.Tactic.Simps.Basic
/- DLC-SEAL lean_proof_ett_base_EncryptThenTagBase: whole-file closure seal of `lean_proof/ett/base/EncryptThenTagBase.lean`. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL lean_proof_ett_base_EncryptThenTagBase: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


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
