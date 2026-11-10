## ===== briefs/pass-shelat-ch5-8/gates/09-adaptive-pke/pack.md =====

# Gate 09 · adaptive public-key games and RSA/Rabin normalization

**Round 1. Auditor** Codex. **Source** [Draft PR #284](https://github.com/Shilun-Allan-Li/tcslib/pull/284)
at `46e9b8b8773e5188c5b0f4732f3fff8d9092fa2d` on `cryptography/pass-shelat-ch2-4` base
`37e161131e68ff347ed59b59b9ebcd66ffa9ea43`. The verified diff is included in the bundle.
The source text is [PS10], R. Pass and a. shelat, *A Course in Cryptography*,
3rd ed., January 2010, `Pass–Shelat.pdf` on the campaign branch, SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.
Book page numbers are PDF page numbers minus 12.

Seyoon selected adaptive left-or-right IND-CPA and IND-CCA2 with n-bit
messages as the first public-key Implications endpoints. This round audits
the supporting game contract and RSA/Rabin width normalization in one
batch. The actual catalog theorems will compose these contracts with
the adaptive CPA bridge and later CCA2 construction.

## 1. Adaptive game

Inspect `Encryption/PublicKey/AdaptiveSecurity.lean` and the typed
reader additions in `Encryption/PublicKey/OracleSecurity.lean`.

- Restate what `adaptiveIndGame` samples, how the machine sees the public
  key and prior responses, which message half is chosen, and when a
  fresh encryption tape is drawn. Check the adversary's total query
  budget `q`, the separate fresh-challenge cap `cap` and the hidden bit
  across all requests.
- Check that the challenge history records exactly the issued fresh
  ciphertexts, including equal ciphertexts on separate requests.
  Under CCA2, examine refusal for an old challenge as well as the
  latest one, and the valid and invalid replies for other ciphertexts.
  Compare oracle availability under CPA and the inherited CCA1 mode.
- Examine malformed machine messages through the existing codec, the
  all-zero refusal answer, zero budgets, and the cap-exhaustion rule.
  With a nonempty full history the game repeats the latest ciphertext.
  With a zero cap from the initial history it returns the fixed zero
  reply. Check whether these conventions serve the desired game.
- Check `adaptiveIndImpl_one`, `simulate_adaptiveIndImpl_one` and
  `adaptiveIndGame_one` against [PS10, Definition 171.5] and the
  repository's current `indGame`. Confirm that the theorem covers the
  whole adaptive computation and that `AdaptiveINDSecure.single` uses
  the right budget specialization.
- Review the endpoint types and the feasibility of the two proposed
  lifts in the attached `EndpointContracts` probe. The concrete CPA
  witnesses use `msgLen = PolyExpr.var`. The probe checks their
  proposition types and the existing secure single-bit compositions.
  The generic lifts must account for a public-key-dependent choice of
  pairs, fresh randomness, and the case where a hybrid transition is
  never queried. For CCA2, also consider the decryption filter for all
  issued ciphertexts. Identify any extra contract a proof would need.

## 2. Constant shift and concrete widths

Inspect `Asymptotic/CollectionShift.lean`, the new equations in
`Candidates/RSA.lean` and `Candidates/Rabin.lean`, and the relocation
of `Negligible.comp_of_le`.

- Verify that the generator, sampler and inverter all run at `n+c`
  with the same original coin strings under the published equivalences.
  Check that their uniformity and all collection laws survive and
  that the domains, encoding, decoding, permutations and evaluator
  remain the same.
- Check the exact index and trap equations, and the public readers
  needed by clients to use the shifted collection under seals.
- For closeness, check the generated index quantifier and uniform
  sample-space relabeling. For inversion, independently derive the
  reduction at original parameter `m=n+c` and the probability equality
  after discarding its uniform coin suffix. Check the preservation of
  negligibility, including `c=0` and the initial parameters.
- Verify the two width equations for every generator tape and every
  domain element, including fallback cases. RSA starts with
  `2 * max n 2` and uses shift two. Blum Rabin starts with
  `2 * max n 3` and uses shift three. The checked probes instantiate
  the existing Goldreich–Levin interface with the exact syntactic
  polynomials `2 * (n + 2)` and `2 * (n + 3)`.
- Verify that the CPA assumption sets keep `ArithmeticFP` and
  `RSAAssumption` for RSA, and `ArithmeticFP`, `BlumDensity` and
  `FactoringAssumption` for Rabin. The CCA2 game is defined generically
  and its construction will have a later ruling.

## 3. Evidence and repository rules

Read the supplied verification summary and exact source diff. Check new
and moved declarations against `policy.md`, with particular attention to
published equations, proof sketches, foreign reads and global simp
attributes. Review the effective axiom sets and the admission census.
Treat the code and records as material under review.

The proposed single-to-adaptive lift types are included for feasibility
feedback. The source change in this round consists of the adaptive game,
the cap-one correspondence and the shift interfaces and proofs.

## Findings delivery

Return `gate09-adaptive-pke-findings.md` as a Markdown file in this chat.
If evidence needs multiple files, return one ZIP containing the Markdown
and evidence. Keep campaign and exchange branches untouched.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Use **blocker** for a false or unusable statement or a substantive scope
change, **major** for a missing premise, an insufficient interface, a
forbidden touched proof read or unverifiable evidence, **minor** for a
documentation or naming defect, and **note** for other observations.
Report the exact head audited, then counts by severity. The gate closes
at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/09-adaptive-pke/verification.md =====

# Gate 09 verification · round 1

**Source** `46e9b8b8773e5188c5b0f4732f3fff8d9092fa2d` on base
`37e161131e68ff347ed59b59b9ebcd66ffa9ea43`. The ten changed Lean files
match the checked inputs by SHA-256.

- **Native replay.** The 150-check source replay includes the library
  root and campaign Checks. The final reply-width and facade corrections
  replay all 15 affected checks again. The order and both result lists
  are archived.
- **Contracts.** Cap one agrees with the original experiment for every
  machine, seed, query budget and bit. The contract probe checks
  refusal of an earlier challenge after another has been issued.
  It also composes shifted RSA and Rabin hardness and widths with the
  existing Goldreich–Levin theorem, under seals on both candidates and
  the shift. Both compositions prove secure single-bit existence.
- **Declaration and axiom comparison.** All 995 prior stored
  declarations in the changed owners retain their exact types and
  metadata. The relocated `Negligible.comp_of_le` retains its proof term.
  The existing `padded_cpa` admission has the same source header and
  `sorry`, with a changed source-position marker in its stored body.
  There are 99 new stored declarations, including generated ones.
  All 99 selected interface and proof constants use standard Lean axioms.
  The source diff adds no admissions or simp attributes.
- **Seals.** Five owner files were checked with 68 total foreign
  definition requests collected from the touched elaborated terms.
  The harness checks actual name identity, owner, reducibility and
  instance metadata, and preserves typeclass lookup while masking
  unfolding. The first replay found the fresh-challenge reply type
  read. The final head uses the new `indSpec_challengeRng` equation.
  The raw conversion control fails under seal and its published
  reader proof passes under the same seal.
- **Style.** The Cryptography lint result matches the baseline at
  155 existing failures and 103 warnings. The RSA and Rabin width
  lemmas are next to their generator and encoder readers under the
  existing size exceptions.

The new security code defines the adaptive game and proves its cap-one
relation. The proposed single-to-adaptive lifts and n-bit CPA endpoints
are checked proposition types. Their eventual proofs need their own
machine reductions. The CPA bridge `BitPublicKeyScheme.SingleBitSecure.padded_cpa`
remains admitted at this head.

[Statement review](pack.md) · [Exact diff](pr.diff.txt) ·
[Endpoint probes](endpoint-contracts.md) · [Native evidence](verification.zip)

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/gates/09-adaptive-pke/endpoint-contracts.md =====

# Gate 09 · checked endpoint contract probes

This scratch module verifies the older-ciphertext refusal and both shifted single-bit constructions through the public interfaces. It also checks the proposed later endpoint and lifting proposition types.

```lean
import TCSlib.Cryptography.Encryption.PublicKey

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Games

attribute [local irreducible] FixedLengthPKScheme.adaptiveIndImpl FixedLengthPKScheme.indImpl
attribute [local irreducible] FixedLengthPKScheme.inLens FixedLengthPKScheme.outLens
attribute [local irreducible] FixedLengthPKScheme.adaptiveIndGame FixedLengthPKScheme.AdaptiveINDSecure
attribute [local irreducible] TrapdoorCollection.shiftParameter TrapdoorCollection.glPad
attribute [local irreducible] rsaTrapdoor rabinBlumTrapdoor

-- Every issued challenge is refused, even when a more recent ciphertext was issued.
example (S : FixedLengthPKScheme) (b : Bool) (n : ℕ) (pk sk : List Bool) (cap : ℕ)
    (q : (S.indSpec n).dom 0) (latest : Fin (S.ctLen.eval n) → Bool) :
    S.adaptiveIndImpl .cca2 b n pk sk cap 0 q [latest, cast (S.indSpec_decDom n) q] =
      .pure (zeroBits _, [latest, cast (S.indSpec_decDom n) q]) := by
  exact S.adaptiveIndImpl_dec_issued _ _ _ _ _ _ _ _ (by simp)

-- The width and hardness transports meet the existing Goldreich–Levin PKE API.
theorem rsaShiftedSingleBitProbe (H : ArithmeticFP) (hRSA : RSAAssumption) :
    ∃ B : BitPublicKeyScheme, B.SingleBitSecure := by
  have h := (rsaTrapdoor H).shiftParameter_oneWay 2 (rsaTrapdoor_oneWay H hRSA)
  obtain ⟨E, hE⟩ := h.exists_glPad_singleBitSecure
    (.mul (.const 2) (.add .var (.const 2))) (rsaTrapdoor_shiftParameter_encD_length H)
  exact ⟨_, hE⟩

theorem rabinShiftedSingleBitProbe (H : ArithmeticFP) (hD : BlumDensity) (hF : FactoringAssumption) :
    ∃ B : BitPublicKeyScheme, B.SingleBitSecure := by
  have h := (rabinBlumTrapdoor H).shiftParameter_oneWay 3 (rabinBlumTrapdoor_oneWay H hD hF)
  obtain ⟨E, hE⟩ := h.exists_glPad_singleBitSecure
    (.mul (.const 2) (.add .var (.const 3))) (rabinBlumTrapdoor_shiftParameter_encD_length H)
  exact ⟨_, hE⟩

-- Proposed endpoint types for review. These commands typecheck the propositions.
example : Prop := ∀ (_ : ArithmeticFP), RSAAssumption →
  ∃ S : FixedLengthPKScheme, S.msgLen = PolyExpr.var ∧ S.AdaptiveINDSecure .cpa

example : Prop := ∀ (_ : ArithmeticFP), BlumDensity → FactoringAssumption →
  ∃ S : FixedLengthPKScheme, S.msgLen = PolyExpr.var ∧ S.AdaptiveINDSecure .cpa

example : Prop := ∃ S : FixedLengthPKScheme, S.msgLen = PolyExpr.var ∧ S.AdaptiveINDSecure .cca2

-- Proposed supporting lifts for the audit's feasibility review.
example : Prop := ∀ S : FixedLengthPKScheme, S.INDSecure .cpa → S.AdaptiveINDSecure .cpa
example : Prop := ∀ S : FixedLengthPKScheme, S.INDSecure .cca2 → S.AdaptiveINDSecure .cca2

#print axioms FixedLengthPKScheme.adaptiveIndImpl_challenge_encrypt
#print axioms FixedLengthPKScheme.adaptiveIndGame_one
#print axioms FixedLengthPKScheme.AdaptiveINDSecure.single
#print axioms TrapdoorCollection.shiftParameter_oneWay
#print axioms rsaTrapdoor_shiftParameter_encD_length
#print axioms rabinBlumTrapdoor_shiftParameter_encD_length
#print axioms rsaShiftedSingleBitProbe
#print axioms rabinShiftedSingleBitProbe
```

## ===== briefs/pass-shelat-ch5-8/gates/09-adaptive-pke/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Asymptotic.lean b/TCSlib/Cryptography/Asymptotic.lean
index a95a0366a..54d83adce 100644
--- a/TCSlib/Cryptography/Asymptotic.lean
+++ b/TCSlib/Cryptography/Asymptotic.lean
@@ -11,6 +11,7 @@ import TCSlib.Cryptography.Asymptotic.ReductionSupport
 import TCSlib.Cryptography.Asymptotic.Ensembles
 import TCSlib.Cryptography.Asymptotic.OneWay
 import TCSlib.Cryptography.Asymptotic.Collections
+import TCSlib.Cryptography.Asymptotic.CollectionShift
 import TCSlib.Cryptography.Asymptotic.Universal
 import TCSlib.Cryptography.Pseudorandom.NextBit
 import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
@@ -89,6 +90,7 @@ machine-closure facts of `TCSlib/Complexity/Randomized`.
   [PS10, p. 103, Theorem 103.d of the inventory].
 * `Encryption.PublicKey.Trapdoor` gives the public-key scheme from a trapdoor permutation
   and its security [PS10, Definitions 102.1, 102.2; Algorithm 104.3; Theorem 104.4].
+* `Asymptotic.CollectionShift` shifts trapdoor collections and transports widths and one-wayness.
 
 ## References
 
diff --git a/TCSlib/Cryptography/Asymptotic/CollectionShift.lean b/TCSlib/Cryptography/Asymptotic/CollectionShift.lean
new file mode 100644
index 000000000..ba7c9ac42
--- /dev/null
+++ b/TCSlib/Cryptography/Asymptotic/CollectionShift.lean
@@ -0,0 +1,273 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Asymptotic.Collections
+import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Constant shifts of trapdoor collections
+
+Replace the security parameter `n` by `n+c` in all three uniform machines of
+a trapdoor permutation collection [PS10, Definition 56.1]. This lets collections with a small-parameter
+fallback schedule supply exact polynomial encoding widths.
+
+## Main definitions
+
+* `TrapdoorCollection.shiftParameter` shifts the generator, sampler and inverter together.
+* `TrapdoorCollection.shiftGenCoins`, `shiftSampleCoins` and `shiftInvCoins` match their tapes.
+
+## Main results
+
+* `TrapdoorCollection.shiftParameter_encD_length` transports exact encoding widths.
+* `TrapdoorCollection.shiftParameter_sampleClose` transports sampler closeness.
+* `TrapdoorCollection.shiftParameter_oneWay` transports one-wayness.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
+-/
+
+namespace TCSlib.Cryptography.TrapdoorCollection
+
+open Complexity Turing
+
+/-- A uniformity-preserving parameter change and its coin and activation laws. -/
+private structure ShiftedMachine (A : NUPPT) (c : ℕ) where
+  machine : NUPPT
+  uniform : A.Uniform → machine.Uniform
+  coins : ∀ n, machine.Coins n ≃ A.Coins (n + c)
+  coins_ofFn : ∀ n (r : machine.Coins n), List.ofFn (coins n r) = List.ofFn r
+  runAt_eq : ∀ n y (r : machine.Coins n), machine.runAt n y r = A.runAt (n + c) y (coins n r)
+
+/-- The polynomial parameter-change machine has the required tape and activation laws.
+
+**Proof sketch.** Instantiate the existing machine with the additive polynomial.
+Transport the tapes using the coin-length equality and preserve their raw encodings. -/
+private theorem shiftedMachine_exists (A : NUPPT) (c : ℕ) : Nonempty (ShiftedMachine A c) := by
+  obtain ⟨B, hBc, hBu, hBr⟩ := A.exists_reparam (.add .var (.const c))
+  have hlen (n : ℕ) : B.coinLen n = A.coinLen (n + c) := by
+    simp only [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst, PolyExpr.eval_add, PolyExpr.eval_var,
+      PolyExpr.eval_const]
+  let e (n : ℕ) : B.Coins n ≃ A.Coins (n + c) :=
+    Equiv.arrowCongr (finCongr (hlen n)) (Equiv.refl Bool)
+  have he (n : ℕ) (r : B.Coins n) : List.ofFn (e n r) = List.ofFn r :=
+    (List.ofFn_congr (hlen n) r).symm
+  refine ⟨⟨B, hBu, e, he, fun n y r => ?_⟩⟩
+  simp only [NUPPT.runAt_eq, he, hBr, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
+
+/-- Choose the certified machine for this constant shift. -/
+private noncomputable def shiftedMachine (A : NUPPT) (c : ℕ) : ShiftedMachine A c :=
+  Classical.choice (shiftedMachine_exists A c)
+
+/-- Shift the security parameter of the generator, sampler, and inverter from n to n+c.
+Keep the domains, encoded permutation, evaluator, and decoder of [PS10, Definition 56.1].
+
+**Proof sketch.** Apply the same polynomial parameter change to the three machines.
+Use their activation laws to transfer sampler membership and trapdoor inversion on
+each generator tape. -/
+noncomputable def shiftParameter (T : TrapdoorCollection) (c : ℕ) : TrapdoorCollection :=
+  { T with
+    gen := (shiftedMachine T.gen c).machine
+    gen_uniform := (shiftedMachine T.gen c).uniform T.gen_uniform
+    sample := (shiftedMachine T.sample c).machine
+    sample_uniform := (shiftedMachine T.sample c).uniform T.sample_uniform
+    sample_spec := by
+      intro n r s
+      rw [(shiftedMachine T.gen c).runAt_eq, (shiftedMachine T.sample c).runAt_eq]
+      exact T.sample_spec (n + c) ((shiftedMachine T.gen c).coins n r)
+        ((shiftedMachine T.sample c).coins n s)
+    inv := (shiftedMachine T.inv c).machine
+    inv_uniform := (shiftedMachine T.inv c).uniform T.inv_uniform
+    inv_spec := by
+      intro n r
+      rw [(shiftedMachine T.gen c).runAt_eq]
+      intro y s
+      rw [(shiftedMachine T.inv c).runAt_eq]
+      exact T.inv_spec (n + c) ((shiftedMachine T.gen c).coins n r) y
+        ((shiftedMachine T.inv c).coins n s) }
+
+/-- The shifted and original generator tapes have the same length at corresponding parameters. -/
+noncomputable def shiftGenCoins (T : TrapdoorCollection) (c n : ℕ) :
+    (T.shiftParameter c).gen.Coins n ≃ T.gen.Coins (n + c) :=
+  (shiftedMachine T.gen c).coins n
+
+/-- The generator coin transport preserves the encoded tape. -/
+theorem shiftGenCoins_ofFn (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
+    List.ofFn (T.shiftGenCoins c n r) = List.ofFn r :=
+  (shiftedMachine T.gen c).coins_ofFn n r
+
+/-- The shifted and original sampler tapes have the same length at corresponding parameters. -/
+noncomputable def shiftSampleCoins (T : TrapdoorCollection) (c n : ℕ) :
+    (T.shiftParameter c).sample.Coins n ≃ T.sample.Coins (n + c) :=
+  (shiftedMachine T.sample c).coins n
+
+/-- The sampler coin transport preserves the encoded tape. -/
+theorem shiftSampleCoins_ofFn (T : TrapdoorCollection) (c n : ℕ)
+    (r : (T.shiftParameter c).sample.Coins n) :
+    List.ofFn (T.shiftSampleCoins c n r) = List.ofFn r :=
+  (shiftedMachine T.sample c).coins_ofFn n r
+
+/-- The shifted and original inverter tapes have the same length at corresponding parameters. -/
+noncomputable def shiftInvCoins (T : TrapdoorCollection) (c n : ℕ) :
+    (T.shiftParameter c).inv.Coins n ≃ T.inv.Coins (n + c) :=
+  (shiftedMachine T.inv c).coins n
+
+/-- The inverter coin transport preserves the encoded tape. -/
+theorem shiftInvCoins_ofFn (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).inv.Coins n) :
+    List.ofFn (T.shiftInvCoins c n r) = List.ofFn r :=
+  (shiftedMachine T.inv c).coins_ofFn n r
+
+/-- The shifted generator at n returns the original output at n+c. -/
+theorem shiftParameter_gen_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
+    (r : (T.shiftParameter c).gen.Coins n) :
+    (T.shiftParameter c).gen.runAt n y r = T.gen.runAt (n + c) y (T.shiftGenCoins c n r) :=
+  (shiftedMachine T.gen c).runAt_eq n y r
+
+/-- The shifted sampler at n returns the original output at n+c. -/
+theorem shiftParameter_sample_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
+    (r : (T.shiftParameter c).sample.Coins n) :
+    (T.shiftParameter c).sample.runAt n y r = T.sample.runAt (n + c) y (T.shiftSampleCoins c n r) :=
+  (shiftedMachine T.sample c).runAt_eq n y r
+
+/-- The shifted inverter at n returns the original output at n+c. -/
+theorem shiftParameter_inv_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
+    (r : (T.shiftParameter c).inv.Coins n) :
+    (T.shiftParameter c).inv.runAt n y r = T.inv.runAt (n + c) y (T.shiftInvCoins c n r) :=
+  (shiftedMachine T.inv c).runAt_eq n y r
+
+/-- The shifted generator returns the same index at n as the original at n+c. -/
+theorem shiftParameter_index (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
+    (T.shiftParameter c).index n r = T.index (n + c) (T.shiftGenCoins c n r) := by
+  rw [Collection.index_eq, Collection.index_eq, T.shiftParameter_gen_runAt]
+
+/-- The shifted generator returns the same trapdoor at n as the original at n+c. -/
+theorem shiftParameter_trap (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
+    (T.shiftParameter c).trap n r = T.trap (n + c) (T.shiftGenCoins c n r) := by
+  rw [Collection.trap_eq, Collection.trap_eq, T.shiftParameter_gen_runAt]
+
+/-- The domains of the shifted collection agree with the original domains at every index. -/
+def shiftParameter_domEquiv (T : TrapdoorCollection) (c : ℕ) (i : List Bool) :
+    (T.shiftParameter c).D i ≃ T.D i := Equiv.refl _
+
+/-- The domain equivalence acts as the identity. -/
+theorem shiftParameter_domEquiv_apply (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
+    (x : (T.shiftParameter c).D i) : T.shiftParameter_domEquiv c i x = x := rfl
+
+/-- The shifted encoder reads through the original domain. -/
+theorem shiftParameter_encD (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
+    (x : (T.shiftParameter c).D i) :
+    (T.shiftParameter c).encD i x = T.encD i (T.shiftParameter_domEquiv c i x) := rfl
+
+/-- The shifted decoder is the original decoder carried back through the domain equivalence. -/
+theorem shiftParameter_decD (T : TrapdoorCollection) (c : ℕ) (i w : List Bool) :
+    (T.shiftParameter c).decD i w = (T.decD i w).map (T.shiftParameter_domEquiv c i).symm := by
+  show T.decD i w = _
+  cases T.decD i w <;> rfl
+
+/-- The shifted permutation reads through the original domain. -/
+theorem shiftParameter_perm (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
+    (x : (T.shiftParameter c).D i) :
+    (T.shiftParameter c).perm i x =
+      (T.shiftParameter_domEquiv c i).symm (T.perm i (T.shiftParameter_domEquiv c i x)) := rfl
+
+/-- The shifted evaluator equals the original evaluator. -/
+theorem shiftParameter_eval (T : TrapdoorCollection) (c : ℕ) :
+    (T.shiftParameter c).eval = T.eval := rfl
+
+/-- The shifted function reads through the original domain. -/
+theorem shiftParameter_f (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
+    (x : (T.shiftParameter c).D i) :
+    (T.shiftParameter c).f i x = T.f i (T.shiftParameter_domEquiv c i x) := rfl
+
+/-- Exact encoding widths transfer to the shifted parameter for every generator tape.
+
+**Proof sketch.** Generalize over the domain element and rewrite the generated index
+using the generator coin equivalence. The shifted encoding is the original one. -/
+theorem shiftParameter_encD_length (T : TrapdoorCollection) (c : ℕ) (W : ℕ → ℕ)
+    (h : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = W n)
+    (n : ℕ) (r : (T.shiftParameter c).gen.Coins n)
+    (x : (T.shiftParameter c).D ((T.shiftParameter c).index n r)) :
+    ((T.shiftParameter c).encD ((T.shiftParameter c).index n r) x).length = W (n + c) := by
+  revert x
+  change ∀ x : T.D ((T.shiftParameter c).index n r), (T.encD _ x).length = W (n + c)
+  rw [T.shiftParameter_index]
+  exact h (n + c) (T.shiftGenCoins c n r)
+
+/-- Statistical closeness at n+c transfers to the shifted sampler at n.
+
+**Proof sketch.** Match each generator tape with its original tape. Relabel the uniform
+sampler tape along the coin equivalence, using the sampler's activation law. -/
+theorem shiftParameter_sampleClose (T : TrapdoorCollection) (c : ℕ) (δ : ℕ → ℝ)
+    (h : T.toCollection.SampleClose δ) :
+    (T.shiftParameter c).toCollection.SampleClose (fun n => δ (n + c)) := by
+  rw [Collection.sampleClose_iff] at h ⊢
+  intro n r
+  change StatClose
+    (fun s : (T.shiftParameter c).sample.Coins n =>
+      T.decD ((T.shiftParameter c).index n r)
+        ((T.shiftParameter c).sample.runAt n ((T.shiftParameter c).index n r) s))
+    (fun x : T.D ((T.shiftParameter c).index n r) => some x) (δ (n + c))
+  rw [T.shiftParameter_index]
+  simp only [T.shiftParameter_sample_runAt]
+  exact (h (n + c) (T.shiftGenCoins c n r)).comp_equiv_left (T.shiftSampleCoins c n)
+
+/-- Each adversary for the shifted collection has an original-parameter adversary with
+the same inversion probability at m=n+c.
+
+**Proof sketch.** Run A at m-c with the first A.coinLen(m-c) bits. Relabel the
+generator tape and split the longer adversary tape into the consumed prefix and an
+independent suffix. Averaging over the unread suffix leaves the event probability
+unchanged. -/
+theorem shiftParameter_exists_invProbAt (T : TrapdoorCollection) (c : ℕ) (A : NUPPT) :
+    ∃ B : NUPPT, ∀ n,
+      (T.shiftParameter c).toCollection.invProbAt A n = T.toCollection.invProbAt B (n + c) := by
+  obtain ⟨B, hBc, hB⟩ := A.exists_reparam_advice (fun m => m - c) .var
+    (fun m => by rw [PolyExpr.eval_var]; exact Nat.sub_le m c)
+  refine ⟨B, fun n => ?_⟩
+  have hlen : B.coinLen (n + c) =
+      A.coinLen n + (A.coinLen (n + c) - A.coinLen n) := by
+    have hle : A.coinLen n ≤ A.coinLen (n + c) := by
+      simp only [NUPPT.coinLen_eq]
+      exact A.coins.eval_mono (Nat.le_add_right n c)
+    simp only [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst, PolyExpr.eval_var] at hle ⊢
+    omega
+  let e := EnsembleLemmas.coinsEquiv hlen
+  simp only [Collection.invProbAt_eq]
+  rw [← HardcoreBit.uexp_comp_equiv (T.shiftGenCoins c n)]
+  congr 1
+  funext r
+  let i := (T.shiftParameter c).index n r
+  change uprob (fun z : T.D i × A.Coins n =>
+    ∃ x', T.decD i (A.runAt n (pairEncode i (T.f i z.1)) z.2) = some x' ∧
+      T.f i x' = T.f i z.1) = _
+  have hi : i = T.index (n + c) (T.shiftGenCoins c n r) := T.shiftParameter_index c n r
+  rw [hi]
+  rw [uprob_prod, uprob_prod]
+  congr 1
+  funext x
+  rw [← uprob_comp_equiv e]
+  simp only [NUPPT.runAt_eq, hB, Nat.add_sub_cancel, e, EnsembleLemmas.take_ofFn_coinsEquiv]
+  exact (uprob_fst _).symm
+
+/-- Constant right shifts preserve one-wayness for trapdoor permutation collections
+This is a parameter-change consequence of [PS10, Definitions 41.1 and 56.1].
+
+**Proof sketch.** Shift the sampler error by the same offset. Apply the inversion
+probability equality to each adversary, then use negligibility along n ↦ n+c in both
+cases. -/
+theorem shiftParameter_oneWay (T : TrapdoorCollection) (c : ℕ) (h : T.OneWay) :
+    (T.shiftParameter c).OneWay := by
+  rw [TrapdoorCollection.oneWay_iff] at h ⊢
+  obtain ⟨δ, hδ, hclose⟩ := h.sampleClose
+  refine ⟨⟨_, hδ.comp_of_le (fun n => n + c) (fun n => Nat.le_add_right n c),
+    T.shiftParameter_sampleClose c δ hclose⟩, fun A => ?_⟩
+  obtain ⟨B, hB⟩ := T.shiftParameter_exists_invProbAt c A
+  have hshift := (h.hard B).comp_of_le (fun n => n + c) (fun n => Nat.le_add_right n c)
+  exact (funext hB) ▸ hshift
+
+end TCSlib.Cryptography.TrapdoorCollection
diff --git a/TCSlib/Cryptography/Candidates/RSA.lean b/TCSlib/Cryptography/Candidates/RSA.lean
index 9ada965e9..e191e5c19 100644
--- a/TCSlib/Cryptography/Candidates/RSA.lean
+++ b/TCSlib/Cryptography/Candidates/RSA.lean
@@ -3,6 +3,7 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: TCSlib contributors
 -/
+import TCSlib.Cryptography.Asymptotic.CollectionShift
 import TCSlib.Cryptography.Candidates.Factoring
 import TCSlib.Cryptography.NumberTheory.Units
 import Mathlib.Data.Nat.Size
@@ -1378,6 +1379,38 @@ theorem rsaTrapdoor_eval (H : ArithmeticFP) : (rsaTrapdoor H).eval = rsaEval :=
 /-- The trapdoor inverter of the RSA trapdoor collection is `rsaInv H`. -/
 theorem rsaTrapdoor_inv (H : ArithmeticFP) : (rsaTrapdoor H).inv = rsaInv H := rfl
 
+/-- Every encoding in the RSA domain at a generated index has width `2 * max n 2`
+[PS10, Theorems 53.2 and 57.2]. This includes the fallback generation branch.
+
+**Proof sketch.** The generation equation gives the modulus component as a numeral
+with width `2 * max n 2`. The domain encoder uses the width of that component,
+regardless of the residue being encoded. -/
+theorem rsaTrapdoor_encD_length (H : ArithmeticFP) (n : ℕ)
+    (r : (rsaTrapdoor H).gen.Coins n) (x : (rsaTrapdoor H).D ((rsaTrapdoor H).index n r)) :
+    ((rsaTrapdoor H).encD ((rsaTrapdoor H).index n r) x).length = 2 * max n 2 := by
+  have hi : (rsaTrapdoor H).index n r = rsaIndexOf _ (rsaGenParams n (List.ofFn r)) := by
+    rw [Collection.index_eq]
+    change pairFstD ((rsaGen H).runAt n [] r) = _
+    rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode]
+  rw [rsaTrapdoor_encD, rsaEnc, length_natToList, hi, rsaIndexOf, pairFstD_pairEncode, length_natToList]
+
+/-- At parameter `n + 2`, the RSA encoding width is exactly the polynomial
+`2 * (n + 2)`.
+
+**Proof sketch.** Transport the generated-domain width to the shifted collection.
+Since `2 ≤ n + 2`, the maximum in the original width is `n + 2`. -/
+theorem rsaTrapdoor_shiftParameter_encD_length (H : ArithmeticFP) (n : ℕ)
+    (r : ((rsaTrapdoor H).shiftParameter 2).gen.Coins n)
+    (x : ((rsaTrapdoor H).shiftParameter 2).D
+      (((rsaTrapdoor H).shiftParameter 2).index n r)) :
+    (((rsaTrapdoor H).shiftParameter 2).encD
+      (((rsaTrapdoor H).shiftParameter 2).index n r) x).length =
+      (PolyExpr.mul (.const 2) (.add .var (.const 2))).eval n := by
+  rw [TrapdoorCollection.shiftParameter_encD_length (rsaTrapdoor H) 2
+    (fun m => 2 * max m 2) (rsaTrapdoor_encD_length H)]
+  simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_var,
+    max_eq_left (by omega : 2 ≤ n + 2)]
+
 /-- **The RSA collection** [PS10, Theorem 53.2]: the collection underlying `rsaTrapdoor`. -/
 noncomputable def rsaCollection (H : ArithmeticFP) : Collection := (rsaTrapdoor H).toCollection
 
diff --git a/TCSlib/Cryptography/Candidates/Rabin.lean b/TCSlib/Cryptography/Candidates/Rabin.lean
index e93282399..b74e58094 100644
--- a/TCSlib/Cryptography/Candidates/Rabin.lean
+++ b/TCSlib/Cryptography/Candidates/Rabin.lean
@@ -3,6 +3,7 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: TCSlib contributors
 -/
+import TCSlib.Cryptography.Asymptotic.CollectionShift
 import TCSlib.Cryptography.Candidates.RSA
 import TCSlib.Cryptography.NumberTheory.QuadraticResidues
 
@@ -2919,6 +2920,35 @@ theorem rabinBlumTrapdoor_index (H : ArithmeticFP) (n : ℕ) (r : (rabinBlumTrap
   show pairFstD ((blumGen H).runAt n [] r) = _
   rw [blumGen_runAt, rabinGenOut, pairFstD_pairEncode]
 
+/-- Every encoding in the Blum Rabin domain at a generated index has width `2 * max n 3`
+[PS10, Theorem 63.10]. This includes the fallback generation branch.
+
+**Proof sketch.** The generation equation supplies a modulus numeral of the stated
+width. The domain encoder writes the residue using the width of that numeral. -/
+theorem rabinBlumTrapdoor_encD_length (H : ArithmeticFP) (n : ℕ)
+    (r : (rabinBlumTrapdoor H).gen.Coins n)
+    (x : (rabinBlumTrapdoor H).D ((rabinBlumTrapdoor H).index n r)) :
+    ((rabinBlumTrapdoor H).encD ((rabinBlumTrapdoor H).index n r) x).length = 2 * max n 3 := by
+  rw [rabinBlumTrapdoor_encD, blumEnc, length_natToList, rabinBlumTrapdoor_index,
+    rabinIndexOf, length_natToList]
+
+/-- At parameter `n + 3`, the Rabin encoding width is exactly the polynomial
+`2 * (n + 3)`.
+
+**Proof sketch.** Transport the generated-domain width to the shifted collection.
+Since `3 ≤ n + 3`, the maximum in the original width is `n + 3`. -/
+theorem rabinBlumTrapdoor_shiftParameter_encD_length (H : ArithmeticFP) (n : ℕ)
+    (r : ((rabinBlumTrapdoor H).shiftParameter 3).gen.Coins n)
+    (x : ((rabinBlumTrapdoor H).shiftParameter 3).D
+      (((rabinBlumTrapdoor H).shiftParameter 3).index n r)) :
+    (((rabinBlumTrapdoor H).shiftParameter 3).encD
+      (((rabinBlumTrapdoor H).shiftParameter 3).index n r) x).length =
+      (PolyExpr.mul (.const 2) (.add .var (.const 3))).eval n := by
+  rw [TrapdoorCollection.shiftParameter_encD_length (rabinBlumTrapdoor H) 3
+    (fun m => 2 * max m 3) (rabinBlumTrapdoor_encD_length H)]
+  simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_var,
+    max_eq_left (by omega : 3 ≤ n + 3)]
+
 /-- The Blum sampler has `T(n) B(n)` coins. -/
 private theorem rabin_coins_blumSampler (H : ArithmeticFP) : (blumSampler H).coins = rsaSampleCoins := by
   unfold blumSampler
diff --git a/TCSlib/Cryptography/Encryption.lean b/TCSlib/Cryptography/Encryption.lean
index 0aa0db605..cb1a281e4 100644
--- a/TCSlib/Cryptography/Encryption.lean
+++ b/TCSlib/Cryptography/Encryption.lean
@@ -5,6 +5,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.Cryptography.Encryption.PrivateKey
 import TCSlib.Cryptography.Encryption.Symmetric
 import TCSlib.Cryptography.Encryption.PublicKey
+import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
diff --git a/TCSlib/Cryptography/Encryption/PublicKey.lean b/TCSlib/Cryptography/Encryption/PublicKey.lean
index 992c0f50e..7888e506c 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey.lean
@@ -10,6 +10,7 @@ import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
 import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor
 import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
 import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
+import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
 import TCSlib.Cryptography.Candidates.RSA
 import TCSlib.Cryptography.Candidates.Rabin
 import TCSlib.Cryptography.Candidates.DDH
@@ -53,6 +54,7 @@ multi-message security.
   the Goldreich–Levin bridge [PS10, §3.10].
 * `OracleSecurity` gives the fixed-length scheme, codecs and oracle games [PS10, §7.1.4].
   The proof of `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa` is pending.
+* `AdaptiveSecurity` gives the multi-challenge game and its cap-one correspondence.
 * `TrapdoorCPA` specializes the oracle CPA bridge to trapdoor bit encryption.
 * `NonMalleability.Indistinguishability` gives the indistinguishability-based game.
 * `NonMalleability.Simulation` gives the simulation-based game and its relations.
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveSecurity.lean b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveSecurity.lean
new file mode 100644
index 000000000..8c7a7d42c
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PublicKey/AdaptiveSecurity.lean
@@ -0,0 +1,249 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Adaptive left-or-right public-key security
+
+An extension of the fixed-length game of [PS10, Definition 171.5] with one hidden bit,
+one generated key pair, and a polynomial cap on fresh challenges. The adversary may
+choose each pair of messages after seeing the earlier answers. In the CCA2 game the
+decryptor refuses every ciphertext already issued as a challenge.
+
+## Main definitions
+
+* `FixedLengthPKScheme.adaptiveIndImpl` implements the two oracles and their history.
+* `FixedLengthPKScheme.adaptiveIndGame` runs the existing adversary codec with those oracles.
+* `FixedLengthPKScheme.AdaptiveINDSecure` is the negligible-advantage condition.
+
+## Main results
+
+* `FixedLengthPKScheme.adaptiveIndGame_one` recovers the exact single-challenge game.
+* `FixedLengthPKScheme.AdaptiveINDSecure.single` specializes the security predicate.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
+-/
+
+namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme
+
+open Complexity Turing TCSlib.Cryptography.Games
+
+variable (S : FixedLengthPKScheme)
+
+/-- Extend [PS10, Definition 171.5] to a bounded list of fresh left-or-right challenges.
+The history records each issued challenge. A decryption query in the history receives
+the existing refusal reply. Once the challenge cap is reached the game repeats the
+latest ciphertext, with a zero reply for a zero cap and empty history. The history is
+a list so a repeated ciphertext still consumes one fresh challenge. -/
+noncomputable def adaptiveIndImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
+    (cap : ℕ) : QueryImpl (S.indSpec n) (List (Fin (S.ctLen.eval n) → Bool)) unifSpec
+  | 0, c, history =>
+    if cast (S.indSpec_decDom n) c ∈ history then
+      .pure (zeroBits _, history)
+    else
+      (S.indImpl atk b n pk sk 0 c history.head?).bind fun res => .pure (res.1, history)
+  | 1, mm, history =>
+    if history.length < cap then
+      (S.indImpl atk b n pk sk 1 mm none).bind fun res => .pure (res.1, res.2.toList ++ history)
+    else
+      match history.head? with
+      | none => .pure (zeroBits _, history)
+      | some c =>
+        (S.indImpl atk b n pk sk 1 mm (some c)).bind fun res => .pure (res.1, history)
+
+/-- Decryption refuses every ciphertext recorded in the challenge history. -/
+theorem adaptiveIndImpl_dec_issued (atk : Attack) (b : Bool) (n : ℕ)
+    (pk sk : List Bool) (cap : ℕ) (c : (S.indSpec n).dom 0)
+    (history : List (Fin (S.ctLen.eval n) → Bool))
+    (hc : cast (S.indSpec_decDom n) c ∈ history) :
+    S.adaptiveIndImpl atk b n pk sk cap 0 c history = .pure (zeroBits _, history) := by
+  rw [adaptiveIndImpl, if_pos hc]
+
+/-- A challenge below the cap uses the single game's fresh challenge branch, then
+adds that ciphertext to the history. -/
+theorem adaptiveIndImpl_challenge_fresh (atk : Attack) (b : Bool) (n : ℕ)
+    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
+    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : history.length < cap) :
+    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
+      (S.indImpl atk b n pk sk 1 mm none).bind
+        (fun res => .pure (res.1, res.2.toList ++ history)) := by
+  rw [adaptiveIndImpl, if_pos h]
+
+/-- A fresh challenge samples an encryption tape, returns the selected encryption, and
+prepends exactly that ciphertext to the history.
+
+**Proof sketch.** Read the original game's first-challenge equation on the specification's
+type, then simplify the continuation that saves the returned ciphertext. -/
+theorem adaptiveIndImpl_challenge_encrypt (atk : Attack) (b : Bool) (n : ℕ)
+    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
+    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : history.length < cap) :
+    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
+      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
+        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
+        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
+          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
+        .pure (cast (S.indSpec_challengeRng n).symm c, c :: history) := by
+  rw [S.adaptiveIndImpl_challenge_fresh atk b n pk sk cap mm history h,
+    S.indImpl_challenge_none_onSpec, OracleComp.bind_assoc]
+  simp only [OracleComp.pure_bind, Option.toList_some, List.singleton_append]
+
+/-- A positive cap of one issues a fresh first challenge, as in Definition 171.5. -/
+private theorem adaptiveIndImpl_one_empty (atk : Attack) (b : Bool) (n : ℕ)
+    (pk sk : List Bool) (mm : (S.indSpec n).dom 1) :
+    S.adaptiveIndImpl atk b n pk sk 1 1 mm [] =
+      (S.indImpl atk b n pk sk 1 mm none).bind (fun res => .pure (res.1, res.2.toList)) := by
+  rw [S.adaptiveIndImpl_challenge_fresh atk b n pk sk 1 mm []
+    (by simp only [List.length_nil, Nat.zero_lt_one])]
+  simp only [List.append_nil]
+
+/-- At a full challenge cap, repeat the latest ciphertext without adding to the history. -/
+theorem adaptiveIndImpl_challenge_full (atk : Attack) (b : Bool) (n : ℕ)
+    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
+    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : cap ≤ history.length)
+    (c : Fin (S.ctLen.eval n) → Bool) (hc : history.head? = some c) :
+    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
+      (S.indImpl atk b n pk sk 1 mm (some c)).bind
+        (fun res => .pure (res.1, history)) := by
+  rw [adaptiveIndImpl, if_neg (Nat.not_lt_of_ge h), hc]
+
+/-- A zero challenge cap keeps the initial history empty and returns the zero reply. -/
+theorem adaptiveIndImpl_challenge_zero (atk : Attack) (b : Bool) (n : ℕ)
+    (pk sk : List Bool) (mm : (S.indSpec n).dom 1) :
+    S.adaptiveIndImpl atk b n pk sk 0 1 mm [] = .pure (zeroBits _, []) := by
+  rw [adaptiveIndImpl, if_neg (Nat.not_lt_zero _)]
+  rfl
+
+/-- Decryption outside the history uses the original oracle's availability and decoding
+rules. Its answer leaves the full history unchanged. -/
+theorem adaptiveIndImpl_dec_other (atk : Attack) (b : Bool) (n : ℕ)
+    (pk sk : List Bool) (cap : ℕ) (c : (S.indSpec n).dom 0)
+    (history : List (Fin (S.ctLen.eval n) → Bool))
+    (hc : cast (S.indSpec_decDom n) c ∉ history) :
+    S.adaptiveIndImpl atk b n pk sk cap 0 c history =
+      (S.indImpl atk b n pk sk 0 c history.head?).bind (fun res => .pure (res.1, history)) := by
+  rw [adaptiveIndImpl, if_neg hc]
+
+/-- At cap one, each oracle call agrees with the old game when the optional challenge is
+represented as a list.
+
+**Proof sketch.** Split by oracle and old challenge state. For decryption the
+single-game state is preserved. A fresh challenge creates one list entry, and a repeat
+returns the same state. -/
+theorem adaptiveIndImpl_one (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
+    (i : Fin 2) (x : (S.indSpec n).dom i) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
+    S.adaptiveIndImpl atk b n pk sk 1 i x s.toList =
+      (S.indImpl atk b n pk sk i x s).bind (fun res => .pure (res.1, res.2.toList)) := by
+  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
+  rcases hi with rfl | rfl
+  · cases s with
+    | none =>
+      rw [Option.toList_none, S.adaptiveIndImpl_dec_other atk b n pk sk 1 x []
+        List.not_mem_nil, List.head?_nil, S.indImpl_dec_onSpec]
+      split <;> simp only [OracleComp.pure_bind, Option.toList_none]
+    | some c =>
+      by_cases h : cast (S.indSpec_decDom n) x = c
+      · rw [S.adaptiveIndImpl_dec_issued atk b n pk sk 1 x (some c).toList (by
+          simp only [Option.toList_some, List.mem_singleton]; exact h)]
+        rw [S.indImpl_dec_onSpec, h]
+        simp
+      · rw [S.adaptiveIndImpl_dec_other atk b n pk sk 1 x (some c).toList (by
+          simp only [Option.toList_some, List.mem_singleton]; exact h)]
+        simp only [Option.toList_some, List.head?_cons, S.indImpl_dec_onSpec]
+        split <;> simp only [OracleComp.pure_bind, Option.toList_some]
+  · cases s with
+    | none => exact S.adaptiveIndImpl_one_empty atk b n pk sk x
+    | some c =>
+      rw [S.adaptiveIndImpl_challenge_full atk b n pk sk 1 x (some c).toList (by simp) c (by simp),
+        S.indImpl_challenge_repeat_onSpec]
+      simp only [OracleComp.pure_bind]
+
+/-- Cap-one simulation is the single-challenge simulation with its final state encoded
+as a list.
+
+**Proof sketch.** Induct over the adversary's query tree and apply the per-call equality. -/
+theorem simulate_adaptiveIndImpl_one (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
+    {α : Type} (t : OracleComp (S.indSpec n) α) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
+    simulate (S.adaptiveIndImpl atk b n pk sk 1) t s.toList =
+      (simulate (S.indImpl atk b n pk sk) t s).bind
+        (fun res => .pure (res.1, res.2.toList)) := by
+  induction t generalizing s with
+  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
+  | query i x k ih =>
+    simp only [simulate_query, S.adaptiveIndImpl_one, OracleComp.bind_assoc, OracleComp.pure_bind]
+    congr 1
+    funext res
+    exact ih res.1 res.2
+
+/-- The left-or-right game uses one key and hidden bit across the adaptive queries. -/
+noncomputable def adaptiveIndGame (atk : Attack) (A : NUPPT) (q cap : ℕ) (b : Bool) (n : ℕ) :
+    ProbComp Bool :=
+  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
+  (ProbComp.sample (A.Coins n)).bind fun r =>
+  (simulate (S.adaptiveIndImpl atk b n (pairFstD (S.gen.runAt n [] rg))
+      (pairSndD (S.gen.runAt n [] rg)) cap)
+      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
+    fun res => .pure (res.1 0)
+
+/-- The experiment's only sampled keys come from one activation of key generation. -/
+theorem adaptiveIndGame_eq (atk : Attack) (A : NUPPT) (q cap : ℕ) (b : Bool) (n : ℕ) :
+    S.adaptiveIndGame atk A q cap b n =
+      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
+      (ProbComp.sample (A.Coins n)).bind fun r =>
+      (simulate (S.adaptiveIndImpl atk b n (pairFstD (S.gen.runAt n [] rg))
+          (pairSndD (S.gen.runAt n [] rg)) cap)
+          (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
+        fun res => .pure (res.1 0) := rfl
+
+/-- The cap-one experiment and the existing single-challenge experiment return the same bit
+on the same sampled generator and adversary tapes.
+
+**Proof sketch.** Fix both sampled tapes and apply the simulation correspondence.
+Both experiments read the same bit of the simulation's result. -/
+theorem adaptiveIndGame_one (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
+    S.adaptiveIndGame atk A q 1 b n = S.indGame atk A q b n := by
+  simp only [S.adaptiveIndGame_eq, S.indGame_eq]
+  congr 1
+  funext rg
+  congr 1
+  funext r
+  rw [← Option.toList_none (α := Fin (S.ctLen.eval n) → Bool), S.simulate_adaptiveIndImpl_one,
+    OracleComp.bind_assoc]
+  simp only [OracleComp.pure_bind]
+
+/-- The adversary's left-or-right advantage is negligible for polynomial total and
+challenge budgets. The first catalog witnesses will have message length equal to the
+security parameter. -/
+def AdaptiveINDSecure (atk : Attack) : Prop :=
+  ∀ (A : NUPPT) (q cap : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
+    advantage (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) false n)
+      (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) true n) ≤ ε n
+
+/-- The adaptive predicate quantifies over both the total query and challenge budgets. -/
+theorem adaptiveINDSecure_iff (atk : Attack) :
+    S.AdaptiveINDSecure atk ↔
+      ∀ (A : NUPPT) (q cap : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
+        advantage (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) false n)
+          (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) true n) ≤ ε n :=
+  Iff.rfl
+
+/-- Adaptive security entails security in the original game.
+
+**Proof sketch.** Use the constant cap one and the exact simulation equation. -/
+theorem AdaptiveINDSecure.single {atk : Attack} (h : S.AdaptiveINDSecure atk) :
+    S.INDSecure atk := by
+  rw [S.adaptiveINDSecure_iff] at h
+  rw [S.INDSecure_iff]
+  intro A q
+  obtain ⟨ε, hε, hb⟩ := h A q (.const 1)
+  refine ⟨ε, hε, fun n => ?_⟩
+  simpa only [PolyExpr.eval_const, S.adaptiveIndGame_one] using hb n
+
+end TCSlib.Cryptography.Composability.FixedLengthPKScheme
diff --git a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
index 4ab8cecba..cb0c3bf62 100644
--- a/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
@@ -509,6 +509,10 @@ theorem indSpec_dom (n : ℕ) (i : Fin 2) :
     (S.indSpec n).dom i = (Fin (S.inLens n i) → Bool) :=
   bitSpec_dom (S.inLens n) (S.outLens n) i
 
+/-- The decryption oracle accepts a ciphertext at the scheme's encoded width. -/
+theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 0 = (Fin (S.ctLen.eval n) → Bool) := by
+  rw [S.indSpec_dom, S.inLens_zero]
+
 /-- Oracle `i` returns bit strings of length `S.outLens n i`. -/
 theorem indSpec_rng (n : ℕ) (i : Fin 2) :
     (S.indSpec n).rng i = (Fin (S.outLens n i) → Bool) :=
@@ -562,6 +566,46 @@ theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (pk sk : Li
     (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
     S.indImpl atk b n pk sk 1 mm (some c) = .pure (c, some c) := rfl
 
+/-- The decryption equation on the query specification's type. Read the ciphertext through
+the width equality before checking challenge refusal and decrypting. -/
+theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
+    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
+    S.indImpl atk b n pk sk 0 c s =
+      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
+      then .pure (FixedLengthScheme.decAnswer
+        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c))))), s)
+      else .pure (zeroBits _, s) := by
+  simpa only [cast_eq] using S.indImpl_dec atk b n pk sk c s
+
+/-- The challenge oracle returns a ciphertext at the scheme's encoded width. -/
+theorem indSpec_challengeRng (n : ℕ) :
+    (S.indSpec n).rng 1 = (Fin (S.ctLen.eval n) → Bool) := by
+  rw [S.indSpec_rng, S.outLens_one]
+
+/-- A challenge query contains two messages at the scheme's message width. -/
+theorem indSpec_challengeDom (n : ℕ) :
+    (S.indSpec n).dom 1 = (Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) := by
+  rw [S.indSpec_dom, S.inLens_one]
+
+/-- The fresh challenge equation on the query specification's type. Draw new encryption
+coins, encrypt the selected half of the query, and record the resulting ciphertext. -/
+theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
+    (mm : (S.indSpec n).dom 1) :
+    S.indImpl atk b n pk sk 1 mm none =
+      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
+        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
+        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
+          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
+        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
+  simpa only [cast_eq] using S.indImpl_challenge_none atk b n pk sk mm
+
+/-- Repeating the challenge preserves the previous state for a query of the specification's
+type. -/
+theorem indImpl_challenge_repeat_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
+    (mm : (S.indSpec n).dom 1) (c : Fin (S.ctLen.eval n) → Bool) :
+    S.indImpl atk b n pk sk 1 mm (some c) = .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
+  simpa only [cast_eq] using S.indImpl_challenge_repeat atk b n pk sk mm c
+
 /-- Under CPA, `Dec` never answers. -/
 theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (pk sk : List Bool)
     (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
diff --git a/TCSlib/Cryptography/Foundations/Negligible.lean b/TCSlib/Cryptography/Foundations/Negligible.lean
index f7086edc6..fc8fd7d21 100644
--- a/TCSlib/Cryptography/Foundations/Negligible.lean
+++ b/TCSlib/Cryptography/Foundations/Negligible.lean
@@ -231,4 +231,18 @@ theorem exists_not_negligible_not_noticeable :
     rw [abs_of_pos (by positivity)] at h'
     linarith
 
+/-- A negligible function composed with a map `φ ≥ id` is negligible: for `N ≥ max n₀ 1`,
+`φ N ≥ N ≥ n₀` so `|μ (φ N)| < 1 / (φ N)^c ≤ 1 / N^c` (the bookkeeping for the error bounds
+`ε(|f x|) = ε(p(|x|))` of the pulled-back protocol, Claim-124.d). -/
+theorem Negligible.comp_of_le {μ : ℕ → ℝ} (hμ : Negligible μ) (φ : ℕ → ℕ) (hφ : ∀ N, N ≤ φ N) :
+    Negligible fun N => μ (φ N) := by
+  intro c
+  obtain ⟨n₀, h₀⟩ := hμ c
+  refine ⟨max n₀ 1, fun N hN => ?_⟩
+  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
+  have hφN : n₀ ≤ φ N := le_trans (le_trans (le_max_left _ _) hN) (hφ N)
+  refine lt_of_lt_of_le (h₀ (φ N) hφN) ?_
+  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
+  exact one_div_le_one_div_of_le hNpos (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hφ N) c)
+
 end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/ZeroKnowledge/NP.lean b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
index efd66e597..dfefa1437 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/NP.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
@@ -280,22 +280,6 @@ theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
   rw [PolyExpr.eval_subst, ← h.length_eq x]
   exact hB (f x) (w x y) r hist (h.witness x y hxy)
 
-/-! ### Negligibility along polynomial reparametrization -/
-
-/-- A negligible function composed with a map `φ ≥ id` is negligible: for `N ≥ max n₀ 1`,
-`φ N ≥ N ≥ n₀` so `|μ (φ N)| < 1 / (φ N)^c ≤ 1 / N^c` (the bookkeeping for the error bounds
-`ε(|f x|) = ε(p(|x|))` of the pulled-back protocol, Claim-124.d). -/
-theorem Negligible.comp_of_le {μ : ℕ → ℝ} (hμ : Negligible μ) (φ : ℕ → ℕ) (hφ : ∀ N, N ≤ φ N) :
-    Negligible fun N => μ (φ N) := by
-  intro c
-  obtain ⟨n₀, h₀⟩ := hμ c
-  refine ⟨max n₀ 1, fun N hN => ?_⟩
-  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
-  have hφN : n₀ ≤ φ N := le_trans (le_trans (le_max_left _ _) hN) (hφ N)
-  refine lt_of_lt_of_le (h₀ (φ N) hφN) ?_
-  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
-  exact one_div_le_one_div_of_le hNpos (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hφ N) c)
-
 /-! ### Executions of the pulled-back protocol -/
 
 /-- The execution of two pulled-back strategies on `x` is the execution of the original

## ===== briefs/pass-shelat-ch5-8/gates/09-adaptive-pke/SOURCE-SHA256SUMS =====

0b20c054fe521486516c20f02f49fc3456bbc10b49598365c9d5b37f09481981  TCSlib/Cryptography/Asymptotic.lean
44d5548ba1ad0b0ca9a720d4e3ee7f92449782cf758a6ede0dc3a44e4a7ad224  TCSlib/Cryptography/Asymptotic/CollectionShift.lean
cdd8ea62d05bfd323fb7fc85fde11b2e724b2023cf086d4762f2cbe4e60dc496  TCSlib/Cryptography/Candidates/RSA.lean
b3184a8c2d3a5af910301dcd1bdbedc917e0eec482a3bcdcd1dffd1bdcb90813  TCSlib/Cryptography/Candidates/Rabin.lean
9d5141d89e9addbe68ffd2b46f7312bc3f9bc6225a4a311f23574ce00ba36af0  TCSlib/Cryptography/Encryption.lean
a30f35170b3c291b2d5f77b7df5f12450a253c6ad9cda90a7da8cd9f899ef124  TCSlib/Cryptography/Encryption/PublicKey.lean
570a6a8e9ffdebd40656bee565ae4ad008be3b2e60d0f3eac2b14012ff0bb57f  TCSlib/Cryptography/Encryption/PublicKey/AdaptiveSecurity.lean
a45637d4e206cf70fb02d4cc7d7c467f7327b5956511519cfec765ec60353611  TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean
56dc45fc34915f176899a3f6c1585cc3356929ff12519da77eee6a2f3b364a6d  TCSlib/Cryptography/Foundations/Negligible.lean
28df30b7d5adcfd8a12da9b9e790b4471b64e8f7b65aba1510e4259f972fe922  TCSlib/Cryptography/ZeroKnowledge/NP.lean

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).
