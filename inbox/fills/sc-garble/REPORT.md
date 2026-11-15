# sc-garble — checkpoint 1

This is a partial unit delivery, not a final fill. The wrong-key checkpoint is proved;
the direct multi-message result was also completed early because it uses the same readers.
The remaining B1, B2 and Yao work continues on the local branch.

## Pins, identity and transport

- Issued exchange pin: `7d85785c2e98f0bfdec081a875a9343f06043a8a`; both issued packs pass `shasum -a 256 -c`.
- Proof base: `fbd37f447596d4207c8d08b7ef7602f57fe95198`, PR #315's prf-long head, not the records tip.
- Local-only branch: `fill/sc-garble`; checkpoint head: `13f745ed00e49924631c89c00dae2bb110eca6e2`.
- Worker: Codex on Seyoon's Mac, in the role called “Claude” by the brief.
- Proof worktree: `/Users/seyoonr/.codex/worktrees/sc-garble/tcslib-exchange`.
- Delivery worktree: `/Users/seyoonr/.codex/worktrees/exchange-sc-garble/tcslib-exchange`.
- Git author and committer: Seyoon Ragavan <complexzetaprime@gmail.com>, the checkout's
  resolved identity. Signing is disabled with `commit.gpgsign=false`; `COMMITS.tsv` says `none`.
- A separate scratch Git clone reproduces every patch commit hash exactly; see
  `evidence/replay/checkpoint1.log`. No proof branch is pushed and no campaign PR is opened.

## Target status

| Declaration | Checkpoint status |
|---|---|
| `spDecStr_wrongKey` | Proved; standard axioms only |
| `specialScheme_wrongKey` | Proved; standard axioms only |
| `nestedSpecial_wrongKeyBot` | Proved; standard axioms only |
| `specialScheme_multiMessageSecure` | Proved directly from D4; standard axioms only |
| `uprob_not_good_le` | Pending B2 |
| `yaoSeed_good_whp` | Pending disjoint-block push-forward and B2 |
| `sliceMultiMessageSecure_of_prfOut` | Pending slice post-processor and maximizing advice |
| Required `uprob_not_good_le_of_perm` | Pending; not claimed or published by this checkpoint |

The source admission comparison is exactly 32 → 28, with only the four completed targets
removed and no added admission. The 28 remaining admissions are in 13 modules. The full final
target remains 25 admissions in 11 modules.

## Proofs and edge cases

The efficient prefix test uses the evaluator of `hG'.easy`, not a polynomial-time assumption
on `E'`. D3 supplies the one-query machine; D1 supplies its negligible budget-one advantage.
Its real acceptance is prefix collision. Uniform evaluation, restriction and point probability
give random acceptance exactly `(2⁻¹)^n`. Honest ciphertexts pass the length guard and fail
decryption exactly when their pad prefixes differ. One further positive `(2⁻¹)^n` gives the
strict lower bound even at `n=0`.

The scheme theorem relabels the two key coin strings and nonce, averages away decryption
coins, and uses monotonicity: string failure produces `1^{n+1}`, which decodes to `none`.
It does not need a converse about successful decryption.

The nesting theorem handles zero positions by impossibility of distinct assignments, one
position by the inner marginal, two positions with the first key different by conditioning
on the inner ciphertext, and two positions with the first key equal by outer correctness
followed by the inner marginal. The two errors are nonnegative and their sum is negligible.
Key values may coincide; only the sampled coordinates, not the values, must be distinct.

The direct multi-message proof uses masks `0^n ++ m_i`, the full `2n`-bit answer, and D4.
It has no import from `SpecialEncryptionMulti` and no repeated PRF hybrid or collision proof.
The proofs are uniform in the messages and work at `n=0`, `q(n)=0`, and zero message length
where those types occur. Slice-specific edge cases remain for B1; no claim about them is made here.

## Files and sketches

All changed source files have at most 1000 lines and every line has at most 100 Python
characters. No new `@[simp]` attribute is introduced. Yao and Garbling are byte-identical to
the issue base at this checkpoint.

| Repository path | Base lines | Checkpoint lines |
|---|---:|---:|
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean` | 87 | 111 |
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean` | 0 | 58 |
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean` | 0 | 140 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean` | 325 | 283 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean` | 157 | 332 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/Pad.lean` | 0 | 56 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean` | 0 | 222 |

The three security target sketches describe the delivered proofs. The nesting sketch's
three cases are realized by `GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds`.
Each proof of at least 15 lines has a sketch and the longer proofs have step structure.
The public coin equivalences have both equation and string-preservation readers.

## Gate 27 hand-off

1. Maximizing slice advice and the empty-fit-set convention: pending B1.
2. Slice post-processor: pending B1. The shared zero-prefix pad identity is already published
   as `spEncStr_eq_zeroPrefixMask` and used by the direct scheme proof.
3. Random-function slice law: D2/D4 provide full uniform pads; the eventual B1 proof must
   identify its reliance on their uniform windows. The current direct proof consumes D4.
4. Triangle and collision bounds: consumed inside D4, not rebuilt by this unit.
5. Frozen `specialScheme_multiMessageSecure`: proved directly from D4. The downstream
   `specialScheme_multiMessageSecure_of_joint` remains proved through the new public readers.
6. B2: pending. The approved circuit reader is planned for that checkpoint.

## Overlap and reuse

The pre-implementation statement-shape searches were run in the chat. Their key families
are re-captured in `evidence/reuse/searches.log` against the pinned base and pinned Mathlib.
The search covers probability, expectation, advantage, push-forward, point probability,
list windows, XOR and encoded-list identities before their use.

- **SG-1 replacement, no ledger debt.** The six private helpers in
  `SpecialEncryptionMulti.lean` are removed. `specialScheme_gen_runAt` and
  `specialScheme_enc_runAt` are published upstream; `specialKeyEq`/`ofFn_specialKeyEq` become
  `specialScheme_keyCoinsEquiv`/`specialScheme_keyCoinsEquiv_ofFn`, and the nonce pair becomes
  `specialScheme_nonceCoinsEquiv`/`specialScheme_nonceCoinsEquiv_ofFn`. The two equivalences
  additionally have `_eq` readers. The corollary's only proof change is reader-name replacement
  and line wrapping. Its header and entire docstring stay byte-identical. Old/new proofs and
  their diff, and the base search showing the private helpers occur only in their source file,
  are under `evidence/headers/`. The surviving private XOR lemma is untouched.
- The scheme relabelling is also near `prfScheme_coinsEquiv` in
  `Encryption/PrivateKey/FromPRF.lean`; that equivalence is for a different scheme and cannot
  type the special scheme's coins. The public NUPPT coin equivalences and string readers are reused.
- `specialScheme_dec_runAt` specializes the public `runAt_spDec` activation theorem to the
  special scheme, exposing its overlong failure word without unfolding a foreign definition.
- `spEncStr_eq_zeroPrefixMask` specializes the pad splitting of Algorithm 157.2. Its nearest
  string relatives are `MultiMsg.zipWith_xor_histBlockOut_maskBlockOut`
  (`FromPRF/ReductionMachine.lean:263`) and `zipWith_xor_replicate_false` (line 241).
  It reuses that zero-mask identity, `List.zipWith_append`, and `List.zipWith_comm_of_comm`;
  it concerns the special ciphertext format rather than the query-history encoding.
- The prefix test's efficient composition is near the prefix comparison in
  `SpecialEncryption.polyTimeComputable_spDecFun`; its input is an oracle answer and independent
  key, so it is a different adapter. It consumes the published efficient string operations.
- `uprob_random_prefix` is a specialization and composition of
  `HardcoreBit.pushesUniform_eval` (Basic:250), `pushesUniform_restrict` (Basic:220),
  `OneWay.uprob_eq_one_div_card` (Basic:144), and `take_ofFn_castLE`
  (`Asymptotic/ReductionSupport.lean:288`). None of those laws is re-proved.
- The collision advantage reads `prfAdv_eq` (`Functions/Defs.lean:87`) directly. It does not
  re-prove `prfAdv_eq_expect`, and does not import the post-base #314 promotion.
- The position/nonce marginal composes `pushesUniform_eval`, `pushesUniform_eval_pair`,
  `PushesUniform.prodMap` and the standard product associator. The conditional two-layer case
  uses `piFinTwoEquiv` and `Equiv.prodProdProdComm`; probability is averaged by `uprob_prod`.
- `uprob_isSome_lt_of_none` is the option-valued corollary of `uprob_not`
  (`Foundations/Probability.lean:109`) and `Option.isSome_iff_ne_none`, rather than a new
  complement proof. It is a candidate for promotion to the shared probability layer.
- `length_nestedInner` packages the length fact previously proved inline in
  `GarblingSpecial.nestedSpecial_decCorrect` (its `hc`, around base line 122). That inline
  fact has no reusable declaration. The helper re-derives the corollary only from the public
  `length_spEncStr`, evaluator reader and `innerLen_eq`; promotion to `GarblingSpecial` is requested.
  This overlap is disclosed explicitly; that frozen file is not changed in this checkpoint.
- No D1–D4 machine, hybrid, random-function law, collision bound, or `encodeList` identity is copied.

## Scope requests and exceptions

Seyoon explicitly approved the single `DAGCircuit.isFaninTwo_iff` reader proposed in
`evidence/scope-request/fanin-reader.patch`; the exact request and answer are preserved.
Its implementation was prepared and temporarily restored while collecting baseline evidence;
the reader is not part of this checkpoint's source commit and is planned for B2.
No other frozen-file exception is used in this checkpoint.

Seyoon subsequently authorized best judgment on exceptions while asleep, with full disclosure,
and authorized messages coordinating the shared Mac resources. The instruction is preserved in
`evidence/scope-request/autonomy.md`.

**Evidence sequencing at this partial checkpoint.** Complete A/B seals (strict and coe), paired
negative controls, the explicit-unfold scan and the final full-order sweep are deferred until
the remaining proofs stabilize. They are mandatory final-delivery work, not waived checks.
The pilot whole-file strict A seal of Pad passes with 1618 sealed definitions and 633 notation
exclusions. Failed seal-harness setup runs are retained; they are not counted as proof results.
The unmodified base's full bootstrap, current seven-module checks, source freeze controls,
name scan, admissions, axioms and lint are complete. This checkpoint is not represented as a
fully validated final unit.

## Host resources and coordination

The binding host-wide cap is **3 Lean processes**. Every command of this worker that starts
Lean, Lake or `lean_check_tree.sh` uses the issued wrapper, default `~/.lean-slots`, tag
`sc-garble`. The sole narrowed cache command holds `-k 3`; module checks release the slot
between modules. No `lake build`, unfiltered cache fetch, RAM disk, copied dependency tree,
or Python invocation without `python3 -I` was used.

The Mac has 12 CPUs and 19,327,352,832 bytes of physical memory. The worktree preflight's
headroom computation and APFS disk figures are in `evidence/logs/preflight.log`; it passed
the 4 GiB memory and 12 GiB disk floors. The toolchain is the shared host Lean 4.25.0 install.
All packages are this worktree's fresh `.lake/packages`, at exact manifest URLs and revisions;
the four documentation packages are correctly reported ABSENT. Package verification passes.
The 71-root narrowed fetch unpacked 2066 already-cached archives with zero download failures.
The archive store pre-existed this run (32,667 files, 1,623,212 KiB; origin unknown), and is not
claimed as a download by this session.

The Ladner worker initially reported a different lock directory. I asked it to join the
issued slot domain, notified derand, and coordinated one gap with seq-zk when the wrapper's
five-second poll was starved by short modules. Ladner released its temporary legacy-runner
reservation at 09:12:38 UTC and finished Lean at 09:32:16 UTC. No other worker's process or
lock was edited or killed. I do not certify aggregate global scheduling before all workers
joined the same lock domain; my observed process snapshot had three native Lean processes.
Scoped wrapper traffic is delivered in `evidence/logs/slots.log`.

## Evidence and checks

- Base bootstrap: all 166 issued modules, zero errors, exactly 32 admission warnings.
- Checkpoint source checks: all seven changed modules/helpers pass; no new helper admission.
- Four completed targets: only `propext`, `Classical.choice`, `Quot.sound`.
- Changed-file inventory: 69 stored constants, 67 standard-only; the known pending B1 target
  and `garbling_good_whp` retain `sorryAx` through the pending work. The latter must become
  standard-only after B2. The two Yao end-to-end consumers retain their baseline admissions.
- Frozen headers/definitions: 139 base declarations, six expected SG-1 removals, zero other
  differences. One-character and seventh-removal controls each detect exactly one violation.
- Name scan: 1,275 base source files, 29,518 resolved explicit names; 20 additions,
  two authorized SG-1 replacements, no clash. Generated descendants also receive the final sweep.
- Lint: 92 FAIL / 101 WARN at base and checkpoint; the exact FAIL and WARN line sets agree.
- Width/length: all seven changed/new source files satisfy 100 characters and 1000 lines.
- Signature inventory: `evidence/declarations/checkpoint1-signatures.txt` and the authoritative
  Lean `#check` output in `evidence/logs/checkpoint1-signatures/`.
- Every current evidence file, including failed probe/seal setup sources and raw logs, is
  included. The evidence and top-level SHA-256 manifests have exact relative path sets,
  without leading `./`. Transient Python bytecode is excluded.

## New declarations: source signatures

Section parameters `G E hE hGE` have their original types from the base file. Lean's full
elaboration, including those parameters and implicit binders, is recorded by the signature probe.

```lean
TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
theorem specialScheme_gen_runAt (n : ℕ) :
    ∀ rg : (specialScheme G E hE hGE).gen.Coins n,
      (specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
theorem specialScheme_enc_runAt (n : ℕ) :
    ∀ (k m : List Bool) (re : (specialScheme G E hE hGE).enc.Coins n),
      (specialScheme G E hE hGE).enc.runAt n (pairEncode k m) re =
        spEncStr E k m (List.ofFn re)

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
theorem specialScheme_dec_runAt (n : ℕ) :
    ∀ (k c : List Bool) (rd : (specialScheme G E hE hGE).dec.Coins n),
      (specialScheme G E hE hGE).dec.runAt n (pairEncode k c) rd =
        (spDecStr E n n k c).getD (true :: List.replicate n true)

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
noncomputable def specialScheme_keyCoinsEquiv (n : ℕ) :
    (specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool)

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
theorem specialScheme_keyCoinsEquiv_eq (n : ℕ) :
    specialScheme_keyCoinsEquiv G E hE hGE n =
      (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
        ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
          (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
theorem specialScheme_keyCoinsEquiv_ofFn (n : ℕ) (rg : (specialScheme G E hE hGE).gen.Coins n) :
    List.ofFn (specialScheme_keyCoinsEquiv G E hE hGE n rg) = List.ofFn rg

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
noncomputable def specialScheme_nonceCoinsEquiv (n : ℕ) :
    (specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool)

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
theorem specialScheme_nonceCoinsEquiv_eq (n : ℕ) :
    specialScheme_nonceCoinsEquiv G E hE hGE n =
      (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
        ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
          (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
theorem specialScheme_nonceCoinsEquiv_ofFn (n : ℕ) (re : (specialScheme G E hE hGE).enc.Coins n) :
    List.ofFn (specialScheme_nonceCoinsEquiv G E hE hGE n re) = List.ofFn re

TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean
theorem pushesUniform_position_keys_coin {K : Type} [Fintype K] [Nonempty K]
    {len : ℕ} (j : Fin len) {b b' : Bool} (hb : b ≠ b') (c : Bool) :
    HardcoreBit.PushesUniform (fun t : (Fin len → Bool → K) × (K × K) =>
      (t.1 j b, t.1 j b', if c then t.2.2 else t.2.1))

TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean
theorem uprob_isSome_lt_of_none {Ω α : Type} [Fintype Ω] [Nonempty Ω]
    (X : Ω → Option α) {ε : ℝ} (h : 1 - ε < uprob (fun t => X t = none)) :
    uprob (fun t => (X t).isSome = true) < ε

TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean
theorem length_nestedInner
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {E : List Bool → List Bool}
    (hGE : ∀ n (k r : Fin n → Bool), E (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G n k r)) (n : ℕ) (k m r : Fin n → Bool) :
    (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)).length = innerLen.eval n

TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean
theorem nestedSpecial_wrongKeyBot_of_string_bounds
    (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
    (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
      (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
    (E₁ E₂ : List Bool → List Bool)
    (hGE₁ : ∀ n (k r : Fin n → Bool), E₁ (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G₁ n k r))
    (hGE₂ : ∀ n (k r : Fin n → Bool), E₂ (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G₂ n k r)) (n : ℕ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h₁ : ∀ m : Fin n → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₁ n n (List.ofFn t.2.1)
          (spEncStr E₁ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₁)
    (h₂ : ∀ m : Fin (innerLen.eval n) → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
          (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₂) :
    (nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂)

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/Pad.lean
theorem spEncStr_eq_zeroPrefixMask (E : List Bool → List Bool) (k m r : List Bool)
    (hp : r.length + m.length ≤ (E (pairEncode k r)).length) :
    spEncStr E k m r = pairEncode r
      (List.zipWith xor (List.replicate r.length false ++ m) (E (pairEncode k r)))

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean
def prefixTest (E : List Bool → List Bool) (z : List Bool) : List Bool

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean
theorem prefixTest_eq (E : List Bool → List Bool) (z : List Bool) :
    prefixTest E z =
      [decide ((pairSndD (NUPPT.inArg z)).take (NUPPT.inParam z).length =
        (E (pairEncode (NUPPT.inCoins z) (pairFstD (NUPPT.inArg z)))).take
          (NUPPT.inParam z).length)]

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean
theorem polyTimeComputable_prefixTest {E : List Bool → List Bool}
    (hE : PolyTimeComputable E) : PolyTimeComputable (prefixTest E)

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean
theorem uprob_random_prefix {n L : ℕ} (h : n ≤ L) (r v : Fin n → Bool) :
    uprob (fun R : (Fin n → Bool) → (Fin L → Bool) =>
      (List.ofFn (R r)).take n = List.ofFn v) = (2 : ℝ)⁻¹ ^ n

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean
theorem exists_negligible_prefix_collision (ℓ : PolyExpr)
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
      (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (k r : Fin n → Bool), E (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (F n k r))
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .add .var ℓ) F).Indist
      (OracleEnsemble.random .var (.add .var ℓ))) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (List.ofFn (F n t.1 t.2.2)).take n =
          (List.ofFn (F n t.2.1 t.2.2)).take n) ≤ ε n

TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean
theorem spDecStr_none_iff_prefix_ne {n l : ℕ}
    (F : (Fin n → Bool) → (Fin n → Bool) → (Fin (n + l) → Bool))
    (E : List Bool → List Bool)
    (hFE : ∀ k r, E (pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (F k r))
    (k k' r : Fin n → Bool) (m : Fin l → Bool) :
    spDecStr E n l (List.ofFn k')
      (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)) = none ↔
        (List.ofFn (F k r)).take n ≠ (List.ofFn (F k' r)).take n
```
