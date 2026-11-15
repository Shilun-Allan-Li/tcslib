# sc-garble · final delivery

All seven frozen targets and the stronger B2 theorem are proved. The final 174-module sweep
has zero errors and exactly the required 25 admissions in 11 modules, down from 32 in 15.
The seven removed declarations are precisely the seven assigned targets. New helpers have
no admissions. The proof branch remains local; this payload is for maintainer review and
landing after PR #315 merges.

**Issue base:** `fbd37f447596d4207c8d08b7ef7602f57fe95198`, the exact #315 head, without later
records changes. **Issued pack:** `7d85785c2e98f0bfdec081a875a9343f06043a8a`; both checksum
packs passed. **Final proof head:** `81795f776e7de58a6ab112d12fbd5be4e7aaa2f8`. Lean is 4.25.0 with the pinned Mathlib manifest.
The full unsigned patch series and `COMMITS.tsv`, including signing, reproduce every hash
from the issue base in the delivered scratch-clone replay log. No proof branch or PR was pushed.

## Target status and B2

| Target | Final status |
|---|---|
| `spDecStr_wrongKey` | Proved; standard axioms only |
| `specialScheme_wrongKey` | Proved; standard axioms only |
| `specialScheme_multiMessageSecure` | Proved directly from D4; standard axioms only |
| `nestedSpecial_wrongKeyBot` | Proved; standard axioms only |
| `uprob_not_good_le` | Proved by averaging B2 |
| `yaoSeed_good_whp` | Proved using B2's uniform-data strengthening and disjoint blocks |
| `sliceMultiMessageSecure_of_prfOut` | Proved by the D4 consumer reduction |
| `uprob_not_good_le_of_perm` | Published with the prescribed stronger statement; proved |

The required B2 signature, with its section parameters made explicit, is:

```lean
theorem uprob_not_good_le_of_perm {K C ρ : Type} [Inhabited K] {n : ℕ}
    (M : MultiEnc K C ρ) (Cc : DAGCircuit n) [Fintype K] [Fintype ρ]
    (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
    (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)) :
    uprob (fun t : (Fin Cc.size → Bool → K) ×
        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
      ¬ Good M Cc (t.1, t.2, π)) ≤ 12 * Cc.gates.length * δ
```

The shared `uprob_not_good_le_of_uniform_data` proves more: the permutation family may depend
on the raw seed, provided the joint key/row-coin marginal is uniform. Cross-opening events do
not read row order. The prescribed fixed-permutation API is an exact corollary, and the old
uniform-permutation target averages it. This is a strengthening, with no extra hypothesis on B2.

## Proofs and edge cases

The wrong-key string proof takes its efficient evaluator from `hG'.easy`, without adding a
polynomial-time hypothesis on `E'`. The published one-query machine and budget-one PRF bound
control prefix collision. Uniform evaluation, restriction and the published point probability
give random acceptance `(2⁻¹)^n`. Honest ciphertexts pass the length guard; adding a further
positive `(2⁻¹)^n` gives the strict inequality even at `n=0`. Scheme decryption failure follows
by monotonicity and the overlong failure word; a converse about successful decoding is unused.

Nesting handles zero positions by impossibility of distinct assignments, one position by the
inner wrong-key bound, two positions with different first keys by conditioning on the inner
ciphertext, and equal first keys by outer correctness followed by the inner bound. The two
nonnegative negligible errors add. Distinct sampled coordinates need not have distinct values.

B2 restricts vertex keys to the distinct argument vertices and the different output vertex,
reads independent row coins, and averages over the output key. At most four assignments and
three other rows give twelve cross-opening events per gate. Correctness and the published
first-success list facts imply goodness when no such event occurs.

Yao's key block indices `b*S+v` and row-half indices `2*S+2*(4*i+idx(a))+b` are injective below
`10*S`. Restriction and standard equivalences give the full uniform key/row-coin marginal,
including zero-length blocks. The stronger B2 seed law permits the XOR shifts to depend on
any coins, so no separate shift-conditioning law is needed. Each output's two independent
keys coincide with probability `2^{-n}`; the output union bound allows repeated vertices.
`12*S(n)*δ₀(n) + outLen(n)*2^{-n}` is negligible. The generic output-collision helper has
`[Nonempty ρ]`, satisfied by Yao's pair of bit-vector coin spaces; B2 has no added such hypothesis.

For B1, `Option` of fitting configurations and message pairs is finite. Give `none` advantage
zero and maximize over it. If no vector fits, the dependent configuration type is empty,
so the maximum is exactly zero and advice is empty. If a maximum of zero is selected even
when vectors fit, D4 on equal zero masks supplies the nonnegative bound needed by that branch.
Only the maximizing offsets and lengths are advice, bounded by `(q(n)+1)*(6*ℓ(n)+6)` bits.
D4 already bounds every mask pair uniformly, so the maximizing messages need no extra advice.

The total efficient parser reads descriptor and ciphertext lists in parallel, keeps each nonce,
and cuts the body at offset `o_i` and width `n+len_i`. Full-width masks
`0^{o_i+n} ++ m_i ++ 0^{ℓ(n)-(o_i+n+len_i)}` give exactly the slice sampler pointwise on the
same key/nonce seed. NUPPT composition and advice closure compile `D ∘ P`; the coin reader and
`distAdv_comp` transport D4's bound. The PRF, random-function, collision and triangle proofs
are consumed inside D4, not rebuilt.

All statements include `n=0`, `ℓ(n)=0`, no fitting slice (`ℓ(n)<n`), `q(n)=0`, empty messages,
exactly fitting windows, arities zero/one/two, constant gates, zero gates, and repeated outputs.
The formal goodness conclusion remains first-success correctness, as frozen, rather than
asserting the source's stronger unique-opening property.

## Files, sketches and source discipline

The five owned files and eight permitted helper modules changed, plus the single approved
circuit reader. Every final source line has at most 100 Python characters and every file at
most 1000 lines; Yao has 970. Yao changes only the permitted body, sketch and results bullet.
No new simp attribute is added. Garbling's two helper modules are definition-free.

| Repository path | Base lines | Final lines |
|---|---:|---:|
| `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` | 627 | 636 |
| `TCSlib/Cryptography/SecureComputation/Garbling.lean` | 427 | 659 |
| `TCSlib/Cryptography/SecureComputation/Garbling/CoinBlocks.lean` | 0 | 206 |
| `TCSlib/Cryptography/SecureComputation/Garbling/Probability.lean` | 0 | 113 |
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean` | 87 | 111 |
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean` | 0 | 58 |
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean` | 0 | 210 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean` | 325 | 368 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceParser.lean` | 0 | 180 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceReduction.lean` | 0 | 150 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean` | 157 | 332 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/Pad.lean` | 0 | 116 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean` | 0 | 222 |
| `TCSlib/Cryptography/SecureComputation/Yao.lean` | 942 | 970 |

Target sketches describe the delivered proofs; long helper proofs have formula docstrings,
sketches and step structure. Every public definition has its equation reader. The source
header checker covers all 139 base declarations, including private/prefixed declarations and
whole definition bodies. It reports exactly six SG-1 removals and zero other differences.
Both controls detect exactly one violation. Removing the nine approved reader lines restores
the entire frozen DAGCircuit file byte-for-byte.

## Gate 27 hand-off

1. **Maximizing advice and empty-set convention:** the finite `Config`, `Pack`, `adv`, `μ`, `β`
   construction in `sliceMultiMessageSecure_of_prfOut`; `none` has value zero.
   `length_sliceAdvice_le` and `exists_slicePost_nuppt` provide the polynomial advice and machine.
2. **Post-processor:** `slicePost`, `polyTimeComputable_slicePost`, `slicePost_encode`,
   `slicePost_tuple`, and the shared `spEncStr_eq_sliceMask`. The sampler identity preserves seeds.
3. **Random-function slice law:** D2/D4's full uniform pads give uniform selected windows;
   `slicePost_tuple` identifies those windows without reproving their probability law.
4. **Triangle/collision bound:** exactly `MultiMsg.exists_negligible_distAdv_prfEncRealOut` (D4).
5. **Frozen scheme theorem:** `specialScheme_multiMessageSecure` is proved directly from D4
   upstream. `specialScheme_multiMessageSecure_of_joint` remains proved downstream, using the
   SG-1 public readers; its frozen header/docstring and the surviving private XOR lemma remain.
6. **B2:** `uprob_not_good_le_of_perm`; the uniform-seed and Yao targets are proved corollaries
   of the shared strengthened bound.

## Overlap and reuse

Searches were run before the corresponding implementations; their statement-shape families
are retained in `evidence/reuse/` and the chat. The following includes private relatives and
inline specializations, not only new named lemmas.

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
  `Encryption/PrivateKey/FromPRF.lean:271`; that equivalence is for a different scheme and cannot
  type the special scheme's coins. The public NUPPT coin equivalences and string readers are reused.
- `specialScheme_dec_runAt` specializes the public `SpecialEncryption.lean:248` (`runAt_spDec`) activation theorem to the
  special scheme, exposing its overlong failure word without unfolding a foreign definition.
- `spEncStr_eq_zeroPrefixMask` specializes the pad splitting of Algorithm 157.2. Its nearest
  string relatives are `MultiMsg.zipWith_xor_histBlockOut_maskBlockOut`
  (`FromPRF/ReductionMachine.lean:263`) and `zipWith_xor_replicate_false` (line 241).
  It reuses that zero-mask identity, `List.zipWith_append`, and `List.zipWith_comm_of_comm`;
  it concerns the special ciphertext format rather than the query-history encoding.
- The prefix test's efficient composition is near the prefix comparison in
  `SpecialEncryption.lean:214` (`polyTimeComputable_spDecFun`); its input is an oracle answer and independent
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

- `findSome_eq_some_of_dichotomy` combines Core's `List.findSome?_eq_none_iff` and
  `List.exists_of_findSome?_eq_some` (Init/Data/List/Find.lean:48 and 40); it does not re-prove either list law.
- Output/argument marginals compose `HardcoreBit.pushesUniform_restrict` (Basic:220),
  `pushesUniform_eval` (250), product maps, and sum/product equivalences. The dependent row
  marginal uses `Equiv.piCurry` (Mathlib Logic/Equiv/Basic:170) and uniform evaluation.
- `wrongKeyBot_nonneg` is the one-position nonnegativity consequence of the published
  `MultiEnc.wrongKeyBot_iff` and `uprob_nonneg`; no probability identity is re-proved.
- The cross-opening bound averages the published wrong-key property with `uprob_prod`,
  `OneWay.uexp_mono` and `OneWay.uexp_const` (OneWayFunctions/Basic:69).
- The two nested finite union bounds use `uprob_exists_le` (Foundations/Probability:137),
  Finset sums and cardinality readers. The inline count specializes `2^arity*(2^arity-1) ≤ 12`
  to arities at most two; this is arithmetic bookkeeping, not a new union-bound proof.
- The old uniform-seed theorem uses `uprob_comp_equiv`, Fubini and constant expectation.
- `assignmentFold_small` packages the existing Yao binary fold's arity-zero/one/two facts.
  No public bound/injection theorem for `assignIdx` existed at the base; the helper is generic
  and definition-free and Yao supplies its own `assignIdx_eq` reader.
- `pushesUniform_bits_of_blocks` specializes uniform restriction to disjoint bit blocks and
  curries the selected table. Nearest relative: the block injection `dla_blockPos` and its
  injectivity proof in `Candidates/Concrete.lean:831–856`; that proof concerns a different
  candidate layout outside the issued order. Standard `finProdFinEquiv` and restriction are
  reused rather than any imported candidate construction.
- `key_row_blocks_injective` is arithmetic for this concrete layout; no probability law is
  repeated. `pushesUniform_key_row_blocks` composes it with the general block restriction and
  standard `sumArrowEquivProdArrow`, curry, `boolArrowEquivProd` and `piCurry` equivalences.
- Output collisions reuse `MultiMsg.uprob_eq_pair` (FromPRF/HybridLemmas:111), which itself
  supplies the Fubini/point-probability proof. The inline marginal merely composes uniform
  projection, evaluation and `pushesUniform_eval_pair` (HardcoreBit/Basic:263).
- The approved `DAGCircuit.isFaninTwo_iff` is an `Iff.rfl` reader of the existing definition.
  It is not an alternate circuit predicate or a re-proof of well-formedness.

- `sliceMask` and its readers use `padFin` and `ofFn_padFin_of_length`
  (`Asymptotic/Adversary.lean:216`). Its zero/message/zero layout is the slice-specific adapter
  to D4's full-width masks, not another PRF encryption definition.
- `spEncStr_eq_sliceMask` composes the shared zero-prefix identity with Core's
  `List.drop_zipWith`, `take_zipWith`, drop/take append readers and
  `zipWith_eq_zipWith_take_min` (Init/Data/List/Nat/TakeDrop.lean:570).
  The frozen private `zipWith_xor_append_of_le` in SpecialEncryptionMulti is downstream and
  cannot be imported upstream; the more general public truncation law is reused instead.
- `parserStep`, `parserEmit`, `slicePost` and their equation readers are layout adapters.
  Polynomial time consumes `Games.polyTimeComputable_iterEmit`
  (`Games/Efficiency/OracleBridge.lean:92`), with the exact list law from `iterEmit_encode` (110).
  The parser uses self-delimited list heads, so it needs no duplicate fixed-block parser.
- `length_parserStep_le` reuses the public
  `OneWay.PosLoop.length_pairEncode_pairFstD_le` (`Asymptotic/OneWayLemmas.lean:767`) plus
  `length_pairSndD_le` and the pairing length formula. A final overlap review replaced its
  original pair-case proof with that published bound; the helper was re-sealed afterward.
- `length_le_encodeList` and `length_encodeList_le` are the PrivateKeyScheme encoding's size
  adapters. Nearest relatives are the private `ETTGame.length_le_length_encodeLog`
  (`EncryptThenTag/Machines.lean:95`), public `EffFill.length_le_length_encodeHist`
  (`Games/Efficiency/OracleBridge.lean:231`), and `EffFill.length_encodeLog_le`
  (`Games/Efficiency/Strings.lean:74`). Those use structured QueryLog/encodeHist carriers;
  no published bridge represents arbitrary ciphertext words by those encodings. These two
  bounds derive only from this encoder's public nil/cons readers and `length_pairEncode`.
  Promotion beside PrivateKeyScheme.encodeList is requested. The parser's inline fuel bound
  applies the former lemma; it does not repeat a log-length proof silently.
- `length_sliceAdvice_le` specializes the latter encoding bound using the fit inequality.
  `exists_slicePost_nuppt` adapts the published NUPPT `exists_comp` (Closure:272),
  `exists_withAdvice` (358), `coinsCongr` and activation/verdict readers. No machine is rebuilt.
- `slicePost_tuple` composes `encodeTupleOut_eq`, `prfEncRealOut_apply`, the parser law,
  `zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean:131`) and the shared mask identity.
  It is the mandated B1 step-0 specialization, not a duplicate hybrid.
- The B1 inline maximum follows `Finset.exists_max_image`, as D4
  (`FromPRF/MultiMsgOut.lean:120`) does for masks, but maximizes a different dependent type
  of fitting slices and messages and explicitly adds the empty case. The advantage transport
  reuses `distAdv_comp` (Indistinguishability:141) and `acceptProb_coins_equiv`
  (`Asymptotic/ReductionSupport.lean:221`), not a new probability reindexing proof.

Further promotion requests are the generic option-complement bound, dependent row marginal,
first-success dichotomy and bit-block restriction, and the nested-string length reader beside
nestedSpecial. No frozen-file promotion is made beyond the separately approved circuit reader.

## Scope requests and exceptions

Seyoon approved exactly `DAGCircuit.isFaninTwo_iff`: “Approve the reader addition”. The complete
request, exact patch and verbatim answer are under `evidence/scope-request/`. The added reader
is `Iff.rfl` and leaves the definition unchanged. It is the only extra frozen-file edit.
SG-1 authorizes exactly the six private deletions and the downstream corollary proof repair.

Seyoon then authorized best judgment on exceptions while asleep, full disclosure, and messages
coordinating shared Mac resources; his instruction is preserved verbatim. The mathematical
route change is the stronger seed-dependent B2 law above. Checkpoints 1 and 2 explicitly
postponed complete seals and the final sweep until proof stabilization; those checks are now
complete, not waived. Historical reports remain under `evidence/history/`.

The first seal pass found three hidden coin-map reductions in local-alias preservation facts.
Only the local aliases `ek`, `er`, `eD` were made explicit before the existing equivalence
readers. Corrected whole-file runs pass both A regimes. Original failing logs and their exact
source snapshots are retained, and the final matrix selects the corrected runs.

Two own check drivers were accidentally queued together during B2 development. The issued
wrapper serialized their actual Lean runs, so no concurrent olean writers occurred. Their
queue-time snapshots were too early; originals and the correction are retained. A new local
driver guard and source capture inside the host slot prevent recurrence, and the authoritative
serialized rerun passed. One verified own runaway collision check was interrupted after
177 seconds; explicit finite marginals and the needed generic nonempty coin hypothesis fixed
it. No other worker's native process or lock was touched.

The true-base comparison temporarily installed only the six base source files in this own
worktree, rebuilt its baseline consumers, ran 24 seals, and restored all 14 saved final files
byte-for-byte. After restoration and before the sweep reached the parser (position 157), its
length proof was simplified to the published bound. The final sweep's captured inputs equal
every delivered source blob; the parser's four updated seals also pass. The source-hash and
phase records make this sequencing explicit. A width-only commit wraps one earlier long line.

Automatic approval review rejected the first combined checkpoint-1 pull/push using the general
README rule. The explicit task §4 and host §5 authorization override were supplied; the same
scoped direct push was approved and succeeded. The event is recorded in
`evidence/coordination/checkpoint1-push-review.md`. Checkpoint 2 pushed normally. No force push,
proof-branch push, or change to another delivery path occurred.

## Rule 10, controls and diagnostics

Whole-file seals cover each changed/new file's full imported TCSlib definition closure,
including matchers and projections. Reducible notation is excluded, with complete requested
and excluded name lists in raw logs. A treats PolyExpr.eval as the Q1 notation ruling requires;
B seals it diagnostically. Coe is canonical; strict also seals non-reducible projection
coercions. No unsafe reducibility override is used. The explicit argument scan additionally
checks Core and Mathlib definitions; kernel rfl/decide reductions are allowed by policy.

Base A: all 6 files pass strict and coe (12/12). Final A: all 14 files pass strict and
coe (28/28). B has 21 baseline diagnostics per coercion variant in three files, and 30 final
diagnostics per variant in five files. Every B failure is an explicitly attributed
PolyExpr.eval notation conversion. Strict and coe have identical diagnostic declarations;
there is no coercion-sensitive failure difference. All 80 base/final whole-file matrix
entries are complete; corrected runs supersede retained historical failures.

Every B failure is attributed by declaration and raw type mismatch in
`evidence/seals/B-attribution.md`, including all added body/helper failures. In particular,
new eval conversions are not dismissed as “where the base fails”. Both coercion variants have
the same diagnostic declarations. All four unsealed controls pass and each of four sealed
negatives fails exactly once. A fixture verifies both `error:` and `error(…)` counting.
The explicit-unfold scan has zero unresolved foreign-definition violations. Its initial
conservative token scan produced false positives for terms inside reader arguments; the
balanced rule-head scan and eight local-binder resolutions are documented in
`evidence/unfold/scan-review.md`, with the original results retained.

## Checks, axioms and evidence

- Baseline bootstrap: 166 modules, zero errors, 32 admissions in 15 modules.
- Final sweep: 174 modules, zero errors, 25 admissions in 11 modules; the only removed
  admissions are the seven targets. The import graph is closed and acyclic.
- All seven targets, B2, the joint corollary and `garbling_good_whp` are standard-only.
  `yaoHybrid_hbcSecure` and `yaoProtocol_hbcSecure` retain sorryAx only through the outside-unit
  `yaoHybrid_polyTime` and `yaoHybrid_simulators`; these two bodies stay frozen.
- Complete stored-constant inventory: 531 stored constants, 528 standard-only; the three remaining sorryAx-bearing constants are the two frozen Yao admissions and their Yao hybrid consumer.
- Name scan: 1,275 base source files, 29,518 resolved explicit names; 55 additions,
  two authorized SG-1 replacements, zero clashes. Generated descendants pass the full sweep.
- Lint is 92 FAIL / 101 WARN at both base and final, with identical line sets.
- Header, width/length, signatures, source matching, axioms, seals, controls, replay and
  manifest checks are delivered with scripts, sources and raw logs, including failed development
  attempts. Transient Python bytecode is excluded. Both SHA256SUMS manifests have exactly the
  delivered relative paths, with no leading `./`, and were verified with shasum.

Every own Lean/Lake/check command uses the issued wrapper with tag `sc-garble`, default shared
`~/.lean-slots`, cap **three**. Own module checks are serial and release slots between modules.
The narrowed cache used `-k 3`; there was no lake build, unfiltered cache, copied package tree
or RAM disk. All Python ran as `python3 -I`. The Mac preflight passed memory/disk floors;
package URLs and revisions match the pinned manifest, with the four expected documentation
packages absent. The shared pre-existing archive-store counts and fresh own .lake/packages
provenance are retained. Authorized peer messages coordinated wrapper use and boundary gaps;
waiting was logged as normal scheduling, not E-RES. No sub-agent proved any part of this unit.

## New declarations: final signatures

The complete Lean-elaborated signatures, including section and implicit parameters, follow.
The authoritative raw probe is also delivered under `evidence/logs/final-probes/`.

```lean
BoolCircuit.DAGCircuit.isFaninTwo_iff {n : ℕ} (C : BoolCircuit.DAGCircuit n) :
  C.IsFaninTwo ↔
    (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = BoolCircuit.GateKind.not → g.args.length = 1)) ∧
      ∀ g ∈ C.gates, g.args.length ≤ 2
TCSlib.Cryptography.SecureComputation.good_of_no_crossOpening {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) (hdec : M.DecCorrect)
  (hC : Cc.IsFaninTwo) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed Cc K ρ)
  (hcross :
    ∀ (i : Fin Cc.gates.length) (a a' : Fin Cc.gates[i].args.length → Bool),
      a ≠ a' →
        M.dec (TCSlib.Cryptography.SecureComputation.argKeys Cc s i a')
            (TCSlib.Cryptography.SecureComputation.garbledRow M Cc s i a) =
          none) :
  TCSlib.Cryptography.SecureComputation.Good M Cc s
TCSlib.Cryptography.SecureComputation.wrongKeyBot_nonneg {K C ρ : Type} [Inhabited K]
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) [Fintype K] [Fintype ρ] {δ : ℝ} (hδ : M.WrongKeyBot δ) :
  0 ≤ δ
TCSlib.Cryptography.SecureComputation.uprob_crossOpening_le_of_perm {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) [Fintype K] [Fintype ρ]
  {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
  (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin Cc.gates[i].args.length → Bool)) (i : Fin Cc.gates.length)
  (a a' : Fin Cc.gates[i].args.length → Bool) (hne : a ≠ a') :
  (TCSlib.Cryptography.uprob fun t =>
      (M.dec (TCSlib.Cryptography.SecureComputation.argKeys Cc (t.1, t.2, π) i a')
            (TCSlib.Cryptography.SecureComputation.garbledRow M Cc (t.1, t.2, π) i a)).isSome =
        true) ≤
    δ
TCSlib.Cryptography.SecureComputation.uprob_not_good_le_of_uniform_data {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) [Fintype K] [Fintype ρ]
  (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) {Ω : Type} [Fintype Ω]
  (d : Ω → (Fin Cc.size → Bool → K) × ((i : Fin Cc.gates.length) → (Fin Cc.gates[i].args.length → Bool) → ρ))
  (hd : TCSlib.Cryptography.HardcoreBit.PushesUniform d)
  (π : Ω → (i : Fin Cc.gates.length) → Equiv.Perm (Fin Cc.gates[i].args.length → Bool)) :
  (TCSlib.Cryptography.uprob fun w => ¬TCSlib.Cryptography.SecureComputation.Good M Cc ((d w).1, (d w).2, π w)) ≤
    12 * ↑Cc.gates.length * δ
TCSlib.Cryptography.SecureComputation.uprob_not_good_le_of_perm {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) [Fintype K] [Fintype ρ]
  (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
  (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin Cc.gates[i].args.length → Bool)) :
  (TCSlib.Cryptography.uprob fun t => ¬TCSlib.Cryptography.SecureComputation.Good M Cc (t.1, t.2, π)) ≤
    12 * ↑Cc.gates.length * δ
TCSlib.Cryptography.SecureComputation.GarblingProbability.assignmentFold_small (len : ℕ) (hlen : len ≤ 2) :
  (∀ (a : Fin len → Bool), List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a) < 4) ∧
    Function.Injective fun a => List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_bits_of_blocks {I : Type} [Fintype I]
  [DecidableEq I] {B n tail : ℕ} (c : I → Fin B) (hinj : Function.Injective c) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun r i t => (List.ofFn r).getD (↑(c i) * n + ↑t) false
TCSlib.Cryptography.SecureComputation.GarblingProbability.key_row_blocks_injective {S V G : ℕ} (hV : V ≤ S) (hG : G ≤ S)
  {A : Fin G → Type} (idx : (i : Fin G) → A i → ℕ) (hidx : ∀ (i : Fin G) (a : A i), idx i a < 4)
  (hinj : ∀ (i : Fin G), Function.Injective (idx i)) :
  have c :=
    Sum.elim (fun p => p.2.toNat * S + ↑p.1) fun p => 2 * S + (4 * ↑p.1.fst + idx p.1.fst p.1.snd) * 2 + p.2.toNat;
  (∀ (p : Fin V × Bool ⊕ ((i : Fin G) × A i) × Bool), c p < 10 * S) ∧ Function.Injective c
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_key_row_blocks {S V G n : ℕ} (hV : V ≤ S)
  (hG : G ≤ S) {A : Fin G → Type} [(i : Fin G) → Fintype (A i)] [(i : Fin G) → DecidableEq (A i)]
  (idx : (i : Fin G) → A i → ℕ) (hidx : ∀ (i : Fin G) (a : A i), idx i a < 4)
  (hinj : ∀ (i : Fin G), Function.Injective (idx i)) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun r =>
    (fun v b t => (List.ofFn r).getD ((b.toNat * S + ↑v) * n + ↑t) false, fun i a =>
      (fun t => (List.ofFn r).getD (2 * S * n + (4 * ↑i + idx i a) * (2 * n) + ↑t) false, fun t =>
        (List.ofFn r).getD (2 * S * n + (4 * ↑i + idx i a) * (2 * n) + n + ↑t) false))
TCSlib.Cryptography.SecureComputation.GarblingProbability.findSome_eq_some_of_dichotomy {α β : Type} (l : List α)
  (f : α → Option β) (b : β) (hex : ∃ a ∈ l, f a = some b) (hall : ∀ a ∈ l, f a = none ∨ f a = some b) :
  List.findSome? f l = some b
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_output_argKeys {I J K : Type} [Fintype I]
  [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [Nonempty K] (arg : J → I) (hinj : Function.Injective arg)
  (out : I) (hne : ∀ (j : J), arg j ≠ out) (b : Bool) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun ks => (ks out b, fun j => ks (arg j))
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_rowCoin {I : Type} [Fintype I] [DecidableEq I]
  {A : I → Type} [(i : I) → Fintype (A i)] [(i : I) → DecidableEq (A i)] {ρ : Type} [Fintype ρ] (i : I) (a : A i) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun r => r i a
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_output_argKeys_row {I J K R ρ : Type}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [Nonempty K] [Fintype R] [Fintype ρ] (arg : J → I)
  (hinj : Function.Injective arg) (out : I) (hne : ∀ (j : J), arg j ≠ out) (b : Bool) (coin : R → ρ)
  (hcoin : TCSlib.Cryptography.HardcoreBit.PushesUniform coin) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun t => (t.1 out b, fun j => t.1 (arg j), coin t.2)
TCSlib.Cryptography.SecureComputation.GarblingCoins.pushesUniform_position_keys_coin {K : Type} [Fintype K] [Nonempty K]
  {len : ℕ} (j : Fin len) {b b' : Bool} (hb : b ≠ b') (c : Bool) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun t => (t.1 j b, t.1 j b', if c = true then t.2.2 else t.2.1)
TCSlib.Cryptography.SecureComputation.GarblingCoins.uprob_isSome_lt_of_none {Ω α : Type} [Fintype Ω] [Nonempty Ω]
  (X : Ω → Option α) {ε : ℝ} (h : 1 - ε < TCSlib.Cryptography.uprob fun t => X t = none) :
  (TCSlib.Cryptography.uprob fun t => (X t).isSome = true) < ε
TCSlib.Cryptography.SecureComputation.GarblingCoins.length_nestedInner
  {G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool} {E : List Bool → List Bool}
  (hGE : ∀ (n : ℕ) (k r : Fin n → Bool), E (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (G n k r))
  (n : ℕ) (k m r : Fin n → Bool) :
  (TCSlib.Cryptography.SecureComputation.spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)).length =
    TCSlib.Cryptography.SecureComputation.innerLen.eval n
TCSlib.Cryptography.SecureComputation.GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ :
    (n : ℕ) →
      (Fin n → Bool) →
        (Fin n → Bool) →
          Fin ((Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen).eval n) → Bool)
  (E₁ E₂ : List Bool → List Bool)
  (hGE₁ : ∀ (n : ℕ) (k r : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (G₁ n k r))
  (hGE₂ : ∀ (n : ℕ) (k r : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (G₂ n k r))
  (n : ℕ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
  (h₁ :
    ∀ (m : Fin n → Bool),
      (TCSlib.Cryptography.uprob fun t =>
          (TCSlib.Cryptography.SecureComputation.spDecStr E₁ n n (List.ofFn t.2.1)
                (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn t.1) (List.ofFn m)
                  (List.ofFn t.2.2))).isSome =
            true) ≤
        ε₁)
  (h₂ :
    ∀ (m : Fin (TCSlib.Cryptography.SecureComputation.innerLen.eval n) → Bool),
      (TCSlib.Cryptography.uprob fun t =>
          (TCSlib.Cryptography.SecureComputation.spDecStr E₂ n (TCSlib.Cryptography.SecureComputation.innerLen.eval n)
                (List.ofFn t.2.1)
                (TCSlib.Cryptography.SecureComputation.spEncStr E₂ (List.ofFn t.1) (List.ofFn m)
                  (List.ofFn t.2.2))).isSome =
            true) ≤
        ε₂) :
  (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂)
TCSlib.Cryptography.SecureComputation.uprob_not_good_distinct_le_of_uniform_data {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) [Fintype K] [Fintype ρ]
  [Nonempty ρ] (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) {Ω : Type} [Fintype Ω]
  (s : Ω → TCSlib.Cryptography.SecureComputation.GarbleSeed Cc K ρ)
  (hs : TCSlib.Cryptography.HardcoreBit.PushesUniform fun w => ((s w).1, (s w).2.1)) {m : ℕ} (out : Fin m → ℕ)
  (hout : ∀ (j : Fin m), out j < Cc.size) :
  (TCSlib.Cryptography.uprob fun w =>
      ¬(TCSlib.Cryptography.SecureComputation.Good M Cc (s w) ∧
          ∀ (j : Fin m),
            TCSlib.Cryptography.SecureComputation.keyAt Cc (s w) (out j) false ≠
              TCSlib.Cryptography.SecureComputation.keyAt Cc (s w) (out j) true)) ≤
    12 * ↑Cc.gates.length * δ + ↑m * (1 / ↑(Fintype.card K))
TCSlib.Cryptography.SecureComputation.SliceReduction.parserStep (z : List Bool) : List Bool
TCSlib.Cryptography.SecureComputation.SliceReduction.parserStep_eq (z : List Bool) :
  TCSlib.Cryptography.SecureComputation.SliceReduction.parserStep z =
    Turing.pairEncode (Complexity.pairSndD (Complexity.pairFstD z)) (Complexity.pairSndD (Complexity.pairSndD z))
TCSlib.Cryptography.SecureComputation.SliceReduction.parserEmit (z : List Bool) : List Bool
TCSlib.Cryptography.SecureComputation.SliceReduction.parserEmit_eq (z : List Bool) :
  TCSlib.Cryptography.SecureComputation.SliceReduction.parserEmit z =
    if Complexity.pairSndD z = [] then []
    else
      Turing.pairEncode
        (Turing.pairEncode (Complexity.pairFstD (Complexity.pairFstD (Complexity.pairSndD z)))
          (List.take (Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z))).length
            (List.drop (Complexity.pairFstD (Complexity.pairFstD (Complexity.pairFstD z))).length
              (Complexity.pairSndD (Complexity.pairFstD (Complexity.pairSndD z))))))
        []
TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost (z : List Bool) : List Bool
TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost_eq (z : List Bool) :
  TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost z =
    TCSlib.Cryptography.Games.iterEmit TCSlib.Cryptography.SecureComputation.SliceReduction.parserStep
      TCSlib.Cryptography.SecureComputation.SliceReduction.parserEmit (z.length + 1) z
TCSlib.Cryptography.SecureComputation.SliceReduction.length_parserStep_le (z : List Bool) :
  (TCSlib.Cryptography.SecureComputation.SliceReduction.parserStep z).length ≤ max z.length 2
TCSlib.Cryptography.SecureComputation.SliceReduction.polyTimeComputable_slicePost :
  Complexity.PolyTimeComputable TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost
TCSlib.Cryptography.SecureComputation.SliceReduction.length_le_encodeList (l : List (List Bool)) :
  l.length ≤ (TCSlib.Cryptography.PrivateKeyScheme.encodeList l).length
TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost_encode (l : List (List Bool × List Bool)) :
  TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost
      (Turing.pairEncode (TCSlib.Cryptography.PrivateKeyScheme.encodeList (List.map Prod.fst l))
        (TCSlib.Cryptography.PrivateKeyScheme.encodeList (List.map Prod.snd l))) =
    TCSlib.Cryptography.PrivateKeyScheme.encodeList
      (List.map
        (fun e =>
          Turing.pairEncode (Complexity.pairFstD e.2)
            (List.take (Complexity.pairSndD e.1).length
              (List.drop (Complexity.pairFstD e.1).length (Complexity.pairSndD e.2))))
        l)
TCSlib.Cryptography.SecureComputation.SliceReduction.exists_slicePost_nuppt (D : Complexity.NUPPT) (β : ℕ → List Bool)
  (b : Complexity.PolyExpr) (hβ : ∀ (n : ℕ), (β n).length ≤ b.eval n) :
  ∃ B,
    ∀ (n : ℕ),
      ∃ e,
        ∀ (y : List Bool) (r : D.Coins n),
          B.distinguisherL n y (e r) =
            D.distinguisherL n
              (TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost (Turing.pairEncode (β n) y)) r
TCSlib.Cryptography.SecureComputation.SliceReduction.sliceAdvice {Q : ℕ} (n : ℕ) (o len : Fin Q → ℕ) : List Bool
TCSlib.Cryptography.SecureComputation.SliceReduction.sliceAdvice_eq {Q : ℕ} (n : ℕ) (o len : Fin Q → ℕ) :
  TCSlib.Cryptography.SecureComputation.SliceReduction.sliceAdvice n o len =
    TCSlib.Cryptography.PrivateKeyScheme.encodeList
      (List.ofFn fun i => Turing.pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true))
TCSlib.Cryptography.SecureComputation.SliceReduction.length_encodeList_le (l : List (List Bool)) (B : ℕ)
  (h : ∀ c ∈ l, c.length ≤ B) : (TCSlib.Cryptography.PrivateKeyScheme.encodeList l).length ≤ l.length * (2 * B + 2)
TCSlib.Cryptography.SecureComputation.SliceReduction.length_sliceAdvice_le {Q : ℕ} (L n : ℕ) (o len : Fin Q → ℕ)
  (hfit : ∀ (i : Fin Q), o i + n + len i ≤ L) :
  (TCSlib.Cryptography.SecureComputation.SliceReduction.sliceAdvice n o len).length ≤ Q * (6 * L + 6)
TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost_tuple {n L q : ℕ}
  (F : (Fin n → Bool) → (Fin n → Bool) → Fin L → Bool) (o len : Fin (q + 1) → ℕ)
  (hfit : ∀ (i : Fin (q + 1)), o i + n + len i ≤ L) (m : (i : Fin (q + 1)) → Fin (len i) → Bool)
  (t : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) :
  TCSlib.Cryptography.SecureComputation.SliceReduction.slicePost
      (Turing.pairEncode (TCSlib.Cryptography.SecureComputation.SliceReduction.sliceAdvice n o len)
        (TCSlib.Cryptography.encodeTupleOut
          (TCSlib.Cryptography.prfEncRealOut F
            (fun i => TCSlib.Cryptography.SecureComputation.sliceMask L n (o i) (List.ofFn (m i))) t))) =
    TCSlib.Cryptography.PrivateKeyScheme.encodeList
      (List.ofFn fun i =>
        TCSlib.Cryptography.SecureComputation.spEncStr (fun x => List.drop (o i) (List.ofFn (F t.1 (t.2 i))))
          (List.ofFn t.1) (List.ofFn (m i)) (List.ofFn (t.2 i)))
TCSlib.Cryptography.SecureComputation.specialScheme_gen_runAt
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (rg : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).gen.Coins n) :
  (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg
TCSlib.Cryptography.SecureComputation.specialScheme_enc_runAt
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (k m : List Bool) (re : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).enc.Coins n) :
  (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).enc.runAt n (Turing.pairEncode k m) re =
    TCSlib.Cryptography.SecureComputation.spEncStr E k m (List.ofFn re)
TCSlib.Cryptography.SecureComputation.specialScheme_dec_runAt
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (k c : List Bool) (rd : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).dec.Coins n) :
  (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).dec.runAt n (Turing.pairEncode k c) rd =
    (TCSlib.Cryptography.SecureComputation.spDecStr E n n k c).getD (true :: List.replicate n true)
TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool)
TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv_eq
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) :
  TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv G E hE hGE n =
    (Complexity.NUPPT.coinsCongr ⋯ n).trans
      ((Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform Complexity.polyTimeComputable_pairSndD Complexity.PolyExpr.var
            n).trans
        ((finCongr ⋯).arrowCongr (Equiv.refl Bool)))
TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv_ofFn
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (rg : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).gen.Coins n) :
  List.ofFn ((TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv G E hE hGE n) rg) = List.ofFn rg
TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool)
TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv_eq
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) :
  TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv G E hE hGE n =
    (Complexity.NUPPT.coinsCongr ⋯ n).trans
      ((Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform ⋯ Complexity.PolyExpr.var n).trans
        ((finCongr ⋯).arrowCongr (Equiv.refl Bool)))
TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv_ofFn
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (re : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).enc.Coins n) :
  List.ofFn ((TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv G E hE hGE n) re) = List.ofFn re
TCSlib.Cryptography.SecureComputation.spEncStr_eq_zeroPrefixMask (E : List Bool → List Bool) (k m r : List Bool)
  (hp : r.length + m.length ≤ (E (Turing.pairEncode k r)).length) :
  TCSlib.Cryptography.SecureComputation.spEncStr E k m r =
    Turing.pairEncode r (List.zipWith xor (List.replicate r.length false ++ m) (E (Turing.pairEncode k r)))
TCSlib.Cryptography.SecureComputation.sliceMask (L n o : ℕ) (m : List Bool) : Fin L → Bool
TCSlib.Cryptography.SecureComputation.sliceMask_eq (L n o : ℕ) (m : List Bool) :
  TCSlib.Cryptography.SecureComputation.sliceMask L n o m =
    TCSlib.Cryptography.padFin L (List.replicate (o + n) false ++ m ++ List.replicate (L - (o + n + m.length)) false)
TCSlib.Cryptography.SecureComputation.ofFn_sliceMask (L n o : ℕ) (m : List Bool) (h : o + n + m.length ≤ L) :
  List.ofFn (TCSlib.Cryptography.SecureComputation.sliceMask L n o m) =
    List.replicate (o + n) false ++ m ++ List.replicate (L - (o + n + m.length)) false
TCSlib.Cryptography.SecureComputation.spEncStr_eq_sliceMask (L o : ℕ) (pad k m r : List Bool) (hp : pad.length = L)
  (hfit : o + r.length + m.length ≤ L) :
  TCSlib.Cryptography.SecureComputation.spEncStr (fun x => List.drop o pad) k m r =
    Turing.pairEncode r
      (List.take (r.length + m.length)
        (List.drop o
          (List.zipWith xor (List.ofFn (TCSlib.Cryptography.SecureComputation.sliceMask L r.length o m)) pad)))
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.prefixTest (E : List Bool → List Bool) (z : List Bool) : List Bool
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.prefixTest_eq (E : List Bool → List Bool) (z : List Bool) :
  TCSlib.Cryptography.SecureComputation.SpecialWrongKey.prefixTest E z =
    [decide
        (List.take (Complexity.NUPPT.inParam z).length (Complexity.pairSndD (Complexity.NUPPT.inArg z)) =
          List.take (Complexity.NUPPT.inParam z).length
            (E (Turing.pairEncode (Complexity.NUPPT.inCoins z) (Complexity.pairFstD (Complexity.NUPPT.inArg z)))))]
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.polyTimeComputable_prefixTest {E : List Bool → List Bool}
  (hE : Complexity.PolyTimeComputable E) :
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.SpecialWrongKey.prefixTest E)
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.uprob_random_prefix {n L : ℕ} (h : n ≤ L) (r v : Fin n → Bool) :
  (TCSlib.Cryptography.uprob fun R => List.take n (List.ofFn (R r)) = List.ofFn v) = 2⁻¹ ^ n
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.exists_negligible_prefix_collision (ℓ : Complexity.PolyExpr)
  (F : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((Complexity.PolyExpr.var.add ℓ).eval n) → Bool)
  (E : List Bool → List Bool) (hE : Complexity.PolyTimeComputable E)
  (hFE : ∀ (n : ℕ) (k r : Fin n → Bool), E (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (F n k r))
  (hF :
    (TCSlib.Cryptography.OracleEnsemble.keyed F).Indist
      (TCSlib.Cryptography.OracleEnsemble.random Complexity.PolyExpr.var (Complexity.PolyExpr.var.add ℓ))) :
  ∃ ε,
    TCSlib.Cryptography.Negligible ε ∧
      ∀ (n : ℕ),
        (TCSlib.Cryptography.uprob fun t =>
            List.take n (List.ofFn (F n t.1 t.2.2)) = List.take n (List.ofFn (F n t.2.1 t.2.2))) ≤
          ε n
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.spDecStr_none_iff_prefix_ne {n l : ℕ}
  (F : (Fin n → Bool) → (Fin n → Bool) → Fin (n + l) → Bool) (E : List Bool → List Bool)
  (hFE : ∀ (k r : Fin n → Bool), E (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (F k r))
  (k k' r : Fin n → Bool) (m : Fin l → Bool) :
  TCSlib.Cryptography.SecureComputation.spDecStr E n l (List.ofFn k')
        (TCSlib.Cryptography.SecureComputation.spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)) =
      none ↔
    List.take n (List.ofFn (F k r)) ≠ List.take n (List.ofFn (F k' r))
```
