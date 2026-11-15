## ===== briefs/pass-shelat-ch5-8/gates/31-prf-long/pack.md =====

# Gate 31 · The PRF machinery at ℓ(n)-bit outputs (`prf-long`, ruling B3)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #315](https://github.com/Shilun-Allan-Li/tcslib/pull/315) at
  `fbd37f447596d4207c8d08b7ef7602f57fe95198` (branch `land/pass-shelat-prf-long`, tree
  `c0609c53b694d1899f8e2b8b6b0f7fd9357dc4cf`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `dd98360d4886ac68fab34899b8bd0d12ae9a0aef` (the merge base).
  - The fill was issued on `7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee`. Between the issue base and the PR base, the only
    non-record paths are those of the merged #311 (B1 statement: `SecureComputation.lean`,
    `SecureComputation/SpecialEncryptionMulti.lean`) and #312 (derand host: `Complexity/Randomized.lean`,
    `Complexity/Randomized/SeedMajority.lean`), plus `machine-library-design.md`. Re-checked for this pack from git
    objects (`pack-checks/issuedelta.txt` in `verification.zip`): none of the eight scope files changed; no delta
    module is in the closure, at the head, of a changed module. Four head modules are downstream of both a delta module
    and a PR module: `SpecialEncryptionMulti`, the `SecureComputation` facade, root `TCSlib` and
    `audits/pass-shelat/Checks`. All four are in the review's build (below).
  - From the PR base to the records tip `59c2c1fbf8c1bb08f9d191012b7cdd7e15248531` there are 5 commits: records
    commits, and **#314 (the `prfAdv_eq_expect` promotion), merged at `59c2c1fb`** (second parent
    `a24a6313e20a0c3120d457fa4fb0960c72c06312`, after LE-gate30). Its two Lean paths,
    `Pseudorandom/Functions/Defs.lean` and `Encryption/PrivateKey/EncryptThenTag/Reduction.lean`, are not PR paths;
    both are in the closure, at the head, of the PR's changed modules (through `Asymptotic/Defs` and the
    `PrivateKey` facade), and 138 tip modules are downstream of both a #314 module and a PR module
    (`pack-checks/deltacheck-tip.txt`). `git merge-tree --write-tree` of the tip with the head gives tree
    `140e60fb691048f5b8c160c23d388c90fd8e9bdd` with no conflict; it differs from the head exactly in #314's two files
    and from the tip exactly in the PR's six (`pack-checks/mergetrees.txt`). Before #314 merged, the tip
    `0e5e725d` was records-only past the PR base (merge tree `b208dae9`, Lean identical to the head). **Pending merge
    condition** (not an audit item): #315 needs an integration rebuild of `Functions/Defs`' downstream on the merged
    tip before it merges; the maintainer runs that build (question 6).
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...fbd37f44`, which equals `dd98360d..fbd37f44`
    byte for byte (6 paths, 908 insertions, 279 deletions).
- **Commits:** 6.
  - The Claude worker's 4 commits (job `prf-long`), applied with `git am` with the delivered committer data and
    rebased without conflict, author kept: `2d4fb3f68b9a9ef0fb1668da4a83a7110f666db8` (checkpoint 1: D1, D2),
    `ccb5142759650b28a47792353b57e56b1ecb8711` (checkpoint 2: D3), `05deb4d8a1361553a2b4749cf7548ffd8eecc1cb`
    (checkpoint 2: two readers) and `2205e3324d3ce0cbfa4904330c49883cd3ea2501` (final: D4 and the re-derivations). At
    `2205e332` the 6 files are byte-identical to the worker's `src/` (exchange `8d44fa5b`;
    `pack-checks/srcequality.txt`). The worker hashes (`94e7c1eb`, `200b6b50`, `eff869dc`, `40127c58`) reproduce only
    with the environment's SSH commit signing on; the signing was not recorded (review F-03).
  - Landing edit **LE-doc** `ea50e92ccbd397d9fd511e29fdda275b69eae687`: three formula docstrings in
    `ReductionMachine.lean`; docstrings only.
  - Landing edit **LE-ws** `fbd37f447596d4207c8d08b7ef7602f57fe95198` (the head): one blank line restored in
    `Hybrid.lean`; whitespace only.
- **Scope:** a **machinery audit**. Under Seyoon's ruling **B3** (2026-11-14) the PRF machinery of [PS10, Theorem 99.2]
  is generalized from `n`-bit to `ℓ(n)`-bit outputs **first, in a separate job, inside the frozen `FromPRF`/PRF files
  it owns (pre-approved scope), additively**, instead of being duplicated by the secure-computation units. The `n`-bit
  versions are re-derived as corollaries. The job proves **no admitted target** and removes no `sorry`, by design.
  Its consumer is `sc-garble`: the B1 statement `sliceMultiMessageSecure_of_prfOut` (merged in #311, Gate 27 CLEAR)
  and `spDecStr_wrongKey`.
- **Brief:** `fills/prf-long/issued-r1/brief.md` on the records branch (SHA-256 `ce6c4bec…`; exchange pack
  `b97d3595`): the drafted signatures of D1–D4, the owned frozen files and permitted new modules, the binding
  frozen-statement rule with a header check and control, the re-derivation list and its fallback (kept declarations as
  ledger rows), the B1 consumer map as a required REPORT section, the duplication rule with an `## Overlap and reuse`
  section, Rule 10 with the projection-coercion ruling and seals with `PolyExpr.eval` both excluded and sealed, the
  G26-N1 error count, and the evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/`; `F/` is `Encryption/PrivateKey/FromPRF/`. Line counts are base → worker head
`2205e332` → LE-doc `ea50e92c` → PR head.

| File | Status | Lines | New declarations |
|---|---|---:|---:|
| `Pseudorandom/Functions/Asymptotic/Defs.lean` | owned frozen, modified | 447 → 480 → 480 → 480 | 2 (D1) |
| `F/Hybrid.lean` | owned frozen, modified | 349 → 511 → 511 → 512 | 15 (D2) |
| `F/ReductionMachine.lean` | owned frozen, modified | 572 → 889 → 892 → 892 | 38 (D3) |
| `F/MultiMsgOut.lean` | new | 163 → 163 → 163 | 5 (D4) |
| `Encryption/PrivateKey/FromPRF.lean` | owned frozen facade, modified | 424 → 372 → 372 → 372 | 1 (bridge) |
| `Encryption/PrivateKey.lean` | facade: one import, one `## Contents` bullet | 75 → 77 → 77 → 77 | 0 |

`F/HybridLemmas.lean` and `Pseudorandom/Functions.lean` (also owned) are unchanged. The worker REPORT's line counts
(511, 889) are the worker head's, before LE-doc and LE-ws.

**The deliverables** (drafted in the brief; the REPORT lists all 61 new declarations, `evidence/final/new-decls.txt`):
- **D1** `prfAdv_toOracleAdversary_out` (`distAdv` of the keyed and random oracle ensembles at output length `ℓ₂` is
  `prfAdv (F n) …`) and `OracleEnsemble.Indist.negligible_prfAdv` (the ℓ₂-analogue of `PRF.negligible_prfAdv`, on
  `PRFOut`'s clause (2) as hypothesis, since `PRFOut` lives downstream in `SecureComputation`).
- **D2** the concrete hybrids at output width `l`: `prfEncRealOut`, `otpEncOut`, `multiMsgAdvOut` with readers, and
  `acceptProb_oracleDist_multiMsgAdvOut`, `prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_random_otp_le`,
  `acceptProb_otpEncOut`, `distAdv_prfEncRealOut_le`; `rfl` bridges from the frozen `prfEncReal`, `otpEnc`,
  `multiMsgAdv`.
- **D3** `MultiMsg.exists_queryChainOut_nuppt` (the query-chain machine with `ℓ(n)`-bit answers and masks; its tree
  evaluates `D` on the flattened masked transcript `⟨⟨ρ_j, v_j ⊕ g(ρ_j)⟩, []⟩` for every oracle `g`, with a coin
  equivalence) and its corollary `MultiMsg.exists_oneQuery_nuppt`; the string layer at width `ℓ(n)` (`histBlockOut`,
  `maskBlockOut`, `maskOfOut`, `histBlockLenOut`, `postCountOut`, `postOffsetOut`, `postQueryOut`, `postFunOut`,
  `adviceBoundOut`, each with a reader, and their lemmas), with bridges from the frozen `n`-bit definitions.
- **D4** (new `F/MultiMsgOut.lean`) `encodeTupleOut` with `encodeTupleOut_eq` and `encodeTupleOut_eq_flatten`,
  `MultiMsg.encodeList_eq_flatMap`, and the total `MultiMsg.exists_negligible_distAdv_prfEncRealOut`: one negligible
  `ε` bounds `distAdv (encodeTupleOut ∘ prfEncRealOut (F n) w) (… w') (D.distinguisherL n)` for **all** `n, w, w'`.

**Re-derivations** (proof-only, REPORT § *Re-derivations*, `evidence/final/rederivations.txt`: 22 CHANGED theorems,
each now proved from its `Out` form at `l = n`, `ℓ = .var` or `ℓ₂ = .var`): Defs 2, Hybrid 8, ReductionMachine 10,
`FromPRF.lean` 2 (`encodeTuple_eq_flatten`, `prfScheme_multiMessageSecure`). Kept by design: the width-free helpers
the brief lists. **Ledger** residues (REPORT): `histBlockLen`/`eval_histBlockLen` kept beside the `Out` forms (a
different `PolyExpr` term, no `rfl` bridge); `adviceBound` and the frozen private `encodeList_eq_flatMap` of
`FromPRF.lean` now unused; `MultiMsg.encodeList_eq_flatMap` a third copy of a public lemma (ruling 7).

**Disclosed deviations from the brief's lists** (REPORT § *New declarations*): `postQueryOut` added (the brief listed
`postQuery` as width-free, but it reads `postOffset`); `maskBlockOut n w` and `maskOfOut n v` take `n` explicitly;
two extra readers `histBlockLenOut_eq`, `adviceBoundOut_eq`; D1's re-derivation needs an explicit `(ℓ₂ := .var)`.

**Statements:** decls2 from the issue base to the head gives 61 ADDED, 0 CHANGED, 0 REMOVED (review
`statements/decls2.tsv`). Re-checked for this pack from git objects with `maintainer/tools/decls2.py`'s parser: 61
ADDED and 123 unchanged against both the issue base and the PR base (`pack-checks/decls2-vs-*.tsv`), and 0 rows
from the worker head `2205e332` to the PR head. decls2 does not key three base declarations (the private
`zipWith_xor_xor_self` and `encodeList_eq_flatMap` of `FromPRF.lean`, and `decodeOracleMove`; `decls2count.txt`);
their blocks are byte-identical (`private3.txt`), and so are all 38 base definition blocks of the four modified
owned files (`defblocks.txt`). The review's independent `frozencheck.py` covers all 126 base declarations of the 8
scope files (headers with attributes and `omit … in` lines, the statement prose before each sketch, and every
definition in full): 0 differences, and each of its five controls reports exactly one (`landing/frozen-check.txt`,
`statements/frozen/` in `verification.zip`).

## Rulings and records in force

1. **B3 (Seyoon, 2026-11-14): generalize first, in a separate job, inside the owned frozen files, additively.** The
   brief pre-approves edits to six frozen files (`Asymptotic/Defs`, `F/Hybrid`, `F/ReductionMachine`,
   `F/HybridLemmas`, the `FromPRF.lean` facade, the `Pseudorandom/Functions.lean` facade), new modules in `F/` and
   `Functions/Asymptotic/`, and one import plus one `## Contents` bullet per new module in `Encryption/PrivateKey.lean`.
   The delivery stays inside that scope; no scope request was made. **Not a finding** by itself: editing these files.
2. **The frozen-statement rule (the brief, binding).** Every base declaration of an owned file stays in place and in
   order with its header byte-identical (attributes, modifiers, keyword, name, binders and type up to the proof); every
   `def`, `abbrev`, `structure`, `inductive`, `class` and `instance` stays byte-identical, body included; only theorem
   proofs, their sketches ("the case `ℓ = n` of …"), module docstrings and additions may change; nothing is deleted.
3. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** The
   coe-variant seals are canonical; the strict variant is run and its differences attributed. **For this unit strict
   and coe agree in every row**, at the base and the head (`evidence/logs/seal-table.txt`).
4. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal A, which exempts it, is canonical; seal B is run and
   reported because the brief asks for both. The brief itself says the `n`-bit re-derivations differ from the generic
   forms only by `PolyExpr.var.eval n` against `n`.
5. **The facade-completeness lint fix, #305 (Seyoon's ruling of 2026-11-14).** The baseline is **92 FAIL / 101 WARN**
   (re-run at the issue base). The records tip and the landing head both give 92 / 101 with no new FAIL or WARN line;
   two check-8 WARN lines of owned files are **shortened** by bridges named after listed definitions (`Hybrid`:
   `chainTree, otpEnc` → `chainTree`; `ReductionMachine`: 16 → 10 definitions), as the brief anticipates and the
   REPORT discloses (`evidence/lint/linediff.txt`). Under the pre-#305 lint the new module adds one "facade does not
   import child module" FAIL, the class #305 fixed.
6. **LE-doc and LE-ws (the maintainer's landing edits).** LE-doc gives `postOffsetOut` and `postQueryOut` their
   defining formulas and `polyTimeComputable_postFunOut` the formula `PolyTimeComputable (postFunOut ℓ)` (review
   F-04); LE-ws restores the blank line between the re-derived `prfEncReal_apply` and `otpEnc`'s docstring (F-05).
   Re-checked for this pack from git objects (`pack-checks/lecheck.txt`): `2205e332..ea50e92c` is identical after
   blanking doc comments (1 file, 0 failing); `ea50e92c..fbd37f44` is identical after deleting whitespace, and
   `git diff --ignore-blank-lines` is empty; decls2 `2205e332..fbd37f44` gives 0 rows. The precedents are ext-nosrc,
   cca2-ett, dl-crh, hash-sign, lamport and learning.
7. **DL-46 (duplication ledger, open, deferred).** Disclosed by the worker and recorded by the review (F-01, F-02,
   F-06): `MultiMsg.encodeList_eq_flatMap` (`F/MultiMsgOut.lean`) is a third copy of the public
   `TCSlib.Cryptography.encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean:60`), beside the frozen private copy
   in `FromPRF.lean`, now unused. Reuse is blocked: with `BlockEncryptor` in `FromPRF.lean`'s closure the frozen
   private copy fails to declare (the worker's clash probe, `worker/evidence/final/clash-probe.log`: exactly that one
   error). `histBlockLen` is kept beside `histBlockLenOut`; `adviceBound` is now unused. Near relatives (not
   restatements): GGM's `encodeHist_eq_histEnc`, `histEnc_append_single`, `length_histEnc`, and
   `UniformTableauEmitter.encodeList_eq_flatMap`. The worker's promotion request (move `encodeList_eq_flatMap` to
   `EnsembleSecurity`, delete both copies) is deferred to the cleanup (Seyoon's deferral of 2026-11-14).
8. **B1 and Gate 27 (statement, merged).** The B1 statement `sliceMultiMessageSecure_of_prfOut` is the maintainer's
   (ruling B1, 2026-11-14), merged in #311 after Gate 27 closed CLEAR (0/0/1/0; G27-01 fixed by LE-gate27). Gate 27's
   resolutions record Codex's **hand-off obligations**: for `prf-long`, `ℓ`-bit answers with `n`-bit queries, keys and
   nonces, a query-tree evaluation identity for arbitrary oracles with its coin equivalence and its advice and query
   bounds, and polynomial-time post-processing of the full answer transcript by the consumer; for `sc-garble`, the
   maximizing advice with the empty-set convention, the slice post-processor, the random-function slice law, the
   triangle bound, the frozen theorem via the corollary, and B2. The maintainer's check at the time: an "equivalent
   sufficiently general API", to be re-checked at the prf-long review.

## What is frozen

- **Every base declaration of the 8 scope files** (rule 2): 126 declarations, 38 of them definition-like, with their
  headers, statement prose and definition bodies, their order, `set_option`s, `open`s and attributes.
- **Every file outside the scope**, in particular `SecureComputation/*` (the B1 statement and `PRFOut`, owned by
  `sc-garble`), `Pseudorandom/Functions/Defs.lean` (`prfAdv`; #314 added `prfAdv_eq_expect` to it, merged at
  `59c2c1fb`), `OracleAdversary.lean`, `LazySampling.lean`, `SubHybrids.lean`, the GGM files, `OracleFromPRF*`,
  `EncryptThenTag*` and `Games/*` (`Games/Efficiency.lean` at 982 lines).
- **The landing edits:** LE-doc three docstrings; LE-ws one blank line.

## Questions for the audit

**1. Frozen-statement integrity; the re-derivations are proof-only**
- Are all 126 base declarations of the 8 scope files present, in order, with byte-identical headers (attributes,
  modifiers and `omit … in` lines included) and statement prose, and are all 38 definition-like declarations
  byte-identical in full (`landing/frozen-check.txt`; `statements/frozen/` and `pack-checks/` in `verification.zip`)?
- Is each of the 22 changed base theorems changed only in its proof and its `**Proof sketch.**` paragraph, and is each
  new proof a genuine case of its `Out` form (`l = n`, `ℓ = .var`, `ℓ₂ = .var`) through the `rfl` or same-file
  defeq bridges (`postCount`/`postOffset`/`postQuery`/`postFun` at `6n + 6 = 4n + 2n + 6`), not a weakening
  (`evidence/statements/touched.tsv`, `worker/evidence/final/rederivations.txt`)?
- Is anything deleted, private lemmas included, or any `set_option`, `open`, `variable` or attribute removed or
  changed (`evidence/statements/frozen/topcmds.txt`: added `variable {l : ℕ}` and imports only)?
- Are the 15 base constants no longer stored all auto-generated (`.eq_1` equation lemmas, `match_`/`_proof_`
  auxiliaries of replaced proofs), and is that harmless for downstream `rw`/`simp`/`unfold` uses
  (`evidence/logs/census-base-vs-head.tsv`; REPORT § *Checks*, *Axioms*)?

**2. D1–D4: correctness and the drafts**
- Do the 23 drafted D1–D4 declarations match the brief's signatures, names and binders, with the deviations
  disclosed (`evidence/statements/draft-vs-delivered.txt`; REPORT § *New declarations*)? Is `postQueryOut` needed
  as the REPORT says?
- Are the generic statements true and as general as drafted, with no hidden side condition on `n`, `ℓ` or `q`:
  `ℓ(n) = 0`, `n = 0`, `q(n) = 0`, the one-query budget `1` against `(PolyExpr.const 0).eval n + 1`, malformed moves
  and the budget timeout, block lengths `4n + 2ℓ(n) + 6 > 0` (`worker/evidence/final/edge-cases.log` and its source)?
- Is `exists_queryChainOut_nuppt` a legitimate NUPPT next-query machine for every `D`, `q`, `ℓ` and mask family `v`,
  with the coin equivalence correct, the canonical history producing well-formed queries and the verdict at
  `k = q(n) + 1` (neither the malformed-move nor the forced-`false` branch reached), and is `exists_oneQuery_nuppt`
  really its corollary rather than a second machine?
- Does `MultiMsg.exists_negligible_distAdv_prfEncRealOut` give one `ε` uniform in `n`, `w` and `w'` (the
  maximization over the finite mask pairs), with the PRF step at budget `q + 1` and the collision bound
  `C(q+1, 2)/2^n` inside?
- Are the new docstrings' formulas right, with the arguments in Lean order (`evidence/statements/docaudit.tsv`; LE-doc
  in `evidence/landing/le-doc.diff`)? A misstated formula is a minor.

**3. The B1 consumer map and Gate 27's hand-off**
- Is the REPORT's `## B1 consumer map` correct against the merged `SecureComputation/SpecialEncryptionMulti.lean`
  (in the bundle)? In particular: with masks `w_i = 0^{o_i + n} ‖ m_i ‖ 0^{ℓ(n) − o_i − n − ℓ_i}` and the post-map
  `P : (r, u) ↦ (r, (u.drop o_i).take (n + ℓ_i))` applied inside `encodeList`, is `P ∘ encodeTupleOut ∘
  prfEncRealOut (G n) w` exactly `sliceMultiEncDist G n q o len m` on the same seed space
  `(Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)` (review § *Content*; `spEncStr` is `⟨r, p_{<n} ‖ (m ⊕ p_{≥n})⟩`
  with `p = G_k(r)_{≥o}`)?
- Since D4's `ε` precedes the masks, does `D' = D ∘ P` with the maximizing slices and messages as advice, the
  maximization over the finitely many fitting slices (value 0 when none fits), give B1's `ε`, and then
  `specialScheme_multiMessageSecure` through the proved `specialScheme_multiMessageSecure_of_joint`?
- Is `hG.pseudorandom` literally the hypothesis of D1 and D4, with no conversion (the worker's
  `worker/evidence/final/b1-probe.log` and the review's `evidence/probe-sources/consumer/ConsumerB1.lean`, run rc 0 at
  the landing head; note that the probe's second example is a tautology that only checks the two seed types agree)?
- Does the API meet Gate 27's prf-long hand-off: `ℓ`-bit answers with `n`-bit queries, keys and nonces; an evaluation
  identity for arbitrary oracles with the coin equivalence; the advice and query bounds (the review's caveat: they stay
  inside the existential of the NUPPT, and the queries are a non-adaptive chain of uniform points); and transcript
  post-processing folded into the consumer's `D`? Is that enough for `spDecStr_wrongKey` through
  `exists_oneQuery_nuppt` at budget 1?
- What does the map leave to `sc-garble` that the `sc-garble` brief must carry (step 0: the slice post-processor, the
  mask construction, the fit `o_i + n + ℓ_i ≤ ℓ(n)`, the maximization; the random-function probability of
  `spDecStr_wrongKey`)?

**4. Duplication (recent gates graded undisclosed re-proofs as majors)**
- Does any new declaration, or any part of a new or re-derived proof, duplicate a public TCSlib or Mathlib lemma, or
  copy a private one, beyond the worker's `## Overlap and reuse` table and DL-46 (ruling 7)? The recent majors were of
  exactly this class: G23-01 (a private copy of `length_le_length_encodeLog`), G24-01 (`inputWord_take` re-proving
  `take_ofFn_castLE`), prf-mac F-01 (`hadv` = `ETTGame.prfAdv_eq_expect`), learning (`uprob_eq_point` =
  `OneWay.uprob_eq_one_div_card`, an inline `abs_uexp_sub_le_uprob`) and G29-01/G29-02 (`hj` = `OneWay.uexp_const`,
  `firstBit_of_pos` re-proving `LamportFill.headD_drop_ofFn`). Search in particular probability, expectation and list
  identities inside the D2 and D4 proofs (`uexp_*`, `uprob_*`, `prfAdv_eq_expect`, `acceptProb_comp_equiv`,
  `take_drop_ofFn_blocks`, `List.ofFn`/`flatMap`/`take`/`drop` readings, `zipWith_xor_*`).
- Are the disclosed relations accurate and their "why not reused" reasons valid: the chain machine not built from
  `Games/Efficiency` T2/T4; `ETTGame.eval_toOracleAdversary_len` and `PRFGame.eval_toOracleAdversary_width` not
  needed; `NMSim.chunkMap` not used; `MultiMsg.take_drop_ofFn_blocks` (DL-9 twin) and the `zipWith_xor_*` (DL-40)
  reused, not copied (`worker/evidence/overlap/dupsearch-final.log`; the review's `landing/duplication-review.txt`)?
- Is the DL-46 clash argument right (the worker's clash probe), so that the third copy is forced under the frozen rule?

**5. Rule 10**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 6 changed
  files over the full closure, at the base and the head, in both variants (`evidence/logs/seal-table.txt`)? With
  variant **A** canonical (rulings 3, 4), does every file pass, strict and coe?
- Is the **seal-B attribution** sound (`landing/seal-B-attribution.txt`)? At the head 6 declarations fail B that did
  not at the base: `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` (Defs; the base `PRF`,
  `prfAdv_toOracleAdversary`, `PRF.negligible_prfAdv` fail B already), `postFun_layout`, `exists_queryChain_nuppt`
  (ReductionMachine, **whose base passes B**), the D4 total (new file), and `prfScheme_multiMessageSecure`
  (`FromPRF.lean`, beside the three base failures). The attribution reads every B error as a `PolyExpr.eval`
  defeq (`Fin n` against `Fin (PolyExpr.var.eval n)`, `?ℓ.eval n =?= n`) or its unknown-identifier cascade, and the
  three `OTHER`-classified blocks by hand. Is any B error a foreign definition read instead?
- Do the paired controls bite (14 probes per variant, ALL_OK in both harnesses; `evidence/logs/ctlcheck.log`,
  `ctlcheck-strict.log`)? Explicit-unfold scan at the head: 570 items, 0 foreign (`evidence/logs/scan2-head.log`,
  `scan-owned-and-local.txt`).
- Does any proof read a foreign definition other than through a published reader, given that each owned file and the
  new module count as foreign to each other (for example `MultiMsgOut` reading `prfEncRealOut` only through
  `prfEncRealOut_apply`), with only same-file bridges between a frozen definition and its `Out` form?

**6. The interaction with the merged #314 (and the open #313)**
- #314 (the `prfAdv_eq_expect` promotion, Gate 30 CLEAR) is **merged at `59c2c1fb`** (head `a24a6313`, which adds
  LE-gate30's docstring fix to the `5757bc06` the review checked). It edits `Pseudorandom/Functions/Defs.lean`,
  which is upstream of every unit module, and `EncryptThenTag/Reduction.lean`, downstream of `Asymptotic/Defs`.
  Neither PR touches the other's files; `git merge-tree --write-tree` of the head with the merged tip gives
  `140e60fb…` with no conflict (`pack-checks/mergetrees.txt`; the review's check with `5757bc06`,
  `evidence/logs/pr314-overlap.txt`, also found no name clash among the 61 new names in the merge tree).
- **Pending merge condition (not an audit item).** The combined tree is **not** built. Because #314 merged first,
  #315 needs an integration rebuild of `Functions/Defs`' downstream on the merged tip (it contains every unit module)
  before it merges. The maintainer runs that build; treat it as a condition on the merge, not as something for this
  audit to establish. What you can raise: a concrete reason the merged tree cannot build, or a name or instance
  interaction.
- The open #313 (`learning`, Gate 29 HOLD, round 2 pending) imports `F/ReductionMachine` and `F/HybridLemmas` and uses
  `exists_queryChain_nuppt`, `histBlockLen`, `eval_histBlockLen`, `flatMap_range_blocks` and
  `abs_uexp_sub_le_uprob`, all base declarations with unchanged headers here. `git merge-tree --write-tree fbd37f44
  8befc589` gives `64914282…` with no conflict; not built. Whichever of #313 and #315 merges second gets the same
  kind of rebuild.

## Known dispositions (not findings)

- **The review's and the PR description's wording on seal B.** Both say "Seal B fails only where the base already
  fails, on `PolyExpr.eval`." The accurate statement is question 5's: B fails on 6 more declarations at the head, two
  of them in `ReductionMachine.lean`, whose base passes B; every failure is the `PolyExpr.eval` (Q1) class or its
  cascade. Rate the wording if you think it misleads.
- **Commit-hash reproduction (review F-03).** `git am` reproduces the four worker hashes only with the environment's
  deterministic SSH signing on; with `commit.gpgsign=false` the tree is identical and the ids differ
  (`evidence/logs/git-am-integrity*.log`). Briefs going forward require a signing column or `commit.gpgsign=false`.
- **The build ran at `1b5b802b`,** the landing head before the review's second rebase (onto `dd98360d`, records-only
  movement). Its Lean is that of `fbd37f44`: the range-diff is 6/6 identical and the Lean diff of the two heads is empty
  (`evidence/landing/rebase-r2.log`), and every built module's `source_sha256` equals the blob at `fbd37f44`
  (checked for this pack; `landing/root-checks.jsonl`).
- **The worker's own seal and control tables** (REPORT § *Checks*) count per variant and are consistent with the
  review's; the review's runs are the ones cited here. The worker's two earlier control attempts are disclosed and kept
  (logs only).
- **Unused frozen items** (`adviceBound`, the private `encodeList_eq_flatMap`): kept by the rule "delete nothing";
  their removal is DL-46's cleanup (under a frozen-file exception).
- **Old lint +1** (ruling 5): the pre-#305 facade class, recorded, not a finding.
- **Wide lines:** 18 lines over 100 characters remain in the owned files, all base lines kept verbatim; no new wide line
  (`evidence/logs/new-wide-lines.txt`). `ReductionMachine.lean` is at 892 lines (brief limit 1000).

## Also check

**Axioms**
- At the head the 15 endpoints (D1–D4's main results, the re-derived `n`-bit results and the five downstream
  consumers `prfScheme_multiMessageSecure`, `exists_multiMessageSecure_of_exists_prg`,
  `Composability.prfFixedScheme_cpa`, `Composability.ccaScheme_cca2`, `exists_prf_of_exists_prg`) print
  `[propext, Classical.choice, Quot.sound]` (`landing/census-head.log`, lines 1–17: 15 prints, one wrapped over
  three lines). All 321 stored constants of
  the 5 unit modules use subsets of these; no `sorryAx` (`evidence/logs/census-summary.txt`).
- Census base 250 → head 321: 15 removed (all auto-generated), 86 added (61 named), 0 type, attribute or axiom changes
  (`evidence/logs/census-base-vs-head.tsv`). The worker's base-and-final comparison of the five consumers is
  identical (`worker/evidence/axioms/axioms-compare.txt`).
- Nothing new is `@[simp]`, an instance or an abbreviation (the 2 added abbrev-flagged constants are generated
  matchers).

**Admissions:** 40 in 19 modules at the issue base and the head, unchanged, as designed (`evidence/logs/sorry-census.txt`).

**Sizes and widths:** every file at most 892 lines; no new line over 100 characters (`source-head.json`,
`evidence/logs/sizes-widths.txt`).

**Build:** the 121 modules downstream of the 61 modules changed between `eff2dcd0` and the head (the 55 base-delta
modules of #303, #306–#309, #311 and #312, and the 6 unit modules), through root `TCSlib` and both
`audits/*/Checks`, have rc 0, 0 errors in both diagnostic forms (`landing/root-checks.jsonl`, whose last line is the
runner's `done` record; `landing/build-summary.txt`). The whole-tree check covers 1244 modules, RESULT OK
(`landing/tree-check-head.txt`); the olean tree was restored to the base snapshot afterwards
(`evidence/tree/tree-check-post.txt`).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (F-01–F-07).
- **`verification.zip`** (96 entries): every file the review cites and the pack's re-checks, as byte-identical
  originals. Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/prf-long/final-r1/`, SHA-256 `0586d82e…`) and `review-evidence-SHA256SUMS`, its
    manifest. The ZIP has 710 entries, 65 directories and 645 files: under `prf-long-r1/`, exactly the 644 manifest
    paths plus that folder's `SHA256SUMS`, which is byte-identical to the manifest; all 644 hashes verify. It covers
    integrity, the landing and the landing edits, the build and the whole-tree check with the restore, decls2,
    `touched`, the frozen check and its controls, the draft comparison, the docstring and sketch audits, the census
    and axioms, the strict and coe seals at the base and the head, the paired controls in both harnesses, the scan,
    the old and new lint, sizes, the consumer probes, the #314 overlap and the duplication review;
  - `landing/`: the review's extracts `PROVENANCE.txt`, `duplication-review.txt` and `seal-B-attribution.txt` (byte
    copies of ZIP entries);
  - `evidence/` (43): byte copies of the ZIP entries this pack cites;
  - `records/` (16): the issue package `fills/prf-long/issued-r1/`, the decision log, the duplication ledger (DL-46),
    the #305 record (README and patch), Gate 27's resolutions and Codex's Gate 27 findings, and the secure-computation
    plan, at records `59c2c1fbf8c1bb08f9d191012b7cdd7e15248531` (the cited records are unchanged from `0e5e725d`);
  - `worker/` (15): byte copies from exchange `8d44fa5b5cdd408b9361364a246697dc294151fb` (`inbox/fills/prf-long/`):
    `patches/COMMITS.tsv`, the header check and its control, `new-decls.txt`, `rederivations.txt`, the B1, clash and
    edge-case probes with their logs, the final duplication search, the axiom comparison, the lint diff and the
    `git am` check; 11 of them are also byte-identical to the review's delivery extracts;
  - `pack-checks/` (15): the re-checks for this pack, from git objects only (no Lean).
- **The worker's own evidence:** on the exchange at `8d44fa5b5cdd408b9361364a246697dc294151fb`, under
  `inbox/fills/prf-long/`. Its top `SHA256SUMS` lists 1755 files and `evidence/SHA256SUMS` 1742, all delivered.
- **`landing/`:** byte copies of review-evidence entries.
  - `root-checks.jsonl` (= `build/results.jsonl`): the 121 modules, rc 0.
  - `build-summary.txt` (= `build/summary.txt`).
  - `census-head.log` (= `probe-runs/mods/PlProbe_CensusHead.log`): the 15 endpoint axiom prints, then the census rows.
  - `tree-check-head.txt` (= `tree/tree-check-head.txt`): the whole-tree check.
  - `frozen-check.txt` (= `statements/frozen/frozen-check.txt`).
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `8d44fa5b` (byte-identical to the review's
  `logs/worker-REPORT.md`).
- **`pr-description.md`:** the PR #315 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (6 paths, 908 insertions, 279 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 6 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 180 files.
- **The bundle** adds, as context at the head: `SecureComputation/SpecialEncryptionMulti.lean` (the merged B1
  statement), `SecureComputation/SpecialEncryptionSecurity.lean` (`PRFOut`, `spDecStr_wrongKey`) and
  `SecureComputation/SpecialEncryption.lean` (`spEncStr`), which are downstream of the unit and so not in
  `sources.zip`.

## Findings delivery

Return `gate31-prf-long-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish its statement, an API that cannot serve
  the B1 proof or `spDecStr_wrongKey` as mapped, or a scope violation.
- **major:** a changed frozen statement or definition, a re-derivation that is not proof-only, a forbidden read in a
  touched declaration not covered by the rulings, an undisclosed copied private lemma or undisclosed re-proof of a
  public one outside DL-46, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, proof sketch or consumer-map
  step.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/31-prf-long/review.md =====

# prf-long · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The edits are LE-doc (three formula docstrings) and LE-ws (one blank line).
No undisclosed restatement was found.

## Delivery and landing branch

**Delivery**
- **Source:** Claude worker, ruling B3. Exchange final `8d44fa5b5cdd408b9361364a246697dc294151fb`; checkpoints
  `6941fe67` and `36067085`. Issue base `7b307d62`.
- **Scope:** the PRF machinery at ℓ(n)-bit outputs (D1–D4), added to the owned frozen `FromPRF`/PRF files, with the
  n-bit versions re-derived from it. The unit proves no admitted target, by design.

**Landing branch** `land/pass-shelat-prf-long`
- **Rebase:** onto records tip `dd98360d`, which includes #303, #306–#309, #311 and #312. No conflict.
- **Head:** `fbd37f447596d4207c8d08b7ef7602f57fe95198`, tree `c0609c53b694d1899f8e2b8b6b0f7fd9357dc4cf`.
- **Commits:** `2d4fb3f6` (D1, D2), `ccb51427` (D3), `05deb4d8` (readers), `2205e332` (D4 and the re-derivations),
  `ea50e92c` (LE-doc) and `fbd37f44` (LE-ws).
- **Files:** six, +908/−279.
  - modified: `Asymptotic/Defs.lean`, `FromPRF/Hybrid.lean`, `FromPRF/ReductionMachine.lean` (892 lines) and
    `FromPRF.lean`;
  - new: `FromPRF/MultiMsgOut.lean`;
  - modified: the `PrivateKey.lean` facade, by one import and one Contents bullet.

**Evidence:** `review-evidence.zip`, SHA-256 `0586d82ed786e77bf21aa4263e20bd0f9f2cd62f7adde8c003458d0a2126c4d4`.
- It has 645 entries: the manifest paths plus `SHA256SUMS`. The manifest is `evidence-SHA256SUMS`.
- The duplication and seal-B logs are in `landing/`.

## Checks

**Integrity**
- The manifests verify 1755/1755 and 1742/1742, with exact path sets.
- `git am` reproduces all four worker hashes, but only with the environment's SSH signing turned on (F-03).
- The issue package verifies 7/7, and its sources 434/434.

**Build**
- All 121 modules downstream of the changed modules, plus the 55-module base delta, give rc 0 with 0 errors. This runs
  through root `TCSlib` and both `audits/*/Checks`.
- The whole-tree check covers 1244 modules, and passes.

**Statements**
- **Frozen rule:** an independent `frozencheck.py` compared headers, the prose before each sketch, and whole
  definition bodies. It found 0 differences, and each of its five controls reports exactly one.
- **decls2:** 61 ADDED, 0 CHANGED, 0 REMOVED.
- **Signatures:** all 23 drafted D1–D4 signatures match. The only additions are disclosed extra helpers.

**Axioms**
- All 15 endpoints and all 321 stored constants use only the standard three.
- No type, attribute or axiom changed.

**Rule 10**
- Variant A (the canonical one) passes in every file, both strict and coe. Strict and coe agree.
- Variant B fails only where the base already fails, on `PolyExpr.eval`. The attribution is in
  `landing/seal-B-attribution.txt`.
- Paired controls: 14 per variant, ALL_OK.
- The explicit-unfold scan finds 0 foreign definitions.

**Admissions:** 40 in 19 modules, unchanged, as expected.

**Lint:** 92/101 at the tip and at the head, with no new line.

**Content**
- The n-bit results are literal cases of the `Out` forms.
- **The B1 consumer map is correct.**
  - Use the masks `w_i = 0^{o_i+n} ‖ m_i ‖ 0^…` and the post-map `P : (r,u) ↦ (r, (u.drop o).take (n+ℓ_i))`.
  - `P ∘ prfEncRealOut` is then exactly `sliceEnc`, on the same seed space.
  - The total D4 is uniform in the masks, so `sc-garble` obtains the maximization over slices directly.
- **Gate 27's hand-off is met by an equivalent general API.**
  - D3 has ℓ-bit answers, n-bit queries and keys, an evaluation identity for every oracle, and the coin
    equivalence.
  - The consumer does its post-processing inside `D`.
  - Caveats: the queries are a non-adaptive chain of uniform points, which is enough for the slice proof and for
    `spDecStr_wrongKey`. The advice and query bounds stay inside the existential.

**Overlap with #314:** the trial merge is clean, and neither PR touches the other's files. Whichever lands second
needs an integration rebuild of `Functions/Defs`' downstream.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | minor, disclosed | `MultiMsg.encodeList_eq_flatMap` (`MultiMsgOut.lean`) is a third copy of the public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`). The others are that public lemma and the frozen private copy in `FromPRF.lean`, which is now unused. A private/public name clash blocks reuse. | Ledger **DL-46**. The worker's promotion request goes to a follow-up: move the lemma to `EnsembleSecurity` and delete both copies. |
| F-02 | minor, disclosed | `histBlockLen` is kept beside `histBlockLenOut`: they are different `PolyExpr` terms, with no `rfl` bridge. `adviceBound` and the private `encodeList_eq_flatMap` are now unused. | Ledger **DL-46**. The unused frozen items go in a later cleanup. |
| F-03 | info | The commit hashes reproduce only with SSH signing on, and the signing is not recorded (same as prf-mac F-05). | Briefs going forward require a signing column in `COMMITS.tsv`, or `commit.gpgsign=false`. |
| F-04 | info | Three new public declarations had no formula docstring. | **Fixed** by LE-doc. |
| F-05 | info | A blank line was lost. | **Fixed** by LE-ws. |
| F-06 | info | Undisclosed near-relatives, not restatements: GGM's `encodeHist_eq_histEnc`, `histEnc_append_single`, `length_histEnc`, and `UniformTableauEmitter.encodeList_eq_flatMap`. | Ledger note, DL-46. |
| F-07 | info | Seal-B failures only on `PolyExpr.eval`, where the base also fails. | None. |

## ===== briefs/pass-shelat-ch5-8/gates/31-prf-long/worker-report.md =====

# Fill `prf-long` · final (D1–D4, B1 consumer map)

**Worker** Claude. **Unit** `prf-long` (ruling B3: the PRF machinery of [PS10, Theorem 99.2] at `ℓ(n)`-bit
outputs). **Issue base** `7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee` (`cryptography/pass-shelat-ch2-4`), read
from the exchange at `b97d359517f8cebbf7e03071e30bc21e66c8403e` (pack verified 7/7 and SOURCE 434/434:
`evidence/logs/inputs-check.log`). **Proof branch** `fill/prf-long` (local), four commits over the base:

| commit | content | exchange |
|---|---|---|
| `94e7c1eb09f8cfd27389d5282962e3e95bdf4bcf` | checkpoint 1: D1, D2 | `6941fe671` |
| `200b6b502d26bfcf72215ce403f7821561a311ba` | checkpoint 2: D3 | `360670852` |
| `eff869dc9e20b37b5252f9681b616d8b74d7d4d5` | checkpoint 2: readers `histBlockLenOut_eq`, `adviceBoundOut_eq` | `360670852` |
| `40127c58490da57b824f9c4f8a384d7395b06dcb` | final: D4, the `FromPRF.lean` re-derivations, facade lines; `encodeHist_eq_flatMap` proof | this delivery |

This unit proves **no admitted target and removes no `sorry`** (census unchanged, below). Nothing of #311/#312
is imported or depended on.

## Files

| file | base lines | final lines | change |
|---|---|---|---|
| `Pseudorandom/Functions/Asymptotic/Defs.lean` | 447 | 480 | D1: 2 declarations added, 2 re-derived |
| `Encryption/PrivateKey/FromPRF/Hybrid.lean` | 349 | 511 | D2: 15 added, 8 re-derived |
| `Encryption/PrivateKey/FromPRF/ReductionMachine.lean` | 572 | 889 | D3: 38 added, 10 re-derived |
| `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean` (**new**) | — | 163 | D4: 5 declarations |
| `Encryption/PrivateKey/FromPRF.lean` | 424 | 372 | 1 added (bridge), 2 re-derived; import + docstring lines |
| `Encryption/PrivateKey.lean` (facade) | 75 | 77 | one import, one Contents bullet |

Not changed: `FromPRF/HybridLemmas.lean`, `Pseudorandom/Functions.lean` (no module was added there). All files
≤ 1000 lines; no new line over 100 characters (`evidence/checks/widths-final.txt`).

## New declarations

The full headers of all **61** new declarations, in file order, are in `evidence/final/new-decls.txt` (tool
`newdecls.py`). The main statements (namespaces `TCSlib.Cryptography`, `….MultiMsg`):

```lean
-- D1 (Asymptotic/Defs.lean)
theorem prfAdv_toOracleAdversary_out {ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).O n)
        ((OracleEnsemble.random .var ℓ₂).O n)
        (oracleDist (D.toOracleAdversary n n (ℓ₂.eval n) q)) =
      prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) q)
theorem OracleEnsemble.Indist.negligible_prfAdv {ℓ₂ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).Indist
      (OracleEnsemble.random .var ℓ₂))
    (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) (q.eval n))

-- D2 (FromPRF/Hybrid.lean, section Concrete: {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ] {l : ℕ})
def prfEncRealOut (F : K → (Fin n → Bool) → (Fin l → Bool)) (m : Fin (q + 1) → Fin l → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool))
def otpEncOut (m : Fin (q + 1) → Fin l → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool))
def multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin l → Bool)
-- readers prfEncRealOut_apply, otpEncOut_apply, eval_multiMsgAdvOut, multiMsgAdvOut_boundedBy;
-- acceptProb_oracleDist_multiMsgAdvOut, prfAdv_multiMsgAdvOut, distAdv_prfEncRealOut_random_otp_le,
-- acceptProb_otpEncOut, and:
theorem distAdv_prfEncRealOut_le (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m m' : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤
      prfAdv F (multiMsgAdvOut m D) + prfAdv F (multiMsgAdvOut m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n)
-- rfl bridges prfEncReal_eq_prfEncRealOut, otpEnc_eq_otpEncOut, multiMsgAdv_eq_multiMsgAdvOut

-- D3 (FromPRF/ReductionMachine.lean)
theorem MultiMsg.exists_queryChainOut_nuppt (D : NUPPT) (q ℓ : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool))
        (ρ : Fin (q.eval n + 1) → Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true])
theorem MultiMsg.exists_oneQuery_nuppt (D : NUPPT) (ℓ : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) (r : Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) 1 (φ (r, c))).eval g =
          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true])
-- string layer: histBlockOut, maskBlockOut (n explicit), maskOfOut (n explicit), histBlockLenOut,
-- postCountOut, postOffsetOut, postQueryOut, postFunOut, adviceBoundOut, each with its `_eq`
-- reader; length_histBlockOut, encodeHist_eq_flatMapOut, eval_histBlockLenOut,
-- pairFstD_pairFstD_histBlockOut, length_maskBlockOut, zipWith_xor_histBlockOut_maskBlockOut,
-- polyTimeComputable_postFunOut, length_maskOfOut, eval_adviceBoundOut, postFunOut_layout,
-- preFun_encodeHistOut; bridges histBlock_eq_histBlockOut, maskBlock_eq_maskBlockOut,
-- maskOf_eq_maskOfOut (rfl), postCount/postOffset/postQuery/postFun_eq_…Out (case ℓ = var)

-- D4 (FromPRF/MultiMsgOut.lean, new)
def encodeTupleOut {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) : List Bool
theorem encodeTupleOut_eq … -- the defining equation
theorem MultiMsg.encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
theorem encodeTupleOut_eq_flatten {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
    encodeTupleOut v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten
theorem MultiMsg.exists_negligible_distAdv_prfEncRealOut {ℓ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ))
    (D : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (w w' : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w z))
        (fun z => encodeTupleOut (prfEncRealOut (F n) w' z)) (D.distinguisherL n) ≤ ε n

-- FromPRF.lean
theorem encodeTuple_eq_encodeTupleOut {n q : ℕ}
    (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : encodeTuple v = encodeTupleOut v
```

All D1–D4 statements are **as drafted** in the brief. Disclosed deviations from the brief's lists:

* **`postQueryOut` added** (D3). The brief lists `postQuery` among the width-free helpers, but `postQuery` reads
  `postOffset`, whose block length is `histBlockLen = 6n + 6`; at width `ℓ(n)` the offset is `postOffsetOut ℓ`,
  so the query move needs its `Out` form (with reader and bridge).
* **`maskBlockOut n w`, `maskOfOut n v` take `n` explicitly**: `n` occurs only in the zero prefix `0^{4n+4}` and
  cannot be inferred from `w : Fin l → Bool`.
* **Two extra readers** `histBlockLenOut_eq`, `adviceBoundOut_eq` (the drafted names would have left the new
  `PolyExpr` definitions without a check-8 reader; see *Lint*).
* **Binder note (D2).** `prfEncRealOut_apply`, `eval_multiMsgAdvOut`, `multiMsgAdvOut_boundedBy` and the bridges
  carry `omit [Fintype K]`/`omit [Fintype ρ]` exactly as their `n`-bit originals do.
* **D1 re-derivation** needs the explicit `(ℓ₂ := .var)`; without it the elaborator must solve
  `PolyExpr.eval ?ℓ₂ n =?= n` and times out.
* `encodeTuple_eq_encodeTupleOut` is proved by `rw [encodeTuple, encodeTupleOut_eq]`: `encodeTuple` is
  `FromPRF.lean`'s own definition, `encodeTupleOut` (foreign, new module) is read through its reader.

## Re-derivations

Every `n`-bit declaration the brief lists is **re-derived** from its `Out` form as the case `l = n` / `ℓ = var`
/ `ℓ₂ = var`; its `**Proof sketch.**` paragraph now says so (statements and headers byte-identical, see
*Frozen-statement check*). The complete per-declaration list with the new proof text is
`evidence/final/rederivations.txt` (tool `rederiv.py`: 22 `CHANGED`, 96 `same`; the tool skips the one `inductive`, `OracleMove`, which the header check
finds byte-identical).

| file | re-derived (new proof) |
|---|---|
| `Asymptotic/Defs` | `prfAdv_toOracleAdversary := prfAdv_toOracleAdversary_out (ℓ₂ := .var) F D n q`; `PRF.negligible_prfAdv := hF.pseudorandom.negligible_prfAdv D q` |
| `Hybrid` | `prfEncReal_apply`, `eval_multiMsgAdv`, `multiMsgAdv_boundedBy`, `acceptProb_oracleDist_multiMsgAdv`, `prfAdv_multiMsgAdv`, `distAdv_prfEncReal_random_otp_le`, `acceptProb_otpEnc`, `distAdv_prfEncReal_le` (each: rewrite by the bridges, `exact` the `Out` lemma) |
| `ReductionMachine` | `length_histBlock`, `encodeHist_eq_flatMap` (the term `encodeHist_eq_flatMapOut h`), `pairFstD_pairFstD_histBlock`, `length_maskBlock`, `zipWith_xor_histBlock_maskBlock`, `polyTimeComputable_postFun`, `length_maskOf`, `postFun_layout`, `preFun_encodeHist`, `exists_queryChain_nuppt := exists_queryChainOut_nuppt D q .var v` |
| `FromPRF.lean` | `encodeTuple_eq_flatten` (bridge + `encodeTupleOut_eq_flatten`); `prfScheme_multiMessageSecure` (from `MultiMsg.exists_negligible_distAdv_prfEncRealOut hF.pseudorandom D q` through `prfScheme_multiEncDist`, the bridges and `acceptProb_comp_equiv`) |

Kept as they are, by design (reused, as the brief lists): `chainTree`, `uprob_not_injective_le`,
`pushesUniform_comp_injective`; the width-free string helpers (`length_flatMap_of_length`, `flatMap_range_blocks`,
`flatMap_const_*`, `dbl_append`, `zipWith_xor_*`, `take_drop_ofFn_blocks`, `blockMapFun`, `takePolyFun`,
`dropPolyFun`, `preFun`, `postHist`, `postPoints`, `postBudget`, `postAns`, `postVerdict`,
`length_flatten_of_length`, `decodeOracleMove_query`/`_ret`, `flatMap_ofFn`). The frozen `n`-bit
**definitions** keep their bodies (the rule); each has a bridge to its `Out` form: `rfl` for `prfEncReal`,
`otpEnc`, `multiMsgAdv`, `histBlock`, `maskBlock`, `maskOf`, `encodeTuple`; by `simp only`/`rw` at `ℓ = var` for
`postCount`, `postOffset`, `postQuery`, `postFun` (block lengths `6n + 6 = 4n + 2n + 6`).

Ledger rows (nothing kept because a re-derivation was too invasive; these are the residues the maintainer may
want on the duplication ledger):

| declaration | status | reason |
|---|---|---|
| `MultiMsg.histBlockLen`, `eval_histBlockLen` (`ReductionMachine.lean`) | **ledger**: kept beside `histBlockLenOut`/`eval_histBlockLenOut` | frozen definition `6·var + 6`; `histBlockLenOut .var = 4·var + 2·var + 6` is a different `PolyExpr` term (equal after `eval`), so no `rfl` bridge; still used by the frozen `postCount`/`postOffset` and by their bridges |
| `MultiMsg.adviceBound` (`ReductionMachine.lean`) | **ledger**: kept, now **unused** | frozen definition; its only consumer was the base proof of `exists_queryChain_nuppt`, now a re-derivation (which uses `adviceBoundOut .var`); deleting a base declaration is outside the frozen-statement rule. No other use in TCSlib |
| private `encodeList_eq_flatMap` (`FromPRF.lean`) | **ledger**: kept, now **unused**, as the brief instructs ("leave the private copy in place") | its general public form is `MultiMsg.encodeList_eq_flatMap` (`MultiMsgOut.lean`) |
| `MultiMsg.encodeList_eq_flatMap` (`MultiMsgOut.lean`, new) | **ledger**: a third copy of the statement of the public `TCSlib.Cryptography.encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean:60`) | reusing it would put `BlockEncryptor` in `FromPRF.lean`'s closure, where the frozen private copy then fails to declare (clash probe); see *Overlap and reuse* and *Promotion requests* |

## B1 consumer map

This unit does **not** prove B1. The statement was read at the PR head
`46b780dc1b286f59da18e2d10f188b0faaab8088` (`stmt/pass-shelat-b1-multimsg`, file
`SecureComputation/SpecialEncryptionMulti.lean`, not imported and not depended on):

```lean
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G
```

`hG.pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) G).Indist (OracleEnsemble.random .var ℓ)`
(clause (2) of `PRFOut`, `SpecialEncryptionSecurity.lean:56`) is literally the hypothesis `hF` of
`OracleEnsemble.Indist.negligible_prfAdv` and of `MultiMsg.exists_negligible_distAdv_prfEncRealOut`, with
`F := G`; no conversion is needed. `PRFOut` is at the issue base, so this is checked: probe
`scratch-src/probe/B1Probe.lean` (log `evidence/final/b1-probe.log`: exit 0, no diagnostics) applies
`MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q` (step 3) and
`hG.pseudorandom.negligible_prfAdv B (q.add (.const 1))` (step 1) to `hG : SecureComputation.PRFOut ℓ G`, and
`exists_oneQuery_nuppt` with `hG'.pseudorandom.negligible_prfAdv B (.const 1)` to the hypothesis of
`spDecStr_wrongKey`. The B1 file itself (#311) is not elaborated here.

How each step of the B1 sketch uses the delivered lemmas, with the final names:

0. **Reduction to tuples (`sc-garble`, not part of this unit).** For slices `(o_i, ℓ_i)` and messages `m_i` the
   consumer forms the masks `w_i = 0^{o_i + n} ‖ m_i ‖ 0^{ℓ(n) − o_i − n − ℓ_i} : Fin (ℓ.eval n) → Bool` and shows
   that, up to the coin relabelling (`acceptProb_comp_equiv`), `sliceMultiEncDist G n q o len m` is
   `P_{o,ℓ} ∘ encodeTupleOut ∘ prfEncRealOut (G n) w`, reading `encodeTupleOut` only through
   `encodeTupleOut_eq`/`encodeTupleOut_eq_flatten` and `prfEncRealOut` only through `prfEncRealOut_apply`
   (Rule 10: the new module and `Hybrid` are foreign to `SecureComputation`). `D' = D ∘ P` with the maximizing
   slices as advice comes from `NUPPT.exists_comp`, `NUPPT.exists_withAdvice` and a block parser.
1. **PRF step.** Inside `MultiMsg.exists_negligible_distAdv_prfEncRealOut` (the consumer does not repeat it):
   the two machines `MultiMsg.exists_queryChainOut_nuppt D' q ℓ (μ n).1/.2`, identified with
   `multiMsgAdvOut w (D' ∘ encodeTupleOut)` by `MultiMsg.prfAdv_congr_equiv`, `eval_multiMsgAdvOut`,
   `encodeTupleOut_eq_flatten`; the hybrid bound `distAdv_prfEncRealOut_le` (whose PRF terms are
   `prfAdv_multiMsgAdvOut`); negligibility by `OracleEnsemble.Indist.negligible_prfAdv hG.pseudorandom B_b
   (.add q (.const 1))`.
2. **Random function and collision.** Inside `distAdv_prfEncRealOut_le`: `distAdv_prfEncRealOut_random_otp_le`
   (collision bound `C(q+1, 2) / 2^n` via `uprob_not_injective_le` on the `n`-bit points) and
   `acceptProb_otpEncOut` (the full `ℓ(n)`-bit pads are uniform, so every window of them is too: the
   consumer's `P` is applied after the bound, inside `D'`).
3. **Total.** `MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q` gives one negligible `ε`
   with `distAdv (encodeTupleOut ∘ prfEncRealOut (G n) w) (encodeTupleOut ∘ prfEncRealOut (G n) w')
   (D'.distinguisherL n) ≤ ε n` for **all** `n, w, w'`; since `ε` precedes the masks, the consumer's maximization
   over the finitely many fitting slices and message pairs (step 0, hard-wired in `D'`) gives B1's `ε`.
   `MultiMsg.negligible_choose_div_two_pow` is inside the total.

`spDecStr_wrongKey` (`SpecialEncryptionSecurity.lean:127`, hypothesis `hG' : PRFOut (.add .var ℓ) G'`): the
distinguisher samples `k'` (its own coins) and the point `r`, makes one query and compares the first `n` bits
of the answer with `E'(⟨k', r⟩)`; `exists_oneQuery_nuppt D (.add .var ℓ)` turns such a `D` (reading
`⟨⟦r⟧, ⟦g r⟧⟩`) into a one-query oracle machine with coins `(r, c)`, and
`OracleEnsemble.Indist.negligible_prfAdv hG'.pseudorandom B (.const 1)` makes its PRF advantage negligible
(`(PolyExpr.const 1).eval n = 1` by `PolyExpr.eval_const`). The random-function probability `2^{-n}` is the
consumer's.

`specialScheme_multiMessageSecure` follows from B1 by `specialScheme_multiMessageSecure_of_joint` (PR #311); it
uses nothing of this unit directly.

Gaps this unit leaves to `sc-garble` (as the brief assigns): step 0 (the slice post-processing `P`, the mask
construction and the fit `o_i + n + ℓ_i ≤ ℓ(n)`), the random-function probability of `spDecStr_wrongKey`.

## Edge cases (brief: *Check the edge cases*)

The generic statements carry **no side condition** on `n`, `ℓ` or `q`. `evidence/final/edge-cases.log` (probe
`scratch-src/probe/EdgeCases.lean`, run against the final olean tree: exit 0, no diagnostics) instantiates them:

* `ℓ(n) = 0`: `length_histBlockOut` at `l = 0` gives `4n + 6`; `exists_queryChainOut_nuppt` at `ℓ = const 0`.
* `n = 0`: `distAdv_prfEncRealOut_random_otp_le (n := 0)` simplifies to `≤ C(q+1, 2)`.
* `q(n) = 0`: `distAdv_prfEncRealOut_random_otp_le (q := 0)` simplifies to `≤ 0`.
* Budget `1` against `(PolyExpr.const 0).eval n + 1`: `exists_oneQuery_nuppt` states the literal `1` (the proof
  transports along `1 = (const 0).eval n + 1`); `hF.negligible_prfAdv B (.const 1)` reads as budget `1` after
  `PolyExpr.eval_const`.
* Malformed moves and the budget timeout: `exists_queryChainOut_nuppt` is an equality of `eval` for every
  oracle `g`; on the canonical history the post-processor emits a well-formed query `⟨[false], ρ_k⟩` for
  `k ≤ q(n)` (`decodeOracleMove_query`) and the verdict `[true, b]` at `k = q(n) + 1` (`decodeOracleMove_ret`),
  so neither the malformed-move nor the forced-`false` branch of `buildTree` is reached; this is proved, not
  assumed (`hquery`, `hret`, `main`).
* Block lengths `0 < 4n + 2ℓ(n) + 6` (`hpos` in `postFunOut_layout`; probe on `eval_histBlockLenOut`).
* The bridges at `l = n` and `ℓ = var` (probe: `encodeTuple_eq_encodeTupleOut`, `postFun_eq_postFunOut`).

## Frozen-statement check

`evidence/headers/headers-final.txt` (tool `evidence/tools/headers.py`): every base declaration of the seven
scope files (`Asymptotic/Defs`, `FromPRF/Hybrid`, `FromPRF/ReductionMachine`, `FromPRF/HybridLemmas`,
`FromPRF.lean`, `Pseudorandom/Functions.lean`, `Encryption/PrivateKey.lean`) is present in the same file and
order, with its header (keyword line to the top-level `:=`/`|`/`where`), its `omit … in` lines and its
statement prose (docstring before `**Proof sketch`) byte-identical, and every `def`/`abbrev`/`structure`/
`instance` byte-identical in full: **0 differences** (Defs 36 → 38 declarations, Hybrid 16 → 31,
ReductionMachine 44 → 82, FromPRF 23 → 24, HybridLemmas 7 → 7, facades 0 → 0; order kept). Control
(`evidence/headers/control-final.txt`, files in `control-final/`): one character changed in the header of
`prfScheme_multiMessageSecure` is reported as exactly **one** difference. The checkpoint runs and controls are
kept (`headers-cp1/cp2`, `control-cp1/cp2`). What changed in base declarations: proofs, `**Proof sketch.**`
paragraphs, module docstrings, added imports and declarations — nothing else.

## Checks

* **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; no cgroup memory limit, headroom = MemAvailable
  ≈ 15.5 GiB; disk 11.0 GiB free at first (below the 12 GiB floor), so I removed only this session's own
  finished worktrees (`/workspace/prfbase`, `/workspace/folds`; their branches keep their commits): 14.15 GiB.
* **Packages and cache.** `.lake/packages` is a symlink to this host's populated tree at exactly the manifest's
  pins (the addendum's alternative; the manifest at `7b307d62` is byte-identical to that tree's).
  `evidence/logs/packages-check.log`: 11 match, 0 mismatch, 4 absent. The 111 Mathlib roots computed from
  `order.txt` equal `roots.txt`; the narrowed `lake exe cache get` exited 0, "No files to download" (2,400
  decompressed from the store of 2,402 archives left by earlier sessions on this host: `cache-store.log`); no
  zero-size olean (`zero-oleans.log`); probe `import Mathlib.Algebra.BigOperators.Field` passed
  (`cache-probe.log`). No `lake build`, no unfiltered cache get; Python always as `python3 -I` (one exception,
  disclosed under *Bootstrap*).
* **Bootstrap** (`evidence/logs/bootstrap.tsv`, raw logs `evidence/logs/bootstrap/`): 434/434 exit 0, 0 error
  diagnostics with `^\S+\.lean:\d+:\d+: error[:(]` (`evidence/base/bootstrap-errors.txt`). History
  (`bootstrap-run.log`): the first background loop ran `sweep.py` without `-I` for 8 modules and was restarted
  with `python3 -I`; I paused it after 176 modules to try the edits, then restored the base sources and rebuilt
  every module from position 149 (the first owned module) at the base before finishing (first-pass rows:
  `bootstrap-pass1.tsv`).
* **Final recheck and sweep** (`evidence/final/`). Order: `order-final.txt` = `order.txt` with the new
  `FromPRF/MultiMsgOut` inserted at position 154, just before its consumer `FromPRF` (`reorder.log`, tool
  `reorder.py`). First the owned and new modules in order (`recheck.tsv`, `recheck/`: `Asymptotic/Defs`,
  `HybridLemmas`, `ReductionMachine`, `Hybrid`, `MultiMsgOut`, `FromPRF`: 6/6 exit 0, 0 errors), then the whole
  order, **all 435 modules from the first**, at `40127c584`: **435/435 exit 0, 0 error diagnostics** with
  `^\S+\.lean:\d+:\d+: error[:(]` (`sweep-errors.txt`, rows `sweep.tsv`, raw logs `sweep/`, run log
  `sweep-run.log`).
  Checkpoint sweeps (286 modules from position 149 each) are kept in `evidence/cp1/`, `evidence/cp2/`: both
  286/286, 0 errors, census identical; a first cp2 run that I stopped after 7 modules to add the two readers is
  kept in `evidence/cp2/aborted/`.
* **Sorry census** (`evidence/final/sorry-census-final.txt`, tool `sorrycensus.py`, from the final sweep's
  logs, all 435 modules): **40 declarations in 19 modules, identical** to the base census
  (`evidence/base/sorry-census-base.txt`) and to `base-sorries.txt`; no admission removed or added.
* **Axioms** (`evidence/axioms/axioms-final.log`, tool `axioms.py`; comparison
  `evidence/axioms/axioms-compare.txt`): every stored constant of the six changed/new modules (321) depends on at
  most `propext`, `Classical.choice`, `Quot.sound`; this includes all **61 new** declarations and all **22
  re-derived** ones. **Every base constant still stored has exactly its base axiom list** (0 changed; the
  checkpoint-2 change of `encodeHist_eq_flatMap` to `[Quot.sound, propext]` is undone: its proof is now the
  term `encodeHist_eq_flatMapOut h`, back to `[propext]`). The five endpoints `prfScheme_multiMessageSecure`,
  `exists_multiMessageSecure_of_exists_prg`, `Composability.prfFixedScheme_cpa`, `Composability.ccaScheme_cca2`,
  `exists_prf_of_exists_prg`: `[Classical.choice, Quot.sound, propext]` at base and final, **identical**.
  Disclosed: 15 base constants are no longer stored, all **auto-generated** (equation lemmas
  `multiMsgAdv.eq_1`, `otpEnc.eq_1`, `histBlock.eq_1`, `maskBlock.eq_1`, `maskOf.eq_1`, `adviceBound.eq_1`, and
  `match_`/`_proof_`/`_simp_` auxiliaries of the replaced proofs): the base proofs realized them by unfolding
  the definitions, the re-derived proofs go through the bridges. None is a source declaration or named
  anywhere; any later `rw`/`simp`/`unfold` realizes the equation lemmas on demand (the sweep is clean).
  Checkpoint logs: `axioms-cp1.log`, `axioms-cp2.log`.
* **Rule 10: seals** (`evidence/seals/final/`, tool `seals.py`, probe sources `scratch-src/seal/final/`; base
  runs `evidence/seals/base/`). Whole-file seals of every changed or new file over its full TCSlib import closure
  (every closure module foreign): all non-reducible TCSlib definitions and matchers made `local irreducible`;
  variant **A** treats `PolyExpr.eval` as notation (Q1), variant **B** seals it too; **strict** also seals the
  projection coercion `FinDist.instCoeFunForallReal`, **coe** exempts it. The harness re-verifies after the
  file that every request is still irreducible (`SEAL-VERIFY` lines). Errors counted with
  `^\S+\.lean:\d+:\d+: error[:(]`, attributed to the enclosing declaration.

  | file | A (strict = coe) | B (strict = coe): failing declarations | base B |
  |---|---|---|---|
  | `Asymptotic/Defs` (652 requests) | **pass** | 8 errors: `PRF`, `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary` (as at base); `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` (new) | 4 errors, the three base names |
  | `FromPRF/Hybrid` (617) | **pass** | pass | pass |
  | `FromPRF/ReductionMachine` (1577) | **pass** | 2 errors: `postFun_layout`, `exists_queryChain_nuppt` (re-derivations) | pass |
  | `FromPRF/MultiMsgOut` (1640, new) | **pass** | 1 error: `MultiMsg.exists_negligible_distAdv_prfEncRealOut` | — |
  | `FromPRF.lean` (1772) | **pass** | 5 errors: `prfScheme`, `prfScheme_coinsEquiv`, `prfScheme_coinsEquiv_ofFn` (as at base); `prfScheme_multiMessageSecure` (re-derivation) | 4 errors, the three base names |
  | `Encryption/PrivateKey.lean` (2435) | **pass** | pass | pass |

  **Attribution.** Every B error (read in the raw logs) is an `Application type mismatch`/`Type mismatch`
  between `Fin n` and `Fin (PolyExpr.var.eval n)`, plus one cascade (`Unknown identifier
  prfAdv_toOracleAdversary_out` after that declaration failed): (i) the drafted statements of D1 and D4 take
  `OracleEnsemble.keyed (ℓ₁ := .var) F` with `F n : (Fin n → Bool) → …`, exactly like the base `PRF`; (ii) the
  re-derivations at `ℓ = var` (`exists_queryChain_nuppt := exists_queryChainOut_nuppt D q .var v`,
  `postFun_layout`, `prfScheme_multiMessageSecure`, `prfAdv_toOracleAdversary`) use `PolyExpr.var.eval n ≡ n`,
  which the brief names as notation (Q1) and says the re-derivations differ by. With `PolyExpr.eval` as notation
  (A, canonical) every file passes in both coe and strict forms; strict and coe give identical results for every
  file (the projection coercion is not reached by these files' proofs).
* **Rule 10: paired controls** (`evidence/seals/controls/`, tool `controls2.py`, source
  `scratch-src/controls/Controls.lean`; requests = the final census of everything the controls import, 1781–1783):
  six `CONTROL`/`READER` pairs on definitions of four owned files: C1 `MultiMsg.histBlockOut`, C4
  `MultiMsg.maskOfOut` (ReductionMachine), C2 `prfEncRealOut` (Hybrid), C3 `encodeTupleOut` (MultiMsgOut), C7
  `encodeHist` (Asymptotic/Defs), and C5 `PolyExpr.eval`. Unsealed: exit 0, no error. Sealed: **each negative
  fails exactly once** in all four variants (C5 only in the B variants, as designed: it closes when
  `PolyExpr.eval` is notation), every reader closes. The probe C6 (`FinDist`'s projection coercion read by `rfl`)
  closes in all variants (recorded, not a control). Two earlier attempts are kept, disclosed:
  `controls-attempt1/` (my C7 reader omitted `(ℓ₁ := .var)` and failed even unsealed) and `controls-attempt2/`
  (C7 on `OracleEnsemble.keyed`, whose statement `(keyed F).O n s` is itself ill-typed once `keyed` is sealed,
  so the reader failed too); C7 was then moved to `encodeHist`/`encodeHist_cons`. Only the logs of the attempts are
  kept; their sources differed from the delivered `Controls.lean` in C7 alone, as described.
* **Explicit-unfold scan** (`evidence/rwids/final/`, base `evidence/base/rwids/`; tools `rwids.py`,
  `rwids_run.py`, scan sources `scratch-src/rwids/`): every identifier passed to `rw`/`simp`/`unfold`/… in the six
  files, resolved in the file's namespace with its `open`s: **0 foreign TCSlib definitions, 0 core/Mathlib
  definitions** (base: 0 and 0). The 32 (file, definition) rows of class `own-def` (base: 27) are each the file's
  own definition: in `ReductionMachine` the new `…Out` definitions, the frozen ones inside their bridges and the
  helpers the base proofs already unfolded (`blockMapFun`, `takePolyFun`, `post…`); in `Hybrid` `chainTree`,
  `otpEncOut`, `multiMsgAdvOut`; in `FromPRF.lean` `encodeTuple` (in the bridge) and the base's
  `prfDecFun`/`prfDecWF`/`prfEncFun`; in `Asymptotic/Defs` the base's `buildTree`/`decodeOracleMove`.
  `MultiMsgOut` unfolds nothing. 222 identifiers are theorems; 63 are local hypotheses or private names.
* **Lint** (`evidence/lint/`): base 92 FAIL / 101 WARN (re-run at `7b307d62`, as the brief states), final
  **92 / 101** (`lint-final.txt`). Line-set diff (`lintdiff-final.txt`): **no new FAIL line**; two WARN lines
  **changed**, both check-8 lines of owned files, both **shortened** by bridges named after listed definitions
  (the effect the brief anticipates), and no new definition listed:
  * `Hybrid.lean`: "2 … chainTree, otpEnc" → "1 … chainTree" (bridge `otpEnc_eq_otpEncOut`);
  * `ReductionMachine.lean`: 16 → 10 definitions: `histBlock`, `maskBlock`, `maskOf`, `postCount`,
    `postOffset`, `postQuery` drop out (bridges `histBlock_eq_histBlockOut`, …, `postQuery_eq_postQueryOut`); the
    remaining ten are base names (`adviceBound`, `blockMapFun`, `dropPolyFun`, `histBlockLen`, `postAns`,
    `postBudget`, `postHist`, `postPoints`, `postVerdict`, `takePolyFun`).
  `FromPRF.lean`'s line (`prfDecFun`, `prfDecWF`, `prfEncFun`) is unchanged; `MultiMsgOut.lean` has no WARN or
  FAIL line. Every new public `def` has a reader beside it (`_eq`/`_apply`; `multiMsgAdvOut` through
  `eval_multiMsgAdvOut`); no new `abbrev`; no `@[simp]` added.
* **Sketches** (`evidence/checks/sketches-final.txt`): every proof of 15 lines or more has a `**Proof sketch.**`
  paragraph, except the base definition `prfScheme` (`FromPRF.lean`, a 17-line structure body, frozen and
  unchanged, listed at the base too). `exists_queryChainOut_nuppt` keeps the base step comments;
  `exists_oneQuery_nuppt` and `MultiMsg.exists_negligible_distAdv_prfEncRealOut` have their own. Every new public
  declaration has a docstring stating its formula; the main ones carry `[PS10, Definition 96.2 / Theorem 99.2,
  … with ℓ-bit outputs]`.
* **Compiler warnings**: over all 435 logs, 649 warnings at final against 650 at the base, and per module the same
  count except `ReductionMachine` (1 → 0: the base's unused simp argument `dbl_nil` at line 203 was in the
  proof of `zipWith_xor_histBlock_maskBlock`, now a re-derivation). `FromPRF.lean` keeps the base's one warning
  (unused simp argument `prfDecFun`, line 128 → 132, untouched proof). No new warning anywhere.

## Overlap and reuse

| New declaration | Nearest relative (`path:line` at the base) | Relation, and why not reused |
|---|---|---|
| `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` | `Pseudorandom/Functions/Asymptotic/Defs.lean:430,441` `prfAdv_toOracleAdversary`, `PRF.negligible_prfAdv` | generalization to `ℓ₂`; originals **re-derived**. `SecureComputation/SpecialEncryptionSecurity.lean:67` `prfOut_var_iff` (DL-8) relates `PRFOut .var` and `PRF`; the new lemma takes `PRFOut`'s clause (2) as its hypothesis (no import of `SecureComputation`), so DL-8 is untouched. |
| `prfEncRealOut`, `otpEncOut`, `multiMsgAdvOut` + readers, bridges | `FromPRF/Hybrid.lean:95,108,118` `prfEncReal`, `otpEnc`, `multiMsgAdv` | generalization to `l`; frozen definitions bridged by `rfl`; every lemma **re-derived**. |
| `acceptProb_oracleDist_multiMsgAdvOut`, `prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_le` | `Hybrid.lean:142,157,321` | generalization; originals re-derived. |
| `distAdv_prfEncRealOut_random_otp_le` | `Hybrid.lean:243`; `HardcoreBit.pushesUniform_restrict` (DL-2) | reuses `uprob_not_injective_le`, `pushesUniform_comp_injective`, `MultiMsg.abs_uexp_sub_le_uprob` unchanged; original re-derived. |
| `acceptProb_otpEncOut` | `Hybrid.lean:286`; `HardcoreBit.zipWith_xor_ofFn_add`, `distAdv_comp` (DL-2) | the same Boolean-group relabelling of the pads; original re-derived; no copy of the DL-2 lemmas. |
| `MultiMsg.exists_queryChainOut_nuppt` | `ReductionMachine.lean:461` `exists_queryChain_nuppt`; `Games/Efficiency.lean:844` T2 `exists_interactiveHandlerMachine`, T4 `exists_toOracleAdversary_of_bitCodec` | generalization to `ℓ`; original **re-derived**. Not built from T2/T4: it keeps this file's construction (`preFun`, uniform post-processor, advice, split coins) and changes only the string layer, so the `n`-bit theorem is literally its case `ℓ = var`; a T2/T4 build would be a second construction of the same machine beside the one the `n`-bit theorem needs, and would add an import edge from `ReductionMachine` (position 152 of `order.txt`) to `Games/Efficiency` (position 194; no cycle, as `Efficiency` does not import `FromPRF`, but not in the closure today). |
| `MultiMsg.exists_oneQuery_nuppt` | `exists_queryChainOut_nuppt` | its corollary (`q = const 0`, zero mask, `D ∘ pairFstD`); no second machine, as the brief asks. |
| (width handling of the `Out` machine lemmas) | `EncryptThenTag/Machines.lean:348` `ETTGame.eval_toOracleAdversary_len`, `OracleFromPRF/Reduction.lean:228` `PRFGame.eval_toOracleAdversary_width` | those transport an oracle adversary's `eval` along a propositional width equality via `padFin`. The `Out` lemmas need no transport (the width `ℓ.eval n` is in their types) and the `n`-bit cases use `PolyExpr.var.eval n ≡ n` (Q1). Neither lemma is used or restated. |
| string layer (`histBlockOut`, `maskBlockOut`, `maskOfOut`, `postCountOut`, `postOffsetOut`, `postQueryOut`, `postFunOut`, `histBlockLenOut`, `adviceBoundOut` + lemmas) | the `n`-bit string layer, `ReductionMachine.lean:50–445` (`histBlock` … `preFun_encodeHist`); `NMSim.chunkMap`, `Complexity.polyTimeComputable_blockMap` | generalization; `n`-bit lemmas re-derived via bridges. The block maps reuse this file's `blockMapFun`/`polyTimeComputable_blockMapFun`, as the `n`-bit code does, not `NMSim.chunkMap` (NonMalleability, not imported here). `histBlockLen`/`adviceBound` stay (ledger rows above). |
| (reused) `MultiMsg.take_drop_ofFn_blocks` | `EnsembleLemmas.take_drop_ofFn_blocks` (DL-9) | unchanged twin, used as before; DL-9 stays open on the ledger; no new copy. |
| (reused) `zipWith_xor_*` | the private `zipWith_xor_xor_self` copies (DL-40) | no new copy added. |
| `encodeTupleOut`, `encodeTupleOut_eq`, `encodeTupleOut_eq_flatten` | `FromPRF.lean:237,250` `encodeTuple`, `encodeTuple_eq_flatten` | generalization; `encodeTuple` bridged (`encodeTuple_eq_encodeTupleOut`), `encodeTuple_eq_flatten` re-derived. |
| `MultiMsg.encodeList_eq_flatMap` (public) | **`Asymptotic/BlockEncryptor.lean:60` `TCSlib.Cryptography.encodeList_eq_flatMap`** (same statement); `FromPRF.lean:241` private `encodeList_eq_flatMap`; `ClassP/BinaryArith/Words.lean:49` `encWords` (same right-hand side, other definition) | **duplicate, disclosed (ledger row)**. I found the public BlockEncryptor lemma only in the final search (`dupsearch-final.log`); the brief asked for the general form to be published in the new module. It cannot simply be reused: `MultiMsgOut` is imported by `FromPRF.lean`, and with `BlockEncryptor` in that closure the frozen private `encodeList_eq_flatMap` of `FromPRF.lean` (namespace `TCSlib.Cryptography`) fails with "a non-private declaration … has already been declared" (probe `scratch-src/probe/ClashProbe.lean`, log `evidence/final/clash-probe.log`: exactly that one error, exit 1); that is presumably why the base has the private copy. Hence the namespace `MultiMsg`. Resolution for the maintainer: see *Promotion requests*. |
| `MultiMsg.exists_negligible_distAdv_prfEncRealOut` | `FromPRF.lean:348` `prfScheme_multiMessageSecure` | the scheme-free total at width `ℓ`; the original is **re-derived** from it. |

Searches (`evidence/tools/dupsearch.sh`): `evidence/overlap/dupsearch-base.log` on the issue base and
`evidence/overlap/dupsearch-final.log` on the final tree (names and statement shapes of every new declaration
against TCSlib and Mathlib sources).

## Scope requests

None. Every change is in the pre-approved files plus the new module `FromPRF/MultiMsgOut.lean` (imported by the
facade `FromPRF.lean`; `Encryption/PrivateKey.lean` got one import and one Contents bullet).

## Promotion and reader requests

* **Promotion request (resolves two ledger rows).** Move `encodeList_eq_flatMap` (and
  `length_le_length_encodeList`) from `Asymptotic/BlockEncryptor.lean` to `Encryption/PrivateKey/EnsembleSecurity.lean`,
  next to `PrivateKeyScheme.encodeList` and its readers `encodeList_nil`/`encodeList_cons` (both modules are in
  the closure of every current user). Then the private copy in `FromPRF.lean` and `MultiMsg.encodeList_eq_flatMap`
  can be deleted in favour of it, at landing (this unit may not delete the frozen private copy, and cannot
  promote outside its scope). No other promotion or reader request.

## Patches and reproduction

`patches/0001…0004-*.patch` (the whole `git format-patch` series from the issue base) and `patches/COMMITS.tsv`
(hash, author name/email/date, committer name/email/date). Before pushing, a scratch clone at the issue base
applied the series with `git am`, the committer set from `COMMITS.tsv`, and reproduced every hash and the final
tree (`evidence/amcheck/amcheck-final.log`; the checkpoint logs are kept).

## Evidence

`evidence/SHA256SUMS` covers every evidence file (inputs, raw logs, seal/control/probe/scan sources under
`scratch-src/`, tools under `tools/`); the top-level `SHA256SUMS` covers every delivered file except itself; both
were checked against the delivered paths (nothing missing, nothing extra) before the push. Tool notes: `seals.py`
and `rwids_run.py` were adapted from my prf-mac tools; their docstrings now say so, and the base census sources
in `scratch-src/seal/base/` still carry the old "prf-mac" label in a comment (the code is the same).

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

## ===== briefs/pass-shelat-ch5-8/fills/prf-long/issued-r1/brief.md =====

# Claude fill · PRF machinery at ℓ-bit outputs (`prf-long`, ruling B3)

**Issue base** `7b307d6254f6ed0e98f44cd563f88f9c56b7b1ee` on `cryptography/pass-shelat-ch2-4` (the records tip after #303 and #305–#309;
records-only commits since the #307 merge `25fe1c05`). **Unit** `prf-long`. **Worker** Claude (standing ruling,
2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that commit's `lake-manifest.json`.

Generalize the PRF machinery of [PS10, Theorem 99.2] (`Encryption/PrivateKey/FromPRF*`, `PRF.negligible_prfAdv`)
from `n`-bit to `ℓ(n)`-bit outputs, **additively**, in frozen files under a pre-approved scope. Seyoon ruled on
2026-11-14 (B3) that this machinery is generalized first, in this separate job, instead of being duplicated in the
secure-computation units. This job proves **no admitted target** and removes no `sorry`. Its consumer is the
garbling unit `sc-garble` (not yet issued): the B1 statement `sliceMultiMessageSecure_of_prfOut` (draft PR #311) and
`spDecStr_wrongKey`.

## Why (need analysis)

From the secure-computation plan (`briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`, §2.3,
§2.5 and B3):

- `SecureComputation.PRFOut ℓ G` (`SecureComputation/SpecialEncryptionSecurity.lean:56`) is a PRF with
  `ℓ(n)`-bit outputs. Its clause (2) is an `OracleEnsemble.Indist` at a general `ℓ₂`, so it applies directly to
  `D.toOracleAdversary n n ℓ₂ q`.
- **Missing piece 1:** a one-query next-query machine for an `ℓ₂`-output oracle. The existing
  `MultiMsg.exists_queryChain_nuppt` is specific to `n`-bit outputs.
- **Missing piece 2:** an `ℓ₂` analogue of `PRF.negligible_prfAdv`.
- **The hybrid.** The proof of `prfScheme_multiMessageSecure` (Theorem 99.2) is typed throughout for
  `F : … → (Fin n → Bool) → (Fin n → Bool)`: `prfEncReal`, `multiMsgAdv`, `distAdv_prfEncReal_le`,
  `exists_queryChain_nuppt`, `PRF.negligible_prfAdv`. The B1 proof needs the same three steps at a general output
  length: the PRF step, the random function plus the collision bound, and the total.

## Feasibility (maintainer's assessment)

Feasible. Every `n`-bit proof generalizes without a new idea:

- the concrete hybrids are already generic in the key type `K`; only the answer type is fixed to `Fin n → Bool`;
- `chainTree`, `pushesUniform_comp_injective`, `MultiMsg.abs_uexp_sub_le_uprob` and `MultiMsg.prfAdv_congr_equiv`
  are generic;
- the collision bound `uprob_not_injective_le` concerns the `n`-bit **points**, which do not change;
- the machine's string layer depends on the answer width only through its block lengths: a history block
  `⟨⟨x, y⟩, []⟩` of an `n`-bit query and an `ℓ(n)`-bit answer has `4n + 2ℓ(n) + 6` bits (now `6n + 6`).

No admitted declaration is on the route: the closure's admissions are the machine-library stubs and the open fill
targets, and none of them is used.

**Estimated size:** 700–1,200 lines added (net growth 400–900 after the re-derivations), in the six owned files and
one or two new modules. For calibration, the `n`-bit originals are `Hybrid.lean` 349 lines, `ReductionMachine.lean`
572, `HybridLemmas.lean` 182 and `FromPRF.lean` 424.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/prf-long` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/prf-long/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/prf-long/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill prf-long: checkpoint N` and `fill prf-long: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is merged** in the issue base.
- **#311 (B1 statement) and #312 (derand host statement) are not merged.** Do not import or depend on either:
  `SecureComputation/SpecialEncryptionMulti.lean` and `Complexity/Randomized/SeedMajority.lean` are absent at the
  issue base. Read the B1 statement and its 3-step sketch at the PR head `46b780dc1b286f59da18e2d10f188b0faaab8088` (branch
  `stmt/pass-shelat-b1-multimsg`), only to write the consumer map below.
- **Parallel fills.** `prf-mac` and `learning` are dispatched; `seq-zk`, `canonizer`, `sc-ot` and `sc-compose` are
  staged; `derand` is held. They were issued at `107f1e8c`. None edits a file you own. `prf-mac`, `learning`,
  `ccaScheme_cca2` and `prfFixedScheme_cpa` consume `PRF.negligible_prfAdv`; a proof-only change keeps their
  statements. `sc-ot` and `sc-compose` are told not to build any ℓ-output PRF.

## Scope (pre-approved by ruling B3)

**Owned frozen files.** You may edit these, under the frozen-statement rule below:

| File | Lines at base | What changes |
|---|---|---|
| `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean` | 447 | `prfAdv_toOracleAdversary`, `PRF.negligible_prfAdv` (re-derived from D1) |
| `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/Hybrid.lean` | 349 | `prfEncReal`, `otpEnc`, `multiMsgAdv` and the six-hybrid lemmas (re-derived from D2) |
| `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean` | 572 | `MultiMsg.exists_queryChain_nuppt` and its string layer (re-derived from D3) |
| `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/HybridLemmas.lean` | 182 | already generic (`abs_uexp_sub_le_uprob`, `negligible_choose_div_two_pow`, `prfAdv_congr_equiv`); edit only to add a generic fact the route needs |
| `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean` | 424 | facade of `FromPRF/`; `encodeTuple_eq_flatten` and `prfScheme_multiMessageSecure` (re-derived from D4); `## Contents` |
| `TCSlib/Cryptography/Pseudorandom/Functions.lean` | 52 | facade of `Functions/`; an import and a `## Contents` bullet only, if you add a module there |

**New modules** are permitted in `Encryption/PrivateKey/FromPRF/` (facade `FromPRF.lean`) and in
`Pseudorandom/Functions/Asymptotic/` (facade `Pseudorandom/Functions.lean`). The facade imports each one. The
`Encryption/PrivateKey.lean` facade, which lists the `FromPRF/` helpers one by one, may get one import line and one
`## Contents` bullet per new module, and nothing else.

**Read-only.** Every other file is frozen, in particular:

- `SecureComputation/SpecialEncryptionSecurity.lean` (the definition site of `PRFOut`, owned by `sc-garble`);
- `Pseudorandom/Functions/Defs.lean` (`prfAdv`), `OracleAdversary.lean`, `LazySampling.lean`, `SubHybrids.lean` and
  the GGM files;
- `Encryption/PrivateKey/OracleFromPRF*`, `EncryptThenTag*`, `Games/*`.

`Games/Efficiency.lean` is at 982 lines; do not add to it.

**`PRFOut` stays where it is.** It is defined in `SecureComputation`, downstream of every owned file. So state the
generic lemmas on its clause (2), the hypothesis
`(OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ)`; the consumer passes
`hG.pseudorandom`. Do not import `SecureComputation`, and do not move or restate `PRFOut`.

## The frozen-statement rule (binding; checked)

- **Headers.** Every declaration present at the issue base in an owned file stays in the same file and the same
  order, with its header byte-identical. The header is the attributes and modifiers, the keyword, the name, the
  binders and the type, up to the `:=`, `by`, `where` or first `|` that begins the proof.
- **Definitions are statements.** For a `def`, `abbrev`, `structure`, `inductive`, `class` or `instance`, the
  whole declaration, body included, is byte-identical. So `prfEncReal`, `otpEnc`, `multiMsgAdv`, `histBlock`,
  `postFun`, `encodeTuple` and the rest keep their bodies; relate them to the generic forms by `rfl` bridges.
- **What may change.** Only the proofs of theorems; their `**Proof sketch.**` paragraphs (rewritten to say "the
  case `ℓ = n` of …"); module docstrings (`## Main results`, `## Contents`); and added imports and declarations.
  Statement prose, `set_option`s and attributes do not change. Delete nothing, private lemmas included.
- **Check.** Write a `python3 -I` script that extracts every declaration of each owned file at the base and at the
  final, and compares headers (and whole definitions) byte for byte. Also check that the base declarations appear
  in the same order. Deliver it and its output under `evidence/headers/`, with zero differences. Add a control: a
  copy with one header altered by one character must report exactly one difference.

## Deliverables (draft signatures)

The names are binding unless one clashes. Disclose any rename and any change of binder style. Each new public
declaration needs a formula docstring.

### D1 · the ℓ-analogue of `PRF.negligible_prfAdv` (`Pseudorandom/Functions/Asymptotic/Defs.lean`)

```lean
theorem prfAdv_toOracleAdversary_out {ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).O n)
        ((OracleEnsemble.random .var ℓ₂).O n)
        (oracleDist (D.toOracleAdversary n n (ℓ₂.eval n) q)) =
      prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) q)

theorem OracleEnsemble.Indist.negligible_prfAdv {ℓ₂ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).Indist
      (OracleEnsemble.random .var ℓ₂))
    (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) (q.eval n))
```

Re-derive `prfAdv_toOracleAdversary` as the case `ℓ₂ = .var` of the first, and `PRF.negligible_prfAdv` as
`hF.pseudorandom.negligible_prfAdv D q`. Both differ only by `PolyExpr.var.eval n` against `n`, which is notation
(Q1).

### D2 · the concrete hybrids at output width `l` (`FromPRF/Hybrid.lean`)

```lean
-- section variables as in `section Concrete`: {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ],
-- plus {l : ℕ}, the output width
def prfEncRealOut (F : K → (Fin n → Bool) → (Fin l → Bool)) (m : Fin (q + 1) → Fin l → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))
theorem prfEncRealOut_apply … : prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j))

def otpEncOut (m : Fin (q + 1) → Fin l → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)
theorem otpEncOut_apply … : otpEncOut m z j = (z.1 j, m j + z.2 j)

def multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin l → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2
theorem eval_multiMsgAdvOut … (g : (Fin n → Bool) → Fin l → Bool) … :
    (multiMsgAdvOut m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2
theorem multiMsgAdvOut_boundedBy … : (multiMsgAdvOut m D).BoundedBy (q + 1)
theorem acceptProb_oracleDist_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool)) m D :
    acceptProb F (oracleDist (multiMsgAdvOut m D)) = acceptProb (prfEncRealOut F m) D
theorem prfAdv_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool)) m D :
    prfAdv F (multiMsgAdvOut m D) =
      distAdv (prfEncRealOut F m)
        (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D
theorem distAdv_prfEncRealOut_random_otp_le (m : Fin (q + 1) → Fin l → Bool) D :
    distAdv (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) (otpEncOut m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n
theorem acceptProb_otpEncOut (m m' : Fin (q + 1) → Fin l → Bool) D :
    acceptProb (otpEncOut (n := n) m) D = acceptProb (otpEncOut m') D
theorem distAdv_prfEncRealOut_le (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m m' : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤
      prfAdv F (multiMsgAdvOut m D) + prfAdv F (multiMsgAdvOut m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n)

-- the rfl bridges used by the re-derivations
theorem prfEncReal_eq_prfEncRealOut … : prfEncReal F m = prfEncRealOut F m
theorem otpEnc_eq_otpEncOut … : otpEnc (n := n) m = otpEncOut m
theorem multiMsgAdv_eq_multiMsgAdvOut … : multiMsgAdv m D = multiMsgAdvOut m D
```

Re-derive from D2, as the case `l = n`: `prfEncReal_apply`, `eval_multiMsgAdv`, `multiMsgAdv_boundedBy`,
`acceptProb_oracleDist_multiMsgAdv`, `prfAdv_multiMsgAdv`, `distAdv_prfEncReal_random_otp_le`, `acceptProb_otpEnc`
and `distAdv_prfEncReal_le`. `chainTree`, `uprob_not_injective_le` and `pushesUniform_comp_injective` are reused
as they are.

### D3 · the next-query machine at answer width `ℓ(n)` (`FromPRF/ReductionMachine.lean`)

```lean
namespace TCSlib.Cryptography.MultiMsg

theorem exists_queryChainOut_nuppt (D : NUPPT) (q ℓ : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool))
        (ρ : Fin (q.eval n + 1) → Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true])

theorem exists_oneQuery_nuppt (D : NUPPT) (ℓ : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) (r : Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) 1 (φ (r, c))).eval g =
          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true])
```

`exists_queryChainOut_nuppt` is `exists_queryChain_nuppt` with `ℓ(n)`-bit answers and masks.
`exists_oneQuery_nuppt` is missing piece 1: `q = 0`, the zero mask, and `D` precomposed with `pairFstD`. It is a
corollary of the first; do not build a second machine.

- **String layer.** Generalize only what depends on the answer width: `histBlock`, `length_histBlock`,
  `encodeHist_eq_flatMap`, `histBlockLen`, `pairFstD_pairFstD_histBlock`, `maskBlock`, `length_maskBlock`,
  `zipWith_xor_histBlock_maskBlock`, `postCount`, `postOffset`, `postFun` with `polyTimeComputable_postFun`,
  `maskOf`, `length_maskOf`, `adviceBound`, `postFun_layout` and `preFun_encodeHist`. Use the suffix `Out` and give
  every new `def` its reader.
- **Reuse** the width-free helpers as they are: `length_flatMap_of_length`, `flatMap_range_blocks`,
  `flatMap_const_*`, `dbl_append`, `zipWith_xor_*`, `take_drop_ofFn_blocks`, `blockMapFun`, `takePolyFun`,
  `dropPolyFun`, `preFun`, `postHist`, `postPoints`, `postBudget`, `postAns`, `postQuery`, `postVerdict`,
  `length_flatten_of_length`, `decodeOracleMove_query`/`_ret` and `flatMap_ofFn`.
- **Re-derive** `exists_queryChain_nuppt` as the case `ℓ = .var`. Where it is cheap, also re-derive the `n`-bit
  helpers whose statements are cases of the generic ones.
- **Size.** Keep `ReductionMachine.lean` at most 1000 lines.

### D4 · the total at output length `ℓ` (new module `FromPRF/MultiMsgOut.lean`)

```lean
def encodeTupleOut {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) : List Bool :=
  PrivateKeyScheme.encodeList
    (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))
theorem encodeTupleOut_eq … (the defining equation)
theorem encodeTupleOut_eq_flatten … : encodeTupleOut v =
    (List.ofFn fun j => pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten

theorem MultiMsg.exists_negligible_distAdv_prfEncRealOut {ℓ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ))
    (D : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (w w' : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w z))
        (fun z => encodeTupleOut (prfEncRealOut (F n) w' z)) (D.distinguisherL n) ≤ ε n
```

This module imports `Hybrid`, `HybridLemmas`, `ReductionMachine` and `Asymptotic/Defs`, and `FromPRF.lean` imports
it. The proof is the present proof of `prfScheme_multiMessageSecure` at width `ℓ(n)`, without the scheme:

1. maximize over the finite pairs `(w, w')`;
2. build two machines with `exists_queryChainOut_nuppt`;
3. bound with `distAdv_prfEncRealOut_le` and `prfAdv_congr_equiv`;
4. conclude with `hF.negligible_prfAdv` (budget `q + 1`) and `negligible_choose_div_two_pow`.

Then re-derive, in `FromPRF.lean`, `encodeTuple_eq_flatten` from `encodeTupleOut_eq_flatten` (by `rfl` between
`encodeTuple` and `encodeTupleOut`). Also re-derive `prfScheme_multiMessageSecure` from
`exists_negligible_distAdv_prfEncRealOut hF.pseudorandom D q`, through `prfScheme_multiEncDist` and
`acceptProb_comp_equiv`. `encodeTuple_eq_flatten` rests on the private `encodeList_eq_flatMap`; publish its general
form in the new module, and leave the private copy in place.

### Re-derivation and its fallback

Re-derive every `n`-bit declaration listed above. If a re-derivation is too invasive, keep the `n`-bit
declaration's proof as it is. Examples: an elaboration blow-up at `PolyExpr.var.eval n`, or a file that would pass
1000 lines. For each one kept, add a row to `REPORT.md` § *Overlap and reuse*, marked **ledger**, with the exact
obstacle. The maintainer opens the duplication-ledger row at landing.

**Machine fallback.** If D3 cannot stay in `ReductionMachine.lean` within 1000 lines, put it in a new module
`FromPRF/QueryChainOut.lean` that imports `ReductionMachine`. Then keep `exists_queryChain_nuppt` as it is, since a
re-derivation would be a cycle, and record that as a ledger row.

## Proof route and checkpoints

1. **Checkpoint 1 · D1 and D2.** Deliver the asymptotic analogue and the concrete hybrids at width `l`, with their
   re-derivations, the header check and the sweep. Send this checkpoint.
2. **Checkpoint 2 · D3.** Deliver the string layer at width `ℓ(n)`, `exists_queryChainOut_nuppt`,
   `exists_oneQuery_nuppt` and the re-derivation of `exists_queryChain_nuppt`. Send this checkpoint.
3. **Final · D4 and the consumer map.** Deliver `MultiMsgOut.lean`, the re-derivations in `FromPRF.lean`,
   `## B1 consumer map` and the full evidence.

Check the edge cases:
- `ℓ(n) = 0`: the answers are empty, the random-function table is a singleton, and the history block has
  `4n + 6` bits;
- `n = 0`: the points are `Fin 0 → Bool`, and the collision bound is at most `C(q+1, 2)`;
- `q(n) = 0`: one point, so `C(1, 2) = 0`;
- the one-query budget `1` against `(PolyExpr.const 0).eval n + 1`;
- malformed machine outputs and the budget timeout (`decodeOracleMove`, the forced verdict `false`);
- block lengths `4n + 2ℓ(n) + 6 > 0`;
- the `rfl` bridges at `l = n` and `ℓ = .var`.

If a generic statement is false as drafted, stop and escalate with the exact obligation: a checkpoint with the
counterexample or the missing fact. Do not weaken it silently.

## B1 consumer map (required section of `REPORT.md`)

This job does **not** prove the B1 statement; that belongs to `sc-garble`. `REPORT.md` must still state, with the
final names, how each step of the B1 sketch (PR #311, `sliceMultiMessageSecure_of_prfOut`) uses the delivered
lemmas. The maintainer's draft:

0. **Reduction to tuples (`sc-garble`).** The mask of a slice `(o_i, ℓ_i)` and a message `m_i` is
   `w_i = 0^{o_i + n} ‖ m_i ‖ 0^{ℓ(n) − o_i − n − ℓ_i}`, an `ℓ(n)`-bit string. Up to the coin relabelling,
   the slice sampler is `P_{o,ℓ} ∘ encodeTupleOut ∘ prfEncRealOut (G n) w`. Here `P_{o,ℓ}` maps each
   `⟨r_i, u_i⟩` to `⟨r_i, (u_i.drop o_i).take (n + ℓ_i)⟩`, inside `encodeList`.
   - The consumer builds `D' = D ∘ P` with the maximizing slices as advice: `NUPPT.exists_comp`,
     `NUPPT.exists_withAdvice`, and a block parser (`NMSim.polyTimeComputable_chunkMap` or
     `polyTimeComputable_blockMap`).
   - This post-processing is SecureComputation-specific and is **not** part of `prf-long`.
1. **PRF step.**
   - `distAdv_prfEncRealOut_le` and `prfAdv_multiMsgAdvOut`;
   - the machines from `exists_queryChainOut_nuppt`, with `MultiMsg.prfAdv_congr_equiv`;
   - negligibility from `OracleEnsemble.Indist.negligible_prfAdv hG.pseudorandom` at budget `q + 1`.
2. **Random function and collision.** `distAdv_prfEncRealOut_random_otp_le` (with `uprob_not_injective_le`) and
   `acceptProb_otpEncOut`: the full `ℓ(n)`-bit pads are uniform, so the windows are too.
3. **Total.**
   - `MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q`, uniform in the masks `w, w'`;
   - with step 0 and the maximization over the slices and messages, this gives `ε`;
   - `MultiMsg.negligible_choose_div_two_pow` is inside the total.

`spDecStr_wrongKey` uses `exists_oneQuery_nuppt` and `OracleEnsemble.Indist.negligible_prfAdv` (budget 1).
`specialScheme_multiMessageSecure` follows from B1 (`specialScheme_multiMessageSecure_of_joint`, PR #311).

## Scope and proof discipline

- **Owned files.** As in *Scope*. Update each changed file's module docstring (`## Main results`, `## Contents`).
  Add no admission.
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any file outside the scope.
  - **Scope requests.** If the route needs a change outside the scope, or a frozen-statement exception, stop
    that line of work. Examples: a reader beside a foreign definition, a change to a definition body, a promotion.
    Ask Seyoon in your session, giving the exact file, the diff and the reason, and go ahead only on his approval.
    Record the request and his answer verbatim under `evidence/scope-request/` and in `REPORT.md` § *Scope
    requests*. Seyoon prefers a route with no such exception where one exists.
- **Parallel fills.** See *Base and parallel work*. Edit only the scope above.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran. Every
    `Out` declaration's relative is its `n`-bit original; say whether the original is re-derived or kept
    (**ledger**).
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:**
    - the generic next-query machinery of `Games/Efficiency.lean`: T2 `exists_interactiveHandlerMachine` and T4
      `exists_toOracleAdversary_of_bitCodec` (any `ℓ₁`, `ℓ₂`). Say why the chain machine is or is not built
      from them;
    - `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) and
      `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`);
    - `prfOut_var_iff` (DL-8);
    - `NMSim.chunkMap` and `polyTimeComputable_blockMap`;
    - `EnsembleLemmas.take_drop_ofFn_blocks` (DL-9, a twin of `MultiMsg.take_drop_ofFn_blocks`);
    - `HardcoreBit.pushesUniform_restrict`, `distAdv_comp`, `zipWith_xor_ofFn_add` (DL-2);
    - the private `zipWith_xor_xor_self` copies (DL-40).
- **Statements.** See *The frozen-statement rule*.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source (here Definition 96.2 and
    Theorem 99.2, "with ℓ-bit outputs");
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Each owned file and each new module counts as foreign to the others. A new module reads `prfEncRealOut` only
    through `prfEncRealOut_apply`, and so on.
  - Inside one owned file, the `rfl` bridges between a frozen definition and its `Out` form are allowed.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (434 modules) and the narrow `roots.txt` (111), following the addendum.
  - The order is large because `Asymptotic/Defs.lean` has 80 downstream modules, among them most top-level
    facades.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert new modules before their consumers.
- **Sweep.**
  - Recheck every owned and new module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (40 declarations in 19 modules). They must be
    **unchanged**: this job removes no admission and adds none.
- **Axioms.**
  - Print the axioms of every new declaration and of every re-derived one. Expect only `propext`,
    `Classical.choice` and `Quot.sound`.
  - Also print them for the downstream consumers `prfScheme_multiMessageSecure`,
    `exists_multiMessageSecure_of_exists_prg`, `Composability.prfFixedScheme_cpa` (`OracleFromPRF.lean`),
    `Composability.ccaScheme_cca2` (`EncryptThenTag.lean`) and `exists_prf_of_exists_prg`, at base and final. They
    must be identical.
- **Headers.** The check of *The frozen-statement rule*, with its control.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (re-run at `7b307d62`).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
  - The owned files carry three check-8 WARN lines at base: `Hybrid.lean` (`chainTree`, `otpEnc`),
    `ReductionMachine.lean` (16 defs) and `FromPRF.lean` (`prfDecFun`, `prfDecWF`, `prfEncFun`). A bridge named
    after a listed def covers it and shortens its line. Disclose every such change.
- **Report.** `REPORT.md` gives:
  - the base;
  - the changed and new files, with lines at base and final;
  - the new declarations with their final signatures;
  - **Re-derivations**: each `n`-bit declaration listed above, re-derived or kept (**ledger**, with the obstacle);
  - **B1 consumer map**;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - the header-check script, its output and its control;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing. The unit then
goes to its own gate (decision log, 2026-11-14), before `sc-garble` is issued.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `PRF.prfAdv_eq_expect` (to be published); the list readers above; `GGMRed.tblEnc` | Open | F-01 by the promotion PR; F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |

## ===== briefs/pass-shelat-ch5-8/gates/27-b1-multimsg/resolutions-r1.md =====

# Gate 27 · resolutions, round 1 · CLOSED

Codex's verdict is **CLEAR for the statement gate**: 0 blockers, 0 majors, 1 minor and 0 notes.
- **Findings:** `findings/gate27-b1-multimsg-findings.md`.
- **Audited head:** `46b780dc1b286f59da18e2d10f188b0faaab8088`.

| # | Severity | Disposition |
|---|---|---|
| G27-01 | minor | **Fixed** by **LE-gate27** `542bfb1ef2b64088e02385b74196854d654a719f` (tree `b25e3e0c`): the docstring now reads "Both shapes fit; the outer slice fits exactly." (3 lines re-wrapped to stay within 100 columns; code and all 18 headers identical; 63/63 rc 0 through root `TCSlib`; lint 92/101 byte-identical; evidence `landing-r1/gate27-r1-evidence.zip`, SHA-256 `8345928643b79d42a9d94dfa5c2471e67db9b2578e89ae0e51a41486bede5cef`). |

## What Codex verified
Codex ran no Lean.

- **Truth of the statement.** It gave a full mathematical proof of the statement as written, including the
  quantifier order (slices chosen after `ε`, which is valid because `L = ℓ.eval` is polynomial). One convention is
  needed: the maximum advantage is 0 when no slice vector fits.
- **Sufficiency for Yao step 3.** It confirmed both slice shapes, `(0,n)` and `(2n,4n+2)`, and that the
  non-adaptive interface is enough, using `g.args.Nodup`.
- **The frozen corollary.** It confirmed the corollary.
- **Readers and bridges.** The readers and bridges are Rule-10 clean.
- **Duplication.** It found none.

## Hand-off to the proof jobs (Codex; obligations, not findings)

1. **prf-long.** Answer lengths must be `ℓ`-bit while queries, keys and nonces stay `n`-bit. The job must publish
   a query-tree evaluation identity for arbitrary oracles, together with its coin equivalence and its advice and
   query bounds. The consumer must be able to post-process the full answer transcript in polynomial time.
   - *Maintainer check against the issued prf-long brief (D1–D4):* D3's `exists_queryChainOut_nuppt` evaluates
     `D` on the flattened transcript `⟨⟨ρ_j, v_j ⊕ g(ρ_j)⟩⟩` for arbitrary `D`. The consumer's slice
     post-processor `P` is folded into `D' = D ∘ P` with the slices as advice, as the brief's B1 map records. This
     is an "equivalent sufficiently general API" in Codex's sense.
   - It will be re-checked at the prf-long review.
2. **Reuse.** These existing generic readers can be reused: `OracleEnsemble.keyed_O`, `random_O`,
   `acceptProb_random_eq`, `MultiMsg.chainTree`, `uprob_not_injective_le`, `pushesUniform_comp_injective` and
   `negligible_choose_div_two_pow`.
3. **sc-garble.** It must:
   - build the maximizing advice, with the empty-set convention;
   - build the slice post-processor;
   - prove the random-function slice law;
   - close the triangle bound;
   - prove the frozen theorem via the corollary;
   - meet the B2 requirement.

   These go into the `sc-garble` brief.
4. **sc-yao.** It must formalize the gate and row sub-hybrids, the enumeration of all occurrences with padding, the
   no-dependence argument, the sampler identities, and polynomial-time reconstruction. These go into the `sc-yao`
   brief.

## Disposition

**PR [#311](https://github.com/Shilun-Allan-Li/tcslib/pull/311) is marked ready at `542bfb1e`.** It is a statement PR: the main theorem stays admitted, owned by `sc-garble`.

## ===== briefs/pass-shelat-ch5-8/gates/31-prf-long/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Encryption/PrivateKey.lean b/TCSlib/Cryptography/Encryption/PrivateKey.lean
index 43eb90297..7119b6f89 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey.lean
@@ -10,6 +10,7 @@ import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
 import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
 import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
 import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
 import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
 import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
 import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag
@@ -59,6 +60,7 @@ the PRF scheme [PS10, Theorems 97.3 and 99.2].
 * `Encryption.PrivateKey.FromPRF.Hybrid` proves the finite six-hybrid bound.
 * `Encryption.PrivateKey.FromPRF.HybridLemmas` gives its probability and coin lemmas.
 * `Encryption.PrivateKey.FromPRF.ReductionMachine` implements the next-query reduction.
+* `Encryption.PrivateKey.FromPRF.MultiMsgOut` gives the multi-message bound at `ℓ`-bit outputs.
 * `Encryption.PrivateKey.OracleSecurity` gives the fixed-length interface and adaptive oracle games.
 * `Encryption.PrivateKey.OracleFromPRF` gives the fixed-length PRF scheme and its oracle claims.
   The CPA and CCA1 proofs `prfFixedScheme_cpa` and `prfFixedScheme_cca1` are pending
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean
index 7432497aa..ec6573e3f 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean
@@ -8,6 +8,7 @@ import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
 import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
 import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
 import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
 import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
 
 set_option maxHeartbeats 0
@@ -30,7 +31,8 @@ Decryption recomputes the mask and checks the ciphertext format [PS10, Algorithm
 
 * `prfScheme_multiEncDist` identifies the ciphertext sampler with the encoded real hybrid.
 * `prfScheme_multiMessageSecure` lifts the six-hybrid bound to a negligible advantage against
-  non-uniform polynomial-time distinguishers [PS10, Theorem 99.2].
+  non-uniform polynomial-time distinguishers [PS10, Theorem 99.2]; it is the case `ℓ = var` of
+  `MultiMsg.exists_negligible_distAdv_prfEncRealOut` (`FromPRF.MultiMsgOut`).
 * `exists_multiMessageSecure_of_prf` and `exists_multiMessageSecure_of_exists_prg` give the
   existence results from a PRF and, via GGM, from a PRG.
 
@@ -38,7 +40,9 @@ Decryption recomputes the mask and checks the ciphertext format [PS10, Algorithm
 
 * `FromPRF.Hybrid` proves the concrete six-hybrid bound.
 * `FromPRF.HybridLemmas` supplies the collision and coin-relabelling estimates.
-* `FromPRF.ReductionMachine` implements the next-query reduction and proves its run agreement.
+* `FromPRF.ReductionMachine` implements the next-query reduction and proves its run agreement,
+  at `ℓ(n)`-bit answers as well.
+* `FromPRF.MultiMsgOut` proves the multi-message bound for a family with `ℓ(n)`-bit outputs.
 
 ## References
 
@@ -237,6 +241,12 @@ distinguisher: `encodeList` of the pairs `⟨r_j, c_j⟩`. -/
 def encodeTuple {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
   PrivateKeyScheme.encodeList (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))
 
+/-- The encoded tuple is the case `l = n` of `encodeTupleOut`:
+`encodeTuple v = encodeTupleOut v` (both are `encodeList` of the pairs `⟨⟦r_j⟧, ⟦c_j⟧⟩`). -/
+theorem encodeTuple_eq_encodeTupleOut {n q : ℕ}
+    (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : encodeTuple v = encodeTupleOut v := by
+  rw [encodeTuple, encodeTupleOut_eq]
+
 /-- `encodeList l` is the concatenation of the self-delimited chunks `⟨c, []⟩`, `c ∈ l`. -/
 private theorem encodeList_eq_flatMap : ∀ l : List (List Bool),
     PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
@@ -251,7 +261,8 @@ theorem encodeTuple_eq_flatten {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool)
     encodeTuple v =
       (List.ofFn fun j =>
         pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
-  rw [encodeTuple, encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]
+  rw [encodeTuple_eq_encodeTupleOut]
+  exact encodeTupleOut_eq_flatten v
 
 /-- **The coins of the multi-message experiment of Algorithm 99.1 are bit strings**: the key
 coins of `Gen` and the `q + 1` coin strings of `Enc` are `n`-bit strings,
@@ -316,96 +327,33 @@ a pseudorandom function family.
 **Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
 `r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).
 
-**Proof sketch.** Fix a non-uniform PPT `D` and a budget polynomial `q`. At each `n` choose a
-pair of message vectors `(mⁿ, m'ⁿ)` maximizing
-`distAdv (multiEncDist n (q n) m) (multiEncDist n (q n) m') (D.distinguisherL n)` over the finite
-type of pairs (`Finset.exists_max_image`; the text: "there exists messages `m̄`, `m̄'` … for
-infinitely many `n`", hard-wired as advice). *Concrete step:* by `prfScheme_multiEncDist` both
-samplers are `encodeTuple ∘ prfEncReal (F n) mⁿ` resp. `m'ⁿ` on the seed space
-`K × (Fin (q n + 1) → {0,1}^n)` (the gen coins are the `n`-bit key and the enc coins the points,
-definitionally), so with `Dⁿ v c := D.distinguisherL n (encodeTuple v) c` the sunglass identity
-`distAdv_comp` and `distAdv_prfEncReal_le` bound the advantage at `n` by
-`prfAdv (F n) (multiMsgAdv mⁿ Dⁿ) + prfAdv (F n) (multiMsgAdv m'ⁿ Dⁿ) + 2 · C(q n + 1, 2) / 2^n`
-— the six hybrids `H¹, …, H⁶` of the text. *Machine step* (Thm-99.2.1 as an `NUPPT`): for
-`v ∈ {m, m'}` the next-query machine `B_v` has advice `⟨encodeList (ofFn (ofFn ∘ vⁿ)), D.advice n⟩`
-(`NUPPT.exists_withAdvice`, bound `.add (.mul (.add q (.const 1)) (.add (.mul (.const 2) .var) (.const 2))) D.adv`-style),
-coins `(q + 1) · var + D.coins` (`NUPPT.exists_split` with `p := .mul (.add q (.const 1)) .var`: the
-first `(q n + 1) n` coins are the points `r₀ … r_{q n}`, read as blocks by
-`Complexity.polyTimeComputable_blockMap .var`), and on the encoded history `hist` outputs: if
-`|hist| ≤ q n` the query `⟨[false], r_{|hist|}⟩` (history length by `polyTimeComputable_blockMap`
-counting, `pairDecode`/`decodeFin` are FP), else the verdict `[true, b]` where `b` is `D`'s
-verdict on `encodeTuple (r_j, v_j ⊕ ans_j)_j` (`polyTimeComputable_pairXor` blockwise,
-`NUPPT.exists_comp`). By induction on the history, `buildTree` with budget `q n + 1` from `[]`
-is the chain `chainTree (q n + 1) r (…)`, i.e.
-`B_v.toOracleAdversary n n n (q n + 1) = multiMsgAdv vⁿ Dⁿ` up to the coin bijection
-`B_v.Coins n ≃ (Fin (q n + 1) → {0,1}^n) × D.Coins n` (`FunFamily.blocks`, `Fin.appendEquiv`),
-so `acceptProb_comp_equiv` gives `prfAdv (F n) (B_v^{(q n + 1)}) = prfAdv (F n) (multiMsgAdv vⁿ Dⁿ)`.
-*Asymptotic step:* `hF.negligible_prfAdv B_v (.add q (.const 1))` makes both PRF terms
-negligible; the collision term is negligible by `negligible_two_pow_neg` and
-`Negligible.mul_pow`/`Negligible.const_mul` with `C(q n + 1, 2) ≤ (q n + 1)^2 ≤ C'(n + 1)^{2d}`
-from `PolyExpr.eval_le` (`Nat.choose_le_pow`); `Negligible.add` twice, and by maximality
-`ε n := ` this sum bounds the advantage for every `n, m, m'`. -/
+**Proof sketch.** The case `ℓ = var` of `MultiMsg.exists_negligible_distAdv_prfEncRealOut`
+(applied to `hF.pseudorandom`), which maximizes over the message pairs, builds the next-query
+machines of Thm-99.2.1 (`MultiMsg.exists_queryChainOut_nuppt`) and bounds the advantage by the
+six hybrids (`distAdv_prfEncRealOut_le`), two PRF advantages and the collision term. The
+ciphertext tuples of Algorithm 99.1 are `encodeTuple ∘ prfEncReal (F n) m` on the seeds
+`prfScheme_coinsEquiv` (`prfScheme_multiEncDist`), i.e. `encodeTupleOut ∘ prfEncRealOut (F n) m`
+(`encodeTuple_eq_encodeTupleOut`, `prfEncReal_eq_prfEncRealOut`); relabel the seeds
+(`acceptProb_comp_equiv`). -/
 theorem prfScheme_multiMessageSecure (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
     (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
     (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
     (prfScheme F E hE hFE).MultiMessageSecure := by
   refine (PrivateKeyScheme.multiMessageSecure_iff _).2 fun D q => ?_
-  -- the worst message pair at each parameter (hard-wired into the reductions)
-  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
-      ∀ w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
-        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
-            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n) ≤
-          distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.1)
-            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.2) (D.distinguisherL n) := by
-    intro n
-    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
-      (fun w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
-        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
-          ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n))
-      Finset.univ_nonempty
-    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
-  choose μ hμ using hmax
-  -- the next-query machines of Thm-99.2.1 for the two hard-wired message vectors
-  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).1
-  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).2
-  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n n (q.eval n + 1)) +
-      prfAdv (F n) (B₁.toOracleAdversary n n n (q.eval n + 1)) +
-      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n m m' => ?_⟩
-  · -- the asymptotic step: two PRF advantages and the collision term
-    simpa only [PolyExpr.eval_add, PolyExpr.eval_const] using
-      ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
-        (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
-        ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
-  · refine (hμ n (m, m')).trans ?_
-    -- the concrete step: the ciphertext tuples are `encodeTuple ∘ prfEncReal`
-    have key : ∀ m₀ : Fin (q.eval n + 1) → Fin n → Bool,
-        (prfScheme F E hE hFE).multiEncDist n (q.eval n) m₀ =
-          fun r => encodeTuple (prfEncReal (F n) m₀ (prfScheme_coinsEquiv F E hE hFE n (q.eval n) r)) :=
-      fun m₀ => funext fun r => prfScheme_multiEncDist F E hE hFE n (q.eval n) m₀ r
-    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdv`
-    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin n → Bool)
-        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
-        (∀ (g : (Fin n → Bool) → (Fin n → Bool)) ρ c,
-          (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
-            decide (D.runAt n (List.ofFn fun j =>
-              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
-                [true])) →
-        prfAdv (F n) (B.toOracleAdversary n n n (q.eval n + 1)) =
-          prfAdv (F n) (multiMsgAdv v fun w c => D.distinguisherL n (encodeTuple w) c) := by
-      intro B v φ hφ
-      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g w => ?_
-      rw [hφ g w.1 w.2, eval_multiMsgAdv, NUPPT.distinguisherL_eq, encodeTuple_eq_flatten]
-    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
-    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
-    dsimp only
-    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁, key, key, distAdv_def,
-      acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
-        (fun s => encodeTuple (prfEncReal (F n) (μ n).1 s)),
-      acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
-        (fun s => encodeTuple (prfEncReal (F n) (μ n).2 s)), ← distAdv_def]
-    exact (distAdv_comp encodeTuple (prfEncReal (F n) (μ n).1) (prfEncReal (F n) (μ n).2)
-      (D.distinguisherL n)).symm.trans_le (distAdv_prfEncReal_le (F n) (μ n).1 (μ n).2
-        (fun w c => D.distinguisherL n (encodeTuple w) c))
+  obtain ⟨ε, hε, hb⟩ := MultiMsg.exists_negligible_distAdv_prfEncRealOut hF.pseudorandom D q
+  refine ⟨ε, hε, fun n m m' => ?_⟩
+  -- the ciphertext tuples are `encodeTupleOut ∘ prfEncRealOut` on relabelled seeds
+  have key : ∀ m₀ : Fin (q.eval n + 1) → Fin n → Bool,
+      (prfScheme F E hE hFE).multiEncDist n (q.eval n) m₀ = fun r =>
+        encodeTupleOut (prfEncRealOut (F n) m₀ (prfScheme_coinsEquiv F E hE hFE n (q.eval n) r)) :=
+    fun m₀ => funext fun r => by
+      rw [prfScheme_multiEncDist, encodeTuple_eq_encodeTupleOut, prfEncReal_eq_prfEncRealOut]
+  rw [key, key, distAdv_def,
+    acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
+      (fun s => encodeTupleOut (prfEncRealOut (F n) m s)),
+    acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
+      (fun s => encodeTupleOut (prfEncRealOut (F n) m' s)), ← distAdv_def]
+  exact hb n m m'
 
 /-- **Multi-message secure private-key encryption exists if a PRF exists** ([PS10, §3.9]):
 the scheme of Algorithm 99.1 with the evaluator of `PRF.easy`. -/
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/Hybrid.lean b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/Hybrid.lean
index fe5cda791..07ef519a5 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/Hybrid.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/Hybrid.lean
@@ -23,6 +23,8 @@ of repeated points. The two independent-pad experiments agree by perfect secrecy
 * `chainTree` asks a fixed tuple of oracle queries.
 * `prfEncReal` and `otpEnc` sample the ciphertext tuples in the real and independent-pad experiments.
 * `multiMsgAdv` runs a tuple distinguisher after querying the oracle at the sampled points.
+* `prfEncRealOut`, `otpEncOut` and `multiMsgAdvOut` are the same at output width `l` (ruling B3);
+  the `n`-bit ones are their cases `l = n` (`prfEncReal_eq_prfEncRealOut`, …).
 
 ## Main results
 
@@ -30,6 +32,9 @@ of repeated points. The two independent-pad experiments agree by perfect secrecy
 * `distAdv_prfEncReal_random_otp_le` bounds the inner switch by the collision probability.
 * `acceptProb_otpEnc` equates the two independent-pad experiments.
 * `distAdv_prfEncReal_le` combines the switches [PS10, Theorem 99.2, proof].
+* `prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_random_otp_le`, `acceptProb_otpEncOut` and
+  `distAdv_prfEncRealOut_le` are the same at output width `l`; the four results above are their
+  cases `l = n`.
 
 **Deviation.** The vector has `q + 1` points, giving collision term `C(q + 1, 2) / 2^n`.
 
@@ -88,6 +93,96 @@ section Concrete
 
 variable {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ]
 
+variable {l : ℕ}
+
+/-! #### The hybrids at output width `l`
+
+The concrete hybrids for a keyed family `F : K → {0,1}^n → {0,1}^l` with `l`-bit outputs (ruling
+B3): the points stay `n`-bit strings, only the answers, messages and pads have `l` bits. The
+`n`-bit hybrids below are their cases `l = n` (`prfEncReal_eq_prfEncRealOut`, …). -/
+
+/-- **The real hybrid at output width `l`** ([PS10, Theorem 99.2, proof, `H¹` and `H²`, with
+`ℓ`-bit outputs]): the ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the
+points `z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^l` and messages
+`m : Fin (q+1) → {0,1}^l`: `prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j))`. -/
+def prfEncRealOut (F : K → (Fin n → Bool) → (Fin l → Bool)) (m : Fin (q + 1) → Fin l → Bool) :
+    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
+  fun z j => (z.2 j, m j + F z.1 (z.2 j))
+
+omit [Fintype K] in
+/-- The real hybrid at width `l`, entrywise:
+`prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j))`. -/
+theorem prfEncRealOut_apply (F : K → (Fin n → Bool) → (Fin l → Bool))
+    (m : Fin (q + 1) → Fin l → Bool) (z : K × (Fin (q + 1) → Fin n → Bool)) (j : Fin (q + 1)) :
+    prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j)) := rfl
+
+/-- **The one-time-pad hybrid at output width `l`** ([PS10, Theorem 99.2, proof, `H³`, with
+`ℓ`-bit outputs]): the tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with `n`-bit points `r_j` and independent
+uniform `l`-bit pads `p_j`, on the seeds `z = (r, p)`: `otpEncOut m z j = (z.1 j, m j + z.2 j)`. -/
+def otpEncOut (m : Fin (q + 1) → Fin l → Bool) :
+    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool) →
+      (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
+  fun z j => (z.1 j, m j + z.2 j)
+
+/-- The one-time-pad hybrid at width `l`, entrywise: `otpEncOut m z j = (z.1 j, m j + z.2 j)`. -/
+theorem otpEncOut_apply (m : Fin (q + 1) → Fin l → Bool)
+    (z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool)) (j : Fin (q + 1)) :
+    otpEncOut m z j = (z.1 j, m j + z.2 j) := rfl
+
+/-- **The oracle adversary of Thm-99.2.1 at output width `l`** ([PS10, Theorem 99.2, proof, with
+`ℓ`-bit outputs]): on coins `c = (r, c')` it queries its `l`-bit-output oracle at `r₀, …, r_q`
+(`chainTree`), forms `(r_j, m_j ⊕ ans_j)_j` and runs `D` on it with coins `c'`:
+`multiMsgAdvOut m D c = chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2`. -/
+def multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
+    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin l → Bool) :=
+  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2
+
+omit [Fintype ρ] in
+/-- Evaluating the hybrid adversary at width `l` against the oracle `g` runs `D` on the masked
+tuple: `(multiMsgAdvOut m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2`
+[PS10, Theorem 99.2, proof]. -/
+theorem eval_multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool)
+    (g : (Fin n → Bool) → Fin l → Bool) (c : (Fin (q + 1) → Fin n → Bool) × ρ) :
+    (multiMsgAdvOut m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2 := by
+  rw [multiMsgAdvOut, eval_chainTree]
+
+omit [Fintype ρ] in
+/-- `multiMsgAdvOut m D` makes at most `q + 1` queries: `(multiMsgAdvOut m D).BoundedBy (q + 1)`. -/
+theorem multiMsgAdvOut_boundedBy (m : Fin (q + 1) → Fin l → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
+    (multiMsgAdvOut m D).BoundedBy (q + 1) :=
+  (OracleAdversary.boundedBy_iff _ _).2 fun c => boundedBy_chainTree (q + 1) c.1 _
+
+/-- Running `multiMsgAdvOut m D` with the oracle `F k` for a uniform key accepts with the
+probability that `D` accepts the hybrid at width `l`:
+`acceptProb F (oracleDist (multiMsgAdvOut m D)) = acceptProb (prfEncRealOut F m) D`
+(reassociation of the seed space `K × (points × coins)`). -/
+theorem acceptProb_oracleDist_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool))
+    (m : Fin (q + 1) → Fin l → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
+    acceptProb F (oracleDist (multiMsgAdvOut m D)) = acceptProb (prfEncRealOut F m) D := by
+  rw [acceptProb_def, acceptProb_def]
+  rw [← uprob_comp_equiv (Equiv.prodAssoc K (Fin (q + 1) → Fin n → Bool) ρ)]
+  congr 1
+  funext z
+  simp only [oracleDist_apply, multiMsgAdvOut, eval_chainTree, Equiv.prodAssoc_apply]
+  rfl
+
+/-- **Thm-99.2.1 at output width `l`: the gap `H¹ → H²` is a PRF advantage** ([PS10,
+Theorem 99.2, proof, with `ℓ`-bit outputs]):
+`prfAdv F (multiMsgAdvOut m D) = distAdv (prfEncRealOut F m) (prfEncRealOut R m) D` with
+`R = randomFunction {0,1}^n {0,1}^l` (unfolding of `prfAdv`, `oracleDist` and `acceptProb`). -/
+theorem prfAdv_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool))
+    (m : Fin (q + 1) → Fin l → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
+    prfAdv F (multiMsgAdvOut m D) =
+      distAdv (prfEncRealOut F m)
+        (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D := by
+  rw [prfAdv_def, distAdv_def, distAdv_def, acceptProb_oracleDist_multiMsgAdvOut,
+    acceptProb_oracleDist_multiMsgAdvOut]
+
 /-- The ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the points
 `z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^n`. With `F` the PRF this is the
 hybrid `H¹` ("real encryptions"); with `F = randomFunction` (keys are function tables) it is
@@ -96,12 +191,20 @@ def prfEncReal (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1
     K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
   fun z j => (z.2 j, m j + F z.1 (z.2 j))
 
+omit [Fintype K] in
+/-- The real hybrid is the case `l = n` of the hybrid at width `l`:
+`prfEncReal F m = prfEncRealOut F m` (`rfl`). -/
+theorem prfEncReal_eq_prfEncRealOut (F : K → (Fin n → Bool) → (Fin n → Bool))
+    (m : Fin (q + 1) → Fin n → Bool) : prfEncReal F m = prfEncRealOut F m := rfl
+
 omit [Fintype K] in
 /-- The hybrid ciphertext at position `j` contains the point `z.2 j` and the message
 masked with the oracle's value at that point [PS10, Theorem 99.2, proof]. -/
 theorem prfEncReal_apply (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool)
     (z : K × (Fin (q + 1) → Fin n → Bool)) (j : Fin (q + 1)) :
-    prfEncReal F m z j = (z.2 j, m j + F z.1 (z.2 j)) := rfl
+    prfEncReal F m z j = (z.2 j, m j + F z.1 (z.2 j)) := by
+  rw [prfEncReal_eq_prfEncRealOut]
+  exact prfEncRealOut_apply F m z j
 
 /-- The ciphertext tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with independent uniform pads `p_j`: the
 hybrid `H³` ("using OTP") of [PS10, Theorem 99.2, proof]; seeds `(r, p)`. -/
@@ -110,6 +213,11 @@ def otpEnc (m : Fin (q + 1) → Fin n → Bool) :
       (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
   fun z j => (z.1 j, m j + z.2 j)
 
+/-- The one-time-pad hybrid is the case `l = n` of the hybrid at width `l`:
+`otpEnc m = otpEncOut m` (`rfl`). -/
+theorem otpEnc_eq_otpEncOut (m : Fin (q + 1) → Fin n → Bool) :
+    otpEnc (n := n) m = otpEncOut m := rfl
+
 /-- **The oracle adversary of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
 otherwise (by closure under efficient operations) we contradict the pseudorandomness property"]):
 on coins `(r, c)` it queries its oracle at `r₀, …, r_q` (a chain of `q + 1` queries), forms the
@@ -120,6 +228,13 @@ def multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
     OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin n → Bool) :=
   fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2
 
+omit [Fintype ρ] in
+/-- The hybrid adversary is the case `l = n` of the adversary at width `l`:
+`multiMsgAdv m D = multiMsgAdvOut m D` (`rfl`). -/
+theorem multiMsgAdv_eq_multiMsgAdvOut (m : Fin (q + 1) → Fin n → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
+    multiMsgAdv m D = multiMsgAdvOut m D := rfl
+
 omit [Fintype ρ] in
 /-- Evaluating the hybrid adversary on an oracle runs the tuple distinguisher on the sampled
 points and the messages masked by the oracle values [PS10, Theorem 99.2, proof]. -/
@@ -127,14 +242,16 @@ theorem eval_multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
     (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool)
     (g : (Fin n → Bool) → Fin n → Bool) (c : (Fin (q + 1) → Fin n → Bool) × ρ) :
     (multiMsgAdv m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2 := by
-  rw [multiMsgAdv, eval_chainTree]
+  rw [multiMsgAdv_eq_multiMsgAdvOut]
+  exact eval_multiMsgAdvOut m D g c
 
 omit [Fintype ρ] in
 /-- `multiMsgAdv m D` makes at most `q + 1` queries. -/
 theorem multiMsgAdv_boundedBy (m : Fin (q + 1) → Fin n → Bool)
     (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
-    (multiMsgAdv m D).BoundedBy (q + 1) :=
-  (OracleAdversary.boundedBy_iff _ _).2 fun c => boundedBy_chainTree (q + 1) c.1 _
+    (multiMsgAdv m D).BoundedBy (q + 1) := by
+  rw [multiMsgAdv_eq_multiMsgAdvOut]
+  exact multiMsgAdvOut_boundedBy m D
 
 /-- Running `multiMsgAdv m D` with the oracle `F k` (for a uniform key `k`) accepts with the
 probability that `D` accepts the hybrid sampler `prfEncReal F m` (reassociation of the seed
@@ -143,12 +260,8 @@ theorem acceptProb_oracleDist_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n
     (m : Fin (q + 1) → Fin n → Bool)
     (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
     acceptProb F (oracleDist (multiMsgAdv m D)) = acceptProb (prfEncReal F m) D := by
-  rw [acceptProb_def, acceptProb_def]
-  rw [← uprob_comp_equiv (Equiv.prodAssoc K (Fin (q + 1) → Fin n → Bool) ρ)]
-  congr 1
-  funext z
-  simp only [oracleDist_apply, multiMsgAdv, eval_chainTree, Equiv.prodAssoc_apply]
-  rfl
+  rw [multiMsgAdv_eq_multiMsgAdvOut, prfEncReal_eq_prfEncRealOut]
+  exact acceptProb_oracleDist_multiMsgAdvOut F m D
 
 /-- **Thm-99.2.1: the gap `H¹ → H²` is a PRF advantage.** The advantage of `D` between the real
 encryptions `(r_j, m_j ⊕ F_k(r_j))_j` and the random-function encryptions
@@ -159,8 +272,8 @@ theorem prfAdv_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
     (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
     prfAdv F (multiMsgAdv m D) =
       distAdv (prfEncReal F m) (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D := by
-  rw [prfAdv_def, distAdv_def, distAdv_def, acceptProb_oracleDist_multiMsgAdv,
-    acceptProb_oracleDist_multiMsgAdv]
+  simp only [multiMsgAdv_eq_multiMsgAdvOut, prfEncReal_eq_prfEncRealOut]
+  exact prfAdv_multiMsgAdvOut F m D
 
 /-- **The collision bound** ([PS10, Theorem 99.2, proof, "`∃ i, j` such that `r_i = r_j`, but this
 happens only with probability `C(q,2) · 2^{−n}`"]): `q + 1` uniform `n`-bit points fail to be
@@ -224,85 +337,155 @@ theorem pushesUniform_comp_injective {I O : Type*} [Fintype I] [DecidableEq I] [
     simp only [uexp_def, univ_eq_empty, sum_empty, zero_div]
   · exact HardcoreBit.pushesUniform_restrict hr
 
-/-- **Thm-99.2.2: the gap `H² → H³` is at most the collision probability**
+/-- **Thm-99.2.2 at output width `l`: the gap `H² → H³` is at most the collision probability**
 ([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
-`∃ i, j` such that `r_i = r_j`"]): the advantage of `D` between the random-function encryptions
-`(r_j, m_j ⊕ R(r_j))_j` and the one-time-pad encryptions `(r_j, m_j ⊕ p_j)_j` is at most
-`C(q+1, 2) / 2^n`.
+`∃ i, j` such that `r_i = r_j`", with `ℓ`-bit outputs]): with `R = randomFunction {0,1}^n {0,1}^l`,
+`distAdv (prfEncRealOut R m) (otpEncOut m) D ≤ C(q+1, 2) / 2^n`. The bound concerns the `n`-bit
+points only; it does not depend on `l`.
 
 **Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
 `r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).
 
 **Proof sketch.** Write both acceptance probabilities as averages over the points `r`
-(`uprob_prod` after `uprob_prod_comm`): `a(r) := Pr_R[D((r_j, m_j ⊕ R(r_j))_j) = 1]` and
-`b(r) := Pr_p[D((r_j, m_j ⊕ p_j)_j) = 1]`. When `r` is injective, `(R(r_j))_j` is uniform
-(`pushesUniform_comp_injective`, `PushesUniform.uprob_eq`), so `a(r) = b(r)`; otherwise
-`|a(r) − b(r)| ≤ 1` (`uprob_nonneg`, `uprob_le_one`). Hence
-`|E_r a − E_r b| ≤ E_r |a − b| ≤ E_r [¬ Injective r] = uprob (¬ Injective)` (`uexp` is monotone
-and `|∑| ≤ ∑ |·|`, `uprob_eq_uexp_ite`), and `uprob_not_injective_le` bounds the last term. -/
-theorem distAdv_prfEncReal_random_otp_le (m : Fin (q + 1) → Fin n → Bool)
-    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
-    distAdv (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) (otpEnc m) D ≤
+(`uprob_prod` after reassociating the seeds): `a(r) := Pr_R[D((r_j, m_j ⊕ R(r_j))_j) = 1]` and
+`b(r) := Pr_p[D((r_j, m_j ⊕ p_j)_j) = 1]`. When `r` is injective, `(R(r_j))_j` is uniform on
+`({0,1}^l)^{q+1}` (`pushesUniform_comp_injective`, `PushesUniform.uprob_eq`), so `a(r) = b(r)`;
+otherwise `|a(r) − b(r)| ≤ 1`. Hence `|E_r a − E_r b| ≤ uprob (¬ Injective)`
+(`MultiMsg.abs_uexp_sub_le_uprob`), and `uprob_not_injective_le` bounds it. -/
+theorem distAdv_prfEncRealOut_random_otp_le (m : Fin (q + 1) → Fin l → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
+    distAdv (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) (otpEncOut m) D ≤
       (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
   classical
   -- the acceptance probabilities conditioned on the points `r`
   let a : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
-    uprob fun w : ((Fin n → Bool) → (Fin n → Bool)) × ρ =>
+    uprob fun w : ((Fin n → Bool) → (Fin l → Bool)) × ρ =>
       D (fun j => (r j, m j + w.1 (r j))) w.2 = true
   let b : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
-    uprob fun w : (Fin (q + 1) → Fin n → Bool) × ρ => D (fun j => (r j, m j + w.1 j)) w.2 = true
-  have ha : acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D =
+    uprob fun w : (Fin (q + 1) → Fin l → Bool) × ρ => D (fun j => (r j, m j + w.1 j)) w.2 = true
+  have ha : acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D =
       uexp a := by
-    rw [acceptProb_def, show randomFunction (Fin n → Bool) (Fin n → Bool) = id from
+    rw [acceptProb_def, show randomFunction (Fin n → Bool) (Fin l → Bool) = id from
       funext fun f => randomFunction_apply _ _ f]
     exact (uprob_comp_equiv ((Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
-      ((Fin n → Bool) → (Fin n → Bool)) ρ).symm.trans
+      ((Fin n → Bool) → (Fin l → Bool)) ρ).symm.trans
         ((Equiv.prodComm _ _).prodCongr (Equiv.refl ρ))) _).symm.trans
       (by rw [uprob_prod]; rfl)
-  have hb : acceptProb (otpEnc m) D = uexp b := by
+  have hb : acceptProb (otpEncOut m) D = uexp b := by
     rw [acceptProb_def]
     exact (uprob_comp_equiv (Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
-      (Fin (q + 1) → Fin n → Bool) ρ).symm _).symm.trans (by rw [uprob_prod]; rfl)
+      (Fin (q + 1) → Fin l → Bool) ρ).symm _).symm.trans (by rw [uprob_prod]; rfl)
   -- at injective points the table values are fresh uniform pads
   have hab : ∀ r : Fin (q + 1) → Fin n → Bool, Function.Injective r → a r = b r := by
     intro r hr
-    exact ((pushesUniform_comp_injective (O := Fin n → Bool) hr).prodMap
+    exact ((pushesUniform_comp_injective (O := Fin l → Bool) hr).prodMap
       (HardcoreBit.pushesUniform_id (Ω := ρ))).uprob_eq
-      (fun v : (Fin (q + 1) → Fin n → Bool) × ρ => D (fun j => (r j, m j + v.1 j)) v.2 = true)
+      (fun v : (Fin (q + 1) → Fin l → Bool) × ρ => D (fun j => (r j, m j + v.1 j)) v.2 = true)
   rw [distAdv_def, ha, hb]
   exact (MultiMsg.abs_uexp_sub_le_uprob a b (fun r => ¬ Function.Injective r)
     (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩)
     (fun r hr => hab r (not_not.mp hr))).trans uprob_not_injective_le
 
-/-- **Thm-99.2.3: `H³ = H⁴` by the perfect secrecy of the one-time pad** ([PS10, Theorem 99.2,
-proof, "`H³` and `H⁴` are identical by the perfect secrecy of the OTP"], the vector version of
-Claim-92.a): for independent uniform pads `p_j`, the tuples `(r_j, m_j ⊕ p_j)_j` and
-`(r_j, m'_j ⊕ p_j)_j` are identically distributed, so every distinguisher accepts them with the
-same probability.
+/-- **Thm-99.2.3 at output width `l`: `H³ = H⁴` by the perfect secrecy of the one-time pad**
+([PS10, Theorem 99.2, proof, with `ℓ`-bit outputs]): for independent uniform `l`-bit pads,
+`acceptProb (otpEncOut m) D = acceptProb (otpEncOut m') D` for all messages `m`, `m'`.
 
 **Proof sketch.** The map `(r, p) ↦ (r, p ⊕ (m ⊕ m'))` is a bijection of the seed space
 (`Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))`) carrying the sampler for `m'` to the
 sampler for `m` (in the Boolean group `x + x = 0`); relabel by it (`acceptProb_comp_equiv`). -/
-theorem acceptProb_otpEnc (m m' : Fin (q + 1) → Fin n → Bool)
-    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
-    acceptProb (otpEnc m) D = acceptProb (otpEnc m') D := by
-  have key : ∀ z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool),
-      otpEnc m' ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z) = otpEnc m z := by
+theorem acceptProb_otpEncOut (m m' : Fin (q + 1) → Fin l → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
+    acceptProb (otpEncOut (n := n) m) D = acceptProb (otpEncOut m') D := by
+  have key : ∀ z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool),
+      otpEncOut m' ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z) =
+        otpEncOut m z := by
     intro z
     funext j
-    simp only [otpEnc, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight, Prod.map_fst,
-      Prod.map_snd, id_eq, Pi.add_apply]
+    simp only [otpEncOut, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight,
+      Prod.map_fst, Prod.map_snd, id_eq, Pi.add_apply]
     refine Prod.ext rfl ?_
     funext i
     simp only [Pi.add_apply]
     cases m j i <;> cases m' j i <;> cases z.2 j i <;> rfl
-  calc acceptProb (otpEnc m) D
-      = acceptProb (fun z => otpEnc m'
+  calc acceptProb (otpEncOut m) D
+      = acceptProb (fun z => otpEncOut m'
           ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z)) D := by
         congr 1
         funext z
         exact (key z).symm
-    _ = acceptProb (otpEnc m') D := acceptProb_comp_equiv _ (otpEnc m') D
+    _ = acceptProb (otpEncOut m') D := acceptProb_comp_equiv _ (otpEncOut m') D
+
+/-- **[PS10, Theorem 99.2], concrete form, at output width `l`: the six-hybrid bound** (with
+`ℓ`-bit outputs). For a keyed family `F : K → {0,1}^n → {0,1}^l`, message vectors
+`m, m' ∈ ({0,1}^l)^{q+1}` and any distinguisher `D` of ciphertext tuples,
+`distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤ prfAdv F (multiMsgAdvOut m D) +
+prfAdv F (multiMsgAdvOut m' D) + 2 · C(q+1, 2) / 2^n`.
+
+**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
+`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).
+
+**Proof sketch.** Hybrids `H¹ = prfEncRealOut F m`, `H² = prfEncRealOut R m`, `H³ = otpEncOut m`,
+`H⁴ = otpEncOut m'`, `H⁵ = prfEncRealOut R m'`, `H⁶ = prfEncRealOut F m'`: `|H¹ − H²|` and
+`|H⁵ − H⁶|` are the two PRF advantages (`prfAdv_multiMsgAdvOut`), `|H² − H³|` and `|H⁴ − H⁵|`
+are at most the collision bound (`distAdv_prfEncRealOut_random_otp_le`), `H³ = H⁴`
+(`acceptProb_otpEncOut`); the triangle inequality (`abs_sub_le`, three times) finishes. -/
+theorem distAdv_prfEncRealOut_le (F : K → (Fin n → Bool) → (Fin l → Bool))
+    (m m' : Fin (q + 1) → Fin l → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
+    distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤
+      prfAdv F (multiMsgAdvOut m D) + prfAdv F (multiMsgAdvOut m' D) +
+        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
+  have h12 := prfAdv_multiMsgAdvOut F m D
+  have h56 := prfAdv_multiMsgAdvOut F m' D
+  have h23 := distAdv_prfEncRealOut_random_otp_le m D
+  have h45 := distAdv_prfEncRealOut_random_otp_le m' D
+  have h34 := acceptProb_otpEncOut m m' D
+  simp only [distAdv_def] at h12 h56 h23 h45 ⊢
+  rw [h12, h56, abs_sub_comm (acceptProb (prfEncRealOut F m') D)]
+  rw [abs_sub_comm (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m')
+    D)] at h45
+  have t1 := abs_sub_le (acceptProb (prfEncRealOut F m) D)
+    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D)
+    (acceptProb (prfEncRealOut F m') D)
+  have t2 := abs_sub_le
+    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D)
+    (acceptProb (otpEncOut m) D) (acceptProb (prfEncRealOut F m') D)
+  have t3 := abs_sub_le (acceptProb (otpEncOut m') D)
+    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m') D)
+    (acceptProb (prfEncRealOut F m') D)
+  rw [← h34] at t3 h45
+  linarith
+
+/-- **Thm-99.2.2: the gap `H² → H³` is at most the collision probability**
+([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
+`∃ i, j` such that `r_i = r_j`"]): the advantage of `D` between the random-function encryptions
+`(r_j, m_j ⊕ R(r_j))_j` and the one-time-pad encryptions `(r_j, m_j ⊕ p_j)_j` is at most
+`C(q+1, 2) / 2^n`.
+
+**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
+`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).
+
+**Proof sketch.** The case `l = n` of `distAdv_prfEncRealOut_random_otp_le`
+(`prfEncReal_eq_prfEncRealOut`, `otpEnc_eq_otpEncOut`). -/
+theorem distAdv_prfEncReal_random_otp_le (m : Fin (q + 1) → Fin n → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
+    distAdv (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) (otpEnc m) D ≤
+      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
+  rw [prfEncReal_eq_prfEncRealOut, otpEnc_eq_otpEncOut]
+  exact distAdv_prfEncRealOut_random_otp_le m D
+
+/-- **Thm-99.2.3: `H³ = H⁴` by the perfect secrecy of the one-time pad** ([PS10, Theorem 99.2,
+proof, "`H³` and `H⁴` are identical by the perfect secrecy of the OTP"], the vector version of
+Claim-92.a): for independent uniform pads `p_j`, the tuples `(r_j, m_j ⊕ p_j)_j` and
+`(r_j, m'_j ⊕ p_j)_j` are identically distributed, so every distinguisher accepts them with the
+same probability.
+
+**Proof sketch.** The case `l = n` of `acceptProb_otpEncOut` (`otpEnc_eq_otpEncOut`). -/
+theorem acceptProb_otpEnc (m m' : Fin (q + 1) → Fin n → Bool)
+    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
+    acceptProb (otpEnc m) D = acceptProb (otpEnc m') D := by
+  rw [otpEnc_eq_otpEncOut, otpEnc_eq_otpEncOut]
+  exact acceptProb_otpEncOut m m' D
 
 /-- **[PS10, Theorem 99.2], concrete form: the six-hybrid bound.** For a keyed family
 `F : K → {0,1}^n → {0,1}^n`, message vectors `m, m' ∈ ({0,1}^n)^{q+1}` and any distinguisher
@@ -313,36 +496,16 @@ is at most `prfAdv F (A_m D) + prfAdv F (A_{m'} D) + 2 · C(q+1, 2) / 2^n`, wher
 **Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
 `r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).
 
-**Proof sketch.** Hybrids `H¹ = prfEncReal F m`, `H² = prfEncReal R m`, `H³ = otpEnc m`,
-`H⁴ = otpEnc m'`, `H⁵ = prfEncReal R m'`, `H⁶ = prfEncReal F m'`: `|H¹ − H²|` and `|H⁵ − H⁶|` are
-the two PRF advantages (`prfAdv_multiMsgAdv`), `|H² − H³|` and `|H⁴ − H⁵|` are at most the
-collision bound (`distAdv_prfEncReal_random_otp_le`), `H³ = H⁴` (`acceptProb_otpEnc`); the
-triangle inequality (`abs_sub_le`, five times) finishes. -/
+**Proof sketch.** The case `l = n` of `distAdv_prfEncRealOut_le` (`prfEncReal_eq_prfEncRealOut`,
+`multiMsgAdv_eq_multiMsgAdvOut`). -/
 theorem distAdv_prfEncReal_le (F : K → (Fin n → Bool) → (Fin n → Bool))
     (m m' : Fin (q + 1) → Fin n → Bool)
     (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
     distAdv (prfEncReal F m) (prfEncReal F m') D ≤
       prfAdv F (multiMsgAdv m D) + prfAdv F (multiMsgAdv m' D) +
         2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
-  have h12 := prfAdv_multiMsgAdv F m D
-  have h56 := prfAdv_multiMsgAdv F m' D
-  have h23 := distAdv_prfEncReal_random_otp_le m D
-  have h45 := distAdv_prfEncReal_random_otp_le m' D
-  have h34 := acceptProb_otpEnc m m' D
-  simp only [distAdv_def] at h12 h56 h23 h45 ⊢
-  rw [h12, h56, abs_sub_comm (acceptProb (prfEncReal F m') D)]
-  rw [abs_sub_comm (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m') D)]
-    at h45
-  have t1 := abs_sub_le (acceptProb (prfEncReal F m) D)
-    (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D)
-    (acceptProb (prfEncReal F m') D)
-  have t2 := abs_sub_le (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D)
-    (acceptProb (otpEnc m) D) (acceptProb (prfEncReal F m') D)
-  have t3 := abs_sub_le (acceptProb (otpEnc m') D)
-    (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m') D)
-    (acceptProb (prfEncReal F m') D)
-  rw [← h34] at t3 h45
-  linarith
+  simp only [prfEncReal_eq_prfEncRealOut, multiMsgAdv_eq_multiMsgAdvOut]
+  exact distAdv_prfEncRealOut_le F m m' D
 
 end Concrete
 
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/MultiMsgOut.lean b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/MultiMsgOut.lean
new file mode 100644
index 000000000..13f04d8db
--- /dev/null
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/MultiMsgOut.lean
@@ -0,0 +1,163 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
+import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
+import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
+import TCSlib.Cryptography.Pseudorandom.Indistinguishability
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The multi-message bound at `ℓ(n)`-bit outputs
+
+The total of [PS10, Theorem 99.2] for a keyed family with `ℓ(n)`-bit outputs (ruling B3), without
+the scheme: for a family `F` whose keyed ensemble is oracle-indistinguishable from the random
+functions with `ℓ(n)`-bit outputs, every non-uniform PPT `D` distinguishes the encoded real
+hybrids of any two mask vectors with negligible advantage, uniformly in the masks
+(`MultiMsg.exists_negligible_distAdv_prfEncRealOut`). The `n`-bit scheme's
+`prfScheme_multiMessageSecure` is its case `ℓ = var`.
+
+## Main definitions
+
+* `encodeTupleOut`: the encoded tuple of ciphertext pairs with `n`-bit points and `l`-bit pads.
+
+## Main results
+
+* `MultiMsg.encodeList_eq_flatMap`: `encodeList` as a concatenation of chunks (the general form of
+  a private lemma of `FromPRF.lean`).
+* `encodeTupleOut_eq_flatten`: the encoded tuple as the machine produces it.
+* `MultiMsg.exists_negligible_distAdv_prfEncRealOut`: the total.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
+  (§3.8, Definition 96.2, and §3.9, Theorem 99.2, with `ℓ`-bit outputs.)
+-/
+
+namespace TCSlib.Cryptography
+
+open Complexity Turing Finset
+
+/-- **The encoded ciphertext tuple at output width `l`**: `encodeList` of the pairs
+`⟨r_j, c_j⟩` of an `n`-bit point and an `l`-bit string,
+`encodeTupleOut v = encodeList (List.ofFn fun j => ⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩)`. -/
+def encodeTupleOut {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
+    List Bool :=
+  PrivateKeyScheme.encodeList
+    (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))
+
+/-- The defining equation:
+`encodeTupleOut v = encodeList (List.ofFn fun j => ⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩)`. -/
+theorem encodeTupleOut_eq {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
+    encodeTupleOut v = PrivateKeyScheme.encodeList
+      (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) :=
+  rfl
+
+/-- **`encodeList` is a concatenation of chunks**: `encodeList l` is the concatenation of the
+self-delimited chunks `⟨c, []⟩`, `encodeList l = l.flatMap fun c => ⟨c, []⟩`. -/
+theorem MultiMsg.encodeList_eq_flatMap : ∀ l : List (List Bool),
+    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
+  | [] => by rw [PrivateKeyScheme.encodeList_nil, List.flatMap_nil]
+  | c :: l => by
+    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, MultiMsg.encodeList_eq_flatMap l]
+    simp [pairEncode_eq]
+
+/-- The encoded tuple at width `l` is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
+form in which `MultiMsg.exists_queryChainOut_nuppt` produces it):
+`encodeTupleOut v = (List.ofFn fun j => ⟨⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩, []⟩).flatten`. -/
+theorem encodeTupleOut_eq_flatten {n l q : ℕ}
+    (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
+    encodeTupleOut v =
+      (List.ofFn fun j =>
+        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
+  rw [encodeTupleOut_eq, MultiMsg.encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]
+
+/-- **[PS10, Theorem 99.2] at `ℓ(n)`-bit outputs, the total** (with `ℓ`-bit outputs; ruling B3):
+if the keyed ensemble of `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ(n)}` is oracle-indistinguishable
+from the random functions with `ℓ(n)`-bit outputs, then for every non-uniform PPT `D` and
+polynomial `q` there is a negligible `ε` with, for every `n` and all masks
+`w, w' ∈ ({0,1}^{ℓ(n)})^{q(n)+1}`,
+`distAdv (encodeTupleOut ∘ prfEncRealOut (F n) w) (encodeTupleOut ∘ prfEncRealOut (F n) w')
+(D.distinguisherL n) ≤ ε n`, the seeds being a uniform key and `q(n) + 1` uniform points.
+
+**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
+`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).
+
+**Proof sketch.** As `prfScheme_multiMessageSecure`, without the scheme.
+1. At each `n` choose the pair of masks maximizing the advantage (`Finset.exists_max_image`).
+2. For the two maximizing mask vectors, build the next-query machines `B₀`, `B₁`
+   (`MultiMsg.exists_queryChainOut_nuppt`, budget `q + 1`); with `MultiMsg.prfAdv_congr_equiv`,
+   `eval_multiMsgAdvOut` and `encodeTupleOut_eq_flatten` their PRF advantages are those of
+   `multiMsgAdvOut w (D ∘ encodeTupleOut)`.
+3. `distAdv_comp` and `distAdv_prfEncRealOut_le` bound the advantage by
+   `prfAdv (F n) B₀ + prfAdv (F n) B₁ + 2 · C(q(n)+1, 2) / 2^n`.
+4. This is negligible: `OracleEnsemble.Indist.negligible_prfAdv` at the budget `q + 1` and
+   `MultiMsg.negligible_choose_div_two_pow`, with `Negligible.add` and `Negligible.const_mul`. -/
+theorem MultiMsg.exists_negligible_distAdv_prfEncRealOut {ℓ : PolyExpr}
+    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
+    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ))
+    (D : NUPPT) (q : PolyExpr) :
+    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (w w' : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
+      distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w z))
+        (fun z => encodeTupleOut (prfEncRealOut (F n) w' z)) (D.distinguisherL n) ≤ ε n := by
+  -- the worst mask pair at each parameter (hard-wired into the reductions)
+  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
+      (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
+      ∀ w : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
+          (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
+        distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w.1 z))
+            (fun z => encodeTupleOut (prfEncRealOut (F n) w.2 z)) (D.distinguisherL n) ≤
+          distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) p.1 z))
+            (fun z => encodeTupleOut (prfEncRealOut (F n) p.2 z)) (D.distinguisherL n) := by
+    intro n
+    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
+      (fun w : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
+          (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) =>
+        distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w.1 z))
+          (fun z => encodeTupleOut (prfEncRealOut (F n) w.2 z)) (D.distinguisherL n))
+      Finset.univ_nonempty
+    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
+  choose μ hμ using hmax
+  -- the next-query machines for the two hard-wired mask vectors
+  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChainOut_nuppt D q ℓ fun n => (μ n).1
+  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChainOut_nuppt D q ℓ fun n => (μ n).2
+  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) +
+      prfAdv (F n) (B₁.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) +
+      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n w w' => ?_⟩
+  · -- the asymptotic step: two PRF advantages and the collision term
+    simpa only [PolyExpr.eval_add, PolyExpr.eval_const] using
+      ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
+        (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
+        ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
+  · refine (hμ n (w, w')).trans ?_
+    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdvOut`
+    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool)
+        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
+        (∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) ρ c,
+          (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
+            decide (D.runAt n (List.ofFn fun j =>
+              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
+                [true])) →
+        prfAdv (F n) (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) =
+          prfAdv (F n) (multiMsgAdvOut v fun x c => D.distinguisherL n (encodeTupleOut x) c) := by
+      intro B v φ hφ
+      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g x => ?_
+      rw [hφ g x.1 x.2, eval_multiMsgAdvOut, NUPPT.distinguisherL_eq, encodeTupleOut_eq_flatten]
+    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
+    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
+    dsimp only
+    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁]
+    -- the concrete step: the six hybrids at width `ℓ(n)`
+    exact (distAdv_comp encodeTupleOut (prfEncRealOut (F n) (μ n).1)
+      (prfEncRealOut (F n) (μ n).2) (D.distinguisherL n)).symm.trans_le
+        (distAdv_prfEncRealOut_le (F n) (μ n).1 (μ n).2
+          (fun x c => D.distinguisherL n (encodeTupleOut x) c))
+
+end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean
index 11f31f81a..1875deaae 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean
@@ -22,6 +22,10 @@ distinguisher to the encoded vector of masked messages [PS10, Theorem 99.2, proo
 
 * `MultiMsg.histBlock` and `MultiMsg.maskBlock` give the encodings of a history entry and a mask.
 * `MultiMsg.preFun` and `MultiMsg.postFun` give the input and output processing for each move.
+* `MultiMsg.histBlockOut`, `maskBlockOut`, `maskOfOut`, `histBlockLenOut`, `postCountOut`,
+  `postOffsetOut`, `postQueryOut`, `postFunOut` and `adviceBoundOut`: the string layer at answer
+  width `ℓ(n)` (ruling B3); the `n`-bit versions are their cases `ℓ = var`
+  (`histBlock_eq_histBlockOut`, …).
 
 ## Main results
 
@@ -30,6 +34,9 @@ distinguisher to the encoded vector of masked messages [PS10, Theorem 99.2, proo
   processing by polynomial time.
 * `MultiMsg.exists_queryChain_nuppt` packages the reduction and proves its agreement with
   the tuple experiment after relabelling its coins.
+* `MultiMsg.exists_queryChainOut_nuppt` does so at `ℓ(n)`-bit answers and masks, and
+  `MultiMsg.exists_oneQuery_nuppt` is its one-query case; `exists_queryChain_nuppt` is the case
+  `ℓ = var`.
 
 ## References
 
@@ -45,24 +52,51 @@ open Complexity Turing Finset
 
 /-! ### Strings: chunked encodings, history blocks, mask blocks -/
 
+/-- **The history block at answer width `l`** (ruling B3): the self-delimited chunk
+`histBlockOut p = ⟨⟨⟦p.1⟧, ⟦p.2⟧⟩, []⟩` of one pair of an `n`-bit query and an `l`-bit answer. -/
+def histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) : List Bool :=
+  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []
+
+/-- `histBlockOut p = ⟨⟨⟦p.1⟧, ⟦p.2⟧⟩, []⟩`. -/
+theorem histBlockOut_eq {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
+    histBlockOut p = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) [] := rfl
+
+/-- A history block of an `n`-bit query and an `l`-bit answer has `4n + 2l + 6` bits:
+`|histBlockOut p| = 4n + 2l + 6`. -/
+theorem length_histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
+    (histBlockOut p).length = 4 * n + 2 * l + 6 := by
+  simp only [histBlockOut, length_pairEncode, List.length_ofFn, List.length_nil]
+  omega
+
+/-- The encoded history is the concatenation of its blocks, at any widths:
+`encodeHist h = h.flatMap histBlockOut`. -/
+theorem encodeHist_eq_flatMapOut {ℓ₁ ℓ₂ : ℕ} : ∀ h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)),
+    encodeHist h = h.flatMap histBlockOut
+  | [] => by rw [encodeHist_nil, List.flatMap_nil]
+  | p :: h => by
+    rw [encodeHist_cons, encodeHist_eq_flatMapOut h, List.flatMap_cons]
+    simp [histBlockOut, pairEncode_eq]
+
 /-- The block contributed to an encoded history by one (query, answer) pair of `n`-bit
 strings: the self-delimited chunk `⟨⟨x, y⟩, []⟩`. -/
 def histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
   pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []
 
+/-- The `n`-bit history block is the case `l = n` of `histBlockOut`:
+`histBlock p = histBlockOut p` (`rfl`). -/
+theorem histBlock_eq_histBlockOut {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
+    histBlock p = histBlockOut p := rfl
+
 /-- A history block of `n`-bit strings has length `6n + 6`. -/
 theorem length_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
     (histBlock p).length = 6 * n + 6 := by
-  simp only [histBlock, length_pairEncode, List.length_ofFn, List.length_nil]
+  rw [histBlock_eq_histBlockOut, length_histBlockOut]
   omega
 
 /-- The encoded history is the concatenation of its blocks. -/
 theorem encodeHist_eq_flatMap {n : ℕ} : ∀ h : List ((Fin n → Bool) × (Fin n → Bool)),
     encodeHist h = h.flatMap histBlock
-  | [] => by rw [encodeHist_nil, List.flatMap_nil]
-  | p :: h => by
-    rw [encodeHist_cons, encodeHist_eq_flatMap h, List.flatMap_cons]
-    simp [histBlock, pairEncode_eq]
+  | h => encodeHist_eq_flatMapOut h
 
 /-- The syntactic block length `6n + 6` of a history block. -/
 def histBlockLen : PolyExpr := .add (.mul (.const 6) .var) (.const 6)
@@ -72,6 +106,22 @@ theorem eval_histBlockLen (n : ℕ) : histBlockLen.eval n = 6 * n + 6 := by
   simp only [histBlockLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
     PolyExpr.eval_var]
 
+/-- The syntactic block length at answer width `ℓ`:
+`histBlockLenOut ℓ = 4 · var + 2 · ℓ + 6`. -/
+def histBlockLenOut (ℓ : PolyExpr) : PolyExpr :=
+  .add (.add (.mul (.const 4) .var) (.mul (.const 2) ℓ)) (.const 6)
+
+/-- `histBlockLenOut ℓ = 4 · var + 2 · ℓ + 6` (the defining equation). -/
+theorem histBlockLenOut_eq (ℓ : PolyExpr) :
+    histBlockLenOut ℓ = .add (.add (.mul (.const 4) .var) (.mul (.const 2) ℓ)) (.const 6) :=
+  rfl
+
+/-- `(histBlockLenOut ℓ).eval n = 4n + 2ℓ(n) + 6`. -/
+theorem eval_histBlockLenOut (ℓ : PolyExpr) (n : ℕ) :
+    (histBlockLenOut ℓ).eval n = 4 * n + 2 * ℓ.eval n + 6 := by
+  simp only [histBlockLenOut, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+    PolyExpr.eval_var]
+
 /-- The length of a concatenation of chunks of a common length `b`. -/
 theorem length_flatMap_of_length {α : Type*} (f : α → List Bool) (b : ℕ) :
     ∀ L : List α, (∀ x ∈ L, (f x).length = b) → (L.flatMap f).length = L.length * b
@@ -134,11 +184,36 @@ theorem flatMap_const_replicate {α : Type*} (n : ℕ) : ∀ L : List α,
     rw [List.flatMap_cons, flatMap_const_replicate n L, List.length_cons, Nat.succ_mul, add_comm,
       List.replicate_add]
 
+/-- The query component of a history block at answer width `l`:
+`pairFstD (pairFstD (histBlockOut p)) = ⟦p.1⟧`. -/
+theorem pairFstD_pairFstD_histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
+    pairFstD (pairFstD (histBlockOut p)) = List.ofFn p.1 := by
+  simp [histBlockOut]
+
 /-- The query component of a history block: `pairFstD (pairFstD (histBlock p))` is the query
 `p.1`. -/
 theorem pairFstD_pairFstD_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
     pairFstD (pairFstD (histBlock p)) = List.ofFn p.1 := by
-  simp [histBlock]
+  rw [histBlock_eq_histBlockOut, pairFstD_pairFstD_histBlockOut]
+
+/-- **The mask block at answer width `l`** for `n`-bit queries: zeros under the (doubled) query
+and the separators, `w` doubled under the (doubled) answer:
+`maskBlockOut n w = 0^{4n+4} ++ dbl ⟦w⟧ ++ [0, 0]`. -/
+def maskBlockOut {l : ℕ} (n : ℕ) (w : Fin l → Bool) : List Bool :=
+  List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]
+
+/-- `maskBlockOut n w = 0^{4n+4} ++ dbl ⟦w⟧ ++ [0, 0]`. -/
+theorem maskBlockOut_eq {l : ℕ} (n : ℕ) (w : Fin l → Bool) :
+    maskBlockOut n w = List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false] :=
+  rfl
+
+/-- A mask block at answer width `l` has the length of a history block:
+`|maskBlockOut n w| = 4n + 2l + 6`. -/
+theorem length_maskBlockOut {l : ℕ} (n : ℕ) (w : Fin l → Bool) :
+    (maskBlockOut n w).length = 4 * n + 2 * l + 6 := by
+  simp only [maskBlockOut, List.length_append, List.length_replicate, length_dbl, List.length_ofFn,
+    List.length_cons, List.length_nil]
+  omega
 
 /-- The mask block of the message `w`: zeros under the (doubled) query and the separators,
 `w` doubled under the (doubled) answer, so that `histBlock (x, y) ⊕ maskBlock w` is the
@@ -146,10 +221,14 @@ history block of `(x, w ⊕ y)`. -/
 def maskBlock {n : ℕ} (w : Fin n → Bool) : List Bool :=
   List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]
 
+/-- The `n`-bit mask block is the case `l = n` of `maskBlockOut`:
+`maskBlock w = maskBlockOut n w` (`rfl`). -/
+theorem maskBlock_eq_maskBlockOut {n : ℕ} (w : Fin n → Bool) : maskBlock w = maskBlockOut n w :=
+  rfl
+
 /-- A mask block has the length `6n + 6` of a history block. -/
 theorem length_maskBlock {n : ℕ} (w : Fin n → Bool) : (maskBlock w).length = 6 * n + 6 := by
-  simp only [maskBlock, List.length_append, List.length_replicate, length_dbl, List.length_ofFn,
-    List.length_cons, List.length_nil]
+  rw [maskBlock_eq_maskBlockOut, length_maskBlockOut]
   omega
 
 /-- Doubling distributes over concatenation. -/
@@ -174,36 +253,47 @@ theorem zipWith_xor_dbl : ∀ a b : List Bool,
   | x :: a, y :: b => by
     simp only [dbl_cons, List.zipWith_cons_cons, zipWith_xor_dbl a b]
 
-/-- **Masking a history block**: the exclusive-or of the history block of `(x, y)` with the
-mask block of `w` is the history block of `(x, w ⊕ y)` (strings `x, y, w` of the same length).
+/-- **Masking a history block at answer width `l`**: for an `n`-bit query `x` and `l`-bit
+strings `y`, `w`, `histBlockOut (x, y) ⊕ maskBlockOut n w = ⟨⟨⟦x⟧, ⟦w + y⟧⟩, []⟩`.
 
 **Proof sketch.** `⟨⟨x, y⟩, []⟩ = dbl (dbl x) ++ 0011 ++ dbl y ++ 01`; the mask is
-`0^{4n+4} ++ dbl w ++ 00`; `List.zipWith_append` splits the exclusive-or along these
-segments, zeros are neutral (`zipWith_xor_replicate_false`) and `dbl y ⊕ dbl w = dbl (y ⊕ w)`
+`0^{4n+4} ++ dbl w ++ 00`; `List.zipWith_append` splits the exclusive-or along these segments,
+zeros are neutral (`zipWith_xor_replicate_false`) and `dbl y ⊕ dbl w = dbl (y ⊕ w)`
 (`zipWith_xor_dbl`). -/
-theorem zipWith_xor_histBlock_maskBlock {n : ℕ} (x y w : Fin n → Bool) :
-    List.zipWith xor (histBlock (x, y)) (maskBlock w) =
+theorem zipWith_xor_histBlockOut_maskBlockOut {n l : ℕ} (x : Fin n → Bool) (y w : Fin l → Bool) :
+    List.zipWith xor (histBlockOut (x, y)) (maskBlockOut n w) =
       pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
   have hyw : List.zipWith xor (List.ofFn y) (List.ofFn w) = List.ofFn (w + y) := by
     rw [zipWith_xor_ofFn_add, add_comm]
-  have h1 : histBlock (x, y) =
+  have h1 : histBlockOut (x, y) =
       (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]) ++
         (dbl (List.ofFn y) ++ [false, true]) := by
-    simp only [histBlock, pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc,
+    simp only [histBlockOut, pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc,
       dbl_cons, List.cons_append, List.nil_append]
-  have h2 : maskBlock w =
+  have h2 : maskBlockOut n w =
       List.replicate (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]).length false ++
         (dbl (List.ofFn w) ++ [false, false]) := by
-    simp only [maskBlock, List.length_append, length_dbl, List.length_ofFn, List.length_cons,
+    simp only [maskBlockOut, List.length_append, length_dbl, List.length_ofFn, List.length_cons,
       List.length_nil, List.append_assoc]
     congr 2
     omega
   rw [h1, h2, List.zipWith_append (List.length_replicate ..).symm, zipWith_xor_replicate_false,
     List.zipWith_append (by simp only [length_dbl, List.length_ofFn]), zipWith_xor_dbl, hyw]
-  simp only [pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc, dbl_cons, dbl_nil,
+  simp only [pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc, dbl_cons,
     List.cons_append, List.nil_append]
   rfl
 
+/-- **Masking a history block**: the exclusive-or of the history block of `(x, y)` with the
+mask block of `w` is the history block of `(x, w ⊕ y)` (strings `x, y, w` of the same length).
+
+**Proof sketch.** The case `l = n` of `zipWith_xor_histBlockOut_maskBlockOut`
+(`histBlock_eq_histBlockOut`, `maskBlock_eq_maskBlockOut`). -/
+theorem zipWith_xor_histBlock_maskBlock {n : ℕ} (x y w : Fin n → Bool) :
+    List.zipWith xor (histBlock (x, y)) (maskBlock w) =
+      pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
+  rw [histBlock_eq_histBlockOut, maskBlock_eq_maskBlockOut]
+  exact zipWith_xor_histBlockOut_maskBlockOut x y w
+
 /-- The exclusive-or of two concatenations of `k` chunks of pairwise equal lengths is the
 concatenation of the chunkwise exclusive-ors. -/
 theorem zipWith_xor_flatten_ofFn : ∀ {k : ℕ} (F G : Fin k → List Bool),
@@ -289,23 +379,73 @@ def postQuery (z : List Bool) : List Bool :=
 def postVerdict (z : List Bool) : List Bool :=
   [true] ++ [decide (pairFstD (pairEncode (postAns z) [true]) = pairSndD (pairEncode (postAns z) [true]))]
 
-/-- **The post-processing of the next-query machine** on the raw layout
-`⟨⟨⟨1^n, ⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩⟩, []⟩, r⟩`: if the history already has `|u|` blocks, the
-verdict `[true, [a = [true]]]`; otherwise the query `⟨[false], ρ_k⟩` at the `k`-th point,
-`k` the number of history blocks. -/
-def postFun (z : List Bool) : List Bool :=
-  if decide ((postBudget z).length ≤ (postCount z).length) = true then postVerdict z
-  else postQuery z
+/-- The unary count `1^k` of the history blocks at answer width `ℓ(n)` (block length
+`histBlockLenOut ℓ`): `postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true])
+⟨inParam z, postHist z⟩`. -/
+def postCountOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
+  blockMapFun (histBlockLenOut ℓ) (fun _ => [true]) (pairEncode (NUPPT.inParam z) (postHist z))
 
-/-- `postFun` is polynomial-time.
+/-- `postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true]) ⟨inParam z, postHist z⟩`.
+-/
+theorem postCountOut_eq (ℓ : PolyExpr) (z : List Bool) :
+    postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true])
+      (pairEncode (NUPPT.inParam z) (postHist z)) :=
+  rfl
+
+/-- The unary offset `1^{k·n}` of the next point at answer width `ℓ(n)`: the block map emitting
+`1^{|x|}` for the query `x` of each block of length `histBlockLenOut ℓ`,
+`postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun blk => 1^{|fst (fst blk)|})
+⟨inParam z, postHist z⟩`. -/
+def postOffsetOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
+  blockMapFun (histBlockLenOut ℓ) (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
+    (pairEncode (NUPPT.inParam z) (postHist z))
+
+/-- `postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun blk => 1^{|fst (fst blk)|})
+⟨inParam z, postHist z⟩`. -/
+theorem postOffsetOut_eq (ℓ : PolyExpr) (z : List Bool) :
+    postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ)
+      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
+      (pairEncode (NUPPT.inParam z) (postHist z)) :=
+  rfl
 
-**Proof sketch.** Projections of the layout (`NUPPT.polyTimeComputable_inArg`,
-`polyTimeComputable_pairFstD`/`pairSndD`), two block maps
-(`Complexity.polyTimeComputable_blockMap`), the typed cuts
-(`polyTimeComputable_pairTakePoly`/`pairDropPoly`), a length test
-(`Complexity.StateLoop.lenLe_comp`), an equality test (`Complexity.polyTimeComputable_pairEq`)
-and one branch (`Complexity.polyTimeComputable_ite`). -/
-theorem polyTimeComputable_postFun : PolyTimeComputable postFun := by
+/-- The query move `⟨[false], ρ_k⟩` at answer width `ℓ(n)`: the `n`-bit block of the points
+after the first `k·n` (`postOffsetOut ℓ`), `postQueryOut ℓ z = ⟨[false], takePolyFun var
+⟨inParam z, dropPolyFun var ⟨postOffsetOut ℓ z, postPoints z⟩⟩⟩`. -/
+def postQueryOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
+  pairEncode [false] (takePolyFun .var
+    (pairEncode (NUPPT.inParam z)
+      (dropPolyFun .var (pairEncode (postOffsetOut ℓ z) (postPoints z)))))
+
+/-- `postQueryOut ℓ z = ⟨[false], takePolyFun var ⟨inParam z, dropPolyFun var ⟨postOffsetOut ℓ z,
+postPoints z⟩⟩⟩`. -/
+theorem postQueryOut_eq (ℓ : PolyExpr) (z : List Bool) :
+    postQueryOut ℓ z = pairEncode [false] (takePolyFun .var
+      (pairEncode (NUPPT.inParam z)
+        (dropPolyFun .var (pairEncode (postOffsetOut ℓ z) (postPoints z))))) :=
+  rfl
+
+/-- **The post-processing of the next-query machine at answer width `ℓ(n)`**: the verdict
+`[true, [a = [true]]]` once the history has `|u|` blocks (of length `histBlockLenOut ℓ`), the
+query `⟨[false], ρ_k⟩` before: `postFunOut ℓ z = if |postBudget z| ≤ |postCountOut ℓ z| then
+postVerdict z else postQueryOut ℓ z`. -/
+def postFunOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
+  if decide ((postBudget z).length ≤ (postCountOut ℓ z).length) = true then postVerdict z
+  else postQueryOut ℓ z
+
+/-- `postFunOut ℓ z = if |postBudget z| ≤ |postCountOut ℓ z| then postVerdict z
+else postQueryOut ℓ z`. -/
+theorem postFunOut_eq (ℓ : PolyExpr) (z : List Bool) :
+    postFunOut ℓ z =
+      if decide ((postBudget z).length ≤ (postCountOut ℓ z).length) = true then postVerdict z
+      else postQueryOut ℓ z :=
+  rfl
+
+/-- `postFunOut ℓ` is polynomial-time: `PolyTimeComputable (postFunOut ℓ)`.
+
+**Proof sketch.** As `polyTimeComputable_postFun`, with the block length `histBlockLenOut ℓ`:
+projections of the layout, two block maps (`polyTimeComputable_blockMapFun`), the typed cuts, a
+length test (`StateLoop.lenLe_comp`), an equality test and one branch. -/
+theorem polyTimeComputable_postFunOut (ℓ : PolyExpr) : PolyTimeComputable (postFunOut ℓ) := by
   have hArg := NUPPT.polyTimeComputable_inArg
   have hParam := NUPPT.polyTimeComputable_inParam
   have hHist : PolyTimeComputable postHist :=
@@ -318,15 +458,15 @@ theorem polyTimeComputable_postFun : PolyTimeComputable postFun := by
     polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
       (polyTimeComputable_pairFstD.comp hArg))
   have hAns : PolyTimeComputable postAns := polyTimeComputable_pairSndD.comp hArg
-  have hCount : PolyTimeComputable postCount :=
-    (polyTimeComputable_blockMapFun histBlockLen (polyTimeComputable_const [true])).comp
+  have hCount : PolyTimeComputable (postCountOut ℓ) :=
+    (polyTimeComputable_blockMapFun (histBlockLenOut ℓ) (polyTimeComputable_const [true])).comp
       (hParam.pairEncode hHist)
-  have hOffset : PolyTimeComputable postOffset :=
-    (polyTimeComputable_blockMapFun histBlockLen
+  have hOffset : PolyTimeComputable (postOffsetOut ℓ) :=
+    (polyTimeComputable_blockMapFun (histBlockLenOut ℓ)
       (polyTimeComputable_unary.comp
         (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD))).comp
       (hParam.pairEncode hHist)
-  have hQuery : PolyTimeComputable postQuery :=
+  have hQuery : PolyTimeComputable (postQueryOut ℓ) :=
     (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_pairTakePoly .var).comp
       (hParam.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
         (hOffset.pairEncode hPoints))))
@@ -335,10 +475,62 @@ theorem polyTimeComputable_postFun : PolyTimeComputable postFun := by
       (polyTimeComputable_pairEq.comp (hAns.pairEncode (polyTimeComputable_const [true])))
   exact polyTimeComputable_ite (StateLoop.lenLe_comp hCount hBudget) hVerdict hQuery
 
+/-- **The post-processing of the next-query machine** on the raw layout
+`⟨⟨⟨1^n, ⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩⟩, []⟩, r⟩`: if the history already has `|u|` blocks, the
+verdict `[true, [a = [true]]]`; otherwise the query `⟨[false], ρ_k⟩` at the `k`-th point,
+`k` the number of history blocks. -/
+def postFun (z : List Bool) : List Bool :=
+  if decide ((postBudget z).length ≤ (postCount z).length) = true then postVerdict z
+  else postQuery z
+
+/-- The `n`-bit block count is the case `ℓ = var` of `postCountOut`:
+`postCount z = postCountOut var z` (equal block lengths `6n + 6 = 4n + 2n + 6`). -/
+theorem postCount_eq_postCountOut (z : List Bool) : postCount z = postCountOut .var z := by
+  simp only [postCount, postCountOut, blockMapFun, eval_histBlockLen, eval_histBlockLenOut,
+    PolyExpr.eval_var, show ∀ m : ℕ, 4 * m + 2 * m + 6 = 6 * m + 6 from fun m => by omega]
+
+/-- The `n`-bit offset is the case `ℓ = var` of `postOffsetOut`:
+`postOffset z = postOffsetOut var z`. -/
+theorem postOffset_eq_postOffsetOut (z : List Bool) : postOffset z = postOffsetOut .var z := by
+  simp only [postOffset, postOffsetOut, blockMapFun, eval_histBlockLen, eval_histBlockLenOut,
+    PolyExpr.eval_var, show ∀ m : ℕ, 4 * m + 2 * m + 6 = 6 * m + 6 from fun m => by omega]
+
+/-- The `n`-bit query move is the case `ℓ = var` of `postQueryOut`:
+`postQuery z = postQueryOut var z`. -/
+theorem postQuery_eq_postQueryOut (z : List Bool) : postQuery z = postQueryOut .var z := by
+  rw [postQuery, postQueryOut, postOffset_eq_postOffsetOut]
+
+/-- The `n`-bit post-processor is the case `ℓ = var` of `postFunOut`:
+`postFun z = postFunOut var z`. -/
+theorem postFun_eq_postFunOut (z : List Bool) : postFun z = postFunOut .var z := by
+  rw [postFun, postFunOut, postCount_eq_postCountOut, postQuery_eq_postQueryOut]
+
+/-- `postFun` is polynomial-time.
+
+**Proof sketch.** The case `ℓ = var` of `polyTimeComputable_postFunOut`
+(`postFun_eq_postFunOut`). -/
+theorem polyTimeComputable_postFun : PolyTimeComputable postFun :=
+  (polyTimeComputable_postFunOut .var).congr fun z => (postFun_eq_postFunOut z).symm
+
+/-- **The mask of a message vector at answer width `l`** (for `n`-bit queries): the concatenation
+of the mask blocks of its entries,
+`maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten`. -/
+def maskOfOut {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) : List Bool :=
+  (List.ofFn fun j => maskBlockOut n (v j)).flatten
+
+/-- `maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten`. -/
+theorem maskOfOut_eq {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) :
+    maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten :=
+  rfl
+
 /-- The mask of a message vector: the concatenation of the mask blocks of its entries. -/
 def maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) : List Bool :=
   (List.ofFn fun j => maskBlock (v j)).flatten
 
+/-- The `n`-bit mask is the case `l = n` of `maskOfOut`: `maskOf v = maskOfOut n v` (`rfl`). -/
+theorem maskOf_eq_maskOfOut {n k : ℕ} (v : Fin k → Fin n → Bool) : maskOf v = maskOfOut n v :=
+  rfl
+
 /-- The length of a concatenation of strings of a common length `b`. -/
 theorem length_flatten_of_length (b : ℕ) : ∀ L : List (List Bool),
     (∀ x ∈ L, x.length = b) → L.flatten.length = L.length * b
@@ -349,19 +541,48 @@ theorem length_flatten_of_length (b : ℕ) : ∀ L : List (List Bool),
       List.length_cons]
     ring
 
+/-- The mask of `k` messages of `l` bits for `n`-bit queries has `k (4n + 2l + 6)` bits:
+`|maskOfOut n v| = k · (4n + 2l + 6)`. -/
+theorem length_maskOfOut {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) :
+    (maskOfOut n v).length = k * (4 * n + 2 * l + 6) := by
+  unfold maskOfOut
+  rw [length_flatten_of_length (4 * n + 2 * l + 6), List.length_ofFn]
+  intro x hx
+  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.1 hx
+  exact length_maskBlockOut _ _
+
 /-- The length of the mask of `k` messages of `n` bits is `k (6n + 6)`. -/
 theorem length_maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) :
     (maskOf v).length = k * (6 * n + 6) := by
-  unfold maskOf
-  rw [length_flatten_of_length (6 * n + 6), List.length_ofFn]
-  intro x hx
-  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.1 hx
-  exact length_maskBlock _
+  rw [maskOf_eq_maskOfOut, length_maskOfOut]
+  congr 1
+  omega
 
 /-- The advice bound of the next-query machine: `|⟨mask, 1^{q+1}⟩|`. -/
 def adviceBound (q : PolyExpr) : PolyExpr :=
   .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) histBlockLen)) (.const 2)) (.add q (.const 1))
 
+/-- The advice bound of the next-query machine at answer width `ℓ`: `|⟨mask, 1^{q+1}⟩|`,
+`adviceBoundOut q ℓ = 2 · ((q + 1) · histBlockLenOut ℓ) + 2 + (q + 1)`. -/
+def adviceBoundOut (q ℓ : PolyExpr) : PolyExpr :=
+  .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) (histBlockLenOut ℓ))) (.const 2))
+    (.add q (.const 1))
+
+/-- `adviceBoundOut q ℓ = 2 · ((q + 1) · histBlockLenOut ℓ) + 2 + (q + 1)` (the defining
+equation). -/
+theorem adviceBoundOut_eq (q ℓ : PolyExpr) :
+    adviceBoundOut q ℓ =
+      .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) (histBlockLenOut ℓ))) (.const 2))
+        (.add q (.const 1)) :=
+  rfl
+
+/-- `(adviceBoundOut q ℓ).eval n = 2 ((q(n) + 1)(4n + 2ℓ(n) + 6)) + 2 + (q(n) + 1)`. -/
+theorem eval_adviceBoundOut (q ℓ : PolyExpr) (n : ℕ) :
+    (adviceBoundOut q ℓ).eval n =
+      2 * ((q.eval n + 1) * (4 * n + 2 * ℓ.eval n + 6)) + 2 + (q.eval n + 1) := by
+  simp only [adviceBoundOut, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+    eval_histBlockLenOut]
+
 /-- Decoding the well-formed query move `⟨[false], x⟩`. -/
 theorem decodeOracleMove_query (ℓ : ℕ) (x : Fin ℓ → Bool) :
     decodeOracleMove ℓ (pairEncode [false] (List.ofFn x)) = .query x := by
@@ -371,40 +592,44 @@ theorem decodeOracleMove_query (ℓ : ℕ) (x : Fin ℓ → Bool) :
 theorem decodeOracleMove_ret (ℓ : ℕ) (b : Bool) : decodeOracleMove ℓ [true, b] = .ret b :=
   decodeOracleMove_true_two ℓ b
 
-/-- **The post-processor on the layout of the composite machine**: for a history of `k` pairs
-of `n`-bit strings, the points string `P`, a mask `M`, the budget string `u` and the
-distinguisher's output `a`, the move is the verdict `[true, [a = [true]]]` when `|u| ≤ k` and
-the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.
+/-- **The post-processor at answer width `ℓ(n)` on the layout of the composite machine**: for a
+history of `k` pairs of an `n`-bit query and an `ℓ(n)`-bit answer, the points string `P`, a mask
+`M`, the budget string `u` and the distinguisher's output `a`, the move is the verdict
+`[true, [a = [true]]]` when `|u| ≤ k` and the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.
 
 **Proof sketch.** The projections of the layout read the slots; the two block maps on
-`⟨1^n, encodeHist hist⟩` output `1^k` and `1^{k n}` (`encodeHist_eq_flatMap`,
-`flatMap_range_blocks` with blocks of length `6n + 6`, `flatMap_const_singleton`,
+`⟨1^n, encodeHist hist⟩` output `1^k` and `1^{k n}` (`encodeHist_eq_flatMapOut`,
+`flatMap_range_blocks` with blocks of length `4n + 2ℓ(n) + 6 > 0`, `flatMap_const_singleton`,
 `flatMap_const_replicate`); the typed cuts then select the block. -/
-theorem postFun_layout {n : ℕ} (hist : List ((Fin n → Bool) × (Fin n → Bool)))
-    (P M u a : List Bool) :
-    postFun (NUPPT.layout (List.replicate n true)
+theorem postFunOut_layout {n : ℕ} (ℓ : PolyExpr)
+    (hist : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool))) (P M u a : List Bool) :
+    postFunOut ℓ (NUPPT.layout (List.replicate n true)
         (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
       if u.length ≤ hist.length then [true, decide (a = [true])]
       else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
   set z := NUPPT.layout (List.replicate n true)
     (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] [] with hz
-  have harg : NUPPT.inArg z = pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a :=
+  have harg : NUPPT.inArg z =
+      pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a :=
     NUPPT.inArg_layout _ _ _ _
   have hpar : NUPPT.inParam z = List.replicate n true := NUPPT.inParam_layout _ _ _ _
-  have hblocks : ∀ x ∈ hist, (histBlock x).length = 6 * n + 6 := fun x _ => length_histBlock x
-  have hpos : 0 < 6 * n + 6 := by omega
-  have hcount : postCount z = List.replicate hist.length true := by
-    simp only [postCount, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
-      blockMapFun, List.length_replicate, eval_histBlockLen, encodeHist_eq_flatMap]
-    exact (flatMap_range_blocks histBlock (fun _ => [true]) hpos hist hblocks).trans
+  have hblocks : ∀ x ∈ hist, (histBlockOut x).length = 4 * n + 2 * ℓ.eval n + 6 :=
+    fun x _ => length_histBlockOut x
+  have hpos : 0 < 4 * n + 2 * ℓ.eval n + 6 := by omega
+  have hcount : postCountOut ℓ z = List.replicate hist.length true := by
+    simp only [postCountOut, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
+      blockMapFun, List.length_replicate, eval_histBlockLenOut, encodeHist_eq_flatMapOut]
+    exact (flatMap_range_blocks histBlockOut (fun _ => [true]) hpos hist hblocks).trans
       (flatMap_const_singleton hist)
-  have hoffset : postOffset z = List.replicate (hist.length * n) true := by
-    simp only [postOffset, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
-      blockMapFun, List.length_replicate, eval_histBlockLen, encodeHist_eq_flatMap]
-    refine (flatMap_range_blocks histBlock
-      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true) hpos hist hblocks).trans ?_
-    show hist.flatMap (fun x => List.replicate (pairFstD (pairFstD (histBlock x))).length true) = _
-    simp only [pairFstD_pairFstD_histBlock, List.length_ofFn]
+  have hoffset : postOffsetOut ℓ z = List.replicate (hist.length * n) true := by
+    simp only [postOffsetOut, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
+      blockMapFun, List.length_replicate, eval_histBlockLenOut, encodeHist_eq_flatMapOut]
+    refine (flatMap_range_blocks histBlockOut
+      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true) hpos hist
+        hblocks).trans ?_
+    show hist.flatMap
+      (fun x => List.replicate (pairFstD (pairFstD (histBlockOut x))).length true) = _
+    simp only [pairFstD_pairFstD_histBlockOut, List.length_ofFn]
     exact flatMap_const_replicate n hist
   have hbudget : postBudget z = u := by
     simp only [postBudget, harg, pairFstD_pairEncode, pairSndD_pairEncode]
@@ -412,14 +637,29 @@ theorem postFun_layout {n : ℕ} (hist : List ((Fin n → Bool) × (Fin n → Bo
     simp only [postAns, harg, pairSndD_pairEncode]
   have hpoints : postPoints z = P := by
     simp only [postPoints, harg, pairFstD_pairEncode, pairSndD_pairEncode]
-  simp only [postFun, hbudget, hcount, List.length_replicate]
+  simp only [postFunOut, hbudget, hcount, List.length_replicate]
   by_cases h : u.length ≤ hist.length
   · rw [if_pos (by simpa using h), if_pos h]
     simp only [postVerdict, hans, pairFstD_pairEncode, pairSndD_pairEncode]
     rfl
   · rw [if_neg (by simpa using h), if_neg h]
-    simp only [postQuery, takePolyFun, dropPolyFun, hoffset, hpoints, hpar, pairFstD_pairEncode,
-      pairSndD_pairEncode, List.length_replicate, PolyExpr.eval_var]
+    simp only [postQueryOut, takePolyFun, dropPolyFun, hoffset, hpoints, hpar,
+      pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, PolyExpr.eval_var]
+
+/-- **The post-processor on the layout of the composite machine**: for a history of `k` pairs
+of `n`-bit strings, the points string `P`, a mask `M`, the budget string `u` and the
+distinguisher's output `a`, the move is the verdict `[true, [a = [true]]]` when `|u| ≤ k` and
+the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.
+
+**Proof sketch.** The case `ℓ = var` of `postFunOut_layout` (`postFun_eq_postFunOut`). -/
+theorem postFun_layout {n : ℕ} (hist : List ((Fin n → Bool) × (Fin n → Bool)))
+    (P M u a : List Bool) :
+    postFun (NUPPT.layout (List.replicate n true)
+        (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
+      if u.length ≤ hist.length then [true, decide (a = [true])]
+      else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
+  rw [postFun_eq_postFunOut]
+  exact postFunOut_layout .var hist P M u a
 
 /-- Concatenating the chunks `f (F i)` of a tuple: `flatMap` over `ofFn`. -/
 theorem flatMap_ofFn {α : Type*} {k : ℕ} (F : Fin k → α) (f : α → List Bool) :
@@ -427,6 +667,23 @@ theorem flatMap_ofFn {α : Type*} {k : ℕ} (F : Fin k → α) (f : α → List
   rw [List.flatMap_def, List.map_ofFn]
   rfl
 
+/-- **Masking the canonical history at answer width `l`**: the pre-processor on the encoded
+history `((ρ_j, g ρ_j))_j` with the mask `maskOfOut n v` outputs the encoded tuple
+`(ρ_j, v_j ⊕ g(ρ_j))_j`: `preFun ⟨⟨encodeHist …, P⟩, ⟨maskOfOut n v, u⟩⟩ =
+(List.ofFn fun j => ⟨⟨⟦ρ j⟧, ⟦v j + g (ρ j)⟧⟩, []⟩).flatten` (`zipWith_xor_flatten_ofFn`,
+`zipWith_xor_histBlockOut_maskBlockOut`). -/
+theorem preFun_encodeHistOut {n l k : ℕ} (ρ : Fin k → Fin n → Bool) (v : Fin k → Fin l → Bool)
+    (g : (Fin n → Bool) → (Fin l → Bool)) (P u : List Bool) :
+    preFun (pairEncode (pairEncode (encodeHist (List.ofFn fun i => (ρ i, g (ρ i)))) P)
+        (pairEncode (maskOfOut n v) u)) =
+      (List.ofFn fun j =>
+        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
+  simp only [preFun, pairFstD_pairEncode, pairSndD_pairEncode, encodeHist_eq_flatMapOut,
+    maskOfOut, flatMap_ofFn]
+  rw [zipWith_xor_flatten_ofFn _ _ fun j => by rw [length_histBlockOut, length_maskBlockOut]]
+  exact congrArg List.flatten (congrArg List.ofFn (funext fun j =>
+    zipWith_xor_histBlockOut_maskBlockOut (ρ j) (g (ρ j)) (v j)))
+
 /-- **Masking the canonical history**: the pre-processor on the encoded history
 `((ρ_j, g ρ_j))_j` with the mask of `v` outputs the encoded ciphertext tuple
 `(ρ_j, v_j ⊕ g(ρ_j))_j` (`zipWith_xor_flatten_ofFn`, `zipWith_xor_histBlock_maskBlock`). -/
@@ -436,48 +693,45 @@ theorem preFun_encodeHist {n k : ℕ} (ρ v : Fin k → Fin n → Bool)
         (pairEncode (maskOf v) u)) =
       (List.ofFn fun j =>
         pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
-  simp only [preFun, pairFstD_pairEncode, pairSndD_pairEncode, encodeHist_eq_flatMap, maskOf,
-    flatMap_ofFn]
-  rw [zipWith_xor_flatten_ofFn _ _ fun j => by rw [length_histBlock, length_maskBlock]]
-  exact congrArg List.flatten (congrArg List.ofFn (funext fun j =>
-    zipWith_xor_histBlock_maskBlock (ρ j) (g (ρ j)) (v j)))
-
-/-- **The next-query machine of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
-by closure under efficient operations we contradict the pseudorandomness property"]): for a
-non-uniform PPT `D` (a distinguisher of encoded ciphertext tuples), a budget polynomial `q` and
-message vectors `v n ∈ ({0,1}^n)^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n`
-are, up to a bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, and whose
-query tree with budget `q(n) + 1`, evaluated against any oracle `g`, gives `D`'s verdict on the
-encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c` (an equality of outputs; the sequence of
-queries is not part of the statement).
-
-**Proof sketch.** `B` is `exists_split` (the first `(q(n)+1) n` coins are the points) of
-`exists_withAdvice` (advice `⟨maskOf (v n), 1^{q(n)+1}⟩`) of `exists_seq` of `D ∘ preFun`
-(`exists_comp`) and the uniform machine of `postFun`. On the encoded history `H` of `k`
-blocks the post-processor asks `ρ_k` while `k ≤ q(n)` and otherwise outputs `[true, b]` with
-`b` the verdict of `D` on `H ⊕ maskOf (v n)` (`postFun_layout`, `take_drop_ofFn_blocks`,
-`preFun_encodeHist`). The tree `buildTree` from the empty history is evaluated by induction on
-the remaining budget `j` along the canonical history `((ρ_i, g ρ_i))_{i < q(n)+1-j}`. -/
-theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
-    (v : ∀ n, Fin (q.eval n + 1) → Fin n → Bool) :
+  rw [maskOf_eq_maskOfOut]
+  exact preFun_encodeHistOut ρ v g P u
+
+/-- **The next-query machine of Thm-99.2.1 at answer width `ℓ(n)`** ([PS10, Theorem 99.2, proof,
+with `ℓ`-bit outputs]): for a non-uniform PPT `D`, a budget polynomial `q` and masks
+`v n ∈ ({0,1}^{ℓ(n)})^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n` are, up to a
+bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, such that for every oracle
+`g : {0,1}^n → {0,1}^{ℓ(n)}`,
+`(B.toOracleAdversary n n ℓ(n) (q(n) + 1) (φ (ρ, c))).eval g =
+decide (D.runAt n ⟦(⟨⟨ρ_j, v_j ⊕ g(ρ_j)⟩, []⟩)_j⟧ c = [true])`.
+
+**Proof sketch.** As `exists_queryChain_nuppt`, with the string layer at answer width `ℓ(n)`:
+`B` is `exists_split` (the first `(q(n)+1) n` coins are the points) of `exists_withAdvice` (advice
+`⟨maskOfOut n (v n), 1^{q(n)+1}⟩`, bound `adviceBoundOut q ℓ`) of `exists_seq` of `D ∘ preFun`
+and the uniform machine of `postFunOut ℓ`. On the encoded history of `k` blocks of
+`4n + 2ℓ(n) + 6` bits the post-processor asks `ρ_k` while `k ≤ q(n)`, and then outputs `D`'s
+verdict on the masked history (`postFunOut_layout`, `take_drop_ofFn_blocks`,
+`preFun_encodeHistOut`); `buildTree` is evaluated by induction on the remaining budget along the
+canonical history `((ρ_i, g ρ_i))_i`. -/
+theorem exists_queryChainOut_nuppt (D : NUPPT) (q ℓ : PolyExpr)
+    (v : ∀ n, Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) :
     ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
-      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (q.eval n + 1) → Fin n → Bool)
-        (c : D.Coins n),
-        (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
+      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool))
+        (ρ : Fin (q.eval n + 1) → Fin n → Bool) (c : D.Coins n),
+        (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
           decide (D.runAt n (List.ofFn fun j =>
             pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
               [true]) := by
   classical
-  have hβ : ∀ n, (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)).length ≤
-      (adviceBound q).eval n := by
+  have hβ : ∀ n, (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)).length ≤
+      (adviceBoundOut q ℓ).eval n := by
     intro n
-    simp only [length_pairEncode, length_maskOf, List.length_replicate, adviceBound,
-      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, eval_histBlockLen, le_refl]
+    rw [length_pairEncode, length_maskOfOut, List.length_replicate, eval_adviceBoundOut]
   obtain ⟨D₁, hD₁c, -, -, hD₁⟩ := D.exists_comp polyTimeComputable_preFun polyTimeComputable_id
   obtain ⟨C, hCc, -, hC⟩ :=
-    D₁.exists_seq (NUPPT.ofPolyTimeUniform polyTimeComputable_postFun (.const 0))
+    D₁.exists_seq (NUPPT.ofPolyTimeUniform (polyTimeComputable_postFunOut ℓ) (.const 0))
   obtain ⟨C₂, hC₂c, hC₂⟩ := C.exists_withAdvice
-    (fun n => pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)) (adviceBound q) hβ
+    (fun n => pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true))
+    (adviceBoundOut q ℓ) hβ
   obtain ⟨B, hBc, -, hB⟩ := C₂.exists_split (.mul (.add q (.const 1)) .var)
   refine ⟨B, fun n => ?_⟩
   have hlen : B.coinLen n = (q.eval n + 1) * n + D.coinLen n := by
@@ -497,13 +751,14 @@ theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
     exact (List.ofFn_congr hlen.symm _).symm
   -- the activation of `B` on an encoded history
   have hD₁len : D₁.coinLen n = D.coinLen n := by simp only [NUPPT.coinLen_eq, hD₁c]
-  have hrun : ∀ hist : List ((Fin n → Bool) × (Fin n → Bool)),
+  have hrun : ∀ hist : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)),
       B.runAt n (encodeHist hist) (φ (ρ, c)) =
-        postFun (NUPPT.layout (List.replicate n true)
+        postFunOut ℓ (NUPPT.layout (List.replicate n true)
           (pairEncode (pairEncode (pairEncode (encodeHist hist) Pstr)
-              (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)))
+              (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)))
             (D.runAt n (preFun (pairEncode (pairEncode (encodeHist hist) Pstr)
-              (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)))) c)) [] []) := by
+              (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)))) c))
+          [] []) := by
     intro hist
     have hp : (PolyExpr.mul (.add q (.const 1)) .var).eval n = (q.eval n + 1) * n := by
       simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_var]
@@ -517,7 +772,7 @@ theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
     simp only [NUPPT.layout_eq, NUPPT.advInput_eq, NUPPT.runAt_eq, id_eq]
   -- the canonical history along the points `ρ` against the oracle `g`
   let ρ' : ℕ → Fin n → Bool := fun i => if h : i < q.eval n + 1 then ρ ⟨i, h⟩ else fun _ => false
-  let hist : ℕ → List ((Fin n → Bool) × (Fin n → Bool)) :=
+  let hist : ℕ → List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)) :=
     fun k => List.ofFn fun i : Fin k => (ρ' i, g (ρ' i))
   have hρ' : ∀ (i : ℕ) (hi : i < q.eval n + 1), ρ' i = ρ ⟨i, hi⟩ := fun i hi => dif_pos hi
   have hist_len : ∀ k, (hist k).length = k := fun k => List.length_ofFn
@@ -526,25 +781,26 @@ theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
     simp only [hist]
     rw [List.ofFn_succ', List.concat_eq_append]
     simp only [Fin.coe_castSucc, Fin.val_last]
-  have hist_top : hist (q.eval n + 1) = List.ofFn fun i : Fin (q.eval n + 1) => (ρ i, g (ρ i)) := by
+  have hist_top :
+      hist (q.eval n + 1) = List.ofFn fun i : Fin (q.eval n + 1) => (ρ i, g (ρ i)) := by
     simp only [hist]
     congr 1
     funext i
     rw [hρ' i i.isLt]
   -- the next-query function of `B`
-  set next : List ((Fin n → Bool) × (Fin n → Bool)) → OracleMove n :=
+  set next : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)) → OracleMove n :=
     fun h => decodeOracleMove n (B.runAt n (encodeHist h) (φ (ρ, c))) with hnext
   have hquery : ∀ k (hk : k < q.eval n + 1), next (hist k) = .query (ρ ⟨k, hk⟩) := by
     intro k hk
     simp only [hnext]
-    rw [hrun, postFun_layout, hist_len, if_neg (by simp; omega), hPstr,
+    rw [hrun, postFunOut_layout, hist_len, if_neg (by simp; omega), hPstr,
       take_drop_ofFn_blocks _ k hk, Equiv.apply_symm_apply, decodeOracleMove_query]
   have hret : next (hist (q.eval n + 1)) =
       .ret (decide (D.runAt n (List.ofFn fun j =>
         pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
           [true])) := by
     simp only [hnext]
-    rw [hrun, postFun_layout, hist_len, if_pos (by simp), hist_top, preFun_encodeHist,
+    rw [hrun, postFunOut_layout, hist_len, if_pos (by simp), hist_top, preFun_encodeHistOut,
       decodeOracleMove_ret]
   -- evaluation of the tree by induction on the remaining budget
   have main : ∀ j, j ≤ q.eval n + 1 →
@@ -569,4 +825,68 @@ theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
   rw [NUPPT.toOracleAdversary_eq]
   exact this
 
+/-- **The one-query next-query machine at answer width `ℓ(n)`** ([PS10, Definition 96.2,
+clause (2), with `ℓ`-bit outputs]): for a non-uniform PPT `D` there is a non-uniform PPT `B`
+whose coins at `n` are, up to a bijection `φ`, a point `r ∈ {0,1}^n` and the coins `c` of `D`,
+such that for every oracle `g : {0,1}^n → {0,1}^{ℓ(n)}`, with the budget `1`,
+`(B.toOracleAdversary n n ℓ(n) 1 (φ (r, c))).eval g = decide (D.runAt n ⟨⟦r⟧, ⟦g r⟧⟩ c = [true])`.
+
+**Proof sketch.** `exists_queryChainOut_nuppt` with `q = 0`, the zero mask, and `D` precomposed
+with `pairFstD` (`NUPPT.exists_comp`): the encoded one-entry tuple is `⟨⟨⟦r⟧, ⟦g r⟧⟩, []⟩`, whose
+first component is `⟨⟦r⟧, ⟦g r⟧⟩`. The coins are `r` read as the one-point tuple
+(`Equiv.funUnique`, `finCongr`) and `D`'s coins carried to the composite (`NUPPT.coinsCongr`);
+the budget `(const 0)(n) + 1` is `1` (`PolyExpr.eval_const`). -/
+theorem exists_oneQuery_nuppt (D : NUPPT) (ℓ : PolyExpr) :
+    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
+      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) (r : Fin n → Bool) (c : D.Coins n),
+        (B.toOracleAdversary n n (ℓ.eval n) 1 (φ (r, c))).eval g =
+          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true]) := by
+  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ :=
+    D.exists_comp polyTimeComputable_pairFstD polyTimeComputable_id
+  obtain ⟨B, hB⟩ := exists_queryChainOut_nuppt D₁ (.const 0) ℓ fun _ _ => 0
+  refine ⟨B, fun n => ?_⟩
+  obtain ⟨φ, hφ⟩ := hB n
+  have h1 : 1 = (PolyExpr.const 0).eval n + 1 := by rw [PolyExpr.eval_const]
+  let e : (Fin n → Bool) ≃ (Fin ((PolyExpr.const 0).eval n + 1) → Fin n → Bool) :=
+    (Equiv.funUnique (Fin 1) (Fin n → Bool)).symm.trans
+      (Equiv.arrowCongr (finCongr h1) (Equiv.refl _))
+  have he : ∀ (r : Fin n → Bool) j, e r j = r := fun r j => rfl
+  refine ⟨(e.prodCongr (NUPPT.coinsCongr hD₁c.symm n)).trans φ, fun g r c => ?_⟩
+  -- the budget `1` is `(const 0)(n) + 1`
+  have hbud : ∀ (m : ℕ), m = (PolyExpr.const 0).eval n + 1 → ∀ x : B.Coins n,
+      (B.toOracleAdversary n n (ℓ.eval n) m x).eval g =
+        (B.toOracleAdversary n n (ℓ.eval n) ((PolyExpr.const 0).eval n + 1) x).eval g := by
+    rintro m rfl x
+    rfl
+  rw [hbud 1 h1, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, hφ]
+  congr 2
+  -- the one-entry tuple, read by `pairFstD`
+  rw [NUPPT.runAt_coinsCongr, hD₁, id_eq, ← NUPPT.runAt_eq]
+  congr 1
+  have hnil : ∀ (f : Fin ((PolyExpr.const 0).eval n) → List Bool), List.ofFn f = [] :=
+    fun f => List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
+  rw [List.ofFn_succ, hnil, List.flatten_cons, List.flatten_nil, List.append_nil,
+    pairFstD_pairEncode, he, zero_add]
+
+/-- **The next-query machine of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
+by closure under efficient operations we contradict the pseudorandomness property"]): for a
+non-uniform PPT `D` (a distinguisher of encoded ciphertext tuples), a budget polynomial `q` and
+message vectors `v n ∈ ({0,1}^n)^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n`
+are, up to a bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, and whose
+query tree with budget `q(n) + 1`, evaluated against any oracle `g`, gives `D`'s verdict on the
+encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c` (an equality of outputs; the sequence of
+queries is not part of the statement).
+
+**Proof sketch.** The case `ℓ = var` of `exists_queryChainOut_nuppt`. -/
+theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
+    (v : ∀ n, Fin (q.eval n + 1) → Fin n → Bool) :
+    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
+      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (q.eval n + 1) → Fin n → Bool)
+        (c : D.Coins n),
+        (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
+          decide (D.runAt n (List.ofFn fun j =>
+            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
+              [true]) :=
+  exists_queryChainOut_nuppt D q .var v
+
 end TCSlib.Cryptography.MultiMsg
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean b/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean
index 119db84b3..5a6bd3120 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean
@@ -45,6 +45,9 @@ also gives verdict `false` (foundation decision D7 of `PassShelatChapter2-4Plan.
   finite hybrid bound for oracle ensembles.
 * `TCSlib.Cryptography.prfAdv_toOracleAdversary` and `PRF.negligible_prfAdv`
   connect the PRF contract to the concrete advantage.
+* `TCSlib.Cryptography.prfAdv_toOracleAdversary_out` and
+  `OracleEnsemble.Indist.negligible_prfAdv` do so at `ℓ₂(n)`-bit outputs (ruling B3); the two
+  `n`-bit results are their cases `ℓ₂ = var`.
 
 ## References
 
@@ -424,6 +427,38 @@ structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → B
   /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF_n : F}` as oracle ensembles. -/
   pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)
 
+/-- **The PRF advantage at `ℓ₂(n)`-bit outputs** (the advantage of [PS10, Definition 96.2],
+clause (2), "with `ℓ`-bit outputs"): for a keyed family `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ₂(n)}`,
+the advantage of the next-query machine `D` with budget `q` between the keyed ensemble and the
+random functions with `ℓ₂(n)`-bit outputs is the concrete PRF advantage of [Gar26, Definition 3.9]:
+`distAdv ((keyed F).O n) ((random var ℓ₂).O n) (oracleDist D^{n,ℓ₂(n),q}) =
+prfAdv (F n) D^{n,ℓ₂(n),q}` (definitional: `prfAdv F A = distAdv F (randomFunction I O)
+(oracleDist A)`). -/
+theorem prfAdv_toOracleAdversary_out {ℓ₂ : PolyExpr}
+    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) (D : NUPPT) (n q : ℕ) :
+    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).O n)
+        ((OracleEnsemble.random .var ℓ₂).O n)
+        (oracleDist (D.toOracleAdversary n n (ℓ₂.eval n) q)) =
+      prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) q) := by
+  rw [prfAdv_def]
+  rfl
+
+/-- **Pseudorandomness at `ℓ₂(n)`-bit outputs, unfolded** ([PS10, Definition 96.2], clause (2),
+"with `ℓ`-bit outputs"): if the keyed ensemble of `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ₂(n)}` is
+oracle-indistinguishable from the random functions with `ℓ₂(n)`-bit outputs, then every
+next-query machine `D` with every polynomial budget `q` has negligible concrete PRF advantage:
+`Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n ℓ₂(n) q(n))`. This is the form in
+which a consumer of an `ℓ`-output PRF (such as `SecureComputation.PRFOut`, whose clause (2) is
+the hypothesis) reads it. -/
+theorem OracleEnsemble.Indist.negligible_prfAdv {ℓ₂ : PolyExpr}
+    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)}
+    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).Indist
+      (OracleEnsemble.random .var ℓ₂))
+    (D : NUPPT) (q : PolyExpr) :
+    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) (q.eval n)) :=
+  (congrArg Negligible (funext fun n => prfAdv_toOracleAdversary_out F D n (q.eval n))).mp
+    (hF D q)
+
 /-- The advantage of the next-query machine `D` with budget `q` between the keyed family `F`
 and the random functions is the concrete PRF advantage `prfAdv` of [Gar26, Definition 3.9]
 (definitional: `prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)`). -/
@@ -431,17 +466,15 @@ theorem prfAdv_toOracleAdversary (F : ∀ n, (Fin n → Bool) → (Fin n → Boo
     (D : NUPPT) (n q : ℕ) :
     distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).O n) ((OracleEnsemble.random .var .var).O n)
         (oracleDist (D.toOracleAdversary n n n q)) =
-      prfAdv (F n) (D.toOracleAdversary n n n q) := by
-  rw [prfAdv_def]
-  rfl
+      prfAdv (F n) (D.toOracleAdversary n n n q) :=
+  prfAdv_toOracleAdversary_out (ℓ₂ := .var) F D n q
 
 /-- **Pseudorandomness unfolded**: for a PRF `F`, every next-query machine `D` with every
 polynomial budget `q` has negligible concrete PRF advantage `prfAdv (F n) (D^{(q n)})` — the
 form in which the Garg-layer reductions consume [PS10, Definition 96.2]. -/
 theorem PRF.negligible_prfAdv {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
     (hF : PRF F) (D : NUPPT) (q : PolyExpr) :
-    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n n (q.eval n)) := by
-  exact (congrArg Negligible (funext fun n => prfAdv_toOracleAdversary F D n (q.eval n))).mp
-    (hF.pseudorandom D q)
+    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n n (q.eval n)) :=
+  hF.pseudorandom.negligible_prfAdv D q
 
 end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic oracle indistinguishability and pseudorandom functions

An oracle ensemble samples functions at each parameter. The next-query machine
sees the encoded history, uses one coin tape for the interaction, and runs within
an explicit query budget. The pseudorandom function contract combines an efficient
evaluator with indistinguishability from the random oracle [PS10, Definitions 96.1
and 96.2].

The concrete adversaries, random functions, and lazy runs come from [Gar26, §3.4].
The decoder treats malformed moves as rejection. A query after the budget is spent
also gives verdict `false` (foundation decision D7 of `PassShelatChapter2-4Plan.md`).

## Main definitions

* `TCSlib.Cryptography.OracleEnsemble` samples functions from finite seed types.
  `OracleEnsemble.random` uses the function table and `OracleEnsemble.keyed` uses a key.
* `TCSlib.Cryptography.OracleMove`, `decodeOracleMove`, and `encodeHist` specify the
  interface for a next-query machine. `buildTree` and `Complexity.NUPPT.toOracleAdversary`
  turn such a machine into a bounded query tree.
* `TCSlib.Cryptography.OracleEnsemble.Indist` gives the oracle indistinguishability
  condition. `TCSlib.Cryptography.PRF` packages that condition with efficient evaluation.

## Main results

* `TCSlib.Cryptography.acceptProb_random_eq_lazy` equates the two descriptions of a
  random function, by its table and by lazy sampling [PS10, §3.8.1].
* `Complexity.NUPPT.toOracleAdversary_boundedBy` gives the query bound.
* `TCSlib.Cryptography.OracleEnsemble.indist_iff` expresses the contract through
  negligible advantage. `TCSlib.Cryptography.oracle_hybrid_lemma` gives the
  finite hybrid bound for oracle ensembles.
* `TCSlib.Cryptography.prfAdv_toOracleAdversary` and `PRF.negligible_prfAdv`
  connect the PRF contract to the concrete advantage.
* `TCSlib.Cryptography.prfAdv_toOracleAdversary_out` and
  `OracleEnsemble.Indist.negligible_prfAdv` do so at `ℓ₂(n)`-bit outputs (ruling B3); the two
  `n`-bit results are their cases `ℓ₂ = var`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8.1 and §3.8.2, Definitions 96.1 and 96.2.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (Definitions 3.6–3.9).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Oracle ensembles and random functions [PS10, §3.8.1, Definition 96.1] -/

/-- An **oracle ensemble** [PS10, Definition 96.1]: for every parameter `n` a probability
distribution over functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, given (D6/D7) as the pushforward
of the uniform distribution on a finite seed type `σ n` along a sampler `O n`. For the
random-function ensemble the seed is the function table itself (exponentially long, which is
immaterial at the concrete level); for a keyed family the seed is the key.

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where
  /-- The seed type at parameter `n`. -/
  σ : ℕ → Type
  /-- The seed types are finite. -/
  [fintype : ∀ n, Fintype (σ n)]
  /-- The sampler: the oracle determined by a seed. -/
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)

attribute [instance] OracleEnsemble.fintype

/-- **The random function ensemble** `RF_n` [PS10, §3.8.1, combinatorial description]: the
uniform distribution on functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, sampled by its function
table (the "long array" of the text; `randomFunction I O = id`). The text's count
`2^{n 2^n}` of random functions is `Fintype.card_fun`. -/
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂ where
  σ n := (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
  O _ := randomFunction _ _

/-- **A keyed family as an oracle ensemble**: `{s ← U_n : f_s}` for a family
`F n : {0,1}^n → {0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}` (the first clause of the pseudorandomness
condition of [PS10, Definition 96.2]); the seed is the `n`-bit key. -/
def OracleEnsemble.keyed {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    OracleEnsemble ℓ₁ ℓ₂ where
  σ n := Fin n → Bool
  O n := F n

/-- Unfolding: the random-function ensemble samples by the identity on tables. -/
@[simp] theorem OracleEnsemble.random_O (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (R : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    (OracleEnsemble.random ℓ₁ ℓ₂).O n R = R :=
  randomFunction_apply _ _ R

/-- Unfolding: the keyed ensemble samples by `F n`. -/
@[simp] theorem OracleEnsemble.keyed_O {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) (n : ℕ)
    (s : Fin n → Bool) : (OracleEnsemble.keyed F).O n s = F n s := rfl

/-- Acceptance against the random oracle ensemble is acceptance against a uniform function
table, with the same oracle adversary and its coins. -/
theorem OracleEnsemble.acceptProb_random_eq {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (randomFunction (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) (oracleDist A) :=
  rfl

/-- **The two descriptions of a random function agree** [PS10, §3.8.1, "both of the above
descriptions of a random function give rise to identical distributions"] (Claim-95.b): for an
oracle adversary making at most `q` queries, the probability of accepting with the function
table `RF_n` as oracle equals the probability of accepting when every *new* query is answered
by a fresh uniform value and repeated queries by the recorded answer (the computational
description, `QueryTree.evalLazy` with `q` fresh values `extendStream W`).

**Proof sketch.** Both sides are averages over the adversary's coins `r` (Fubini,
`uprob_prod` after swapping the factors with `uprob_prod_comm`); for each fixed `r` the two
inner probabilities agree by the concrete lazy-sampling theorem `QueryTree.uprob_evalLazy`
applied to the tree `A r`. -/
theorem acceptProb_random_eq_lazy {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) {q : ℕ}
    (hA : A.BoundedBy q) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (fun W : Fin q → (Fin (ℓ₂.eval n) → Bool) => extendStream W) (lazyDist A) := by
  rw [acceptProb_def, acceptProb_def,
    uprob_prod_comm (fun R (r : ρ) => oracleDist A ((OracleEnsemble.random ℓ₁ ℓ₂).O n R) r = true),
    uprob_prod_comm (fun W (r : ρ) => lazyDist A (extendStream W) r = true),
    uprob_prod, uprob_prod]
  congr 1
  funext r
  simp only [OracleEnsemble.random_O, oracleDist_apply, lazyDist_apply]
  exact (QueryTree.uprob_evalLazy (· = true) ((OracleAdversary.boundedBy_iff A q).1 hA r)).symm

/-! ### Next-query machines as oracle adversaries (D7) -/

/-- A move of a next-query oracle machine: either the next query `x ∈ {0,1}^{ℓ₁}` or the
final verdict `b`. -/
inductive OracleMove (ℓ₁ : ℕ)
  /-- Ask the oracle at `x`. -/
  | query (x : Fin ℓ₁ → Bool)
  /-- Stop with the verdict `b`. -/
  | ret (b : Bool)

/-- Decoding of a machine output as a move: `⟨[false], x⟩` with `x` an `ℓ₁`-bit string is the
query `x`; the two-bit string `[true, b]` is the verdict `b`; any other output is the verdict
`false` (D7: ill-formed outputs count as rejection). -/
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁ :=
  match pairDecode w, w with
  | some ([false], x), _ => match decodeFin ℓ₁ x with
    | some x => .query x
    | none => .ret false
  | _, [true, b] => .ret b
  | _, _ => .ret false

/-- The two-bit word `[true, b]` is not a pair: its decoding would start with a doubled bit
(at least four bits) or with the separator `01`. -/
theorem pairDecode_true_two (b : Bool) : pairDecode [true, b] = none := by
  cases h : pairDecode [true, b] with
  | none => rfl
  | some p =>
    obtain ⟨u, v⟩ := p
    have hz := eq_pairEncode_of_pairDecode _ u v h
    rw [pairEncode_eq] at hz
    cases u with
    | nil => simp at hz
    | cons x u =>
      have hl := congrArg List.length hz
      simp only [List.length_cons, List.length_append, List.flatMap_cons, List.length_nil] at hl
      omega

/-- Decoding a pair `⟨[false], x⟩`: the query `x` when `x` has `ℓ₁` bits, else the verdict
`false`: `decodeOracleMove ℓ₁ (pairEncode [false] x) =
match decodeFin ℓ₁ x with | some y => .query y | none => .ret false`. -/
theorem decodeOracleMove_pairEncode_false (ℓ₁ : ℕ) (x : List Bool) :
    decodeOracleMove ℓ₁ (pairEncode [false] x) =
      match decodeFin ℓ₁ x with
      | some y => .query y
      | none => .ret false := by
  unfold decodeOracleMove
  rw [pairDecode_pairEncode, pairEncode_eq]
  rfl

/-- Decoding the two-bit word `[true, b]`: the verdict `b`,
`decodeOracleMove ℓ₁ [true, b] = .ret b`. -/
theorem decodeOracleMove_true_two (ℓ₁ : ℕ) (b : Bool) :
    decodeOracleMove ℓ₁ [true, b] = .ret b := by
  unfold decodeOracleMove
  rw [pairDecode_true_two]

/-- Decoding a well-formed query word: for every `ℓ₁`-bit string `x` (`ℓ₁ = 0` included),
`decodeOracleMove ℓ₁ (pairEncode [false] (List.ofFn x)) = .query x`. -/
theorem decodeOracleMove_pairEncode_ofFn (ℓ₁ : ℕ) (x : Fin ℓ₁ → Bool) :
    decodeOracleMove ℓ₁ (pairEncode [false] (List.ofFn x)) = .query x := by
  rw [decodeOracleMove_pairEncode_false, decodeFin_ofFn]

/-- Decoding a query-shaped word of the wrong length: if `|x| ≠ ℓ₁` then
`decodeOracleMove ℓ₁ (pairEncode [false] x) = .ret false`. -/
theorem decodeOracleMove_pairEncode_false_of_length_ne (ℓ₁ : ℕ) {x : List Bool}
    (hx : x.length ≠ ℓ₁) : decodeOracleMove ℓ₁ (pairEncode [false] x) = .ret false := by
  rw [decodeOracleMove_pairEncode_false]
  cases h : decodeFin ℓ₁ x with
  | none => rfl
  | some y => exact absurd (length_eq_of_decodeFin_eq_some h) hx

/-- **The malformed branch**: a word that is neither a query-shaped pair `⟨[false], x⟩` (for any
string `x`) nor a two-bit verdict word `[true, b]` decodes to the verdict `false`:
`decodeOracleMove ℓ₁ w = .ret false`. Together with `decodeOracleMove_pairEncode_ofFn`,
`decodeOracleMove_pairEncode_false_of_length_ne` and `decodeOracleMove_true_two` this covers every
word, for every `ℓ₁`.

**Proof sketch.** Along the match of `decodeOracleMove`: a decoding
`pairDecode w = some ([false], x)` gives `w = ⟨[false], x⟩` (`eq_pairEncode_of_pairDecode`),
excluded; the word `[true, b]` is excluded; the remaining branch is `.ret false`. -/
theorem decodeOracleMove_of_ne (ℓ₁ : ℕ) {w : List Bool} (hq : ∀ x, w ≠ pairEncode [false] x)
    (hv : ∀ b, w ≠ [true, b]) : decodeOracleMove ℓ₁ w = .ret false := by
  unfold decodeOracleMove
  split
  · rename_i w' o w'' x hx
    exact absurd (eq_pairEncode_of_pairDecode w' _ _ hx) (hq x)
  · rename_i o w' b hp
    exact absurd rfl (hv b)
  · rfl

/-- The encoding of the history of (query, answer) pairs handed to a next-query machine: the
nested pair `⟨⟨x₁, y₁⟩, ⟨⟨x₂, y₂⟩, ⟨…, []⟩⟩⟩`. -/
def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

/-- The empty history is encoded as the empty string: `encodeHist [] = []`. -/
theorem encodeHist_nil {ℓ₁ ℓ₂ : ℕ} :
    encodeHist ([] : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) = [] :=
  rfl

/-- A history is encoded pair by pair:
`encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h)`. -/
theorem encodeHist_cons {ℓ₁ ℓ₂ : ℕ} (p : (Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))
    (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
    encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) :=
  rfl

/-- The query tree of a next-query function `next` (the machine's move on a history) with the
query budget `q`, started from the history `hist`: a verdict stops; a query within budget
becomes a `query` node whose continuation appends the answer to the history; a query when the
budget is exhausted is the forced verdict `false` (D7). -/
def buildTree {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ℕ → List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, hist => match next hist with
    | .ret b => .ret b
    | .query _ => .ret false
  | q + 1, hist => match next hist with
    | .ret b => .ret b
    | .query x => .query x (fun o => buildTree next q (hist ++ [(x, o)]))

section BuildTree

variable {ℓ₁ ℓ₂ : ℕ} {next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁}
  {hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))}

/-- With the budget spent, a verdict stops the tree: `buildTree next 0 hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_zero_of_ret {b : Bool} (h : next hist = .ret b) :
    buildTree next 0 hist = .ret b := by
  rw [buildTree, h]

/-- With the budget spent, a query gives the forced verdict `false`:
`buildTree next 0 hist = ret false` when `next hist = query x`. -/
theorem buildTree_zero_of_query {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next 0 hist = .ret false := by
  rw [buildTree, h]

/-- Within budget, a verdict stops the tree: `buildTree next (q + 1) hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_succ_of_ret {q : ℕ} {b : Bool} (h : next hist = .ret b) :
    buildTree next (q + 1) hist = .ret b := by
  rw [buildTree, h]

/-- Within budget, a query becomes a query node whose continuation appends the answer:
`buildTree next (q + 1) hist = query x (fun o => buildTree next q (hist ++ [(x, o)]))` when
`next hist = query x`. -/
theorem buildTree_succ_of_query {q : ℕ} {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next (q + 1) hist = .query x (fun o => buildTree next q (hist ++ [(x, o)])) := by
  rw [buildTree, h]

end BuildTree

/-- The tree built with budget `q` makes at most `q` queries, from every starting history. -/
theorem buildTree_boundedBy {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      (buildTree next q hist).BoundedBy q
  | 0, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_zero_of_ret h]; exact QueryTree.boundedBy_ret b 0
    | query x => rw [buildTree_zero_of_query h]; exact QueryTree.boundedBy_ret false 0
  | q + 1, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_succ_of_ret h]; exact QueryTree.boundedBy_ret b (q + 1)
    | query x =>
      rw [buildTree_succ_of_query h]
      exact (QueryTree.boundedBy_query_succ x _ q).2
        fun o => buildTree_boundedBy next q (hist ++ [(x, o)])

/-- The query tree of the next-query machine `D` at parameter `n` with budget `q`
([PS10, Definition 96.1]; D7: no oracle tapes, one activation per query on the history). The
machine `D(1^n, ·)` is run, with one random tape `r` for the whole interaction, on the
encoded history; its output is decoded as a query or a verdict. -/
def _root_.Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []

/-- The tree of `D` on the coins `r` is built from the empty history, the next move being `D`'s
output on the encoded history, decoded:
`D.toOracleAdversary n ℓ₁ ℓ₂ q r =
buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []`. -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_eq (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ)
    (r : D.Coins n) :
    D.toOracleAdversary n ℓ₁ ℓ₂ q r =
      buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q [] :=
  rfl

/-- The oracle adversary of a next-query machine with budget `q` makes at most `q` queries on
every coin string (the hypothesis `BoundedBy` of `ggm_prfAdv_le` and `exists_ggmBits_dist`).
Induction on the budget (`buildTree_boundedBy`). -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q :=
  (OracleAdversary.boundedBy_iff _ q).2 fun r => by
    rw [NUPPT.toOracleAdversary_eq]
    exact buildTree_boundedBy _ q []

/-! ### Oracle indistinguishability [PS10, Definition 96.1] -/

/-- **Oracle indistinguishability** [PS10, Definition 96.1]: `{O_n} ≈ {O'_n}` iff for every
non-uniform PPT oracle machine `D` (a next-query `NUPPT`) and every polynomial query budget
`q`, the function `n ↦ |Pr[F ← O_n : D^F(1^n) = 1] − Pr[F ← O'_n : D^F(1^n) = 1]|` is
negligible, where `D^F(1^n)` is the run of the query tree `D.toOracleAdversary n ℓ₁(n) ℓ₂(n) q(n)`
against `F`. (The text writes `{O'_n} ≈ {O'_n}`, a typo.)

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
def OracleEnsemble.Indist {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
    distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))

/-- Oracle ensembles are indistinguishable iff the oracle advantage is negligible for
each next-query machine and polynomial query budget. -/
theorem OracleEnsemble.indist_iff {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) :
    O.Indist O' ↔ ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
      distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) :=
  Iff.rfl

/-- **Reflexivity of oracle indistinguishability** (non-vacuity of
[PS10, Definition 96.1]): every oracle ensemble is indistinguishable from itself, the
advantage being identically `0`. -/
theorem OracleEnsemble.Indist.refl {ℓ₁ ℓ₂ : PolyExpr} (O : OracleEnsemble ℓ₁ ℓ₂) : O.Indist O := by
  intro D q
  have h : (fun n => distAdv (O.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) = fun _ => 0 := by
    funext n
    simp [distAdv_def]
  rw [h]
  exact negligible_zero

/-- **Symmetry of oracle indistinguishability**: the advantage is symmetric in the two
ensembles (`abs_sub_comm`). -/
theorem OracleEnsemble.Indist.symm {ℓ₁ ℓ₂ : PolyExpr} {O O' : OracleEnsemble ℓ₁ ℓ₂}
    (h : O.Indist O') : O'.Indist O := by
  intro D q
  have e : (fun n => distAdv (O'.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) =
      fun n => distAdv (O.O n) (O'.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) := by
    funext n
    rw [distAdv_def, distAdv_def]
    exact abs_sub_comm _ _
  rw [e]
  exact h D q

/-- **Transitivity of oracle indistinguishability** (the two-step case of the hybrid lemma
for oracles, [PS10, §3.8.2, "oracle indistinguishability satisfies … the Hybrid Lemma"]): the
advantage between `O` and `O''` is at most the sum of the advantages between `O, O'` and
`O', O''` (triangle inequality `abs_sub_le`), and sums of negligible functions are negligible
(`Negligible.add`, `Negligible.mono`). -/
theorem OracleEnsemble.Indist.trans {ℓ₁ ℓ₂ : PolyExpr} {O O' O'' : OracleEnsemble ℓ₁ ℓ₂}
    (h₁ : O.Indist O') (h₂ : O'.Indist O'') : O.Indist O'' := by
  intro D q
  refine ((h₁ D q).add (h₂ D q)).mono ⟨0, fun n _ => ?_⟩
  simp only [distAdv_def, abs_abs]
  exact (abs_sub_le _ _ _).trans (le_abs_self _)

/-- **The hybrid lemma for oracles** [PS10, §3.8.2, "oracle indistinguishability satisfies …
the Hybrid Lemma"] (Claim-96.b), at one parameter: if the oracle adversary `A` distinguishes
the oracle distributions `H 0` and `H m` with advantage `ε`, then it distinguishes some
consecutive pair `H i, H (i+1)` (`i < m`) with advantage at least `ε / m`. Apply the
finite hybrid bound `exists_hybrid_gap` to the acceptance probabilities for `oracleDist A`. -/
theorem oracle_hybrid_lemma {σ : Type*} {I O : Type} {ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (H : ℕ → σ → (I → O)) (A : OracleAdversary ρ I O) :
    ∃ i < m, distAdv (H 0) (H m) (oracleDist A) / m ≤ distAdv (H i) (H (i + 1)) (oracleDist A) := by
  simpa only [distAdv_def] using exists_hybrid_gap (fun i => acceptProb (H i) (oracleDist A)) hm

/-! ### Pseudorandom functions [PS10, Definition 96.2] -/

/-- **Pseudorandom function family** [PS10, Definition 96.2]: a family
`{f_s : {0,1}^{|s|} → {0,1}^{|s|}}` given as `F n : {0,1}^n → {0,1}^n → {0,1}^n` (key, input,
output) is pseudorandom iff (1) *easy to compute*: a polynomial-time string function computes
`f_s(x)` from the pair `⟨s, x⟩`; (2) *pseudorandom*: the keyed oracle ensemble `{s ← U_n : f_s}`
is oracle-indistinguishable from the random functions `{F ← RF_n : F}`.

**Deviation:** clause (1) is a deterministic polynomial-time evaluator on `⟨s, x⟩` instead of
a PPT computing `f_s(x)` with probability one (equivalent by `Complexity.NUPPT.Computes` and
`ofPolyTimeUniform`, as for `FunFamily.Easy`); the key length is the parameter `n`
(`{0,1}^{|s|}` with `|s| = n`). -/
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where
  /-- Clause (1): `f_s(x)` is polynomial-time computable from `⟨s, x⟩`. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF_n : F}` as oracle ensembles. -/
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)

/-- **The PRF advantage at `ℓ₂(n)`-bit outputs** (the advantage of [PS10, Definition 96.2],
clause (2), "with `ℓ`-bit outputs"): for a keyed family `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ₂(n)}`,
the advantage of the next-query machine `D` with budget `q` between the keyed ensemble and the
random functions with `ℓ₂(n)`-bit outputs is the concrete PRF advantage of [Gar26, Definition 3.9]:
`distAdv ((keyed F).O n) ((random var ℓ₂).O n) (oracleDist D^{n,ℓ₂(n),q}) =
prfAdv (F n) D^{n,ℓ₂(n),q}` (definitional: `prfAdv F A = distAdv F (randomFunction I O)
(oracleDist A)`). -/
theorem prfAdv_toOracleAdversary_out {ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).O n)
        ((OracleEnsemble.random .var ℓ₂).O n)
        (oracleDist (D.toOracleAdversary n n (ℓ₂.eval n) q)) =
      prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) q) := by
  rw [prfAdv_def]
  rfl

/-- **Pseudorandomness at `ℓ₂(n)`-bit outputs, unfolded** ([PS10, Definition 96.2], clause (2),
"with `ℓ`-bit outputs"): if the keyed ensemble of `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ₂(n)}` is
oracle-indistinguishable from the random functions with `ℓ₂(n)`-bit outputs, then every
next-query machine `D` with every polynomial budget `q` has negligible concrete PRF advantage:
`Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n ℓ₂(n) q(n))`. This is the form in
which a consumer of an `ℓ`-output PRF (such as `SecureComputation.PRFOut`, whose clause (2) is
the hypothesis) reads it. -/
theorem OracleEnsemble.Indist.negligible_prfAdv {ℓ₂ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).Indist
      (OracleEnsemble.random .var ℓ₂))
    (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n (ℓ₂.eval n) (q.eval n)) :=
  (congrArg Negligible (funext fun n => prfAdv_toOracleAdversary_out F D n (q.eval n))).mp
    (hF D q)

/-- The advantage of the next-query machine `D` with budget `q` between the keyed family `F`
and the random functions is the concrete PRF advantage `prfAdv` of [Gar26, Definition 3.9]
(definitional: `prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)`). -/
theorem prfAdv_toOracleAdversary (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).O n) ((OracleEnsemble.random .var .var).O n)
        (oracleDist (D.toOracleAdversary n n n q)) =
      prfAdv (F n) (D.toOracleAdversary n n n q) :=
  prfAdv_toOracleAdversary_out (ℓ₂ := .var) F D n q

/-- **Pseudorandomness unfolded**: for a PRF `F`, every next-query machine `D` with every
polynomial budget `q` has negligible concrete PRF advantage `prfAdv (F n) (D^{(q n)})` — the
form in which the Garg-layer reductions consume [PS10, Definition 96.2]. -/
theorem PRF.negligible_prfAdv {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n n (q.eval n)) :=
  hF.pseudorandom.negligible_prfAdv D q

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/Hybrid.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.HardcoreBit.Basic
import Mathlib.Algebra.Ring.BooleanRing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The finite PRF encryption hybrid

The outer switches use PRF advantage. The inner switches replace random-function
answers at sampled points by independent pads, with a loss bounded by the probability
of repeated points. The two independent-pad experiments agree by perfect secrecy.

## Main definitions

* `chainTree` asks a fixed tuple of oracle queries.
* `prfEncReal` and `otpEnc` sample the ciphertext tuples in the real and independent-pad experiments.
* `multiMsgAdv` runs a tuple distinguisher after querying the oracle at the sampled points.
* `prfEncRealOut`, `otpEncOut` and `multiMsgAdvOut` are the same at output width `l` (ruling B3);
  the `n`-bit ones are their cases `l = n` (`prfEncReal_eq_prfEncRealOut`, …).

## Main results

* `prfAdv_multiMsgAdv` identifies the outer switch with a PRF advantage.
* `distAdv_prfEncReal_random_otp_le` bounds the inner switch by the collision probability.
* `acceptProb_otpEnc` equates the two independent-pad experiments.
* `distAdv_prfEncReal_le` combines the switches [PS10, Theorem 99.2, proof].
* `prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_random_otp_le`, `acceptProb_otpEncOut` and
  `distAdv_prfEncRealOut_le` are the same at output width `l`; the four results above are their
  cases `l = n`.

**Deviation.** The vector has `q + 1` points, giving collision term `C(q + 1, 2) / 2^n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Query chains -/

/-- The query tree that asks the fixed tuple of queries `xs : Fin k → I` in order and then
outputs `f` applied to the tuple of answers: `k` `query` nodes in a chain. -/
def chainTree {I O α : Type} : ∀ (k : ℕ), (Fin k → I) → ((Fin k → O) → α) → QueryTree I O α
  | 0, _, f => .ret (f Fin.elim0)
  | k + 1, xs, f => .query (xs 0) fun o => chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-- Running a query chain against the oracle `g` outputs `f` of the tuple of answers
`g (xs j)`. -/
theorem eval_chainTree {I O α : Type} (g : I → O) :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α),
      (chainTree k xs f).eval g = f fun j => g (xs j)
  | 0, xs, f => by
    simp only [chainTree, QueryTree.eval_ret]
    congr
    funext j
    exact j.elim0
  | k + 1, xs, f => by
    simp only [chainTree, QueryTree.eval_query]
    rw [eval_chainTree g k]
    congr
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.tail_def]

/-- A chain of `k` queries makes at most `k` queries. -/
theorem boundedBy_chainTree {I O α : Type} :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α), (chainTree k xs f).BoundedBy k
  | 0, _, _ => by
    rw [chainTree]
    exact QueryTree.boundedBy_ret _ _
  | k + 1, xs, f => by
    rw [chainTree, QueryTree.boundedBy_query_succ]
    exact fun o => boundedBy_chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-! ### The hybrids of [PS10, Theorem 99.2], concrete -/

section Concrete

variable {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ]

variable {l : ℕ}

/-! #### The hybrids at output width `l`

The concrete hybrids for a keyed family `F : K → {0,1}^n → {0,1}^l` with `l`-bit outputs (ruling
B3): the points stay `n`-bit strings, only the answers, messages and pads have `l` bits. The
`n`-bit hybrids below are their cases `l = n` (`prfEncReal_eq_prfEncRealOut`, …). -/

/-- **The real hybrid at output width `l`** ([PS10, Theorem 99.2, proof, `H¹` and `H²`, with
`ℓ`-bit outputs]): the ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the
points `z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^l` and messages
`m : Fin (q+1) → {0,1}^l`: `prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j))`. -/
def prfEncRealOut (F : K → (Fin n → Bool) → (Fin l → Bool)) (m : Fin (q + 1) → Fin l → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))

omit [Fintype K] in
/-- The real hybrid at width `l`, entrywise:
`prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j))`. -/
theorem prfEncRealOut_apply (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m : Fin (q + 1) → Fin l → Bool) (z : K × (Fin (q + 1) → Fin n → Bool)) (j : Fin (q + 1)) :
    prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j)) := rfl

/-- **The one-time-pad hybrid at output width `l`** ([PS10, Theorem 99.2, proof, `H³`, with
`ℓ`-bit outputs]): the tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with `n`-bit points `r_j` and independent
uniform `l`-bit pads `p_j`, on the seeds `z = (r, p)`: `otpEncOut m z j = (z.1 j, m j + z.2 j)`. -/
def otpEncOut (m : Fin (q + 1) → Fin l → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)

/-- The one-time-pad hybrid at width `l`, entrywise: `otpEncOut m z j = (z.1 j, m j + z.2 j)`. -/
theorem otpEncOut_apply (m : Fin (q + 1) → Fin l → Bool)
    (z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool)) (j : Fin (q + 1)) :
    otpEncOut m z j = (z.1 j, m j + z.2 j) := rfl

/-- **The oracle adversary of Thm-99.2.1 at output width `l`** ([PS10, Theorem 99.2, proof, with
`ℓ`-bit outputs]): on coins `c = (r, c')` it queries its `l`-bit-output oracle at `r₀, …, r_q`
(`chainTree`), forms `(r_j, m_j ⊕ ans_j)_j` and runs `D` on it with coins `c'`:
`multiMsgAdvOut m D c = chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2`. -/
def multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin l → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2

omit [Fintype ρ] in
/-- Evaluating the hybrid adversary at width `l` against the oracle `g` runs `D` on the masked
tuple: `(multiMsgAdvOut m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2`
[PS10, Theorem 99.2, proof]. -/
theorem eval_multiMsgAdvOut (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool)
    (g : (Fin n → Bool) → Fin l → Bool) (c : (Fin (q + 1) → Fin n → Bool) × ρ) :
    (multiMsgAdvOut m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2 := by
  rw [multiMsgAdvOut, eval_chainTree]

omit [Fintype ρ] in
/-- `multiMsgAdvOut m D` makes at most `q + 1` queries: `(multiMsgAdvOut m D).BoundedBy (q + 1)`. -/
theorem multiMsgAdvOut_boundedBy (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    (multiMsgAdvOut m D).BoundedBy (q + 1) :=
  (OracleAdversary.boundedBy_iff _ _).2 fun c => boundedBy_chainTree (q + 1) c.1 _

/-- Running `multiMsgAdvOut m D` with the oracle `F k` for a uniform key accepts with the
probability that `D` accepts the hybrid at width `l`:
`acceptProb F (oracleDist (multiMsgAdvOut m D)) = acceptProb (prfEncRealOut F m) D`
(reassociation of the seed space `K × (points × coins)`). -/
theorem acceptProb_oracleDist_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    acceptProb F (oracleDist (multiMsgAdvOut m D)) = acceptProb (prfEncRealOut F m) D := by
  rw [acceptProb_def, acceptProb_def]
  rw [← uprob_comp_equiv (Equiv.prodAssoc K (Fin (q + 1) → Fin n → Bool) ρ)]
  congr 1
  funext z
  simp only [oracleDist_apply, multiMsgAdvOut, eval_chainTree, Equiv.prodAssoc_apply]
  rfl

/-- **Thm-99.2.1 at output width `l`: the gap `H¹ → H²` is a PRF advantage** ([PS10,
Theorem 99.2, proof, with `ℓ`-bit outputs]):
`prfAdv F (multiMsgAdvOut m D) = distAdv (prfEncRealOut F m) (prfEncRealOut R m) D` with
`R = randomFunction {0,1}^n {0,1}^l` (unfolding of `prfAdv`, `oracleDist` and `acceptProb`). -/
theorem prfAdv_multiMsgAdvOut (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    prfAdv F (multiMsgAdvOut m D) =
      distAdv (prfEncRealOut F m)
        (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D := by
  rw [prfAdv_def, distAdv_def, distAdv_def, acceptProb_oracleDist_multiMsgAdvOut,
    acceptProb_oracleDist_multiMsgAdvOut]

/-- The ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the points
`z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^n`. With `F` the PRF this is the
hybrid `H¹` ("real encryptions"); with `F = randomFunction` (keys are function tables) it is
`H²` ("replace `f` with a truly random function `R`") of [PS10, Theorem 99.2, proof]. -/
def prfEncReal (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))

omit [Fintype K] in
/-- The real hybrid is the case `l = n` of the hybrid at width `l`:
`prfEncReal F m = prfEncRealOut F m` (`rfl`). -/
theorem prfEncReal_eq_prfEncRealOut (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool) : prfEncReal F m = prfEncRealOut F m := rfl

omit [Fintype K] in
/-- The hybrid ciphertext at position `j` contains the point `z.2 j` and the message
masked with the oracle's value at that point [PS10, Theorem 99.2, proof]. -/
theorem prfEncReal_apply (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool)
    (z : K × (Fin (q + 1) → Fin n → Bool)) (j : Fin (q + 1)) :
    prfEncReal F m z j = (z.2 j, m j + F z.1 (z.2 j)) := by
  rw [prfEncReal_eq_prfEncRealOut]
  exact prfEncRealOut_apply F m z j

/-- The ciphertext tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with independent uniform pads `p_j`: the
hybrid `H³` ("using OTP") of [PS10, Theorem 99.2, proof]; seeds `(r, p)`. -/
def otpEnc (m : Fin (q + 1) → Fin n → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)

/-- The one-time-pad hybrid is the case `l = n` of the hybrid at width `l`:
`otpEnc m = otpEncOut m` (`rfl`). -/
theorem otpEnc_eq_otpEncOut (m : Fin (q + 1) → Fin n → Bool) :
    otpEnc (n := n) m = otpEncOut m := rfl

/-- **The oracle adversary of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
otherwise (by closure under efficient operations) we contradict the pseudorandomness property"]):
on coins `(r, c)` it queries its oracle at `r₀, …, r_q` (a chain of `q + 1` queries), forms the
tuple `(r_j, m_j ⊕ ans_j)_j` and runs the distinguisher `D` on it with coins `c`. The messages
`m` are hard-wired (non-uniform advice in the machine version). -/
def multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin n → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2

omit [Fintype ρ] in
/-- The hybrid adversary is the case `l = n` of the adversary at width `l`:
`multiMsgAdv m D = multiMsgAdvOut m D` (`rfl`). -/
theorem multiMsgAdv_eq_multiMsgAdvOut (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    multiMsgAdv m D = multiMsgAdvOut m D := rfl

omit [Fintype ρ] in
/-- Evaluating the hybrid adversary on an oracle runs the tuple distinguisher on the sampled
points and the messages masked by the oracle values [PS10, Theorem 99.2, proof]. -/
theorem eval_multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool)
    (g : (Fin n → Bool) → Fin n → Bool) (c : (Fin (q + 1) → Fin n → Bool) × ρ) :
    (multiMsgAdv m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2 := by
  rw [multiMsgAdv_eq_multiMsgAdvOut]
  exact eval_multiMsgAdvOut m D g c

omit [Fintype ρ] in
/-- `multiMsgAdv m D` makes at most `q + 1` queries. -/
theorem multiMsgAdv_boundedBy (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    (multiMsgAdv m D).BoundedBy (q + 1) := by
  rw [multiMsgAdv_eq_multiMsgAdvOut]
  exact multiMsgAdvOut_boundedBy m D

/-- Running `multiMsgAdv m D` with the oracle `F k` (for a uniform key `k`) accepts with the
probability that `D` accepts the hybrid sampler `prfEncReal F m` (reassociation of the seed
space `K × (points × coins)`). -/
theorem acceptProb_oracleDist_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb F (oracleDist (multiMsgAdv m D)) = acceptProb (prfEncReal F m) D := by
  rw [multiMsgAdv_eq_multiMsgAdvOut, prfEncReal_eq_prfEncRealOut]
  exact acceptProb_oracleDist_multiMsgAdvOut F m D

/-- **Thm-99.2.1: the gap `H¹ → H²` is a PRF advantage.** The advantage of `D` between the real
encryptions `(r_j, m_j ⊕ F_k(r_j))_j` and the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` is exactly the PRF advantage of the `(q+1)`-query oracle adversary
`multiMsgAdv m D` against `F` (unfolding of `prfAdv`, `oracleDist` and `acceptProb`). -/
theorem prfAdv_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    prfAdv F (multiMsgAdv m D) =
      distAdv (prfEncReal F m) (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D := by
  simp only [multiMsgAdv_eq_multiMsgAdvOut, prfEncReal_eq_prfEncRealOut]
  exact prfAdv_multiMsgAdvOut F m D

/-- **The collision bound** ([PS10, Theorem 99.2, proof, "`∃ i, j` such that `r_i = r_j`, but this
happens only with probability `C(q,2) · 2^{−n}`"]): `q + 1` uniform `n`-bit points fail to be
pairwise distinct with probability at most `C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** `¬ Injective r ↔ ∃ (i, j) with i < j, r i = r j`; the union bound
`uprob_exists_le` over the `C(q+1, 2)` pairs `i < j` (`Finset.card_filter` of `univ.filter (i < j)`
on `Fin (q+1) × Fin (q+1)`, `Fin.card_filter_lt`/`Nat.choose_two_right`-style counting); for
`i ≠ j` the pair `(r i, r j)` is uniform on `({0,1}^n)²` (`HardcoreBit.pushesUniform_eval_pair`),
so `uprob (r i = r j) = uprob (fun (a, b) => a = b) = 2^n / 4^n = 1 / 2^n`
(`PushesUniform.uprob_eq`, `uprob_eq_card_filter`, `Fintype.card_fun`, `Fintype.card_bool`). -/
theorem uprob_not_injective_le :
    uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  set S : Finset (Fin (q + 1) × Fin (q + 1)) := univ.filter fun p => p.1 < p.2 with hS
  -- a collision is a pair `i < j` with `r i = r j`
  have h1 : uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      uprob (fun r : Fin (q + 1) → Fin n → Bool => ∃ p ∈ S, r p.1 = r p.2) := by
    refine uprob_mono fun r hr => ?_
    rw [Function.not_injective_iff] at hr
    obtain ⟨i, j, hij, hne⟩ := hr
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨(i, j), by simp [S, h], hij⟩
    · exact ⟨(j, i), by simp [S, h], hij.symm⟩
  -- each pair `i < j` collides with probability `2^{-n}`
  have h3 : ∀ p ∈ S, uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) = 1 / 2 ^ n := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa [S] using hp
    have h : uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) =
        uprob (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2) :=
      (HardcoreBit.pushesUniform_eval_pair (γ := Fin n → Bool) (ne_of_lt hlt)).uprob_eq
        (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2)
    rw [h, MultiMsg.uprob_eq_pair, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp
  -- the union bound over the `C(q+1, 2)` pairs
  have h2 := uprob_exists_le S (fun p (r : Fin (q + 1) → Fin n → Bool) => r p.1 = r p.2)
  rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, hS,
    MultiMsg.card_filter_lt_pairs, mul_one_div] at h2
  exact h1.trans h2

/-- **A uniform table read at distinct points is uniform**: for an injective tuple of points
`r : Fin (q+1) → I`, the map `R ↦ (R (r j))_j` pushes the uniform distribution on tables
`I → O` forward to the uniform distribution on `Fin (q+1) → O` (the generalization of
`HardcoreBit.pushesUniform_eval_pair` from two points to `q + 1` points).

**Proof sketch.** For an empty `O` both averages are over empty types. Otherwise this is the
restriction along the injective `r` (`HardcoreBit.pushesUniform_restrict`). -/
theorem pushesUniform_comp_injective {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    {r : Fin (q + 1) → I} (hr : Function.Injective r) :
    HardcoreBit.PushesUniform (fun R : I → O => fun j => R (r j)) := by
  classical
  rcases isEmpty_or_nonempty O with hO | hO
  · -- no tables and no tuples: both averages are over empty types
    refine (HardcoreBit.pushesUniform_iff _).2 fun F => ?_
    haveI : IsEmpty (I → O) := ⟨fun R => hO.false (R (r 0))⟩
    haveI : IsEmpty (Fin (q + 1) → O) := ⟨fun f => hO.false (f 0)⟩
    simp only [uexp_def, univ_eq_empty, sum_empty, zero_div]
  · exact HardcoreBit.pushesUniform_restrict hr

/-- **Thm-99.2.2 at output width `l`: the gap `H² → H³` is at most the collision probability**
([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
`∃ i, j` such that `r_i = r_j`", with `ℓ`-bit outputs]): with `R = randomFunction {0,1}^n {0,1}^l`,
`distAdv (prfEncRealOut R m) (otpEncOut m) D ≤ C(q+1, 2) / 2^n`. The bound concerns the `n`-bit
points only; it does not depend on `l`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Write both acceptance probabilities as averages over the points `r`
(`uprob_prod` after reassociating the seeds): `a(r) := Pr_R[D((r_j, m_j ⊕ R(r_j))_j) = 1]` and
`b(r) := Pr_p[D((r_j, m_j ⊕ p_j)_j) = 1]`. When `r` is injective, `(R(r_j))_j` is uniform on
`({0,1}^l)^{q+1}` (`pushesUniform_comp_injective`, `PushesUniform.uprob_eq`), so `a(r) = b(r)`;
otherwise `|a(r) − b(r)| ≤ 1`. Hence `|E_r a − E_r b| ≤ uprob (¬ Injective)`
(`MultiMsg.abs_uexp_sub_le_uprob`), and `uprob_not_injective_le` bounds it. -/
theorem distAdv_prfEncRealOut_random_otp_le (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) (otpEncOut m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  -- the acceptance probabilities conditioned on the points `r`
  let a : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : ((Fin n → Bool) → (Fin l → Bool)) × ρ =>
      D (fun j => (r j, m j + w.1 (r j))) w.2 = true
  let b : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : (Fin (q + 1) → Fin l → Bool) × ρ => D (fun j => (r j, m j + w.1 j)) w.2 = true
  have ha : acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D =
      uexp a := by
    rw [acceptProb_def, show randomFunction (Fin n → Bool) (Fin l → Bool) = id from
      funext fun f => randomFunction_apply _ _ f]
    exact (uprob_comp_equiv ((Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      ((Fin n → Bool) → (Fin l → Bool)) ρ).symm.trans
        ((Equiv.prodComm _ _).prodCongr (Equiv.refl ρ))) _).symm.trans
      (by rw [uprob_prod]; rfl)
  have hb : acceptProb (otpEncOut m) D = uexp b := by
    rw [acceptProb_def]
    exact (uprob_comp_equiv (Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      (Fin (q + 1) → Fin l → Bool) ρ).symm _).symm.trans (by rw [uprob_prod]; rfl)
  -- at injective points the table values are fresh uniform pads
  have hab : ∀ r : Fin (q + 1) → Fin n → Bool, Function.Injective r → a r = b r := by
    intro r hr
    exact ((pushesUniform_comp_injective (O := Fin l → Bool) hr).prodMap
      (HardcoreBit.pushesUniform_id (Ω := ρ))).uprob_eq
      (fun v : (Fin (q + 1) → Fin l → Bool) × ρ => D (fun j => (r j, m j + v.1 j)) v.2 = true)
  rw [distAdv_def, ha, hb]
  exact (MultiMsg.abs_uexp_sub_le_uprob a b (fun r => ¬ Function.Injective r)
    (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩)
    (fun r hr => hab r (not_not.mp hr))).trans uprob_not_injective_le

/-- **Thm-99.2.3 at output width `l`: `H³ = H⁴` by the perfect secrecy of the one-time pad**
([PS10, Theorem 99.2, proof, with `ℓ`-bit outputs]): for independent uniform `l`-bit pads,
`acceptProb (otpEncOut m) D = acceptProb (otpEncOut m') D` for all messages `m`, `m'`.

**Proof sketch.** The map `(r, p) ↦ (r, p ⊕ (m ⊕ m'))` is a bijection of the seed space
(`Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))`) carrying the sampler for `m'` to the
sampler for `m` (in the Boolean group `x + x = 0`); relabel by it (`acceptProb_comp_equiv`). -/
theorem acceptProb_otpEncOut (m m' : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    acceptProb (otpEncOut (n := n) m) D = acceptProb (otpEncOut m') D := by
  have key : ∀ z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin l → Bool),
      otpEncOut m' ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z) =
        otpEncOut m z := by
    intro z
    funext j
    simp only [otpEncOut, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight,
      Prod.map_fst, Prod.map_snd, id_eq, Pi.add_apply]
    refine Prod.ext rfl ?_
    funext i
    simp only [Pi.add_apply]
    cases m j i <;> cases m' j i <;> cases z.2 j i <;> rfl
  calc acceptProb (otpEncOut m) D
      = acceptProb (fun z => otpEncOut m'
          ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z)) D := by
        congr 1
        funext z
        exact (key z).symm
    _ = acceptProb (otpEncOut m') D := acceptProb_comp_equiv _ (otpEncOut m') D

/-- **[PS10, Theorem 99.2], concrete form, at output width `l`: the six-hybrid bound** (with
`ℓ`-bit outputs). For a keyed family `F : K → {0,1}^n → {0,1}^l`, message vectors
`m, m' ∈ ({0,1}^l)^{q+1}` and any distinguisher `D` of ciphertext tuples,
`distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤ prfAdv F (multiMsgAdvOut m D) +
prfAdv F (multiMsgAdvOut m' D) + 2 · C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Hybrids `H¹ = prfEncRealOut F m`, `H² = prfEncRealOut R m`, `H³ = otpEncOut m`,
`H⁴ = otpEncOut m'`, `H⁵ = prfEncRealOut R m'`, `H⁶ = prfEncRealOut F m'`: `|H¹ − H²|` and
`|H⁵ − H⁶|` are the two PRF advantages (`prfAdv_multiMsgAdvOut`), `|H² − H³|` and `|H⁴ − H⁵|`
are at most the collision bound (`distAdv_prfEncRealOut_random_otp_le`), `H³ = H⁴`
(`acceptProb_otpEncOut`); the triangle inequality (`abs_sub_le`, three times) finishes. -/
theorem distAdv_prfEncRealOut_le (F : K → (Fin n → Bool) → (Fin l → Bool))
    (m m' : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut F m) (prfEncRealOut F m') D ≤
      prfAdv F (multiMsgAdvOut m D) + prfAdv F (multiMsgAdvOut m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
  have h12 := prfAdv_multiMsgAdvOut F m D
  have h56 := prfAdv_multiMsgAdvOut F m' D
  have h23 := distAdv_prfEncRealOut_random_otp_le m D
  have h45 := distAdv_prfEncRealOut_random_otp_le m' D
  have h34 := acceptProb_otpEncOut m m' D
  simp only [distAdv_def] at h12 h56 h23 h45 ⊢
  rw [h12, h56, abs_sub_comm (acceptProb (prfEncRealOut F m') D)]
  rw [abs_sub_comm (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m')
    D)] at h45
  have t1 := abs_sub_le (acceptProb (prfEncRealOut F m) D)
    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D)
    (acceptProb (prfEncRealOut F m') D)
  have t2 := abs_sub_le
    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) D)
    (acceptProb (otpEncOut m) D) (acceptProb (prfEncRealOut F m') D)
  have t3 := abs_sub_le (acceptProb (otpEncOut m') D)
    (acceptProb (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m') D)
    (acceptProb (prfEncRealOut F m') D)
  rw [← h34] at t3 h45
  linarith

/-- **Thm-99.2.2: the gap `H² → H³` is at most the collision probability**
([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
`∃ i, j` such that `r_i = r_j`"]): the advantage of `D` between the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` and the one-time-pad encryptions `(r_j, m_j ⊕ p_j)_j` is at most
`C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** The case `l = n` of `distAdv_prfEncRealOut_random_otp_le`
(`prfEncReal_eq_prfEncRealOut`, `otpEnc_eq_otpEncOut`). -/
theorem distAdv_prfEncReal_random_otp_le (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) (otpEnc m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  rw [prfEncReal_eq_prfEncRealOut, otpEnc_eq_otpEncOut]
  exact distAdv_prfEncRealOut_random_otp_le m D

/-- **Thm-99.2.3: `H³ = H⁴` by the perfect secrecy of the one-time pad** ([PS10, Theorem 99.2,
proof, "`H³` and `H⁴` are identical by the perfect secrecy of the OTP"], the vector version of
Claim-92.a): for independent uniform pads `p_j`, the tuples `(r_j, m_j ⊕ p_j)_j` and
`(r_j, m'_j ⊕ p_j)_j` are identically distributed, so every distinguisher accepts them with the
same probability.

**Proof sketch.** The case `l = n` of `acceptProb_otpEncOut` (`otpEnc_eq_otpEncOut`). -/
theorem acceptProb_otpEnc (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb (otpEnc m) D = acceptProb (otpEnc m') D := by
  rw [otpEnc_eq_otpEncOut, otpEnc_eq_otpEncOut]
  exact acceptProb_otpEncOut m m' D

/-- **[PS10, Theorem 99.2], concrete form: the six-hybrid bound.** For a keyed family
`F : K → {0,1}^n → {0,1}^n`, message vectors `m, m' ∈ ({0,1}^n)^{q+1}` and any distinguisher
`D` of ciphertext tuples, the advantage of `D` between the real encryptions of `m` and of `m'`
is at most `prfAdv F (A_m D) + prfAdv F (A_{m'} D) + 2 · C(q+1, 2) / 2^n`, where `A_m D` is the
`(q+1)`-query oracle adversary `multiMsgAdv m D`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** The case `l = n` of `distAdv_prfEncRealOut_le` (`prfEncReal_eq_prfEncRealOut`,
`multiMsgAdv_eq_multiMsgAdvOut`). -/
theorem distAdv_prfEncReal_le (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal F m) (prfEncReal F m') D ≤
      prfAdv F (multiMsgAdv m D) + prfAdv F (multiMsgAdv m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
  simp only [prfEncReal_eq_prfEncRealOut, multiMsgAdv_eq_multiMsgAdvOut]
  exact distAdv_prfEncRealOut_le F m m' D

end Concrete

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The next-query machine for PRF encryption

The machine uses its coins for the query points and the distinguisher's coins.
Its advice carries the message vector. After receiving all answers, it applies the
distinguisher to the encoded vector of masked messages [PS10, Theorem 99.2, proof].

## Main definitions

* `MultiMsg.histBlock` and `MultiMsg.maskBlock` give the encodings of a history entry and a mask.
* `MultiMsg.preFun` and `MultiMsg.postFun` give the input and output processing for each move.
* `MultiMsg.histBlockOut`, `maskBlockOut`, `maskOfOut`, `histBlockLenOut`, `postCountOut`,
  `postOffsetOut`, `postQueryOut`, `postFunOut` and `adviceBoundOut`: the string layer at answer
  width `ℓ(n)` (ruling B3); the `n`-bit versions are their cases `ℓ = var`
  (`histBlock_eq_histBlockOut`, …).

## Main results

* `MultiMsg.zipWith_xor_histBlock_maskBlock` relates a masked history block to a ciphertext.
* `MultiMsg.polyTimeComputable_preFun` and `MultiMsg.polyTimeComputable_postFun` bound the
  processing by polynomial time.
* `MultiMsg.exists_queryChain_nuppt` packages the reduction and proves its agreement with
  the tuple experiment after relabelling its coins.
* `MultiMsg.exists_queryChainOut_nuppt` does so at `ℓ(n)`-bit answers and masks, and
  `MultiMsg.exists_oneQuery_nuppt` is its one-query case; `exists_queryChain_nuppt` is the case
  `ℓ = var`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography.MultiMsg

open Complexity Turing Finset

/-! ### Strings: chunked encodings, history blocks, mask blocks -/

/-- **The history block at answer width `l`** (ruling B3): the self-delimited chunk
`histBlockOut p = ⟨⟨⟦p.1⟧, ⟦p.2⟧⟩, []⟩` of one pair of an `n`-bit query and an `l`-bit answer. -/
def histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- `histBlockOut p = ⟨⟨⟦p.1⟧, ⟦p.2⟧⟩, []⟩`. -/
theorem histBlockOut_eq {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
    histBlockOut p = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) [] := rfl

/-- A history block of an `n`-bit query and an `l`-bit answer has `4n + 2l + 6` bits:
`|histBlockOut p| = 4n + 2l + 6`. -/
theorem length_histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
    (histBlockOut p).length = 4 * n + 2 * l + 6 := by
  simp only [histBlockOut, length_pairEncode, List.length_ofFn, List.length_nil]
  omega

/-- The encoded history is the concatenation of its blocks, at any widths:
`encodeHist h = h.flatMap histBlockOut`. -/
theorem encodeHist_eq_flatMapOut {ℓ₁ ℓ₂ : ℕ} : ∀ h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)),
    encodeHist h = h.flatMap histBlockOut
  | [] => by rw [encodeHist_nil, List.flatMap_nil]
  | p :: h => by
    rw [encodeHist_cons, encodeHist_eq_flatMapOut h, List.flatMap_cons]
    simp [histBlockOut, pairEncode_eq]

/-- The block contributed to an encoded history by one (query, answer) pair of `n`-bit
strings: the self-delimited chunk `⟨⟨x, y⟩, []⟩`. -/
def histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- The `n`-bit history block is the case `l = n` of `histBlockOut`:
`histBlock p = histBlockOut p` (`rfl`). -/
theorem histBlock_eq_histBlockOut {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    histBlock p = histBlockOut p := rfl

/-- A history block of `n`-bit strings has length `6n + 6`. -/
theorem length_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    (histBlock p).length = 6 * n + 6 := by
  rw [histBlock_eq_histBlockOut, length_histBlockOut]
  omega

/-- The encoded history is the concatenation of its blocks. -/
theorem encodeHist_eq_flatMap {n : ℕ} : ∀ h : List ((Fin n → Bool) × (Fin n → Bool)),
    encodeHist h = h.flatMap histBlock
  | h => encodeHist_eq_flatMapOut h

/-- The syntactic block length `6n + 6` of a history block. -/
def histBlockLen : PolyExpr := .add (.mul (.const 6) .var) (.const 6)

/-- Evaluating the block length. -/
theorem eval_histBlockLen (n : ℕ) : histBlockLen.eval n = 6 * n + 6 := by
  simp only [histBlockLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The syntactic block length at answer width `ℓ`:
`histBlockLenOut ℓ = 4 · var + 2 · ℓ + 6`. -/
def histBlockLenOut (ℓ : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 4) .var) (.mul (.const 2) ℓ)) (.const 6)

/-- `histBlockLenOut ℓ = 4 · var + 2 · ℓ + 6` (the defining equation). -/
theorem histBlockLenOut_eq (ℓ : PolyExpr) :
    histBlockLenOut ℓ = .add (.add (.mul (.const 4) .var) (.mul (.const 2) ℓ)) (.const 6) :=
  rfl

/-- `(histBlockLenOut ℓ).eval n = 4n + 2ℓ(n) + 6`. -/
theorem eval_histBlockLenOut (ℓ : PolyExpr) (n : ℕ) :
    (histBlockLenOut ℓ).eval n = 4 * n + 2 * ℓ.eval n + 6 := by
  simp only [histBlockLenOut, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The length of a concatenation of chunks of a common length `b`. -/
theorem length_flatMap_of_length {α : Type*} (f : α → List Bool) (b : ℕ) :
    ∀ L : List α, (∀ x ∈ L, (f x).length = b) → (L.flatMap f).length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatMap_cons, List.length_append,
      length_flatMap_of_length f b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- **The block map on a concatenation of equal-length chunks**: reading the string
`f x₀ ++ ⋯ ++ f x_{k−1}` (chunks of length `b > 0`) in blocks of length `b` and applying `g` to
each block gives `g (f x₀) ++ ⋯ ++ g (f x_{k−1})` (the function of
`Complexity.polyTimeComputable_blockMap`).

**Proof sketch.** Induction on the list: the string has `k + 1` blocks
(`length_flatMap_of_length`), `List.range_succ_eq_map` splits off block `0`, which is `f x`
(`List.take_left'`), and block `i + 1` of `f x ++ rest` is block `i` of `rest`
(`List.drop_append`). -/
theorem flatMap_range_blocks {α : Type*} (f : α → List Bool) (g : List Bool → List Bool) {b : ℕ}
    (hb : 0 < b) : ∀ L : List α, (∀ x ∈ L, (f x).length = b) →
      (List.range ((L.flatMap f).length / b)).flatMap
          (fun i => g (((L.flatMap f).drop (i * b)).take b)) =
        L.flatMap fun x => g (f x)
  | [], _ => by simp
  | x :: L, h => by
    have hx : (f x).length = b := h x (by simp)
    have hL : ∀ y ∈ L, (f y).length = b := fun y hy => h y (by simp [hy])
    have hlen : ((x :: L).flatMap f).length = (L.length + 1) * b := by
      rw [length_flatMap_of_length f b _ h, List.length_cons]
    rw [hlen, Nat.mul_div_cancel _ hb, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.flatMap_cons]
    congr 1
    · show g (((f x ++ L.flatMap f).drop (0 * b)).take b) = g (f x)
      rw [Nat.zero_mul, List.drop_zero, List.take_left' hx]
    · show (List.range L.length).flatMap
          (fun i => g (((f x ++ L.flatMap f).drop (i.succ * b)).take b)) = L.flatMap fun y => g (f y)
      rw [← flatMap_range_blocks f g hb L hL, length_flatMap_of_length f b L hL,
        Nat.mul_div_cancel _ hb]
      congr 1
      funext i
      rw [List.drop_append,
        List.drop_of_length_le (by rw [hx]; exact Nat.le_mul_of_pos_left b (Nat.succ_pos i)),
        List.nil_append, show i.succ * b - (f x).length = i * b by
          rw [hx, Nat.succ_mul, Nat.add_sub_cancel]]

/-- A constant block map outputs the unary count of the blocks. -/
theorem flatMap_const_singleton {α : Type*} : ∀ L : List α,
    (L.flatMap fun _ => [true]) = List.replicate L.length true
  | [] => rfl
  | _ :: L => by
    rw [List.flatMap_cons, flatMap_const_singleton L, List.length_cons, List.replicate_succ]
    rfl

/-- A block map outputting `1^n` per block outputs `1^{k·n}` on `k` blocks. -/
theorem flatMap_const_replicate {α : Type*} (n : ℕ) : ∀ L : List α,
    (L.flatMap fun _ => List.replicate n true) = List.replicate (L.length * n) true
  | [] => by simp
  | _ :: L => by
    rw [List.flatMap_cons, flatMap_const_replicate n L, List.length_cons, Nat.succ_mul, add_comm,
      List.replicate_add]

/-- The query component of a history block at answer width `l`:
`pairFstD (pairFstD (histBlockOut p)) = ⟦p.1⟧`. -/
theorem pairFstD_pairFstD_histBlockOut {n l : ℕ} (p : (Fin n → Bool) × (Fin l → Bool)) :
    pairFstD (pairFstD (histBlockOut p)) = List.ofFn p.1 := by
  simp [histBlockOut]

/-- The query component of a history block: `pairFstD (pairFstD (histBlock p))` is the query
`p.1`. -/
theorem pairFstD_pairFstD_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    pairFstD (pairFstD (histBlock p)) = List.ofFn p.1 := by
  rw [histBlock_eq_histBlockOut, pairFstD_pairFstD_histBlockOut]

/-- **The mask block at answer width `l`** for `n`-bit queries: zeros under the (doubled) query
and the separators, `w` doubled under the (doubled) answer:
`maskBlockOut n w = 0^{4n+4} ++ dbl ⟦w⟧ ++ [0, 0]`. -/
def maskBlockOut {l : ℕ} (n : ℕ) (w : Fin l → Bool) : List Bool :=
  List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]

/-- `maskBlockOut n w = 0^{4n+4} ++ dbl ⟦w⟧ ++ [0, 0]`. -/
theorem maskBlockOut_eq {l : ℕ} (n : ℕ) (w : Fin l → Bool) :
    maskBlockOut n w = List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false] :=
  rfl

/-- A mask block at answer width `l` has the length of a history block:
`|maskBlockOut n w| = 4n + 2l + 6`. -/
theorem length_maskBlockOut {l : ℕ} (n : ℕ) (w : Fin l → Bool) :
    (maskBlockOut n w).length = 4 * n + 2 * l + 6 := by
  simp only [maskBlockOut, List.length_append, List.length_replicate, length_dbl, List.length_ofFn,
    List.length_cons, List.length_nil]
  omega

/-- The mask block of the message `w`: zeros under the (doubled) query and the separators,
`w` doubled under the (doubled) answer, so that `histBlock (x, y) ⊕ maskBlock w` is the
history block of `(x, w ⊕ y)`. -/
def maskBlock {n : ℕ} (w : Fin n → Bool) : List Bool :=
  List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]

/-- The `n`-bit mask block is the case `l = n` of `maskBlockOut`:
`maskBlock w = maskBlockOut n w` (`rfl`). -/
theorem maskBlock_eq_maskBlockOut {n : ℕ} (w : Fin n → Bool) : maskBlock w = maskBlockOut n w :=
  rfl

/-- A mask block has the length `6n + 6` of a history block. -/
theorem length_maskBlock {n : ℕ} (w : Fin n → Bool) : (maskBlock w).length = 6 * n + 6 := by
  rw [maskBlock_eq_maskBlockOut, length_maskBlockOut]
  omega

/-- Doubling distributes over concatenation. -/
theorem dbl_append (a b : List Bool) : dbl (a ++ b) = dbl a ++ dbl b := by
  induction a with
  | nil => rw [List.nil_append, dbl_nil, List.nil_append]
  | cons x a ih => rw [List.cons_append, dbl_cons, dbl_cons, ih, List.cons_append, List.cons_append]

/-- Masking with zeros is the identity. -/
theorem zipWith_xor_replicate_false : ∀ l : List Bool,
    List.zipWith xor l (List.replicate l.length false) = l
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, zipWith_xor_replicate_false l,
      Bool.xor_false]

/-- Exclusive-or commutes with doubling. -/
theorem zipWith_xor_dbl : ∀ a b : List Bool,
    List.zipWith xor (dbl a) (dbl b) = dbl (List.zipWith xor a b)
  | [], _ => by rw [dbl_nil, List.zipWith_nil_left, List.zipWith_nil_left, dbl_nil]
  | _ :: _, [] => by rw [dbl_nil, List.zipWith_nil_right, List.zipWith_nil_right, dbl_nil]
  | x :: a, y :: b => by
    simp only [dbl_cons, List.zipWith_cons_cons, zipWith_xor_dbl a b]

/-- **Masking a history block at answer width `l`**: for an `n`-bit query `x` and `l`-bit
strings `y`, `w`, `histBlockOut (x, y) ⊕ maskBlockOut n w = ⟨⟨⟦x⟧, ⟦w + y⟧⟩, []⟩`.

**Proof sketch.** `⟨⟨x, y⟩, []⟩ = dbl (dbl x) ++ 0011 ++ dbl y ++ 01`; the mask is
`0^{4n+4} ++ dbl w ++ 00`; `List.zipWith_append` splits the exclusive-or along these segments,
zeros are neutral (`zipWith_xor_replicate_false`) and `dbl y ⊕ dbl w = dbl (y ⊕ w)`
(`zipWith_xor_dbl`). -/
theorem zipWith_xor_histBlockOut_maskBlockOut {n l : ℕ} (x : Fin n → Bool) (y w : Fin l → Bool) :
    List.zipWith xor (histBlockOut (x, y)) (maskBlockOut n w) =
      pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
  have hyw : List.zipWith xor (List.ofFn y) (List.ofFn w) = List.ofFn (w + y) := by
    rw [zipWith_xor_ofFn_add, add_comm]
  have h1 : histBlockOut (x, y) =
      (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]) ++
        (dbl (List.ofFn y) ++ [false, true]) := by
    simp only [histBlockOut, pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc,
      dbl_cons, List.cons_append, List.nil_append]
  have h2 : maskBlockOut n w =
      List.replicate (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]).length false ++
        (dbl (List.ofFn w) ++ [false, false]) := by
    simp only [maskBlockOut, List.length_append, length_dbl, List.length_ofFn, List.length_cons,
      List.length_nil, List.append_assoc]
    congr 2
    omega
  rw [h1, h2, List.zipWith_append (List.length_replicate ..).symm, zipWith_xor_replicate_false,
    List.zipWith_append (by simp only [length_dbl, List.length_ofFn]), zipWith_xor_dbl, hyw]
  simp only [pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc, dbl_cons,
    List.cons_append, List.nil_append]
  rfl

/-- **Masking a history block**: the exclusive-or of the history block of `(x, y)` with the
mask block of `w` is the history block of `(x, w ⊕ y)` (strings `x, y, w` of the same length).

**Proof sketch.** The case `l = n` of `zipWith_xor_histBlockOut_maskBlockOut`
(`histBlock_eq_histBlockOut`, `maskBlock_eq_maskBlockOut`). -/
theorem zipWith_xor_histBlock_maskBlock {n : ℕ} (x y w : Fin n → Bool) :
    List.zipWith xor (histBlock (x, y)) (maskBlock w) =
      pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
  rw [histBlock_eq_histBlockOut, maskBlock_eq_maskBlockOut]
  exact zipWith_xor_histBlockOut_maskBlockOut x y w

/-- The exclusive-or of two concatenations of `k` chunks of pairwise equal lengths is the
concatenation of the chunkwise exclusive-ors. -/
theorem zipWith_xor_flatten_ofFn : ∀ {k : ℕ} (F G : Fin k → List Bool),
    (∀ j, (F j).length = (G j).length) →
      List.zipWith xor (List.ofFn F).flatten (List.ofFn G).flatten =
        (List.ofFn fun j => List.zipWith xor (F j) (G j)).flatten
  | 0, _, _, _ => rfl
  | k + 1, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons,
      List.flatten_cons, List.zipWith_append (h 0),
      zipWith_xor_flatten_ofFn (fun j => F j.succ) (fun j => G j.succ) fun j => h j.succ]

/-- A string of `q·s` bits read as `q` chunks of `s` bits: chunk `i` is block `i` of
`FunFamily.blocks` (the block window `FunFamily.ofFn_blocks`, read backwards). -/
theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
    ((List.ofFn w).drop (i * s)).take s = List.ofFn (FunFamily.blocks q s w ⟨i, hi⟩) :=
  (FunFamily.ofFn_blocks q s w ⟨i, hi⟩).symm

/-! ### The next-query machine of Thm-99.2.1 -/

/-- The function of `Complexity.polyTimeComputable_blockMap`: on `⟨u, s⟩`, apply `g` to the
consecutive blocks of `s` of length `b(|u|)` and concatenate. -/
def blockMapFun (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
    g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))

/-- The block map is polynomial-time (`Complexity.polyTimeComputable_blockMap`). -/
theorem polyTimeComputable_blockMapFun (b : PolyExpr) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (blockMapFun b g) :=
  polyTimeComputable_blockMap b hg

/-- The typed head cut `⟨u, s⟩ ↦ s.take (p(|u|))` (`Complexity.polyTimeComputable_pairTakePoly`). -/
def takePolyFun (p : PolyExpr) (z : List Bool) : List Bool :=
  (pairSndD z).take (p.eval (pairFstD z).length)

/-- The typed tail cut `⟨u, s⟩ ↦ s.drop (p(|u|))` (`Complexity.polyTimeComputable_pairDropPoly`). -/
def dropPolyFun (p : PolyExpr) (z : List Bool) : List Bool :=
  (pairSndD z).drop (p.eval (pairFstD z).length)

/-- **The pre-processing of the next-query machine**: on `⟨⟨H, ρ⟩, ⟨M, u⟩⟩` output `H ⊕ M`,
the encoded history masked by the hard-wired mask of the messages (which turns the recorded
answers `ans_j` into `m_j ⊕ ans_j`, `zipWith_xor_histBlock_maskBlock`). -/
def preFun (y : List Bool) : List Bool :=
  List.zipWith xor (pairFstD (pairFstD y)) (pairFstD (pairSndD y))

/-- `preFun` is polynomial-time (`Complexity.polyTimeComputable_pairXor` on two projections). -/
theorem polyTimeComputable_preFun : PolyTimeComputable preFun := by
  have h := polyTimeComputable_pairXor.comp
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  convert h using 1
  funext y
  simp [preFun, Function.comp_apply]

/-- The history slot of the post-processor's argument `⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩`. -/
def postHist (z : List Bool) : List Bool := pairFstD (pairFstD (pairFstD (NUPPT.inArg z)))

/-- The points slot `ρ` of the post-processor's argument. -/
def postPoints (z : List Bool) : List Bool := pairSndD (pairFstD (pairFstD (NUPPT.inArg z)))

/-- The budget slot `u = 1^{q+1}` of the post-processor's argument. -/
def postBudget (z : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (NUPPT.inArg z)))

/-- The slot `a` of the post-processor's argument holding the distinguisher's output. -/
def postAns (z : List Bool) : List Bool := pairSndD (NUPPT.inArg z)

/-- The unary count `1^k` of the history blocks (block map with the constant `[true]`). -/
def postCount (z : List Bool) : List Bool :=
  blockMapFun histBlockLen (fun _ => [true]) (pairEncode (NUPPT.inParam z) (postHist z))

/-- The unary offset `1^{k·n}` of the next point in the coin string (block map emitting
`1^{|x|}` for the query `x` of each block). -/
def postOffset (z : List Bool) : List Bool :=
  blockMapFun histBlockLen (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
    (pairEncode (NUPPT.inParam z) (postHist z))

/-- The query move `⟨[false], ρ_k⟩`: the `n`-bit block of the points after the first `k·n`. -/
def postQuery (z : List Bool) : List Bool :=
  pairEncode [false] (takePolyFun .var
    (pairEncode (NUPPT.inParam z) (dropPolyFun .var (pairEncode (postOffset z) (postPoints z)))))

/-- The verdict move `[true, b]` with `b` the distinguisher's acceptance `a = [true]`. -/
def postVerdict (z : List Bool) : List Bool :=
  [true] ++ [decide (pairFstD (pairEncode (postAns z) [true]) = pairSndD (pairEncode (postAns z) [true]))]

/-- The unary count `1^k` of the history blocks at answer width `ℓ(n)` (block length
`histBlockLenOut ℓ`): `postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true])
⟨inParam z, postHist z⟩`. -/
def postCountOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
  blockMapFun (histBlockLenOut ℓ) (fun _ => [true]) (pairEncode (NUPPT.inParam z) (postHist z))

/-- `postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true]) ⟨inParam z, postHist z⟩`.
-/
theorem postCountOut_eq (ℓ : PolyExpr) (z : List Bool) :
    postCountOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun _ => [true])
      (pairEncode (NUPPT.inParam z) (postHist z)) :=
  rfl

/-- The unary offset `1^{k·n}` of the next point at answer width `ℓ(n)`: the block map emitting
`1^{|x|}` for the query `x` of each block of length `histBlockLenOut ℓ`,
`postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun blk => 1^{|fst (fst blk)|})
⟨inParam z, postHist z⟩`. -/
def postOffsetOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
  blockMapFun (histBlockLenOut ℓ) (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
    (pairEncode (NUPPT.inParam z) (postHist z))

/-- `postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ) (fun blk => 1^{|fst (fst blk)|})
⟨inParam z, postHist z⟩`. -/
theorem postOffsetOut_eq (ℓ : PolyExpr) (z : List Bool) :
    postOffsetOut ℓ z = blockMapFun (histBlockLenOut ℓ)
      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
      (pairEncode (NUPPT.inParam z) (postHist z)) :=
  rfl

/-- The query move `⟨[false], ρ_k⟩` at answer width `ℓ(n)`: the `n`-bit block of the points
after the first `k·n` (`postOffsetOut ℓ`), `postQueryOut ℓ z = ⟨[false], takePolyFun var
⟨inParam z, dropPolyFun var ⟨postOffsetOut ℓ z, postPoints z⟩⟩⟩`. -/
def postQueryOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
  pairEncode [false] (takePolyFun .var
    (pairEncode (NUPPT.inParam z)
      (dropPolyFun .var (pairEncode (postOffsetOut ℓ z) (postPoints z)))))

/-- `postQueryOut ℓ z = ⟨[false], takePolyFun var ⟨inParam z, dropPolyFun var ⟨postOffsetOut ℓ z,
postPoints z⟩⟩⟩`. -/
theorem postQueryOut_eq (ℓ : PolyExpr) (z : List Bool) :
    postQueryOut ℓ z = pairEncode [false] (takePolyFun .var
      (pairEncode (NUPPT.inParam z)
        (dropPolyFun .var (pairEncode (postOffsetOut ℓ z) (postPoints z))))) :=
  rfl

/-- **The post-processing of the next-query machine at answer width `ℓ(n)`**: the verdict
`[true, [a = [true]]]` once the history has `|u|` blocks (of length `histBlockLenOut ℓ`), the
query `⟨[false], ρ_k⟩` before: `postFunOut ℓ z = if |postBudget z| ≤ |postCountOut ℓ z| then
postVerdict z else postQueryOut ℓ z`. -/
def postFunOut (ℓ : PolyExpr) (z : List Bool) : List Bool :=
  if decide ((postBudget z).length ≤ (postCountOut ℓ z).length) = true then postVerdict z
  else postQueryOut ℓ z

/-- `postFunOut ℓ z = if |postBudget z| ≤ |postCountOut ℓ z| then postVerdict z
else postQueryOut ℓ z`. -/
theorem postFunOut_eq (ℓ : PolyExpr) (z : List Bool) :
    postFunOut ℓ z =
      if decide ((postBudget z).length ≤ (postCountOut ℓ z).length) = true then postVerdict z
      else postQueryOut ℓ z :=
  rfl

/-- `postFunOut ℓ` is polynomial-time: `PolyTimeComputable (postFunOut ℓ)`.

**Proof sketch.** As `polyTimeComputable_postFun`, with the block length `histBlockLenOut ℓ`:
projections of the layout, two block maps (`polyTimeComputable_blockMapFun`), the typed cuts, a
length test (`StateLoop.lenLe_comp`), an equality test and one branch. -/
theorem polyTimeComputable_postFunOut (ℓ : PolyExpr) : PolyTimeComputable (postFunOut ℓ) := by
  have hArg := NUPPT.polyTimeComputable_inArg
  have hParam := NUPPT.polyTimeComputable_inParam
  have hHist : PolyTimeComputable postHist :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hPoints : PolyTimeComputable postPoints :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hBudget : PolyTimeComputable postBudget :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hAns : PolyTimeComputable postAns := polyTimeComputable_pairSndD.comp hArg
  have hCount : PolyTimeComputable (postCountOut ℓ) :=
    (polyTimeComputable_blockMapFun (histBlockLenOut ℓ) (polyTimeComputable_const [true])).comp
      (hParam.pairEncode hHist)
  have hOffset : PolyTimeComputable (postOffsetOut ℓ) :=
    (polyTimeComputable_blockMapFun (histBlockLenOut ℓ)
      (polyTimeComputable_unary.comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD))).comp
      (hParam.pairEncode hHist)
  have hQuery : PolyTimeComputable (postQueryOut ℓ) :=
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_pairTakePoly .var).comp
      (hParam.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
        (hOffset.pairEncode hPoints))))
  have hVerdict : PolyTimeComputable postVerdict :=
    (polyTimeComputable_prepend [true]).comp
      (polyTimeComputable_pairEq.comp (hAns.pairEncode (polyTimeComputable_const [true])))
  exact polyTimeComputable_ite (StateLoop.lenLe_comp hCount hBudget) hVerdict hQuery

/-- **The post-processing of the next-query machine** on the raw layout
`⟨⟨⟨1^n, ⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩⟩, []⟩, r⟩`: if the history already has `|u|` blocks, the
verdict `[true, [a = [true]]]`; otherwise the query `⟨[false], ρ_k⟩` at the `k`-th point,
`k` the number of history blocks. -/
def postFun (z : List Bool) : List Bool :=
  if decide ((postBudget z).length ≤ (postCount z).length) = true then postVerdict z
  else postQuery z

/-- The `n`-bit block count is the case `ℓ = var` of `postCountOut`:
`postCount z = postCountOut var z` (equal block lengths `6n + 6 = 4n + 2n + 6`). -/
theorem postCount_eq_postCountOut (z : List Bool) : postCount z = postCountOut .var z := by
  simp only [postCount, postCountOut, blockMapFun, eval_histBlockLen, eval_histBlockLenOut,
    PolyExpr.eval_var, show ∀ m : ℕ, 4 * m + 2 * m + 6 = 6 * m + 6 from fun m => by omega]

/-- The `n`-bit offset is the case `ℓ = var` of `postOffsetOut`:
`postOffset z = postOffsetOut var z`. -/
theorem postOffset_eq_postOffsetOut (z : List Bool) : postOffset z = postOffsetOut .var z := by
  simp only [postOffset, postOffsetOut, blockMapFun, eval_histBlockLen, eval_histBlockLenOut,
    PolyExpr.eval_var, show ∀ m : ℕ, 4 * m + 2 * m + 6 = 6 * m + 6 from fun m => by omega]

/-- The `n`-bit query move is the case `ℓ = var` of `postQueryOut`:
`postQuery z = postQueryOut var z`. -/
theorem postQuery_eq_postQueryOut (z : List Bool) : postQuery z = postQueryOut .var z := by
  rw [postQuery, postQueryOut, postOffset_eq_postOffsetOut]

/-- The `n`-bit post-processor is the case `ℓ = var` of `postFunOut`:
`postFun z = postFunOut var z`. -/
theorem postFun_eq_postFunOut (z : List Bool) : postFun z = postFunOut .var z := by
  rw [postFun, postFunOut, postCount_eq_postCountOut, postQuery_eq_postQueryOut]

/-- `postFun` is polynomial-time.

**Proof sketch.** The case `ℓ = var` of `polyTimeComputable_postFunOut`
(`postFun_eq_postFunOut`). -/
theorem polyTimeComputable_postFun : PolyTimeComputable postFun :=
  (polyTimeComputable_postFunOut .var).congr fun z => (postFun_eq_postFunOut z).symm

/-- **The mask of a message vector at answer width `l`** (for `n`-bit queries): the concatenation
of the mask blocks of its entries,
`maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten`. -/
def maskOfOut {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) : List Bool :=
  (List.ofFn fun j => maskBlockOut n (v j)).flatten

/-- `maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten`. -/
theorem maskOfOut_eq {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) :
    maskOfOut n v = (List.ofFn fun j => maskBlockOut n (v j)).flatten :=
  rfl

/-- The mask of a message vector: the concatenation of the mask blocks of its entries. -/
def maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) : List Bool :=
  (List.ofFn fun j => maskBlock (v j)).flatten

/-- The `n`-bit mask is the case `l = n` of `maskOfOut`: `maskOf v = maskOfOut n v` (`rfl`). -/
theorem maskOf_eq_maskOfOut {n k : ℕ} (v : Fin k → Fin n → Bool) : maskOf v = maskOfOut n v :=
  rfl

/-- The length of a concatenation of strings of a common length `b`. -/
theorem length_flatten_of_length (b : ℕ) : ∀ L : List (List Bool),
    (∀ x ∈ L, x.length = b) → L.flatten.length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append,
      length_flatten_of_length b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- The mask of `k` messages of `l` bits for `n`-bit queries has `k (4n + 2l + 6)` bits:
`|maskOfOut n v| = k · (4n + 2l + 6)`. -/
theorem length_maskOfOut {l k : ℕ} (n : ℕ) (v : Fin k → Fin l → Bool) :
    (maskOfOut n v).length = k * (4 * n + 2 * l + 6) := by
  unfold maskOfOut
  rw [length_flatten_of_length (4 * n + 2 * l + 6), List.length_ofFn]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.1 hx
  exact length_maskBlockOut _ _

/-- The length of the mask of `k` messages of `n` bits is `k (6n + 6)`. -/
theorem length_maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) :
    (maskOf v).length = k * (6 * n + 6) := by
  rw [maskOf_eq_maskOfOut, length_maskOfOut]
  congr 1
  omega

/-- The advice bound of the next-query machine: `|⟨mask, 1^{q+1}⟩|`. -/
def adviceBound (q : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) histBlockLen)) (.const 2)) (.add q (.const 1))

/-- The advice bound of the next-query machine at answer width `ℓ`: `|⟨mask, 1^{q+1}⟩|`,
`adviceBoundOut q ℓ = 2 · ((q + 1) · histBlockLenOut ℓ) + 2 + (q + 1)`. -/
def adviceBoundOut (q ℓ : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) (histBlockLenOut ℓ))) (.const 2))
    (.add q (.const 1))

/-- `adviceBoundOut q ℓ = 2 · ((q + 1) · histBlockLenOut ℓ) + 2 + (q + 1)` (the defining
equation). -/
theorem adviceBoundOut_eq (q ℓ : PolyExpr) :
    adviceBoundOut q ℓ =
      .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) (histBlockLenOut ℓ))) (.const 2))
        (.add q (.const 1)) :=
  rfl

/-- `(adviceBoundOut q ℓ).eval n = 2 ((q(n) + 1)(4n + 2ℓ(n) + 6)) + 2 + (q(n) + 1)`. -/
theorem eval_adviceBoundOut (q ℓ : PolyExpr) (n : ℕ) :
    (adviceBoundOut q ℓ).eval n =
      2 * ((q.eval n + 1) * (4 * n + 2 * ℓ.eval n + 6)) + 2 + (q.eval n + 1) := by
  simp only [adviceBoundOut, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    eval_histBlockLenOut]

/-- Decoding the well-formed query move `⟨[false], x⟩`. -/
theorem decodeOracleMove_query (ℓ : ℕ) (x : Fin ℓ → Bool) :
    decodeOracleMove ℓ (pairEncode [false] (List.ofFn x)) = .query x := by
  rw [decodeOracleMove_pairEncode_false, decodeFin_ofFn]

/-- Decoding the verdict move `[true, b]`. -/
theorem decodeOracleMove_ret (ℓ : ℕ) (b : Bool) : decodeOracleMove ℓ [true, b] = .ret b :=
  decodeOracleMove_true_two ℓ b

/-- **The post-processor at answer width `ℓ(n)` on the layout of the composite machine**: for a
history of `k` pairs of an `n`-bit query and an `ℓ(n)`-bit answer, the points string `P`, a mask
`M`, the budget string `u` and the distinguisher's output `a`, the move is the verdict
`[true, [a = [true]]]` when `|u| ≤ k` and the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.

**Proof sketch.** The projections of the layout read the slots; the two block maps on
`⟨1^n, encodeHist hist⟩` output `1^k` and `1^{k n}` (`encodeHist_eq_flatMapOut`,
`flatMap_range_blocks` with blocks of length `4n + 2ℓ(n) + 6 > 0`, `flatMap_const_singleton`,
`flatMap_const_replicate`); the typed cuts then select the block. -/
theorem postFunOut_layout {n : ℕ} (ℓ : PolyExpr)
    (hist : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool))) (P M u a : List Bool) :
    postFunOut ℓ (NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
      if u.length ≤ hist.length then [true, decide (a = [true])]
      else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
  set z := NUPPT.layout (List.replicate n true)
    (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] [] with hz
  have harg : NUPPT.inArg z =
      pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a :=
    NUPPT.inArg_layout _ _ _ _
  have hpar : NUPPT.inParam z = List.replicate n true := NUPPT.inParam_layout _ _ _ _
  have hblocks : ∀ x ∈ hist, (histBlockOut x).length = 4 * n + 2 * ℓ.eval n + 6 :=
    fun x _ => length_histBlockOut x
  have hpos : 0 < 4 * n + 2 * ℓ.eval n + 6 := by omega
  have hcount : postCountOut ℓ z = List.replicate hist.length true := by
    simp only [postCountOut, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLenOut, encodeHist_eq_flatMapOut]
    exact (flatMap_range_blocks histBlockOut (fun _ => [true]) hpos hist hblocks).trans
      (flatMap_const_singleton hist)
  have hoffset : postOffsetOut ℓ z = List.replicate (hist.length * n) true := by
    simp only [postOffsetOut, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLenOut, encodeHist_eq_flatMapOut]
    refine (flatMap_range_blocks histBlockOut
      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true) hpos hist
        hblocks).trans ?_
    show hist.flatMap
      (fun x => List.replicate (pairFstD (pairFstD (histBlockOut x))).length true) = _
    simp only [pairFstD_pairFstD_histBlockOut, List.length_ofFn]
    exact flatMap_const_replicate n hist
  have hbudget : postBudget z = u := by
    simp only [postBudget, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  have hans : postAns z = a := by
    simp only [postAns, harg, pairSndD_pairEncode]
  have hpoints : postPoints z = P := by
    simp only [postPoints, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  simp only [postFunOut, hbudget, hcount, List.length_replicate]
  by_cases h : u.length ≤ hist.length
  · rw [if_pos (by simpa using h), if_pos h]
    simp only [postVerdict, hans, pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  · rw [if_neg (by simpa using h), if_neg h]
    simp only [postQueryOut, takePolyFun, dropPolyFun, hoffset, hpoints, hpar,
      pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, PolyExpr.eval_var]

/-- **The post-processor on the layout of the composite machine**: for a history of `k` pairs
of `n`-bit strings, the points string `P`, a mask `M`, the budget string `u` and the
distinguisher's output `a`, the move is the verdict `[true, [a = [true]]]` when `|u| ≤ k` and
the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.

**Proof sketch.** The case `ℓ = var` of `postFunOut_layout` (`postFun_eq_postFunOut`). -/
theorem postFun_layout {n : ℕ} (hist : List ((Fin n → Bool) × (Fin n → Bool)))
    (P M u a : List Bool) :
    postFun (NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
      if u.length ≤ hist.length then [true, decide (a = [true])]
      else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
  rw [postFun_eq_postFunOut]
  exact postFunOut_layout .var hist P M u a

/-- Concatenating the chunks `f (F i)` of a tuple: `flatMap` over `ofFn`. -/
theorem flatMap_ofFn {α : Type*} {k : ℕ} (F : Fin k → α) (f : α → List Bool) :
    (List.ofFn F).flatMap f = (List.ofFn fun i => f (F i)).flatten := by
  rw [List.flatMap_def, List.map_ofFn]
  rfl

/-- **Masking the canonical history at answer width `l`**: the pre-processor on the encoded
history `((ρ_j, g ρ_j))_j` with the mask `maskOfOut n v` outputs the encoded tuple
`(ρ_j, v_j ⊕ g(ρ_j))_j`: `preFun ⟨⟨encodeHist …, P⟩, ⟨maskOfOut n v, u⟩⟩ =
(List.ofFn fun j => ⟨⟨⟦ρ j⟧, ⟦v j + g (ρ j)⟧⟩, []⟩).flatten` (`zipWith_xor_flatten_ofFn`,
`zipWith_xor_histBlockOut_maskBlockOut`). -/
theorem preFun_encodeHistOut {n l k : ℕ} (ρ : Fin k → Fin n → Bool) (v : Fin k → Fin l → Bool)
    (g : (Fin n → Bool) → (Fin l → Bool)) (P u : List Bool) :
    preFun (pairEncode (pairEncode (encodeHist (List.ofFn fun i => (ρ i, g (ρ i)))) P)
        (pairEncode (maskOfOut n v) u)) =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
  simp only [preFun, pairFstD_pairEncode, pairSndD_pairEncode, encodeHist_eq_flatMapOut,
    maskOfOut, flatMap_ofFn]
  rw [zipWith_xor_flatten_ofFn _ _ fun j => by rw [length_histBlockOut, length_maskBlockOut]]
  exact congrArg List.flatten (congrArg List.ofFn (funext fun j =>
    zipWith_xor_histBlockOut_maskBlockOut (ρ j) (g (ρ j)) (v j)))

/-- **Masking the canonical history**: the pre-processor on the encoded history
`((ρ_j, g ρ_j))_j` with the mask of `v` outputs the encoded ciphertext tuple
`(ρ_j, v_j ⊕ g(ρ_j))_j` (`zipWith_xor_flatten_ofFn`, `zipWith_xor_histBlock_maskBlock`). -/
theorem preFun_encodeHist {n k : ℕ} (ρ v : Fin k → Fin n → Bool)
    (g : (Fin n → Bool) → (Fin n → Bool)) (P u : List Bool) :
    preFun (pairEncode (pairEncode (encodeHist (List.ofFn fun i => (ρ i, g (ρ i)))) P)
        (pairEncode (maskOf v) u)) =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
  rw [maskOf_eq_maskOfOut]
  exact preFun_encodeHistOut ρ v g P u

/-- **The next-query machine of Thm-99.2.1 at answer width `ℓ(n)`** ([PS10, Theorem 99.2, proof,
with `ℓ`-bit outputs]): for a non-uniform PPT `D`, a budget polynomial `q` and masks
`v n ∈ ({0,1}^{ℓ(n)})^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n` are, up to a
bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, such that for every oracle
`g : {0,1}^n → {0,1}^{ℓ(n)}`,
`(B.toOracleAdversary n n ℓ(n) (q(n) + 1) (φ (ρ, c))).eval g =
decide (D.runAt n ⟦(⟨⟨ρ_j, v_j ⊕ g(ρ_j)⟩, []⟩)_j⟧ c = [true])`.

**Proof sketch.** As `exists_queryChain_nuppt`, with the string layer at answer width `ℓ(n)`:
`B` is `exists_split` (the first `(q(n)+1) n` coins are the points) of `exists_withAdvice` (advice
`⟨maskOfOut n (v n), 1^{q(n)+1}⟩`, bound `adviceBoundOut q ℓ`) of `exists_seq` of `D ∘ preFun`
and the uniform machine of `postFunOut ℓ`. On the encoded history of `k` blocks of
`4n + 2ℓ(n) + 6` bits the post-processor asks `ρ_k` while `k ≤ q(n)`, and then outputs `D`'s
verdict on the masked history (`postFunOut_layout`, `take_drop_ofFn_blocks`,
`preFun_encodeHistOut`); `buildTree` is evaluated by induction on the remaining budget along the
canonical history `((ρ_i, g ρ_i))_i`. -/
theorem exists_queryChainOut_nuppt (D : NUPPT) (q ℓ : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool))
        (ρ : Fin (q.eval n + 1) → Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true]) := by
  classical
  have hβ : ∀ n, (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)).length ≤
      (adviceBoundOut q ℓ).eval n := by
    intro n
    rw [length_pairEncode, length_maskOfOut, List.length_replicate, eval_adviceBoundOut]
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ := D.exists_comp polyTimeComputable_preFun polyTimeComputable_id
  obtain ⟨C, hCc, -, hC⟩ :=
    D₁.exists_seq (NUPPT.ofPolyTimeUniform (polyTimeComputable_postFunOut ℓ) (.const 0))
  obtain ⟨C₂, hC₂c, hC₂⟩ := C.exists_withAdvice
    (fun n => pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true))
    (adviceBoundOut q ℓ) hβ
  obtain ⟨B, hBc, -, hB⟩ := C₂.exists_split (.mul (.add q (.const 1)) .var)
  refine ⟨B, fun n => ?_⟩
  have hlen : B.coinLen n = (q.eval n + 1) * n + D.coinLen n := by
    simp only [NUPPT.coinLen_eq, hBc, hC₂c, hCc, hD₁c, NUPPT.coins_ofPolyTimeUniform,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, Nat.add_zero]
  let φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n :=
    ((FunFamily.blocks (q.eval n + 1) n).symm.prodCongr (Equiv.refl (D.Coins n))).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)))
  refine ⟨φ, fun g ρ c => ?_⟩
  set Pstr : List Bool := List.ofFn ((FunFamily.blocks (q.eval n + 1) n).symm ρ) with hPstr
  have hφ : φ (ρ, c) =
      fun i => Fin.append ((FunFamily.blocks (q.eval n + 1) n).symm ρ) c (Fin.cast hlen i) := by
    funext i
    rfl
  have hcoins : List.ofFn (φ (ρ, c)) = Pstr ++ List.ofFn c := by
    rw [hφ, hPstr, ← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen.symm _).symm
  -- the activation of `B` on an encoded history
  have hD₁len : D₁.coinLen n = D.coinLen n := by simp only [NUPPT.coinLen_eq, hD₁c]
  have hrun : ∀ hist : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)),
      B.runAt n (encodeHist hist) (φ (ρ, c)) =
        postFunOut ℓ (NUPPT.layout (List.replicate n true)
          (pairEncode (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)))
            (D.runAt n (preFun (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOfOut n (v n)) (List.replicate (q.eval n + 1) true)))) c))
          [] []) := by
    intro hist
    have hp : (PolyExpr.mul (.add q (.const 1)) .var).eval n = (q.eval n + 1) * n := by
      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_var]
    have hPlen : Pstr.length = (q.eval n + 1) * n := by simp [hPstr]
    have hclen : (List.ofFn c).length = D.coinLen n := by simp
    rw [NUPPT.runAt_eq, hcoins, hB, hp, List.take_left' hPlen, List.drop_left' hPlen]
    have hC₂' := hC₂ n (pairEncode (encodeHist hist) Pstr) (List.ofFn c)
    simp only at hC₂'
    rw [hC₂', hC, hD₁len, List.take_of_length_le hclen.le, List.drop_of_length_le hclen.le, hD₁,
      NUPPT.runAtL_ofPolyTimeUniform]
    simp only [NUPPT.layout_eq, NUPPT.advInput_eq, NUPPT.runAt_eq, id_eq]
  -- the canonical history along the points `ρ` against the oracle `g`
  let ρ' : ℕ → Fin n → Bool := fun i => if h : i < q.eval n + 1 then ρ ⟨i, h⟩ else fun _ => false
  let hist : ℕ → List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)) :=
    fun k => List.ofFn fun i : Fin k => (ρ' i, g (ρ' i))
  have hρ' : ∀ (i : ℕ) (hi : i < q.eval n + 1), ρ' i = ρ ⟨i, hi⟩ := fun i hi => dif_pos hi
  have hist_len : ∀ k, (hist k).length = k := fun k => List.length_ofFn
  have hist_succ : ∀ k, hist (k + 1) = hist k ++ [(ρ' k, g (ρ' k))] := by
    intro k
    simp only [hist]
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.coe_castSucc, Fin.val_last]
  have hist_top :
      hist (q.eval n + 1) = List.ofFn fun i : Fin (q.eval n + 1) => (ρ i, g (ρ i)) := by
    simp only [hist]
    congr 1
    funext i
    rw [hρ' i i.isLt]
  -- the next-query function of `B`
  set next : List ((Fin n → Bool) × (Fin (ℓ.eval n) → Bool)) → OracleMove n :=
    fun h => decodeOracleMove n (B.runAt n (encodeHist h) (φ (ρ, c))) with hnext
  have hquery : ∀ k (hk : k < q.eval n + 1), next (hist k) = .query (ρ ⟨k, hk⟩) := by
    intro k hk
    simp only [hnext]
    rw [hrun, postFunOut_layout, hist_len, if_neg (by simp; omega), hPstr,
      take_drop_ofFn_blocks _ k hk, Equiv.apply_symm_apply, decodeOracleMove_query]
  have hret : next (hist (q.eval n + 1)) =
      .ret (decide (D.runAt n (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
          [true])) := by
    simp only [hnext]
    rw [hrun, postFunOut_layout, hist_len, if_pos (by simp), hist_top, preFun_encodeHistOut,
      decodeOracleMove_ret]
  -- evaluation of the tree by induction on the remaining budget
  have main : ∀ j, j ≤ q.eval n + 1 →
      (buildTree next j (hist (q.eval n + 1 - j))).eval g =
        decide (D.runAt n (List.ofFn fun j =>
          pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
            [true]) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, buildTree_zero_of_ret hret, QueryTree.eval_ret]
    | succ j ih =>
      intro hj
      have hk : q.eval n + 1 - (j + 1) < q.eval n + 1 := by omega
      rw [buildTree_succ_of_query (hquery _ hk), QueryTree.eval_query, ← hρ' _ hk, ← hist_succ,
        show q.eval n + 1 - (j + 1) + 1 = q.eval n + 1 - j by omega]
      exact ih (by omega)
  have h0 : hist 0 = [] := rfl
  have := main (q.eval n + 1) le_rfl
  rw [Nat.sub_self, h0] at this
  rw [NUPPT.toOracleAdversary_eq]
  exact this

/-- **The one-query next-query machine at answer width `ℓ(n)`** ([PS10, Definition 96.2,
clause (2), with `ℓ`-bit outputs]): for a non-uniform PPT `D` there is a non-uniform PPT `B`
whose coins at `n` are, up to a bijection `φ`, a point `r ∈ {0,1}^n` and the coins `c` of `D`,
such that for every oracle `g : {0,1}^n → {0,1}^{ℓ(n)}`, with the budget `1`,
`(B.toOracleAdversary n n ℓ(n) 1 (φ (r, c))).eval g = decide (D.runAt n ⟨⟦r⟧, ⟦g r⟧⟩ c = [true])`.

**Proof sketch.** `exists_queryChainOut_nuppt` with `q = 0`, the zero mask, and `D` precomposed
with `pairFstD` (`NUPPT.exists_comp`): the encoded one-entry tuple is `⟨⟨⟦r⟧, ⟦g r⟧⟩, []⟩`, whose
first component is `⟨⟦r⟧, ⟦g r⟧⟩`. The coins are `r` read as the one-point tuple
(`Equiv.funUnique`, `finCongr`) and `D`'s coins carried to the composite (`NUPPT.coinsCongr`);
the budget `(const 0)(n) + 1` is `1` (`PolyExpr.eval_const`). -/
theorem exists_oneQuery_nuppt (D : NUPPT) (ℓ : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) (r : Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) 1 (φ (r, c))).eval g =
          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true]) := by
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ :=
    D.exists_comp polyTimeComputable_pairFstD polyTimeComputable_id
  obtain ⟨B, hB⟩ := exists_queryChainOut_nuppt D₁ (.const 0) ℓ fun _ _ => 0
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  have h1 : 1 = (PolyExpr.const 0).eval n + 1 := by rw [PolyExpr.eval_const]
  let e : (Fin n → Bool) ≃ (Fin ((PolyExpr.const 0).eval n + 1) → Fin n → Bool) :=
    (Equiv.funUnique (Fin 1) (Fin n → Bool)).symm.trans
      (Equiv.arrowCongr (finCongr h1) (Equiv.refl _))
  have he : ∀ (r : Fin n → Bool) j, e r j = r := fun r j => rfl
  refine ⟨(e.prodCongr (NUPPT.coinsCongr hD₁c.symm n)).trans φ, fun g r c => ?_⟩
  -- the budget `1` is `(const 0)(n) + 1`
  have hbud : ∀ (m : ℕ), m = (PolyExpr.const 0).eval n + 1 → ∀ x : B.Coins n,
      (B.toOracleAdversary n n (ℓ.eval n) m x).eval g =
        (B.toOracleAdversary n n (ℓ.eval n) ((PolyExpr.const 0).eval n + 1) x).eval g := by
    rintro m rfl x
    rfl
  rw [hbud 1 h1, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, hφ]
  congr 2
  -- the one-entry tuple, read by `pairFstD`
  rw [NUPPT.runAt_coinsCongr, hD₁, id_eq, ← NUPPT.runAt_eq]
  congr 1
  have hnil : ∀ (f : Fin ((PolyExpr.const 0).eval n) → List Bool), List.ofFn f = [] :=
    fun f => List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
  rw [List.ofFn_succ, hnil, List.flatten_cons, List.flatten_nil, List.append_nil,
    pairFstD_pairEncode, he, zero_add]

/-- **The next-query machine of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
by closure under efficient operations we contradict the pseudorandomness property"]): for a
non-uniform PPT `D` (a distinguisher of encoded ciphertext tuples), a budget polynomial `q` and
message vectors `v n ∈ ({0,1}^n)^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n`
are, up to a bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, and whose
query tree with budget `q(n) + 1`, evaluated against any oracle `g`, gives `D`'s verdict on the
encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c` (an equality of outputs; the sequence of
queries is not part of the statement).

**Proof sketch.** The case `ℓ = var` of `exists_queryChainOut_nuppt`. -/
theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin n → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (q.eval n + 1) → Fin n → Bool)
        (c : D.Coins n),
        (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true]) :=
  exists_queryChainOut_nuppt D q .var v

end TCSlib.Cryptography.MultiMsg

## ===== TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/MultiMsgOut.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The multi-message bound at `ℓ(n)`-bit outputs

The total of [PS10, Theorem 99.2] for a keyed family with `ℓ(n)`-bit outputs (ruling B3), without
the scheme: for a family `F` whose keyed ensemble is oracle-indistinguishable from the random
functions with `ℓ(n)`-bit outputs, every non-uniform PPT `D` distinguishes the encoded real
hybrids of any two mask vectors with negligible advantage, uniformly in the masks
(`MultiMsg.exists_negligible_distAdv_prfEncRealOut`). The `n`-bit scheme's
`prfScheme_multiMessageSecure` is its case `ℓ = var`.

## Main definitions

* `encodeTupleOut`: the encoded tuple of ciphertext pairs with `n`-bit points and `l`-bit pads.

## Main results

* `MultiMsg.encodeList_eq_flatMap`: `encodeList` as a concatenation of chunks (the general form of
  a private lemma of `FromPRF.lean`).
* `encodeTupleOut_eq_flatten`: the encoded tuple as the machine produces it.
* `MultiMsg.exists_negligible_distAdv_prfEncRealOut`: the total.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8, Definition 96.2, and §3.9, Theorem 99.2, with `ℓ`-bit outputs.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- **The encoded ciphertext tuple at output width `l`**: `encodeList` of the pairs
`⟨r_j, c_j⟩` of an `n`-bit point and an `l`-bit string,
`encodeTupleOut v = encodeList (List.ofFn fun j => ⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩)`. -/
def encodeTupleOut {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
    List Bool :=
  PrivateKeyScheme.encodeList
    (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))

/-- The defining equation:
`encodeTupleOut v = encodeList (List.ofFn fun j => ⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩)`. -/
theorem encodeTupleOut_eq {n l q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
    encodeTupleOut v = PrivateKeyScheme.encodeList
      (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) :=
  rfl

/-- **`encodeList` is a concatenation of chunks**: `encodeList l` is the concatenation of the
self-delimited chunks `⟨c, []⟩`, `encodeList l = l.flatMap fun c => ⟨c, []⟩`. -/
theorem MultiMsg.encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
  | [] => by rw [PrivateKeyScheme.encodeList_nil, List.flatMap_nil]
  | c :: l => by
    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, MultiMsg.encodeList_eq_flatMap l]
    simp [pairEncode_eq]

/-- The encoded tuple at width `l` is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
form in which `MultiMsg.exists_queryChainOut_nuppt` produces it):
`encodeTupleOut v = (List.ofFn fun j => ⟨⟨⟦(v j).1⟧, ⟦(v j).2⟧⟩, []⟩).flatten`. -/
theorem encodeTupleOut_eq_flatten {n l q : ℕ}
    (v : Fin (q + 1) → (Fin n → Bool) × (Fin l → Bool)) :
    encodeTupleOut v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
  rw [encodeTupleOut_eq, MultiMsg.encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]

/-- **[PS10, Theorem 99.2] at `ℓ(n)`-bit outputs, the total** (with `ℓ`-bit outputs; ruling B3):
if the keyed ensemble of `F n : {0,1}^n → {0,1}^n → {0,1}^{ℓ(n)}` is oracle-indistinguishable
from the random functions with `ℓ(n)`-bit outputs, then for every non-uniform PPT `D` and
polynomial `q` there is a negligible `ε` with, for every `n` and all masks
`w, w' ∈ ({0,1}^{ℓ(n)})^{q(n)+1}`,
`distAdv (encodeTupleOut ∘ prfEncRealOut (F n) w) (encodeTupleOut ∘ prfEncRealOut (F n) w')
(D.distinguisherL n) ≤ ε n`, the seeds being a uniform key and `q(n) + 1` uniform points.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** As `prfScheme_multiMessageSecure`, without the scheme.
1. At each `n` choose the pair of masks maximizing the advantage (`Finset.exists_max_image`).
2. For the two maximizing mask vectors, build the next-query machines `B₀`, `B₁`
   (`MultiMsg.exists_queryChainOut_nuppt`, budget `q + 1`); with `MultiMsg.prfAdv_congr_equiv`,
   `eval_multiMsgAdvOut` and `encodeTupleOut_eq_flatten` their PRF advantages are those of
   `multiMsgAdvOut w (D ∘ encodeTupleOut)`.
3. `distAdv_comp` and `distAdv_prfEncRealOut_le` bound the advantage by
   `prfAdv (F n) B₀ + prfAdv (F n) B₁ + 2 · C(q(n)+1, 2) / 2^n`.
4. This is negligible: `OracleEnsemble.Indist.negligible_prfAdv` at the budget `q + 1` and
   `MultiMsg.negligible_choose_div_two_pow`, with `Negligible.add` and `Negligible.const_mul`. -/
theorem MultiMsg.exists_negligible_distAdv_prfEncRealOut {ℓ : PolyExpr}
    {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ))
    (D : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (w w' : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w z))
        (fun z => encodeTupleOut (prfEncRealOut (F n) w' z)) (D.distinguisherL n) ≤ ε n := by
  -- the worst mask pair at each parameter (hard-wired into the reductions)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
      (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      ∀ w : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
          (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
        distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w.1 z))
            (fun z => encodeTupleOut (prfEncRealOut (F n) w.2 z)) (D.distinguisherL n) ≤
          distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) p.1 z))
            (fun z => encodeTupleOut (prfEncRealOut (F n) p.2 z)) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun w : (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) ×
          (Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool) =>
        distAdv (fun z => encodeTupleOut (prfEncRealOut (F n) w.1 z))
          (fun z => encodeTupleOut (prfEncRealOut (F n) w.2 z)) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
  choose μ hμ using hmax
  -- the next-query machines for the two hard-wired mask vectors
  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChainOut_nuppt D q ℓ fun n => (μ n).1
  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChainOut_nuppt D q ℓ fun n => (μ n).2
  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) +
      prfAdv (F n) (B₁.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) +
      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n w w' => ?_⟩
  · -- the asymptotic step: two PRF advantages and the collision term
    simpa only [PolyExpr.eval_add, PolyExpr.eval_const] using
      ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
        (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
        ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
  · refine (hμ n (w, w')).trans ?_
    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdvOut`
    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool)
        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
        (∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) ρ c,
          (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
            decide (D.runAt n (List.ofFn fun j =>
              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
                [true])) →
        prfAdv (F n) (B.toOracleAdversary n n (ℓ.eval n) (q.eval n + 1)) =
          prfAdv (F n) (multiMsgAdvOut v fun x c => D.distinguisherL n (encodeTupleOut x) c) := by
      intro B v φ hφ
      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g x => ?_
      rw [hφ g x.1 x.2, eval_multiMsgAdvOut, NUPPT.distinguisherL_eq, encodeTupleOut_eq_flatten]
    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
    dsimp only
    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁]
    -- the concrete step: the six hybrids at width `ℓ(n)`
    exact (distAdv_comp encodeTupleOut (prfEncRealOut (F n) (μ n).1)
      (prfEncRealOut (F n) (μ n).2) (D.distinguisherL n)).symm.trans_le
        (distAdv_prfEncRealOut_le (F n) (μ n).1 (μ n).2
          (fun x c => D.distinguisherL n (encodeTupleOut x) c))

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multi-message secure encryption from a pseudorandom function

The key generator samples a key. The encryptor samples an independent point, masks the
message with the function value at that point, and returns the point with the masked message.
Decryption recomputes the mask and checks the ciphertext format [PS10, Algorithm 99.1].

## Main definitions

* `prfEncFun`, `prfDecFun` and `prfScheme` implement the scheme from a polynomial-time evaluator.
* `encodeTuple` encodes the fixed vector of ciphertext pairs as a string.

## Main results

* `prfScheme_multiEncDist` identifies the ciphertext sampler with the encoded real hybrid.
* `prfScheme_multiMessageSecure` lifts the six-hybrid bound to a negligible advantage against
  non-uniform polynomial-time distinguishers [PS10, Theorem 99.2]; it is the case `ℓ = var` of
  `MultiMsg.exists_negligible_distAdv_prfEncRealOut` (`FromPRF.MultiMsgOut`).
* `exists_multiMessageSecure_of_prf` and `exists_multiMessageSecure_of_exists_prg` give the
  existence results from a PRF and, via GGM, from a PRG.

## Contents

* `FromPRF.Hybrid` proves the concrete six-hybrid bound.
* `FromPRF.HybridLemmas` supplies the collision and coin-relabelling estimates.
* `FromPRF.ReductionMachine` implements the next-query reduction and proves its run agreement,
  at `ℓ(n)`-bit answers as well.
* `FromPRF.MultiMsgOut` proves the multi-message bound for a family with `ℓ(n)`-bit outputs.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The scheme of [PS10, Algorithm 99.1] -/

/-- The raw string function of `Enc` of [PS10, Algorithm 99.1]: on the machine layout
`⟨⟨⟨1^n, ⟨k, w⟩⟩, α⟩, r⟩` output the pair `⟨r, w ⊕ E(⟨k, r⟩)⟩`, where `E` evaluates the PRF on
`⟨key, input⟩` and the coin string `r` is the fresh point. -/
def prfEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (NUPPT.inCoins z)
    (List.zipWith xor (pairSndD (NUPPT.inArg z))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (NUPPT.inCoins z))))

/-- Whether the ciphertext `⟨r, c⟩` of the layout `⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` has `n`-bit
components: the domain of `Dec` in [PS10, Algorithm 99.1]. -/
def prfDecWF (z : List Bool) : Bool :=
  decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
    decide ((pairSndD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length)

/-- The raw string function of `Dec` of [PS10, Algorithm 99.1]: on the layout
`⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` with `n`-bit `r` and `c`, output `c ⊕ E(⟨k, r⟩)`; on any other
ciphertext, output `⊥`, here the `(n + 1)`-bit string `1^{n+1}`, which decodes to no message.

The source defines `Dec` on pairs of `n`-bit strings only. The guard matters under
chosen-ciphertext attacks: `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, so without it a
malformed ciphertext would evaluate `E` where it is unconstrained, and there it may reveal the
key. -/
def prfDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  if prfDecWF z then
    List.zipWith xor (pairSndD (pairSndD (NUPPT.inArg z)))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))))
  else true :: NUPPT.inParam z

/-- `prfEncFun E` is polynomial-time when `E` is: projections, one evaluation of `E`, one
bitwise exclusive-or (`Complexity.polyTimeComputable_pairXor`) and one pairing. -/
theorem polyTimeComputable_prfEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfEncFun E) := by
  have h := NUPPT.polyTimeComputable_inCoins.pairEncode
    (polyTimeComputable_pairXor.comp
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins))))
  convert h using 1
  funext z
  simp [prfEncFun, Function.comp_apply]

/-- The well-formedness test of `Dec` is polynomial-time: two length comparisons
(`Complexity.polyTimeComputable_lenEq`). -/
theorem polyTimeComputable_prfDecWF : PolyTimeComputable (fun z => [prfDecWF z]) := by
  have hl : ∀ g : List Bool → List Bool, PolyTimeComputable g →
      PolyTimeComputable (fun z => [decide ((g z).length = (NUPPT.inParam z).length)]) := by
    intro g hg
    convert polyTimeComputable_lenEq.comp (hg.pairEncode NUPPT.polyTimeComputable_inParam)
      using 1
    funext z
    simp [Function.comp_apply]
  exact polyTimeComputable_and
    (hl _ ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))
    (hl _ ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))

/-- `prfDecFun E` is polynomial-time when `E` is: the guard, then the branch of the old `Dec`
(`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_prfDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfDecFun E) := by
  refine polyTimeComputable_ite polyTimeComputable_prfDecWF ?_
    ((polyTimeComputable_const [true]).append NUPPT.polyTimeComputable_inParam)
  have h := polyTimeComputable_pairXor.comp
    (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
        NUPPT.polyTimeComputable_inArg).pairEncode
      (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
          NUPPT.polyTimeComputable_inArg))))
  convert h using 1
  funext z
  simp [prfDecFun, Function.comp_apply]

/-- The activation of the encryption machine on `⟨k, w⟩` with coins `r` is
`⟨r, w ⊕ E(⟨k, r⟩)⟩`. -/
theorem runAt_prfEnc {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).runAt n (pairEncode k w) r =
      pairEncode (List.ofFn r) (List.zipWith xor w (E (pairEncode k (List.ofFn r)))) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfEncFun, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- The activation of the decryption machine on `⟨k, ⟨r, c⟩⟩` with `n`-bit `r` and `c` is
`c ⊕ E(⟨k, r⟩)`. -/
theorem runAt_prfDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k r c : List Bool) (hr : r.length = n) (hc : c.length = n)
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k (pairEncode r c)) r' =
      List.zipWith xor c (E (pairEncode k r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfDecFun, prfDecWF, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, hr, hc]

/-- On a ciphertext `w` whose two projections `pairFstD w` and `pairSndD w` are not both `n` bits
long, the decryption machine outputs `⊥`: a string that decodes to no `n`-bit message. -/
theorem decodeFin_runAt_prfDec_of_not_wf {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (coins : PolyExpr) (n : ℕ) (k w : List Bool)
    (hw : ¬ ((pairFstD w).length = n ∧ (pairSndD w).length = n))
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    decodeFin n ((NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k w) r') = none := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  have hf : prfDecWF (pairEncode (pairEncode (NUPPT.advInput n (pairEncode k w)) [])
      (List.ofFn r')) = false := by
    simp only [prfDecWF, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    tauto
  rw [prfDecFun, hf]
  simp [decodeFin_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]

/-- Masking twice with the same pad (at least as long as the message) is the identity
(private copy of the helper of `Encryption/PrivateKey/FromPRG.lean`). -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **The many-message encryption scheme of [PS10, Algorithm 99.1]** for a function family
`F` with polynomial-time evaluator `E` on `⟨s, x⟩`: `Gen(1^n)` outputs a uniform `n`-bit key
`k` (its coin string); `Enc_k(m)` draws `r ← U_n` (its coin string) and outputs
`⟨r, m ⊕ f_k(r)⟩`; `Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` (deterministic, coins `const 0`). Correctness is
`(m ⊕ p) ⊕ p = m` with the `n`-bit pad `p = f_k(r)`.

**Deviation:** `prfScheme`: the key is the `n`-bit coin string of `Gen`; `Enc` draws its `n`-bit
`r` as its coin string; the evaluator `E` of the PRF is an explicit argument rather than
extracted from `PRF.easy`; ciphertexts are the pair `⟨r, m ⊕ f_k(r)⟩`. -/
noncomputable def prfScheme (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_prfEnc hE]
    have h : E (pairEncode (List.ofFn rg) (List.ofFn re)) =
        List.ofFn (F n (NUPPT.coinsEquiv_ofPolyTimeUniform _ _ n rg)
          (NUPPT.coinsEquiv_ofPolyTimeUniform _ _ n re)) := by
      rw [← hFE, NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn]
    have hre : (List.ofFn re).length = n := by
      rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n re, List.length_ofFn, PolyExpr.eval_var]
    rw [h, runAt_prfDec hE _ _ _ _ _ hre (by simp), h,
      zipWith_xor_xor_self _ _ (by simp), decodeFin_ofFn]

/-- The key generator of `prfScheme` is the uniform machine returning its coin string
[PS10, Algorithm 99.1]. -/
theorem prfScheme_gen (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).gen = NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var := rfl

/-- The encryptor of `prfScheme` uses its raw encryption function and `n` coins
[PS10, Algorithm 99.1]. -/
theorem prfScheme_enc (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).enc =
      NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var := rfl

/-- The decryption machine of `prfScheme F E hE hFE` is
`NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)`. -/
theorem prfScheme_dec (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).dec =
      NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0) := rfl

/-- The encoding of a tuple of ciphertext pairs `(r_j, c_j)_j` as the string handed to a
distinguisher: `encodeList` of the pairs `⟨r_j, c_j⟩`. -/
def encodeTuple {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))

/-- The encoded tuple is the case `l = n` of `encodeTupleOut`:
`encodeTuple v = encodeTupleOut v` (both are `encodeList` of the pairs `⟨⟦r_j⟧, ⟦c_j⟧⟩`). -/
theorem encodeTuple_eq_encodeTupleOut {n q : ℕ}
    (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : encodeTuple v = encodeTupleOut v := by
  rw [encodeTuple, encodeTupleOut_eq]

/-- `encodeList l` is the concatenation of the self-delimited chunks `⟨c, []⟩`, `c ∈ l`. -/
private theorem encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
  | [] => by rw [PrivateKeyScheme.encodeList_nil, List.flatMap_nil]
  | c :: l => by
    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, encodeList_eq_flatMap l]
    simp [pairEncode_eq]

/-- The encoded ciphertext tuple is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
form in which the next-query machine of `MultiMsg.exists_queryChain_nuppt` produces it). -/
theorem encodeTuple_eq_flatten {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :
    encodeTuple v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
  rw [encodeTuple_eq_encodeTupleOut]
  exact encodeTupleOut_eq_flatten v

/-- **The coins of the multi-message experiment of Algorithm 99.1 are bit strings**: the key
coins of `Gen` and the `q + 1` coin strings of `Enc` are `n`-bit strings,
`gen.Coins n × (Fin (q + 1) → enc.Coins n) ≃ {0,1}^n × ({0,1}^n)^{q+1}` (the published coin
identifications `NUPPT.coinsEquiv_ofPolyTimeUniform`; they keep every coin string). -/
noncomputable def prfScheme_coinsEquiv (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) :
    (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) :=
  (NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).prodCongr
    (Equiv.piCongrRight fun _ =>
      NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n)

/-- The coin equivalence of the multi-message experiment keeps every coin string: the key,
`List.ofFn (prfScheme_coinsEquiv … r).1 = List.ofFn r.1`, and each point,
`List.ofFn ((prfScheme_coinsEquiv … r).2 j) = List.ofFn (r.2 j)`. -/
theorem prfScheme_coinsEquiv_ofFn (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    List.ofFn (prfScheme_coinsEquiv F E hE hFE n q r).1 = List.ofFn r.1 ∧
      ∀ j, List.ofFn ((prfScheme_coinsEquiv F E hE hFE n q r).2 j) = List.ofFn (r.2 j) :=
  ⟨NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n r.1,
    fun j => NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n (r.2 j)⟩

/-- **The ciphertext tuple of Algorithm 99.1** is the encoding of the hybrid `H¹`: for the key
`k` and the points `r_j` read off the coins `r` (`prfScheme_coinsEquiv`),
`multiEncDist n q m r = encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv … r))`.

**Proof sketch.** `multiEncDist_apply` writes the left side as `encodeList` of the encryptions
`Enc_k(m_j; r_j)`; the key machine outputs its coin string (`runAt_coinKey`) and the encryption
machine outputs `⟨r_j, m_j ⊕ E(⟨k, r_j⟩)⟩` (`runAt_prfEnc`). The coin strings are those of
`prfScheme_coinsEquiv … r` (`prfScheme_coinsEquiv_ofFn`), so `hFE` turns `E(⟨k, r_j⟩)` into
`F n k r_j` and `zipWith_xor_ofFn_add` gives the `j`-th pair of `prfEncReal`. -/
theorem prfScheme_multiEncDist (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    (prfScheme F E hE hFE).multiEncDist n q m r =
      encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv F E hE hFE n q r)) := by
  rw [PrivateKeyScheme.multiEncDist_apply, encodeTuple]
  congr 1
  congr 1
  funext j
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var).runAt n
    (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] r.1)
      (List.ofFn (m j))) (r.2 j) = _
  rw [runAt_coinKey, runAt_prfEnc hE]
  have h1 : List.ofFn r.1 = List.ofFn (prfScheme_coinsEquiv F E hE hFE n q r).1 :=
    (prfScheme_coinsEquiv_ofFn F E hE hFE n q r).1.symm
  have h2 : List.ofFn (r.2 j) = List.ofFn ((prfScheme_coinsEquiv F E hE hFE n q r).2 j) :=
    ((prfScheme_coinsEquiv_ofFn F E hE hFE n q r).2 j).symm
  rw [h1, h2, hFE, zipWith_xor_ofFn_add, prfEncReal_apply]

/-- **[PS10, Theorem 99.2]: the scheme of Algorithm 99.1 is multi-message secure** when `F` is
a pseudorandom function family.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** The case `ℓ = var` of `MultiMsg.exists_negligible_distAdv_prfEncRealOut`
(applied to `hF.pseudorandom`), which maximizes over the message pairs, builds the next-query
machines of Thm-99.2.1 (`MultiMsg.exists_queryChainOut_nuppt`) and bounds the advantage by the
six hybrids (`distAdv_prfEncRealOut_le`), two PRF advantages and the collision term. The
ciphertext tuples of Algorithm 99.1 are `encodeTuple ∘ prfEncReal (F n) m` on the seeds
`prfScheme_coinsEquiv` (`prfScheme_multiEncDist`), i.e. `encodeTupleOut ∘ prfEncRealOut (F n) m`
(`encodeTuple_eq_encodeTupleOut`, `prfEncReal_eq_prfEncRealOut`); relabel the seeds
(`acceptProb_comp_equiv`). -/
theorem prfScheme_multiMessageSecure (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).MultiMessageSecure := by
  refine (PrivateKeyScheme.multiMessageSecure_iff _).2 fun D q => ?_
  obtain ⟨ε, hε, hb⟩ := MultiMsg.exists_negligible_distAdv_prfEncRealOut hF.pseudorandom D q
  refine ⟨ε, hε, fun n m m' => ?_⟩
  -- the ciphertext tuples are `encodeTupleOut ∘ prfEncRealOut` on relabelled seeds
  have key : ∀ m₀ : Fin (q.eval n + 1) → Fin n → Bool,
      (prfScheme F E hE hFE).multiEncDist n (q.eval n) m₀ = fun r =>
        encodeTupleOut (prfEncRealOut (F n) m₀ (prfScheme_coinsEquiv F E hE hFE n (q.eval n) r)) :=
    fun m₀ => funext fun r => by
      rw [prfScheme_multiEncDist, encodeTuple_eq_encodeTupleOut, prfEncReal_eq_prfEncRealOut]
  rw [key, key, distAdv_def,
    acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
      (fun s => encodeTupleOut (prfEncRealOut (F n) m s)),
    acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
      (fun s => encodeTupleOut (prfEncRealOut (F n) m' s)), ← distAdv_def]
  exact hb n m m'

/-- **Multi-message secure private-key encryption exists if a PRF exists** ([PS10, §3.9]):
the scheme of Algorithm 99.1 with the evaluator of `PRF.easy`. -/
theorem exists_multiMessageSecure_of_prf {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) : ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨E, hE, hFE⟩ := hF.easy
  ⟨prfScheme F E hE hFE, prfScheme_multiMessageSecure F hF E hE hFE⟩

/-- **Multi-message secure private-key encryption exists if a PRG exists** ([PS10, Theorems
97.3 and 99.2] combined): GGM gives a PRF, Algorithm 99.1 gives the scheme. -/
theorem exists_multiMessageSecure_of_exists_prg (h : ∃ P : PRG, P.Secure) :
    ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨_, hF⟩ := exists_prf_of_exists_prg h
  exists_multiMessageSecure_of_prf hF

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PrivateKey.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag
-- Preserve the facade's existing permutation-to-PRG and hard-core exports.
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key encryption

The ensemble games compare one ciphertext or a fixed vector of ciphertexts.
The oracle games give the adversary a query budget and specify its access to
encryption, the challenge and decryption.

## Main definitions

`TCSlib.Cryptography.PrivateKeyScheme` packages uniform polynomial-time algorithms
for key generation, encryption and decryption, with perfect correctness [PS10, Definition 24.7].
`TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure` and
`TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure` give the two ensemble games
[PS10, Definitions 91.1 and 93.1].
`TCSlib.Cryptography.Composability.FixedLengthScheme` adds a ciphertext length.
Its `indGame` defines the adaptive CPA, CCA1 and CCA2 games. `INDSecure` requires
negligible advantage in the selected game [PS10, Definition 168.1].

## Main results

`TCSlib.Cryptography.prgScheme_singleMessageSecure` proves single-message security
for the pad scheme given a secure PRG and a matching efficient evaluator
[PS10, Theorem 92.2].
`TCSlib.Cryptography.prfScheme_multiMessageSecure` proves security for fixed vectors
encrypted under one key with independent coins, given a PRF and a matching efficient
evaluator [PS10, Theorem 99.2].
`TCSlib.Cryptography.exists_multiMessageSecure_of_exists_prg` composes GGM with
the PRF scheme [PS10, Theorems 97.3 and 99.2].

## Contents

* `Encryption.PrivateKey.Scheme` gives the uniform polynomial-time scheme interface.
* `Encryption.PrivateKey.EnsembleSecurity` gives the ensemble games and their relations.
* `Encryption.PrivateKey.FromPRG` gives the PRG pad construction and its security proof.
* `Encryption.PrivateKey.FromPRF` gives the PRF scheme and its fixed-vector security proof
  [PS10, Algorithm 99.1 and Theorem 99.2].
* `Encryption.PrivateKey.FromPRF.Hybrid` proves the finite six-hybrid bound.
* `Encryption.PrivateKey.FromPRF.HybridLemmas` gives its probability and coin lemmas.
* `Encryption.PrivateKey.FromPRF.ReductionMachine` implements the next-query reduction.
* `Encryption.PrivateKey.FromPRF.MultiMsgOut` gives the multi-message bound at `ℓ`-bit outputs.
* `Encryption.PrivateKey.OracleSecurity` gives the fixed-length interface and adaptive oracle games.
* `Encryption.PrivateKey.OracleFromPRF` gives the fixed-length PRF scheme and its oracle claims.
  The CPA and CCA1 proofs `prfFixedScheme_cpa` and `prfFixedScheme_cca1` are pending
  [PS10, Theorem 168.2]. The CCA2 counterexample `prfFixedScheme_not_cca2` is proved
  [PS10, §7.1.3, Claim 169.a], and so is `not_prfFixedScheme_cca2`.
* `Encryption.PrivateKey.EncryptThenTag` gives the encrypt-then-tag scheme, which tags the
  whole ciphertext under an independent key [PS10, Algorithm 169.3].
  The CCA2 proof `ccaScheme_cca2` is pending [PS10, Theorem 170.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §2.1, §§3.6–3.9 and §7.1.3.
-/

## ===== TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/HybridLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PolyExpr
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probability and coin relabelling for PRF encryption

## Main definitions

The lemmas use the existing uniform expectations and finite oracle adversaries.

## Main results

* `MultiMsg.abs_uexp_sub_le_uprob` bounds the difference of two expectations by the
  probability of the event on which the functions can disagree.
* `MultiMsg.card_filter_lt_pairs` counts the pairs of distinct query indices in increasing order.
* `MultiMsg.negligible_choose_div_two_pow` proves negligibility of the collision term.
* `MultiMsg.prfAdv_congr_equiv` transports the PRF advantage along a bijection of coins
  when the two adversaries agree on every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography.MultiMsg

open Complexity Turing Finset

/-! ### Probability: coupling, pair counting, the collision term -/

/-- The absolute value of an average is at most the average of the absolute values. -/
theorem abs_uexp_le_uexp_abs {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    |uexp f| ≤ uexp fun ω => |f ω| := by
  rw [uexp_def, uexp_def]
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- **The coupling bound**: two `[0,1]`-valued functions on a finite sample space that agree
outside the event `E` have averages at most `Pr[E]` apart (the "two experiments that agree
on an event `E` have advantage `≤ Pr[¬E]`" step of [PS10, Theorem 99.2, proof, `H²` vs `H³`]).

**Proof sketch.** `|E a − E b| = |E (a − b)| ≤ E |a − b|` (`abs_uexp_le_uexp_abs`), and
pointwise `|a − b| ≤ [E]` since the difference vanishes off `E` and is at most `1` on it. -/
theorem abs_uexp_sub_le_uprob {Ω : Type*} [Fintype Ω] (a b : Ω → ℝ) (E : Ω → Prop)
    [DecidablePred E] (ha : ∀ ω, 0 ≤ a ω ∧ a ω ≤ 1) (hb : ∀ ω, 0 ≤ b ω ∧ b ω ≤ 1)
    (heq : ∀ ω, ¬ E ω → a ω = b ω) :
    |uexp a - uexp b| ≤ uprob E := by
  rw [← HardcoreBit.uexp_sub, uprob_eq_uexp]
  refine (abs_uexp_le_uexp_abs _).trans (HardcoreBit.uexp_mono fun ω => ?_)
  by_cases hE : E ω
  · rw [if_pos hE]
    obtain ⟨h1, h2⟩ := ha ω
    obtain ⟨h3, h4⟩ := hb ω
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · rw [if_neg hE, heq ω hE, sub_self, abs_zero]

/-- **Counting the pairs `i < j`**: there are `C(k, 2)` pairs `(i, j)` with `i < j` in
`Fin k × Fin k` (the `C(q(n)+1, 2)` of the birthday bound of [PS10, Theorem 99.2]).

**Proof sketch.** The pairs `i < j` and their swaps partition the off-diagonal of
`Fin k × Fin k`, which has `k² − k` elements (`Finset.offDiag_card`); the swap is injective,
so `2 · #{i < j} = k(k − 1)` and `Nat.choose_two_right` finishes. -/
theorem card_filter_lt_pairs (k : ℕ) :
    ((univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2).card = k.choose 2 := by
  set S := (univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2 with hS
  have hunion : S ∪ S.image Prod.swap = (univ : Finset (Fin k)).offDiag := by
    ext ⟨i, j⟩
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_offDiag, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨a, b, hab, rfl, rfl⟩)
      · exact ne_of_lt h
      · exact ne_of_gt hab
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr ⟨j, i, h, rfl, rfl⟩
  have hdisj : Disjoint S (S.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hij hji
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq] at hji
    obtain ⟨a, b, hab, rfl, rfl⟩ := hji
    exact absurd hij (not_lt.2 hab.le)
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Prod.swap_injective,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  omega

/-- Two independent uniform elements of a nonempty finite type coincide with probability
`1 / |α|` (Fubini and `OneWay.uprob_eq_one_div_card`). -/
theorem uprob_eq_pair {α : Type*} [Fintype α] [Nonempty α] :
    uprob (fun z : α × α => z.1 = z.2) = 1 / Fintype.card α := by
  rw [uprob_prod]
  have h : ∀ a : α, uprob (fun b : α => a = b) = 1 / Fintype.card α := by
    intro a
    rw [← OneWay.uprob_eq_one_div_card a]
    exact uprob_congr fun b => eq_comm
  simp_rw [h]
  exact HardcoreBit.uexp_const _

/-- **The collision term is negligible**: `n ↦ C(q(n)+1, 2) / 2^n` is negligible for every
syntactic polynomial `q` ([PS10, Theorem 99.2, proof: the collision probability is
negligible]).

**Proof sketch.** `C(k, 2) ≤ k²` (`Nat.choose_le_pow`) and `q(n) + 1 ≤ (C+1)(n+1)^c ≤
(C+1) 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), so the term is at most a constant times
`n^{2c} · 2^{−n}`, negligible by `negligible_two_pow_neg`, `Negligible.mul_pow` and
`Negligible.const_mul`; conclude with `Negligible.mono`. -/
theorem negligible_choose_div_two_pow (q : PolyExpr) :
    Negligible fun n => (Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n := by
  obtain ⟨C, c, hC⟩ := q.eval_le
  have hν : Negligible fun n =>
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow (2 * c)).const_mul _
  refine hν.mono ⟨1, fun n hn => ?_⟩
  have hnat : Nat.choose (q.eval n + 1) 2 ≤ ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by
    have h1 : q.eval n + 1 ≤ (C + 1) * (n + 1) ^ c := by
      have := hC n
      have hp : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos n)
      nlinarith
    have h2 : (n + 1) ^ c ≤ (2 * n) ^ c := Nat.pow_le_pow_left (by omega) c
    calc Nat.choose (q.eval n + 1) 2 ≤ (q.eval n + 1) ^ 2 := Nat.choose_le_pow _ _
      _ ≤ ((C + 1) * (2 * n) ^ c) ^ 2 :=
          Nat.pow_le_pow_left (h1.trans (Nat.mul_le_mul_left _ h2)) 2
      _ = ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by ring
  have hR : (Nat.choose (q.eval n + 1) 2 : ℝ) ≤
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) := by
    exact_mod_cast hnat
  have hinv : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv, ← inv_pow]
  calc (Nat.choose (q.eval n + 1) 2 : ℝ) * (2 : ℝ)⁻¹ ^ n
      ≤ ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hR hinv
    _ = _ := by ring

/-! ### Oracle adversaries: coin relabelling -/

/-- Relabelling the coins of an oracle adversary by a bijection preserves its acceptance
probability against every oracle sampler, provided the two trees agree on every oracle. -/
theorem acceptProb_oracleDist_congr_equiv {σ : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype σ] [Fintype ρ]
    [Fintype ρ'] (X : σ → I → O) (A : OracleAdversary ρ I O) (A' : OracleAdversary ρ' I O)
    (φ : ρ' ≃ ρ) (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    acceptProb X (oracleDist A) = acceptProb X (oracleDist A') := by
  simp only [acceptProb_def, oracleDist_apply]
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr φ)]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, h]

/-- **Coin relabelling preserves the PRF advantage**: oracle adversaries whose trees agree on
every oracle after a bijective relabelling of the coins have the same `prfAdv`. -/
theorem prfAdv_congr_equiv {K : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype ρ] [Fintype ρ'] (F : K → I → O) (A : OracleAdversary ρ I O)
    (A' : OracleAdversary ρ' I O) (φ : ρ' ≃ ρ)
    (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    prfAdv F A = prfAdv F A' := by
  have hF := acceptProb_oracleDist_congr_equiv F A A' φ h
  have hR := acceptProb_oracleDist_congr_equiv (id : (I → O) → I → O) A A' φ h
  simp only [acceptProb_def, oracleDist_apply, id_eq] at hF hR
  rw [prfAdv_eq, prfAdv_eq, hF, hR]

end TCSlib.Cryptography.MultiMsg

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joint, length-generic multi-message security of special encryption (statement phase)

[PS10, Algorithm 157.2] encrypts `m` as `⟨r, (0^n ‖ m) ⊕ f_k(r)⟩`. Yao's protocol uses it in two
layers with two pseudorandom families `G₁` (`2n`-bit outputs, `n`-bit messages) and `G₂`
(`n + (4n + 2)`-bit outputs, `(4n + 2)`-bit messages), and one wire key may key both
(`GarblingSpecial.lean`, `Yao.lean`). The hybrid of `yaoHybrid_simulators` (step 3) needs
multi-message security of both layers *under one key*. Under the joint hypothesis `hG₁₂`, both
layers read their pads from one family `G = G₁ ‖ G₂`, at different offsets.

This module states that property for any `PRFOut` family `G` with `ℓ(n)`-bit outputs. A
ciphertext is cut from a **slice** of `G_k(r)`: the pad of the `i`-th ciphertext is
`G_k(r_i)_{[o_i, o_i + n + ℓ_i)}` for an offset `o_i` and a message length `ℓ_i`, both chosen
per ciphertext. Polynomially many slice ciphertexts under one key `k ← U_n`, with independent
nonces `r_i ← U_n`, are indistinguishable for any two message vectors, uniformly in the slices.
The frozen `specialScheme_multiMessageSecure` (one family, `n`-bit messages) is the corollary
with every slice `(0, n)` (`specialScheme_multiMessageSecure_of_joint`, proved here).

**Placement.** A new module beside `SpecialEncryptionSecurity.lean`, not inside it: this
statement PR is additive and leaves that file (frozen statements, owned by the garbling unit)
byte-identical. It imports `SpecialEncryptionSecurity` for `PRFOut` and `specialScheme`;
`yaoHybrid_simulators`' helper modules import it.

**B3.** The statement uses only existing definitions (`PRFOut`, `spEncStr`, the private-key
`encodeList`, `distAdv`, `NUPPT.distinguisherL`). Its proof needs the PRF hybrid machinery with
`ℓ`-bit outputs, which the separate job `prf-long` provides (ruling B3, 2026-11-14).

## Main definitions

* `SecureComputation.sliceEnc`: Algorithm 157.2 with the pad `G_k(r)_{≥o}` (a slice of `G_k(r)`).
* `SecureComputation.sliceMultiEncDist`: `q + 1` slice ciphertexts under one key.
* `SecureComputation.SliceMultiMessageSecure`: their indistinguishability for any two message
  vectors, uniformly in the slices.

## Main results

* `SecureComputation.sliceMultiMessageSecure_of_prfOut` (stated; `sorry` under a sketch): every
  `PRFOut` family is slice multi-message secure (ruling B1, 2026-11-14).
* `SecureComputation.specialScheme_multiMessageSecure_of_joint` (proved): the frozen Claim
  157.a (i) follows.
* `SecureComputation.sliceEnc_eq_spEncStr`, `sliceEnc_append_left`, `sliceEnc_append_right`
  (proved): slice ciphertexts are special ciphertexts, in particular those of the two layers of
  `nestedSpecial` under `G₁ ‖ G₂`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.7 (Definition 93.1, Theorem 99.2) and §6.2.2 (Algorithm 157.2, book pp. 156–157).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party computation*,
  Journal of Cryptology 22(2), 2009, pp. 161–188 (the hybrid with one inactive key per step).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-! ### Slice ciphertexts -/

/-- **A slice ciphertext**: Algorithm 157.2 [PS10, §6.2.2] under the key `k` with nonce `r`, whose
pad is the slice `p = G_k(r)_{≥o}` of the family's output from offset `o`. That is `spEncStr`
with the constant evaluator `p`, the ciphertext `⟨r, p_{<n} ‖ (m ⊕ p_{≥n})⟩`, where `m` uses
the pad bits `G_k(r)_{[o + n, o + n + |m|)}`. -/
def sliceEnc {L : ℕ → ℕ} (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) : List Bool :=
  spEncStr (fun _ => (List.ofFn (G n k r)).drop o) (List.ofFn k) m (List.ofFn r)

/-- A slice ciphertext is `spEncStr` with the constant pad `G_k(r)_{≥o}`:
`sliceEnc G n o k r m = spEncStr (fun _ => ⟦G_k(r)⟧.drop o) ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_eq {L : ℕ → ℕ} (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n o k r m =
      spEncStr (fun _ => (List.ofFn (G n k r)).drop o) (List.ofFn k) m (List.ofFn r) := rfl

/-- **Slices of an evaluated family**: if `E` evaluates `G` (`E(⟨s, x⟩) = G_s(x)`), the slice
ciphertext from offset `o` is the special ciphertext with the evaluator `z ↦ E(z)_{≥o}`:
`sliceEnc G n o k r m = spEncStr (fun z => (E z).drop o) ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_eq_spEncStr {L : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)} {E : List Bool → List Bool}
    (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G n s x))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n o k r m = spEncStr (fun z => (E z).drop o) (List.ofFn k) m (List.ofFn r) := by
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE]

/-- Masking with a longer pad uses only its first `|m|` bits. -/
private theorem zipWith_xor_append_of_le : ∀ (m p b : List Bool), m.length ≤ p.length →
    List.zipWith xor m (p ++ b) = List.zipWith xor m p
  | [], _, _, _ => by simp
  | _ :: _, [], _, h => by simp at h
  | a :: m, c :: p, b, h => by
    simp only [List.cons_append, List.zipWith_cons_cons, List.cons.injEq, true_and]
    exact zipWith_xor_append_of_le m p b (by simpa using h)

/-- **The inner layer as a slice of `G₁ ‖ G₂`**: if `⟦G_k(r)⟧ = ⟦G₁_k(r)⟧ ++ ⟦G₂_k(r)⟧` and `E₁`
evaluates `G₁` (`2n`-bit outputs), then for `|m| ≤ n` the slice from offset `0` is the
`G₁`-ciphertext: `sliceEnc G n 0 k r m = spEncStr E₁ ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_append_left {L L₂ : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)}
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool)} {E₁ : List Bool → List Bool}
    (hG : ∀ n (s x : Fin n → Bool),
      List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x))
    (n : ℕ) (k r : Fin n → Bool) {m : List Bool} (hm : m.length ≤ n) :
    sliceEnc G n 0 k r m = spEncStr E₁ (List.ofFn k) m (List.ofFn r) := by
  have h₁ : (List.ofFn (G₁ n k r)).length = n + n := List.length_ofFn
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE₁, List.drop_zero, hG, List.length_ofFn,
    List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    zipWith_xor_append_of_le _ _ _ (by rw [List.length_drop]; omega)]

/-- **The outer layer as a slice of `G₁ ‖ G₂`**: if `⟦G_k(r)⟧ = ⟦G₁_k(r)⟧ ++ ⟦G₂_k(r)⟧` with `G₁`
of `2n`-bit outputs and `E₂` evaluates `G₂`, the slice from offset `2n` is the `G₂`-ciphertext:
`sliceEnc G n (n + n) k r m = spEncStr E₂ ⟦k⟧ m ⟦r⟧`, for every message `m`. -/
theorem sliceEnc_append_right {L L₂ : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)}
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool)} {E₂ : List Bool → List Bool}
    (hG : ∀ n (s x : Fin n → Bool),
      List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
    (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₂ n s x))
    (n : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n (n + n) k r m = spEncStr E₂ (List.ofFn k) m (List.ofFn r) := by
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE₂, hG, List.drop_left' List.length_ofFn]

/-! ### Joint multi-message security -/

/-- **`q + 1` slice ciphertexts under one key** (the sampler of [PS10, Definition 93.1], with
slices): from the key `k` and the nonces `r_0, …, r_q` (the seed `(k, r)`, uniform), the
`encodeList` of `sliceEnc G n o_i k r_i m_i` for `i ≤ q`, i.e. of
`⟨r_i, (0^n ‖ m_i) ⊕ G_k(r_i)_{[o_i, o_i + n + ℓ_i)}⟩` with `m_i ∈ {0,1}^{ℓ_i}`. -/
def sliceMultiEncDist {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) (n q : ℕ)
    (o len : Fin (q + 1) → ℕ) (m : ∀ i, Fin (len i) → Bool) :
    (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) → List Bool :=
  fun t => PrivateKeyScheme.encodeList
    (List.ofFn fun i => sliceEnc G n (o i) t.1 (t.2 i) (List.ofFn (m i)))

/-- The slice sampler at the seed `t = (k, r)` is the `encodeList` of the `q + 1` ciphertexts
`sliceEnc G n o_i k r_i ⟦m_i⟧`. -/
theorem sliceMultiEncDist_apply {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) (n q : ℕ)
    (o len : Fin (q + 1) → ℕ) (m : ∀ i, Fin (len i) → Bool)
    (t : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) :
    sliceMultiEncDist G n q o len m t = PrivateKeyScheme.encodeList
      (List.ofFn fun i => sliceEnc G n (o i) t.1 (t.2 i) (List.ofFn (m i))) := rfl

/-- **Slice multi-message security** of a family `G` with `L(n)`-bit outputs ([PS10,
Definition 93.1], with slices and one key): for every non-uniform PPT `D` and polynomial `q`
there is a negligible `ε` such that for all `n`, all offsets and lengths `o, ℓ ∈ ℕ^{q(n)+1}`
with `o_i + n + ℓ_i ≤ L(n)`, and all `m, m'` with `m_i, m'_i ∈ {0,1}^{ℓ_i}`,
`|Pr[k, r ← U : D(1^n, ⟨Enc^{o_i}_k(m_i; r_i)⟩_i) = 1] − Pr[… m' …]| ≤ ε(n)`, where
`Enc^o_k(m; r) = sliceEnc G n o k r m`.

`ε` precedes the slices as well as the messages, so a reduction may choose the slices by advice.
With every slice `(0, n)` and `L(n) = 2n` this is `PrivateKeyScheme.MultiMessageSecure` of
`specialScheme` (`specialScheme_multiMessageSecure_of_joint`).

**Deviation:** `D` receives `1^n`; the ciphertexts are encoded by `encodeList` (as in
`MultiMessageSecure`). -/
def SliceMultiMessageSecure {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (o len : Fin (q.eval n + 1) → ℕ), (∀ i, o i + n + len i ≤ L n) →
      ∀ m m' : ∀ i, Fin (len i) → Bool,
        distAdv (sliceMultiEncDist G n (q.eval n) o len m)
          (sliceMultiEncDist G n (q.eval n) o len m') (D.distinguisherL n) ≤ ε n

/-- The defining property of `SliceMultiMessageSecure`: for every `D` and `q` a negligible `ε`
bounds `D`'s advantage between the slice ciphertexts of any two message vectors, for every
slice vector that fits in `L(n)`. -/
theorem sliceMultiMessageSecure_iff {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) :
    SliceMultiMessageSecure G ↔ ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (o len : Fin (q.eval n + 1) → ℕ), (∀ i, o i + n + len i ≤ L n) →
        ∀ m m' : ∀ i, Fin (len i) → Bool,
          distAdv (sliceMultiEncDist G n (q.eval n) o len m)
            (sliceMultiEncDist G n (q.eval n) o len m') (D.distinguisherL n) ≤ ε n := Iff.rfl

/-- **Joint, length-generic multi-message security** (ruling B1, 2026-11-14) [PS10, §6.2.2, "it
is easy to modify construction 99.1"; Definition 93.1, Theorem 99.2]: every pseudorandom family
`G` with `ℓ(n)`-bit outputs (`PRFOut ℓ G`) is slice multi-message secure. For every
non-uniform PPT `D` and polynomial `q` there is a negligible `ε` with, for all `n`, all slices
`(o_i, ℓ_i)_{i ≤ q(n)}` with `o_i + n + ℓ_i ≤ ℓ(n)` and all `m, m'` with `|m_i| = |m'_i| = ℓ_i`,
`|Pr[D(1^n, ⟨r_i, (0^n ‖ m_i) ⊕ G_k(r_i)_{[o_i, o_i+n+ℓ_i)}⟩_i) = 1] − Pr[… m' …]| ≤ ε(n)`
over `k, r_0, …, r_{q(n)} ← U_n`.

**Corollaries.**
- `specialScheme_multiMessageSecure` (frozen Claim 157.a (i)) is
  `specialScheme_multiMessageSecure_of_joint G E hE hGE (sliceMultiMessageSecure_of_prfOut hG)`:
  every slice is `(0, n)` and `ℓ(n) = 2n`.
- Step 3 of `yaoHybrid_simulators` takes `G = G₁ ‖ G₂` under `hG₁₂`, with
  `ℓ(n) = 2n + (n + (4n + 2))`. The rows under the inactive key `ι_u` where `u` is a second or
  only argument are slices `(0, n)` (`sliceEnc_append_left`: the `G₁`-ciphertexts
  `spEncStr E₁`). Those where `u` is a first argument are slices `(2n, 4n + 2)`
  (`sliceEnc_append_right`: the `G₂`-ciphertexts `spEncStr E₂`). Both shapes fit; the outer
  slice fits exactly. The bound is uniform in the slices, so the reduction's advice may fix
  which rows, of which layer, it embeds.

**Deviations.** [PS10] states the claim for one scheme and `n`-bit messages. Here the claim is
length-generic and joint: the pads of different ciphertexts may come from different slices
of one family under one key. The fit `o_i + n + ℓ_i ≤ ℓ(n)` keeps every pad inside `G_k(r_i)`.

**Proof sketch.** As [PS10, Theorem 99.2] (`prfScheme_multiMessageSecure`), with `ℓ`-bit
outputs. Fix `n` and let `A(n)` be `D`'s largest advantage over the finitely many fitting slice
vectors and message pairs (each `o_i, ℓ_i ≤ ℓ(n)`).
1. *PRF step.* For `b ∈ {0, 1}` the oracle machine `D_b` has as advice the maximizing slices and
   the message vector `m` (`b = 0`) or `m'` (`b = 1`), all of polynomial length. It draws the
   `r_i`, queries `O(r_i)` once each (`q(n) + 1` queries), forms each ciphertext from the slice
   of the answer, and runs `D`. Against `G_k` it is the slice sampler; against a random function
   `F` with `ℓ(n)`-bit outputs it is the same sampler for `F`. Its advantage is negligible by
   `hG.pseudorandom`.
2. *Random function.* If the `r_i` are distinct, the values `F(r_i)` are independent and uniform.
   Within one ciphertext the revealed prefix and the mask are disjoint bits of the slice, so each
   ciphertext is `⟨r_i, u_i⟩` with `u_i` uniform of length `n + ℓ_i`, whatever the message. The
   laws for `m` and `m'` agree off the collision event, which has probability at most
   `C(q(n) + 1, 2) · 2^{-n}` (`MultiMsg.negligible_choose_div_two_pow`).
3. *Total.* `A(n) ≤ adv(D_0) + adv(D_1) + C(q(n) + 1, 2) · 2^{-n}`, which is negligible. Take
   `ε = A`. The ℓ-output PRF hybrid machinery is supplied by `prf-long` (ruling B3). -/
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G := by
  sorry

/-! ### The frozen Claim 157.a (i) as a corollary -/

section Corollary

variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G n s x))

/-- The key generator of `specialScheme` outputs its coins: `Gen(1^n; rg) = ⟦rg⟧`. -/
private theorem specialScheme_gen_runAt (n : ℕ) :
    ∀ rg : (specialScheme G E hE hGE).gen.Coins n,
      (specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg := by
  rw [specialScheme_gen]
  intro rg
  exact runAt_coinKey .var n rg

/-- The encryption machine of `specialScheme` is `spEncStr` with its coins as the nonce. -/
private theorem specialScheme_enc_runAt (n : ℕ) :
    ∀ (k m : List Bool) (re : (specialScheme G E hE hGE).enc.Coins n),
      (specialScheme G E hE hGE).enc.runAt n (pairEncode k m) re =
        spEncStr E k m (List.ofFn re) := by
  rw [specialScheme_enc]
  intro k m re
  exact runAt_spEnc hE .var n k m re

/-- The key coins of `specialScheme` as an `n`-bit key, keeping the string. -/
private noncomputable def specialKeyEq (n : ℕ) :
    (specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦specialKeyEq n rg⟧ = ⟦rg⟧`. -/
private theorem ofFn_specialKeyEq (n : ℕ) (rg : (specialScheme G E hE hGE).gen.Coins n) :
    List.ofFn (specialKeyEq G E hE hGE n rg) = List.ofFn rg := by
  rw [specialKeyEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- The encryption coins of `specialScheme` as an `n`-bit nonce, keeping the string. -/
private noncomputable def specialNonceEq (n : ℕ) :
    (specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦specialNonceEq n re⟧ = ⟦re⟧`. -/
private theorem ofFn_specialNonceEq (n : ℕ) (re : (specialScheme G E hE hGE).enc.Coins n) :
    List.ofFn (specialNonceEq G E hE hGE n re) = List.ofFn re := by
  rw [specialNonceEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- **The frozen Claim 157.a (i) from the joint lemma** [PS10, §6.2.2, Definition 93.1]: if the
length-doubling family `G` is slice multi-message secure, then `specialScheme G E hE hGE` is
multi-message secure. With `sliceMultiMessageSecure_of_prfOut` this gives
`specialScheme_multiMessageSecure`.

**Proof sketch.** Take every slice to be `(0, n)`; it fits, as `0 + n + n ≤ 2n`. Relabel the
coins of `Gen` and `Enc` as an `n`-bit key and `n`-bit nonces, keeping their strings. Under this
bijection the scheme's multi-message sampler is the slice sampler pointwise: `Gen` outputs its
coins (`runAt_coinKey`), `Enc` is `spEncStr E` (`runAt_spEnc`), and a slice from offset `0` is
`spEncStr E` (`sliceEnc_eq_spEncStr`). Acceptance probabilities are invariant under relabelling
the seed (`acceptProb_comp_equiv`), so the slice bound applies verbatim. -/
theorem specialScheme_multiMessageSecure_of_joint (h : SliceMultiMessageSecure G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  rw [PrivateKeyScheme.multiMessageSecure_iff]
  intro D q
  obtain ⟨ε, hε, hb⟩ := (sliceMultiMessageSecure_iff G).mp h D q
  refine ⟨ε, hε, fun n m m' => ?_⟩
  let e : (specialScheme G E hE hGE).gen.Coins n ×
      (Fin (q.eval n + 1) → (specialScheme G E hE hGE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) :=
    (specialKeyEq G E hE hGE n).prodCongr
      (Equiv.piCongrRight fun _ => specialNonceEq G E hE hGE n)
  have hX : ∀ v : Fin (q.eval n + 1) → Fin n → Bool,
      (specialScheme G E hE hGE).multiEncDist n (q.eval n) v =
        fun t => sliceMultiEncDist G n (q.eval n) (fun _ => 0) (fun _ => n) v (e t) := by
    intro v
    funext t
    rw [PrivateKeyScheme.multiEncDist_apply, sliceMultiEncDist_apply]
    refine congrArg PrivateKeyScheme.encodeList (congrArg List.ofFn (funext fun i => ?_))
    rw [specialScheme_gen_runAt, specialScheme_enc_runAt, sliceEnc_eq_spEncStr hGE]
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.piCongrRight_apply,
      Pi.map_apply, List.drop_zero, ofFn_specialKeyEq, ofFn_specialNonceEq]
  rw [distAdv_def, hX m, hX m', acceptProb_comp_equiv, acceptProb_comp_equiv, ← distAdv_def]
  exact hb n (fun _ => 0) (fun _ => n) (fun _ => by show 0 + n + n ≤ n + n; omega) m m'

end Corollary

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The special encryption scheme of Yao's protocol: security (statement phase)

[PS10, Algorithm 157.2] as a `PrivateKeyScheme`, and Claim 157.a (inventory): the scheme is
multi-message secure, and a ciphertext decrypted under an independent key gives `⊥` except with
negligible probability ([PS10, §6.2.2], "the extra property"). The algorithms are in
`SpecialEncryption.lean`.

**The length-doubling PRF.** It is a keyed family with `n`-bit keys and inputs and `2n`-bit
outputs, pseudorandom as an oracle ensemble against random functions with `2n`-bit outputs
(`PRFOut`). This is the ch. 2–4 layer's Definition 96.2 (`PRF`) with the output length a
parameter; `OracleEnsemble.keyed` already allows any output length.

## Main definitions

* `SecureComputation.PRFOut`: a pseudorandom function family with `ℓ₂(n)`-bit outputs.
* `SecureComputation.specialScheme`: Algorithm 157.2 as a `PrivateKeyScheme` (`n`-bit messages),
  correctness proved.

## Main results

* `SecureComputation.specialScheme_multiMessageSecure`, `spDecStr_wrongKey`,
  `specialScheme_wrongKey` (Claim 157.a, stated; `sorry`s under sketches).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Algorithm 157.2 (book pp. 156–157), and Definitions 93.1 and 96.2.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-! ### Pseudorandom functions with any output length -/

/-- **A pseudorandom function family with `ℓ₂(n)`-bit outputs** [PS10, Definition 96.2, with the
output length a parameter]: keys and inputs of `n` bits. (1) A polynomial-time evaluator `E`
computes `f_s(x)` from `⟨s, x⟩`. (2) The keyed ensemble `{s ← U_n : f_s}` is
oracle-indistinguishable from the random functions `{0,1}^n → {0,1}^{ℓ₂(n)}`. With `ℓ₂ = n + n`
it is the source's length-doubling family. -/
structure PRFOut (ℓ₂ : PolyExpr)
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)) : Prop where
  /-- Clause (1): `f_s(x)` is polynomial-time computable from `⟨s, x⟩`. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x)
  /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF : F}` as oracle ensembles. -/
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) G).Indist
    (OracleEnsemble.random .var ℓ₂)

/-- With `n`-bit outputs, `PRFOut` is the ch. 2–4 layer's `PRF` (duplication-ledger item DL-8:
`PRFOut` generalizes `PRF`, and agrees with it at `ℓ₂ = n`). -/
theorem prfOut_var_iff (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) :
    PRFOut .var F ↔ PRF F :=
  ⟨fun h => ⟨h.easy, h.pseudorandom⟩, fun h => ⟨h.easy, h.pseudorandom⟩⟩

variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G n s x))

/-- **The special encryption scheme** [PS10, Algorithm 157.2] as a `PrivateKeyScheme` with
`n`-bit messages, for a length-doubling family `G` with evaluator `E`: the key is `Gen`'s `n`
coins, `Enc` draws `r` as its `n` coins, and `Dec` is deterministic. -/
@[simps (config := { isSimp := false }) gen enc dec]
noncomputable def specialScheme : PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_spDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_spEnc hE, runAt_spDec hE]
    have hk : (List.ofFn rg).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hr : (List.ofFn re).length = n := by
      rw [List.length_ofFn, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform,
        PolyExpr.eval_var]
    have hp : (E (pairEncode (List.ofFn rg) (List.ofFn re))).length = n + n := by
      have hrg := (List.length_ofFn (f := rg)).symm.trans hk
      have hre := (List.length_ofFn (f := re)).symm.trans hr
      rw [List.ofFn_congr hrg rg, List.ofFn_congr hre re, hGE, List.length_ofFn]
    rw [spDecStr_spEncStr E hk (by simp) hr hp, Option.getD_some]
    exact decodeFin_ofFn m

/-! ### Claim 157.a -/

/-- **Claim 157.a (i): the special scheme is multi-message secure** [PS10, §6.2.2, "it is easy to
modify construction 99.1"] when `G` is a length-doubling PRF.

**Proof sketch.** As [PS10, Theorem 99.2] for Algorithm 99.1 (`prfScheme_multiMessageSecure`):
replace `f_k` by a random function with `2n`-bit outputs (PRF security, one oracle query per
ciphertext); then the pads of distinct `r`'s are independent uniform `2n`-bit strings, so the
ciphertexts are independent of the messages unless two `r`'s collide, with probability at most
`C(q(n)+1, 2) · 2^{-n}`. The zero prefix `0^n` is masked like the message. -/
theorem specialScheme_multiMessageSecure (hG : PRFOut (.add .var .var) G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  sorry

/-- **Claim 157.a (ii), on strings: a wrong key gives `⊥`** [PS10, §6.2.2, "the extra property"]
for any polynomial message length `ℓ`: for `G` a PRF with `n + ℓ(n)`-bit outputs and every
`ℓ(n)`-bit message, encrypting under `k` and decrypting under an independent `k'` gives `⊥`
except with negligible probability.

**Proof sketch.** Decryption under `k'` succeeds only if `f_k(r)_{<n} = f_{k'}(r)_{<n}`. The
distinguisher with oracle `O` samples `k'` and `r`, queries `O(r)`, and accepts iff the first `n`
bits agree with `f_{k'}(r)`. Against a random function this has probability `2^{-n}`, so against
`f_k` it has probability at most `2^{-n}` plus the PRF advantage: negligible. The guard does not
fire on honest ciphertexts. -/
theorem spDecStr_wrongKey (ℓ : PolyExpr)
    (G' : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
    (E' : List Bool → List Bool)
    (hGE' : ∀ n (s x : Fin n → Bool), E' (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G' n s x))
    (hG' : PRFOut (.add .var ℓ) G') :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin (ℓ.eval n) → Bool),
      1 - ε n < uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        spDecStr E' n (ℓ.eval n) (List.ofFn t.2.1)
          (spEncStr E' (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none) := by
  sorry

/-- **Claim 157.a (ii) for the scheme**: under an independent key, `Dec` returns `⊥` (an output
that decodes to no `n`-bit message) except with negligible probability, the source's
`Pr[k, k' ← Gen(1^n), c ← Enc_k(m) : Dec_{k'}(c) = ⊥] > 1 − ε(n)`.

**Proof sketch.** `runAt_spEnc` and `runAt_spDec` reduce it to `spDecStr_wrongKey` at `ℓ = n`;
the `⊥` string `1^{n+1}` decodes to no `n`-bit message, and a `some` output has `n` bits. -/
theorem specialScheme_wrongKey (hG : PRFOut (.add .var .var) G) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin n → Bool),
      1 - ε n < uprob (fun t : (specialScheme G E hE hGE).gen.Coins n ×
          (specialScheme G E hE hGE).gen.Coins n × (specialScheme G E hE hGE).enc.Coins n ×
          (specialScheme G E hE hGE).dec.Coins n =>
        decodeFin n ((specialScheme G E hE hGE).dec.runAt n
          (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.2.1)
            ((specialScheme G E hE hGE).enc.runAt n
              (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.1) (List.ofFn m)) t.2.2.1))
          t.2.2.2) = none) := by
  sorry

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryption.lean =====

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
