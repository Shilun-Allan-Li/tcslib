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
