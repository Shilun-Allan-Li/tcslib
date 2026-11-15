# Gate 36 · Special encryption and garbling probability (`sc-garble`, U1, [PS10, §6.2.2–6.2.3])

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #323](https://github.com/Shilun-Allan-Li/tcslib/pull/323) at
  `cd9a48438c2a6548fe9e246ce569be57c9df96b3` (branch `land/pass-shelat-sc-garble`, tree
  `13aa553d035fd55cf73c7123ebb73c1940019f1c`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `1321b9cb358867f5b51974b8c5d0781519a9cfdb` (the merge base: the records tip after #317 and #316 merged).
  - The fill was issued on `fbd37f447596d4207c8d08b7ef7602f57fe95198`, the head of #315 (prf-long), under the
    proved-modulo rule: the proof uses prf-long's D1–D4. #315 has since merged (`10b9be17`), then #314, #317 and #316;
    their 10 Lean files are not in the PR. The 14 PR paths are byte-identical at the issue base and at `1321b9cb`
    (`pack-checks/rebase.txt`), and the review's build covers the delta (below).
  - The records tip is now `540bac18ce13cb8ef37b7dc41d97de5d2deaf661`; it is records only since `1321b9cb`, so the
    PR is current with the tip.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...cd9a4843`, which equals `1321b9cb..cd9a4843`
    byte for byte (14 paths, 1901 insertions, 122 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #313, #318, #319 and #324 is
    clean in each case, and no path is shared (`pack-checks/mergetrees.txt`). **Pending merge condition** (not an audit
    item): whichever of #323 and each open PR with a shared downstream merges second needs an integration rebuild on
    the merged tip; the maintainer runs these builds (question 7).
- **Commits:** 8, all committed by Claude and SSH-signed (`pack-checks/rebase.txt`).
  - The Codex worker's 7 commits (job `sc-garble`, on Seyoon's Mac under the host addendum; author Seyoon Ragavan),
    delivered with `commit.gpgsign=false` and a `COMMITS.tsv` signing column (`none` throughout). `git am` at the issue
    base with the delivered committer data reproduces all 7 hashes unsigned (review `logs/git-am-integrity.log`). They
    were rebased onto `1321b9cb` without conflict, author kept: `git range-diff fbd37f44..81795f77 1321b9cb..e5cb6129`
    is 7/7 `=`. At `e5cb6129` the 14 files are byte-identical to the worker's `src/` (exchange `a73072f1`).
  - Landing edit **LE-doc** `cd9a48438c2a6548fe9e246ce569be57c9df96b3` (the head): docstrings only, 3 files.
- **Scope:** a **proof audit** of seven admitted, frozen statements, and the stronger garbling bound B2:

  | Target | File | Source |
  |---|---|---|
  | `spDecStr_wrongKey` | `SpecialEncryptionSecurity.lean` | Claim 157.a (ii), strings |
  | `specialScheme_wrongKey` | the same | Claim 157.a (ii), the scheme |
  | `specialScheme_multiMessageSecure` | the same | Claim 157.a (i); Definition 93.1, Theorem 99.2 |
  | `nestedSpecial_wrongKeyBot` | `GarblingSecurity.lean` | Claim 157.a (ii) for the nesting |
  | `uprob_not_good_le` | `Garbling.lean` | Claim 159.a, probabilistic part |
  | `yaoSeed_good_whp` (that body only) | `Yao.lean` (shared with `sc-yao`) | Claim 159.a for Protocol 162.6's seed |
  | `sliceMultiMessageSecure_of_prfOut` (B1) | `SpecialEncryptionMulti.lean` | §6.2.2, Theorem 99.2 with slices; [LP09] |
  | **B2** `uprob_not_good_le_of_perm` (new) | `Garbling.lean` | Claim 159.a, fixed-permutation form |

  The first six passed the prong statement phase and Gate 06; B1 passed Gate 27 (CLEAR) and merged in #311. All seven
  are quoted in the brief. Their consumer `garbling_good_whp` (unchanged) now uses only the standard axioms.
- **Brief:** `fills/sc-garble/issued-r1/brief.md` (SHA-256 `203d42ea…`) with **ruling SG-1** (`ruling-SG-1.md`, which
  overrides the brief where they differ). Three checkpoints (the wrong-key property; B2 and Yao's seed; B1 and Claim
  157.a (i)). Five owned files, four helper directories, every other file frozen; `Yao.lean` stricter. The import
  direction for `specialScheme_multiMessageSecure`; the B1 consumer map; Gate 27's hand-off obligations (1)–(6); the
  binding duplication rule with an `## Overlap and reuse` section; Rule 10 with the projection-coercion ruling and seals
  with `PolyExpr.eval` both excluded and sealed; the docstring and sketch rules; the G26-N1 error count; the
  evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/SecureComputation/` unless they start with `TCSlib/`. The PR touches 14 Lean
files: 6 modified (the 5 owned files and `DAGCircuit`) and 8 new helpers (1901 insertions, 122 deletions). Lines are
base → head (`source-head.json`; every line at most 100 characters).

| File | Status | Lines |
|---|---|---:|
| `SpecialEncryptionSecurity.lean` | owned | 157 → 332 |
| `SpecialEncryptionMulti.lean` | owned (SG-1) | 325 → 368 |
| `Garbling.lean` | owned | 427 → 659 |
| `GarblingSecurity.lean` | owned | 87 → 115 |
| `Yao.lean` | owned, shared with `sc-yao` (body only) | 942 → 970 |
| `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` | frozen, one approved reader (SG-F01) | 627 → 636 |
| `Garbling/CoinBlocks.lean`, `Garbling/Probability.lean` | helpers, new | 206, 113 |
| `GarblingSecurity/CoinMarginals.lean`, `GarblingSecurity/NestedBounds.lean` | helpers, new | 58, 215 |
| `SpecialEncryptionMulti/SliceParser.lean`, `SpecialEncryptionMulti/SliceReduction.lean` | helpers, new | 180, 150 |
| `SpecialEncryptionSecurity/Pad.lean`, `SpecialEncryptionSecurity/WrongKey.lean` | helpers, new | 116, 226 |

Each owned file imports its own helpers; after #305 no facade edit is needed, and none was made.

**The proof** (REPORT § *Proofs and edge cases*; review § *Content*; the targets' sketches were rewritten to describe
the delivered proof, the statement prose is unchanged):
1. **`spDecStr_wrongKey`** (`WrongKey`). The distinguisher evaluates `hG'.easy`'s evaluator on `⟨k', r⟩`;
   `MultiMsg.exists_oneQuery_nuppt` (D3) gives the one-query machine; D1 at budget `1`
   (`exists_negligible_prefix_collision`: `prfAdv + 2^{-n}`); against a random function the prefix collision has
   probability `2^{-n}` (`uprob_random_prefix`). `ε = that + 2^{-n}` gives the strict `<`, `n = 0` included.
2. **`specialScheme_wrongKey`**: the string bound at `ℓ = .var`, the coin relabelling, the `dec` coins averaged out
   (`uprob_fst`), and the overlong failure word decodes to `none` (`specialScheme_dec_runAt`).
3. **`nestedSpecial_wrongKeyBot`** (`NestedBounds`, `CoinMarginals`): two string bounds, `δ = ε₁ + ε₂`, and the case
   analysis of `nestedSpecial_wrongKeyBot_of_string_bounds` (0, 1, 2 positions).
4. **B2** `uprob_not_good_le_of_perm` has the brief's signature exactly (whitespace-collapsed, the binding draft). It is
   a corollary of the stronger `uprob_not_good_le_of_uniform_data` (uniform keys and row coins as the push-forward
   `d` of a uniform `Ω`; permutations `π w` may depend on the seed; SG-F02), proved through `good_of_no_crossOpening`
   (correct row opens and no cross-opening ⇒ the first success is the right key; row order irrelevant), 12 events per
   gate (arity ≤ 2) and `uprob_exists_le` twice. **`uprob_not_good_le`** averages B2 over uniform permutations.
5. **`yaoSeed_good_whp`** uses the uniform-data form with Yao's XOR shifts as the seed-dependent permutations,
   `pushesUniform_key_row_blocks` for the disjoint key and row-coin blocks (`b·S + v` and
   `2S + 2(4i + idx(a)) + b`, injective below `10S`), and the output collision `outLen · 2^{-n}`;
   `δ = 12 · S · δ₀ + outLen · 2^{-n}`. The generic push-forward is in `Garbling/CoinBlocks`, so `Yao.lean` changes only
   in this body.
6. **B1** `sliceMultiMessageSecure_of_prfOut` (`SliceParser`, `SliceReduction`, `Pad`): an `Option` of fitting
   configurations with `none ↦ 0` (**the empty-set convention**), the slice vector as unary advice, the parser
   `slicePost` (`polyTimeComputable_slicePost`, `slicePost_tuple`: the pointwise identity with the slice sampler on the
   same seed), `D' = D ∘ P` by `exists_slicePost_nuppt`, D4's `ε` before the masks, `distAdv_comp` and
   `acceptProb_coins_equiv`; the `none` branch uses D4 at equal zero masks for `0 ≤ ε`.
7. **`specialScheme_multiMessageSecure`** is proved **directly from D4** in its own file
   (`MultiMsg.exists_negligible_distAdv_prfEncRealOut` at masks `0^n ‖ m_i`, the relabelled coins,
   `acceptProb_comp_equiv`), upstream of the corollary `specialScheme_multiMessageSecure_of_joint`, as the import
   direction requires (`SpecialEncryptionMulti` imports `SpecialEncryptionSecurity`).

**Gate 27's hand-off obligations** (REPORT § *Gate 27 hand-off*): (1) the maximizing advice with the empty-set
convention, in the B1 proof (`Config`, `Pack`, `adv`, `μ`, `β`; `length_sliceAdvice_le`, `exists_slicePost_nuppt`);
(2) the post-processor `slicePost` with `slicePost_tuple`; (3) the random-function slice law: D2/D4's full pads are
uniform, so every selected window is (`slicePost_tuple` only identifies the windows); (4) the triangle bound: D4
itself; (5) the frozen theorem `specialScheme_multiMessageSecure` proved directly, `of_joint` still proved beside B1;
(6) B2.

**Ruling SG-1.** The six frozen private relabelling helpers of `SpecialEncryptionMulti.lean`
(`specialScheme_gen_runAt`, `specialScheme_enc_runAt`, `specialKeyEq`, `ofFn_specialKeyEq`, `specialNonceEq`,
`ofFn_specialNonceEq`) are deleted. They are published once beside `specialScheme` in
`SpecialEncryptionSecurity.lean`: `specialScheme_gen_runAt`, `specialScheme_enc_runAt` (same names, now public),
`specialScheme_keyCoinsEquiv` (`_eq`, `_ofFn`), `specialScheme_nonceCoinsEquiv` (`_eq`, `_ofFn`), and also
`specialScheme_dec_runAt`. `specialScheme_multiMessageSecure_of_joint` is re-proved through them, proof only: four reader
names and one re-wrap (`pack-checks/sg1.txt` shows both texts).

**The frozen-file change** (SG-F01): `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` gains

```lean
theorem isFaninTwo_iff :
    C.IsFaninTwo ↔
      (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
        ∀ g ∈ C.gates, g.args.length ≤ 2 := Iff.rfl
```

with a formula docstring and the tag `[AB09, Definition 6.1]`. Seyoon approved it in the worker's session (the
delivery's `scope-request/`) and **confirmed his approval on 2026-11-15** (decision log). sc-yao's SY-3 reader is
byte-identical to it.

**Statements.** decls2 from the issue base (and from `1321b9cb`) to the head gives **55 ADDED, 0 CHANGED, 0 REMOVED**
(public declarations; review `statements/head/decls2-vs-base.tsv`; re-checked, `pack-checks/decls2-*.tsv`; 0 rows for
LE-doc).
- The frozen check (`frozencheck_sg.py`, at the final head) compares the **139** base declarations of the 5 owned files
  (6 + 18 + 37 + 2 + 76) and the **72** of `DAGCircuit`: file, kind, name, order, header bytes, statement prose and
  every definition body. It finds **0 differences**, with `SpecialEncryptionMulti`'s six SG-1 helpers listed as
  EXPECTED-REMOVED, 6 of 6 (`landing/frozen-check.txt`).
- **The SG-1 check: exactly 6 REMOVED, 0 CHANGED.** Its 11 controls each report exactly one difference
  (`statements/frozen/controls-summary.txt`), among them the brief's one-character header control (`of_joint`) and
  SG-1's **seventh-removal control** (deleting `zipWith_xor_append_of_le` in a copy reports 1 MISSING).
- Re-checked for this pack from git objects, private declarations included (`pack-checks/headers.txt`, `sg1.txt`):
  every base header in the 6 files byte-identical at the head and in order; removed exactly the six SG-1 names, each
  private at the base; every remaining definition block identical (2 + 3 + 15 + 0 + 24 + 27); only the targets' docstrings
  changed (and `isFaninTwo_iff` new); `of_joint`'s header and docstring byte-identical; the six names occur at the
  issue base only in `SpecialEncryptionMulti.lean`, and at the head only `specialScheme_gen_runAt`/`_enc_runAt`
  remain, as the public readers and their uses; `zipWith_xor_append_of_le` is still present.
- **`Yao.lean`** (`pack-checks/yao.txt`, review `statements/frozen/yao.diff`): 942 → 970 lines, three hunks: the
  `## Main results` bullet (head lines 96–99), the target's sketch (799–806) and its body (813–848). No other
  declaration's header or docstring, no import and no name changes.

## Rulings and records in force

1. **SG-1 (Seyoon, 2026-11-15, before dispatch): the frozen-file exception** above, with its header check (exactly six
   REMOVED, zero CHANGED), its two controls, the private-use search and the `of_joint` seals. With the private copies
   gone the relabelling is not debt, and no ledger row is opened.
2. **SG-F01 (Seyoon confirmed, 2026-11-15):** `DAGCircuit.isFaninTwo_iff`, `Iff.rfl`, equal line for line to the
   approved patch (`pack-checks/dagcircuit.txt`: the 9 added lines = the patch's, 0 removed; the head file with them cut
   out is the base file byte for byte). It is the only change to a frozen file. **Not a finding.**
3. **DL-46** (prf-long, disclosed): `MultiMsg.encodeList_eq_flatMap` is a third copy of the public
   `encodeList_eq_flatMap`; the brief forbids a fourth (none was added). The `zipWith_xor_append_of_le` clash class.
4. **DL-47, extended by SG-F04 (Seyoon, 2026-11-15: ledger).** The new inline getD-of-`List.ofFn` chain in
   `Garbling/CoinBlocks.lean:73–74` (`List.getD_eq_getElem`, `List.getElem_ofFn`, in `pushesUniform_bits_of_blocks`)
   is the chain of Yao's private `getD_ofFn'`; it is re-pointed onto the planned generic getD reader in the cleanup.
   **Not a finding:** any item DL-46 or DL-47 lists.
5. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This is
   `FinDist`'s `⟨FinDist.prob⟩`. The coe-variant seals are canonical; the strict variant is run and its differences
   attributed.
6. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal **A** is canonical; seal B is run and reported, and
   its new failures attributed from the raw logs (Gate 31). So **coe-A is the canonical variant**.
7. **The facade-completeness lint fix, #305.** The baseline is **92 FAIL / 101 WARN** (Cryptography) and **25 / 391**
   (Complexity).
8. **LE-doc (the maintainer's landing edit): docstrings only** (SG-F03). `NestedBounds` and `WrongKey` `## Main results`
   now list their main theorems; the `**Proof sketch.**` of `nestedSpecial_wrongKeyBot` gains one sentence naming the
   delivered route. Re-checked (`pack-checks/lecheck.txt`): `e5cb6129..cd9a4843` touches 3 files (+14/−1), each
   identical with doc comments deleted; one declaration docstring and two module docstrings change; widths ≤ 98.
9. **The host addendum** (`fills/codex-host-2026-11-15/host-addendum.md`): the worker ran on Seyoon's Mac with a
   host-wide 3-slot Lean cap; the preflight, `slots.log` (543 acquire/release pairs) and `-k 3` on every `lake` call
   pass (review § *Integrity*). The REPORT's environment notes (a rejected checkpoint push, the overnight
   "best judgment" authorization in `scope-request/autonomy.md`) are information, not findings.

## What is frozen

- **The seven targets' statements** (quoted in the brief) and every other pre-existing declaration of the five owned
  files, private ones included, with their statement prose; every definition body (`specialScheme`, `GarbleSeed`,
  `Good`, `sliceEnc`, `yaoSeed`, …), apart from the six SG-1 deletions.
- **`Yao.lean`** apart from the one body, its sketch and its bullet.
- **Every other file**, in particular `DAGCircuit.lean` apart from the approved reader, `SpecialEncryption.lean`,
  `GarblingSpecial.lean`, `YaoReal.lean`, prf-long's files (`Functions/Asymptotic/Defs`, `Encryption/PrivateKey/FromPRF*`,
  `PrivateKey.lean`), `Pseudorandom/*`, `Encryption/*` and `Games/*`.
- **The landing edit:** LE-doc, three docstrings.

## Questions for the audit

**1. Correctness against the frozen statements and [PS10, §6.2.2–6.2.3]**
- **`spDecStr_wrongKey`:** does the length guard always pass on honest ciphertexts, so that `none` is exactly the
  prefix mismatch? Is the evaluator of `hG'.easy` the right stand-in for `E'` (which has no `PolyTimeComputable`
  hypothesis; they agree on canonical inputs by `hGE'`)? Is the one-query reduction at budget `1` with
  `exists_oneQuery_nuppt` and D1 right, and is `ε = prfAdv + 2^{-n} + 2^{-n}` (the strict `<` at `n = 0`) correct?
- **`specialScheme_wrongKey`** and **`nestedSpecial_wrongKeyBot`:** the relabellings, the `dec`-coin average, the
  failure word's decoding, the three nesting cases and `δ = ε₁ + ε₂`.
- **B2 and `uprob_not_good_le`:** is `uprob_not_good_le_of_perm` exactly the brief's signature, and is it a corollary of
  `uprob_not_good_le_of_uniform_data`? Is `good_of_no_crossOpening` right (arguments distinct and below the gate by
  `IsFaninTwo`, at most two; constant gates add no event; row order irrelevant), is 12 events per gate right, and is
  the average over uniform permutations a corollary, not a second proof?
- **`yaoSeed_good_whp`:** are the key and row-coin blocks disjoint and inside `yaoCoins = 10 S n + 2 S`
  (`key_row_blocks_injective`), is the XOR-shift family a valid seed-dependent permutation family for the uniform-data
  form, and is the output collision `outLen(n) · 2^{-n}` (outputs may coincide) right?
- **B1:** is `slicePost_tuple` the pointwise identity `P_{o,ℓ}(encodeTupleOut (prfEncRealOut (G n) w t)) =
  sliceMultiEncDist G n q o len m t` on the same seed, reading `prfEncRealOut`, `encodeTupleOut` and `sliceEnc` only
  through their readers? Is the advice polynomial (`length_sliceAdvice_le`) and `slicePost` polynomial-time? Does the
  maximization **keep the empty-set convention** (`none ↦ 0`, e.g. `ℓ(n) < n`), with D4's `ε` chosen before the masks,
  so that every fitting `o, ℓ, m, m'` is bounded? Are **Gate 27's obligations (1)–(6)** met, and does the delivery
  follow **Gate 31's B1 consumer map** (masks `0^{o_i+n} ‖ m_i ‖ 0^{…}`, `D' = D ∘ P` with the slices as advice, steps
  1–3 inside D4)?
- **`specialScheme_multiMessageSecure`:** is it proved **directly from D4** (masks `0^n ‖ m_i`, all slices `(0, n)`, no
  post-map) through the new readers and `acceptProb_comp_equiv`, with no use of the downstream corollary?
- Are the brief's edge cases covered: `n = 0`; `ℓ(n) = 0` and `ℓ(n) < n`; `q(n) = 0`; empty messages; exact fits (Yao's
  outer slice `(2n, 4n + 2)`); `len = 1, 2` and constant gates; fewer than two arguments; the XOR shift at `len = 0`;
  `|gates| = 0`; coinciding output vertices?

**2. Frozen-statement integrity**
- Is the frozen check **0** over the 139 + 72 base declarations, and is the SG-1 report **exactly 6 REMOVED, 0 CHANGED**,
  with both controls (the one-character header control and the seventh-removal control) biting once each? See
  `landing/frozen-check.txt`, `statements/frozen/`, `pack-checks/headers.txt` and `sg1.txt`.
- Is decls2 **55 ADDED / 0 CHANGED / 0 REMOVED**, the six removals all private (so outside decls2), and is every new
  declaration in an owned file or a permitted helper directory?
- **The stricter `Yao.lean` rule:** does `Yao.lean` change only in `yaoSeed_good_whp`'s body, its `**Proof sketch.**` and
  its `## Main results` bullet (`pack-checks/yao.txt`, `statements/frozen/yao.diff`)?
- In `SpecialEncryptionMulti.lean`, did only what SG-1 and the brief allow change: the imports, the title, `## Main
  results` and `## Contents`, the B1 proof and sketch, the six removals and `of_joint`'s proof (header and docstring
  byte-identical)? See `statements/frozen/specialEncryptionMulti.diff`.

**3. The frozen-file change**
- Is `DAGCircuit.isFaninTwo_iff` exactly the approved patch (`worker/final/evidence/scope-request/fanin-reader.patch`,
  `pack-checks/dagcircuit.txt`) and true by `Iff.rfl` from the frozen `IsFaninTwo`? Is it needed under the seal
  (the `Iff.rfl` control fails sealed, the reader passes; `logs/ctlcheck.log`, row `ctlFanin`) and sufficient? Is
  anything else changed in a frozen file?

**4. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's `## Overlap and reuse`, **DL-46** and **DL-47** (with SG-F04)? **Any further undisclosed duplicate
  of a public lemma is a major.** The recent majors of this class are G23-01, G24-01, prf-mac F-01, learning
  (`uprob_eq_point`), G29-01 (`hj` = `OneWay.uexp_const`), G29-02 (`firstBit_of_pos`), sc-ot F-01 and G34-01
  (`OT.getD_zero_eq`/`getD_one_eq'` re-proving `headD_drop`).
- Search in particular:
  - probability and expectation (`uprob_*`, `uexp_*`, `acceptProb_*`, `distAdv_*`, `pushesUniform_*`,
    `uprob_not_injective_le`, `MultiMsg.uprob_eq_pair`, `uprob_exists_le`, `uprob_not`);
  - list windows and XOR (`ofFn_drop_take`, `take_ofFn_castLE`, `take_drop_ofFn_blocks`, `headD_drop_ofFn`,
    `zipWith_xor_*`, `MultiMsg.zipWith_xor_*`, `encodeList_eq_flatMap`, `List.take_append_of_le_length`, …);
  - the getD/headD-of-`List.ofFn` class beyond SG-F04 (`pack-checks/dupscan.txt` and review
    `dup/getd-headd-added-lines.txt`: the other added getD lines are statements, `change` lines and `Option.getD`);
  - coin relabellings (`prfScheme_coinsEquiv`, `coinsEquiv`, `NUPPT.coinsCongr_ofFn`) and machine plumbing (D3's
    machines, `NUPPT.exists_comp`, `exists_withAdvice`, `Games.polyTimeComputable_iterEmit`, `polyTimeComputable_blockMap`,
    `NMSim.chunkMap`);
  - encoding lengths (`length_le_encodeList`, `length_encodeList_le` against `ETTGame.length_le_length_encodeLog`,
    `EffFill.length_le_length_encodeHist`, `EffFill.length_encodeLog_le`, and the private
    `CircuitComplexity/Uniform.lean:208` short-name relative).
- Are the disclosed relations accurate and their "why not reused" reasons valid (for example `length_nestedInner` vs
  `GarblingSpecial`'s inline `hc`, `spEncStr_eq_sliceMask` vs the frozen private `zipWith_xor_append_of_le`, the B1
  maximum vs D4's `Finset.exists_max_image`)? The review's independent search is `evidence/logs/duplication-review.txt`.

**5. Rule 10**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 14 files over
  the full closure, at the base and the head, in all four variants, run with `-DmaxErrors=0` and install/EOF records?
  Requests per file go up to 2106 (0 for `DAGCircuit`, whose closure has no TCSlib definition; `logs/mkseals-*.log`).
  The base phase sealed the six base files in their own base closure (a base `SpecialEncryptionMulti` cannot be sealed
  against the head `SpecialEncryptionSecurity`, whose public `specialScheme_gen_runAt` would clash with the private
  copy).
- With **coe-A canonical**, does every file pass? The review has **A head 14/14 and base 6/6, strict and coe**; strict
  = coe throughout (`logs/seal-table-seals{,-coe}.txt`).
- **SG-1:** does `of_joint` pass A and B, strict and coe, with the new readers?
- **Seal B (SG-F07):** 30 errors at the head in 5 files against 21 at the base in 3 (`GarblingSecurity` 3/2,
  `SpecialEncryptionSecurity` 6/4, `Yao` 15/15, and the new `NestedBounds` 1 and `WrongKey` 5). The 9 new errors are in
  new bodies (`spDecStr_wrongKey`, `nestedSpecial_wrongKeyBot_of_string_bounds`,
  `exists_negligible_prefix_collision` and their calls); `logs/seal-B-attribution.txt` attributes every head B error,
  read from the raw logs, to a `PolyExpr.eval` conversion, matching the worker's `B-attribution.md`. Is that right, and
  is none a foreign-definition unfold?
- Do the paired controls bite? Rows: `PolyExpr.eval` (B), the `FinDist` CoeFun instance, `DAGCircuit.IsFaninTwo` (the
  approved reader), `spEncStr`, `Good`, `sliceMask`, `SliceReduction.slicePost`, `SpecialWrongKey.prefixTest`. Coe
  (canonical): 24 probes, 43 sealed negatives, `logs/ctlcheck.log` ALL_OK. Strict: 28 probes, 57 sealed negatives;
  every sealed negative fails exactly once, and only `ctlCoeReader` fails in the 14 strict sealed probes (the harness
  effect of sc-ot F-09; `logs/controls-strict-attribution.txt`). The first control attempt (`controls-attempt1/`, it
  opened `Turing` where Garbling's closure lacks it) is superseded and kept.
- Explicit-unfold scan at the head: 774 items, 594 theorems, 31 owned definitions, 147 local or unresolved, 2 flagged
  foreign, both local `let` binders (`P`, `g`) resolved to global names (`logs/scan-attribution.txt`): **0 foreign**.
  Does any proof read a foreign definition other than through a published reader (`spEncStr`, `spDecStr`, `sliceEnc`,
  `Good`, `WrongKeyBot`, `nestedSpecial`, `yaoSeed`, `readBits`, `xorShift`, `prfEncRealOut`, `encodeTupleOut`, the
  `NUPPT` layer; one helper's definitions read from another)?

**6. The landing edit and the docstring and sketch rules**
- **LE-doc (ruling 8):** docstrings only (`landing/le-doc.diff`, `landing/le-doc-doconly.txt` in the review ZIP;
  `pack-checks/lecheck.txt`)? Do the new `## Main results` entries and the sketch sentence describe the code?
- Does every new public declaration's docstring state its formula, in Lean argument order, with a `[PS10, …]` tag where
  it comes from the source? The review's docaudit (`statements/head/docaudit.tsv`, before LE-doc, which added no
  formula) has 55 OK and 8 NO-FORMULA: the frozen prose of 5 targets, `of_joint`'s frozen docstring, and 2 Prop
  formulas without a relation symbol (`nestedSpecial_wrongKeyBot_of_string_bounds`, `polyTimeComputable_slicePost`), a
  tool artifact. Are those 2 acceptable?
- Does every proof of 15 lines or more carry a `**Proof sketch.**` (`statements/head/sketchaudit.txt`: 21, 0 without),
  and do the long proofs (B1, B2, `yaoSeed_good_whp`) have step comments? A misstated formula or sketch is a minor.
- Does every new public `def` land with its readers (`sliceMask`, `slicePost`, `parserStep`, `parserEmit`, the two coin
  equivalences with `_eq` and `_ofFn`; lint check 8)? Is nothing new `@[simp]`, an instance or an abbreviation (census:
  none)?

**7. The merge interaction**
- `git merge-tree --write-tree cd9a4843 <x>` is clean, and no path is shared (`pack-checks/mergetrees.txt`):

  | `<x>` | head | merged tree | downstream of both (`pack-checks/downstream.txt`) |
  |---|---|---|---|
  | the tip | `540bac18` | `bb5289bb` | none (records only since the base) |
  | #313 (learning) | `2b6c2981` | `34984d25` | 7: the 5 Learning modules, `Randomness`, root `TCSlib` |
  | #318 (sc-ot) | `f62a25b3` | `23c029c1` | 6: `ObliviousTransfer`, `OT/Predictor`, `OT/ViewB`, `YaoReal`, `SecureComputation`, `TCSlib` |
  | #319 (canonizer) | `6421ac16` | `59401ef7` | 33, through the downstream of `DAGCircuit` and of #319's machine-library files |
  | #324 (sc-compose) | `a6eaebd7` | `e6911ef7` | 3: `YaoReal`, `SecureComputation`, `TCSlib` |

- No open PR changes a module of the unit's closure (166 modules). `DAGCircuit` is upstream of much of the library
  (the review: 273 modules downstream of it), which is why the shared downstream with #313 and #319 is large.
- Of the 388 built modules (build plus edit-build, at the head), all have the tip-merged source and 387 each other
  PR's merged source (`pack-checks/srcequality.txt`). None of the 53 new short names is declared in a file another PR
  changes (`pack-checks/namecheck.txt`); the review's name-clash scan over all TCSlib files has 0 exact clashes.
- **Pending merge condition (not an audit item).** The combined trees are **not** built. Whichever of #323 and #313,
  #318, #319 or #324 merges second needs an integration rebuild of the shared downstream on the merged tip before it
  merges; the maintainer runs that build. Treat it as a condition on the merge, not as something for this audit to
  establish. What you can raise: a concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **SG-F02** (info, disclosed): `yaoSeed_good_whp` goes through the stronger seed-dependent bound. **SG-F03** (info):
  the `## Main results` and sketch gaps, fixed by LE-doc. **SG-F05** (info): the generic
  `uprob_not_good_distinct_le_of_uniform_data` sits in `GarblingSecurity/NestedBounds`, not `Garbling/`; moved in the
  cleanup. **SG-F06** (info): two unused-simp-argument warnings (`SliceParser:168`, `NestedBounds:89`); cleanup.
  **SG-F07** (info): seal B's 9 new errors, all `PolyExpr.eval` conversions.
- **The worker was Codex**, though the brief names Claude (Seyoon moved the job, decision log 2026-11-15); the worker
  commits carry Seyoon's authorship.
- **The review's PROVENANCE** says docaudit's NO-FORMULA rows are "the 6 frozen target proses"; the rows show 5 (the
  8 = 5 + `of_joint` + 2 Prop formulas). Its `statements/head/` audits and `sizes-widths.txt` are at the pre-edit head
  `e5cb6129` (`GarblingSecurity` 111 lines there, 115 at the head); `source-head.json` is at the head.
- **`yaoProtocol_hbcSecure` keeps `sorryAx`** through `yaoHybrid_*` (sc-yao), `otProtocol_*` (#318) and
  `hbcSecure_compose` (#324); `yaoSeed_good_whp` is no longer among its admissions (review DepTrace).
- **Old (pre-#305) lint** shows 8 more lines of the facade class for the 8 helpers (`lint/oldlint-linediff.txt`);
  recorded, not a finding.
- **The worker's promotion requests** (the option-complement bound, the dependent row marginal, the first-success
  dichotomy, the bit-block restriction, `length_nestedInner` beside `nestedSpecial`, the `encodeList` length bounds)
  are for the deferred cleanup.

## Also check

**Axioms**
- At the head, the seven targets, B2, `uprob_not_good_le_of_uniform_data`, `uprob_not_good_distinct_le_of_uniform_data`,
  `garbling_good_whp`, `specialScheme_multiMessageSecure_of_joint` and the helper endpoints each print
  `[propext, Classical.choice, Quot.sound]`; `DAGCircuit.isFaninTwo_iff` depends on no axioms (`landing/census-head.log`).
  At the base every target and `garbling_good_whp` had `sorryAx`.
- The census has **531** stored constants (= the worker's); the axiom union is the standard three plus `sorryAx`, which
  occurs only in `yaoHybrid_polyTime`, `yaoHybrid_simulators` and `yaoHybrid_hbcSecure` (sc-yao's admissions).
  Against the base: removed = the SG-1 privates and their auxiliaries; `specialScheme_gen_runAt`/`_enc_runAt` moved
  private → public with equal types; 0 type-changed; 8 axiom-changed (the 7 targets and `garbling_good_whp`)
  (`logs/census-base-vs-head.tsv`, name map `statements/namemap-sg1.txt`).

**Admissions:** 32 in 15 modules → **25 in 11**, by exactly the seven targets (`Yao.lean` keeps `yaoHybrid_polyTime`,
`yaoHybrid_simulators`; `logs/sorry-census.txt`).

**Sizes and widths:** every file at most 970 lines (`Yao.lean` ≤ 1000), every line at most 100 characters
(`source-head.json`).

**Build:** at the head, **388/388 modules rc 0, 0 errors in both diagnostic forms** (G26-N1; substring "error" 0): the
downstream of every module changed since `eff2dcd0` (82 = 68 base delta + 14 unit; `DAGCircuit` alone puts 273 modules
downstream of the unit) through root `TCSlib` and both `audits/*/Checks` (`landing/root-checks.jsonl`, at the pre-edit
head `e5cb6129`), then the 9 modules LE-doc touches and their dependants (`landing/edit-build-results.jsonl`). The unit
modules have no `sorry` and only the two SG-F06 warnings. Whole-tree check at the head: 1257 modules, RESULT OK
(`landing/tree-check-head.txt`). Restore: `dl-oleans` back at `457ba704…`. Every built source equals its blob at
`cd9a4843` (`pack-checks/srcequality.txt`).

**Lint:** Cryptography 92/101 and Complexity 25/391 at the tip and the head, with identical line sets; the one
changed Complexity line is `DAGCircuit`'s check-8 WARN, which loses `IsFaninTwo` (it now has a reader).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (SG-F01–SG-F07).
- **`verification.zip`** (147 entries): every file the review cites and the pack uses, as byte-identical originals.
  Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/sc-garble/final-r1/`, SHA-256 `5a121c02…`) and `review-evidence-SHA256SUMS`, its
    manifest: 1273 entries, 72 directories and 1201 files, exactly the 1200 manifest paths plus `SHA256SUMS`
    (byte-identical to the manifest; no top folder); every hash verifies;
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `records/` (19): the issue package `fills/sc-garble/issued-r1/` (with `ruling-SG-1.md`), the duplication ledger
    (DL-46, DL-47 with SG-F04), the decision log, Gate 27's resolutions (the hand-off obligations), Gate 31's findings,
    resolutions and worker report (the B1 consumer map), the secure-computation plan, the Codex host addendum and
    sc-yao's `ruling-SY.md` (SY-3), at records `540bac18ce13cb8ef37b7dc41d97de5d2deaf661`;
  - `evidence/` (83): byte copies of the ZIP entries this pack cites;
  - `worker/final/` (19): byte copies from exchange `a73072f19787ee437f2201777711c7eb3154c714`
    (`inbox/fills/sc-garble/`): `COMMITS.tsv`, the scope request and approved patch, the seal-B attribution and
    summary, the axiom summary, the preflight, the header-check results, controls and `Yao.diff`, the corollary diff,
    the private-use search, the clash log and the final signatures (17 of them also byte-identical to the review's
    `logs/delivery-extracts/`);
  - `pack-checks/` (21): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `a73072f1`, under `inbox/fills/sc-garble/`. Its top `SHA256SUMS`
  lists 1278 files and `evidence/SHA256SUMS` 1254, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`), `build-summary.txt`,
  `edit-build-results.jsonl`, `edit-build-summary.txt`, `census-head.log` (= `probe-runs/mods/PlProbe_H_CensusHead.log`),
  `frozen-check.txt` (= `statements/frozen/frozen-check-le.txt`) and `tree-check-head.txt`.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `a73072f1`.
- **`pr-description.md`:** the PR #323 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (14 paths, 1901 insertions, 122 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 14 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 166 files.
- **The bundle** adds, as context at the head: `SpecialEncryption.lean` (`spEncStr`, `spDecStr` and their readers),
  `GarblingSpecial.lean` (`nestedSpecial`), `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean` (D4) and the frozen
  `DAGCircuit.lean` hunk (in `pr.diff.txt`).

## Findings delivery

Return `gate36-sc-garble-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-46 and DL-47, or necessary
  evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
