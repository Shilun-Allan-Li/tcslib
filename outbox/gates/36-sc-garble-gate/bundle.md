## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/review.md =====

# sc-garble · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edit is LE-doc. Draft [PR #323](https://github.com/Shilun-Allan-Li/tcslib/pull/323).

## Delivery and landing
- **Delivery:** a Codex worker on Seyoon's Mac, under the host addendum. The final is at exchange `a73072f1`; the checkpoints are `8313d3d2` and `11b3b808`. The issue base is `fbd37f44`, the head of #315, which has since merged.
- **Landing:** `land/pass-shelat-sc-garble`, head `cd9a48438c2a6548fe9e246ce569be57c9df96b3`, tree `13aa553d`, on `1321b9cb`. The range-diff is 7/7 identical.
  - **Commits:** the worker's `6b23a7b1`, `69f7fc89`, `2ca68a8e`, `60c71312`, `f48ec526`, `04adb34c` and `e5cb6129`, then LE-doc `cd9a4843`.
- **Files:** 14 files, +1901/−122:
  - the five owned files;
  - `Complexity/CircuitComplexity/DAGCircuit.lean`;
  - eight helpers: `Garbling/{CoinBlocks,Probability}`, `GarblingSecurity/{CoinMarginals,NestedBounds}`, `SpecialEncryptionMulti/{SliceParser,SliceReduction}` and `SpecialEncryptionSecurity/{Pad,WrongKey}`.
- **Evidence:** `review-evidence.zip`, SHA-256 `5a121c0290969e1f7725f997b8e5683169613a62ba4db203669a74590bd0e658`, 1201 entries.

## Checks
- **Integrity:**
  - The manifests verify 1278/1278 and 1254/1254.
  - `git am` reproduces all 7 hashes unsigned. The `COMMITS.tsv` signing column reads "none".
  - `src/` equals the 14 files. The package verifies 8/8 and its sources 166/166.
  - The host checks pass: the preflight, `slots.log`, `-k 3` on every `lake` call, and no `lake build`.
- **Build:** 388/388 modules give rc 0, with 0 errors in both forms, through root `TCSlib` and both `audits/*/Checks`. The whole-tree check covers 1257 modules: OK.
- **Statements:**
  - The frozen check covers the 139 base declarations of the owned files and the 72 of DAGCircuit, and finds 0 differences.
  - `SpecialEncryptionMulti` shows exactly the six SG-1 removals and 0 CHANGED. `of_joint` changes only in its proof: four reader names and one re-wrap. Its header and docstring are byte-identical.
  - The 11 controls each report exactly 1 difference. They include the one-character control and the seventh-removal control.
  - In `Yao.lean`, only the target body, its sketch and its bullet change; the file has 970 lines.
  - decls2 gives 55 ADDED, 0 CHANGED, 0 REMOVED. The name-clash scan finds nothing, including `zipWith_xor_append_of_le`.
- **Axioms:** the seven targets, B2, `garbling_good_whp` and `of_joint` use only the standard three, across 531 constants. `yaoProtocol_hbcSecure` keeps `sorryAx` through `yaoHybrid_*` (sc-yao), `otProtocol_*` (#318) and `hbcSecure_compose`.
- **Rule 10:**
  - Seal A passes 14/14 at the head and 6/6 at the base, strict and coe.
  - Seal B has 30 errors at the head against 21 at the base. All are attributed to `PolyExpr.eval` conversions (SG-F07).
  - The coe controls are ALL_OK. The strict ones fail only on `ctlCoeReader`.
  - The scan finds 0 foreign definitions.
- **Admissions:** 32 in 15 modules → 25 in 11, by exactly the seven targets.
- **Lint:** 92/101 and 25/391, with identical line sets. Widths are ≤ 100.
- **Content:**
  - `specialScheme_multiMessageSecure` is proved directly from D4, upstream of the corollary.
  - The B1 maximization keeps the empty-set convention.
  - The Gate 27 hand-off obligations (1)–(6) are met.
  - B2 `uprob_not_good_le_of_perm` has the brief's signature and is a corollary of the stronger `uprob_not_good_le_of_uniform_data` (SG-F02).
- **Overlap:** the trial merges with #313, #318 and #319 are clean.
- **Restore:** `dl-oleans` is exactly `457ba704…`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| SG-F01 | minor | The frozen `DAGCircuit.lean` gains `isFaninTwo_iff`, an `Iff.rfl` reader that equals the approved patch. Seyoon's approval had been recorded only in the delivery's `scope-request/`. | **Confirmed by Seyoon (2026-11-15) and recorded in the decision log.** Accepted. sc-yao's SY-3 reader is byte-identical to it. |
| SG-F02 | info, disclosed | `yaoSeed_good_whp` goes through the stronger seed-dependent bound. | Accept. |
| SG-F03 | info | There were gaps in the sketches and the `## Main results` sections. | **Fixed** by LE-doc. |
| SG-F04 | minor, undisclosed | `Garbling/CoinBlocks.lean:73–74` adds a new inline getD-of-`List.ofFn` chain, of the DL-47 class. | **Ruling (Seyoon): ledger.** DL-47 is extended; the chain is re-pointed onto the planned generic getD reader. |
| SG-F05 | info | The generic bound `uprob_not_good_distinct_le_of_uniform_data` sits in `GarblingSecurity/NestedBounds`, not under `Garbling/`. | Move it in the cleanup. |
| SG-F06 | info | Two unused-simp-argument warnings (`SliceParser:168`, `NestedBounds:89`). | Cleanup. |
| SG-F07 | info | Seal B has 9 new errors, all `PolyExpr.eval` conversions. | None. |

## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/worker-report.md =====

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

## ===== briefs/pass-shelat-ch5-8/fills/sc-garble/issued-r1/brief.md =====

# Claude fill · special encryption and garbling probability (`sc-garble`, U1)

**Issue base** `fbd37f447596d4207c8d08b7ef7602f57fe95198`: the head of draft PR #315 (`prf-long`, branch
`land/pass-shelat-prf-long`), **not** the records tip. **Unit** `sc-garble` (U1 of the secure-computation plan).
**Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that commit's
`lake-manifest.json`.

**Why this base (the `prf-long` dependency).** The B1 proof and `spDecStr_wrongKey` use the PRF machinery at
`ℓ(n)`-bit outputs that `prf-long` delivered (D1–D4, ruling B3). That machinery is not merged: it is draft PR #315,
under its own gate (Gate 31). Under the campaign's **proved-modulo rule** (`policy.md` §1: a consumer cites a
dependency while its own landing is still running), you build on the #315 head `fbd37f44`. Your results are proved
modulo the merge of #315, and `sc-garble` lands only after #315 merges, rebased by the maintainer. The #315 head
contains everything on the records branch up to `dd98360d` (#303, #305–#309, #311 and #312) plus the six prf-long
commits; the records commits since then touch no Lean.

Prove seven admitted, frozen statements:

| Target | File | Source |
|---|---|---|
| `spDecStr_wrongKey` | `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean` | [PS10, §6.2.2], "the extra property" (Claim 157.a (ii), strings) |
| `specialScheme_wrongKey` | the same | Claim 157.a (ii), the scheme |
| `specialScheme_multiMessageSecure` | the same | Claim 157.a (i); [PS10, Definition 93.1, Theorem 99.2] |
| `nestedSpecial_wrongKeyBot` | `TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean` | Claim 157.a (ii) for the nesting, [PS10, §6.2.2–6.2.3] |
| `uprob_not_good_le` | `TCSlib/Cryptography/SecureComputation/Garbling.lean` | Claim 159.a, probabilistic part, [PS10, §6.2.3] |
| `yaoSeed_good_whp` (**only this body** of the file) | `TCSlib/Cryptography/SecureComputation/Yao.lean` | Claim 159.a applied to Protocol 162.6's seed |
| `sliceMultiMessageSecure_of_prfOut` (the B1 statement) | `TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean` | [PS10, §6.2.2, "it is easy to modify construction 99.1"; Definition 93.1, Theorem 99.2]; [LP09] |

All seven are confirmed at the issue base: each is a `theorem` whose body is `sorry` (`base-sorries.txt`). The
first six passed the prong statement phase and Gate 06; the B1 statement passed Gate 27 (CLEAR, 0/0/1/0) and was
merged in #311 (ruling B1, 2026-11-14). All are frozen. Their docstrings hold the maintainer's proof sketches.

Also publish, as the plan's requirement **B2**, a stronger garbling bound (see *Scope* and checkpoint 2).

## Feasibility and size (maintainer's assessment)

**Feasible.** The secure-computation plan (`briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`,
§2.3–2.8 and §3) found none of these statements false as frozen and no missing hypothesis. Codex gave a full
mathematical proof of B1 as written at Gate 27, with one convention (the maximum advantage is `0` when no slice
vector fits). The prf-long review (`fills/prf-long/final-r1/review.md`, § *Content*) checked the B1 consumer map
below against the merged B1 file.

**Estimated size: 2,500–4,700 lines in all.** The plan's estimate was 3,000–5,000, with the multi-message lemma
dominating (1,000–1,800 lines, the `ℓ`-output PRF hybrid included). D1–D4 now supply that hybrid, the query-chain
and one-query machines and the total; what remains of B1 is the slice post-processor, its poly-time parser, the
advice and the maximization.
- checkpoint 1, 700–1,350: `spDecStr_wrongKey` 300–600 (the one-query machine and the budget-1 PRF bound are D3 and
  D1; left are the distinguisher, the length guard, the random-function probability `2^{-n}` and the coin
  bookkeeping), `specialScheme_wrongKey` 100–250, `nestedSpecial_wrongKeyBot` 300–500;
- checkpoint 2, 1,000–1,800: the B2 bound with `uprob_not_good_le` as its corollary 500–900, `yaoSeed_good_whp`
  500–900 (the push-forward through disjoint coin blocks; the output-key collision);
- the final, 800–1,550: the B1 step 0 (masks, the post-map `P`, its poly-time parser and the pointwise identity with
  the slice sampler, the advice and the maximization) 750–1,450, and `specialScheme_multiMessageSecure` 50–100.

## Checkout and delivery

- Fetch `land/pass-shelat-prf-long` (and `cryptography/pass-shelat-ch2-4`). Start a local branch
  `fill/sc-garble` at the exact issue base `fbd37f447596d4207c8d08b7ef7602f57fe95198`, and record the base in
  `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/sc-garble/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, the committer's
    name, email and date, and its **signing** (`none`, or the signature format), so that `git am` at the base
    reproduces every hash. **Commit with `git -c commit.gpgsign=false`** (prf-mac F-05, prf-long F-03: the last
    workers' hashes reproduced only with the environment's deterministic SSH signature, which was not recorded). If
    a commit is signed anyway, say so in its row and in `REPORT.md`. Before you push, check the reproduction in a
    scratch clone and say so in `REPORT.md`;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/sc-garble/` except itself. The
    delivered paths must **equal** the manifest's paths exactly, with nothing missing and nothing extra, and
    without a leading `./`. Check this before each push.
- Commit as `fill sc-garble: checkpoint N` and `fill sc-garble: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by a
  maintainer PR for Seyoon's approval.

## Base and parallel work

- **In the base:** #303, #305–#309, #311 (the B1 statement) and #312 (the derand host), and prf-long's six commits
  (four worker commits, LE-doc, LE-ws). The lint baseline below is re-run at the issue base.
- **#315 (prf-long) is under Gate 31.** Do not edit its files: `Pseudorandom/Functions/Asymptotic/Defs.lean`,
  `Encryption/PrivateKey/FromPRF*` and `Encryption/PrivateKey.lean` are **frozen for this unit**, and D1–D4 are used
  as published. If Gate 31 leads to a resolution edit of #315, stay on `fbd37f44`; the maintainer rebases at
  landing. If a D1–D4 statement turns out not to fit, stop and escalate (*Escalation*); do not restate it.
- **In flight, inside this order, not edited by this unit:**
  - `sc-ot` (final in, under review) changes `SecureComputation/ObliviousTransfer.lean` and adds helpers;
  - `sc-compose` (dispatched) changes `SecureComputation/ComposeSecurity.lean`;
  - `derand` (staged) has pre-approved additions to `Complexity/ClassP/DTIME.lean` and
    `Complexity/Randomized/Build/IterateFind.lean`.

  They are in the closure only as upstream modules, or (`ObliviousTransfer`, `ComposeSecurity`) as modules that
  `YaoReal` imports. Stay on the issue base if any of them merges during the fill.
- **Merged after the issue base:** #314 (the `prfAdv_eq_expect` promotion, Gate 30 CLEAR), at `59c2c1fb` on the
  records branch. It adds `TCSlib.Cryptography.prfAdv_eq_expect` to `Pseudorandom/Functions/Defs.lean` (upstream of
  your order) and re-derives `ETTGame.prfAdv_eq_expect`. It is **not** in your base; do not merge it in. The
  maintainer rebuilds the combined tree at landing (#315 itself needs that integration rebuild before it merges).
- **Later:** `sc-yao` (U3) proves `yaoHybrid_polyTime` and `yaoHybrid_simulators` in `Yao.lean` after this unit
  lands; it shares `Yao.lean` with you (*Scope*). #313 (`learning`) is outside this order.

## Targets (frozen; quoted from the issue base)

```lean
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
```

```lean
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
```

```lean
theorem specialScheme_multiMessageSecure (hG : PRFOut (.add .var .var) G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  sorry
```

```lean
include hGE₁ hGE₂ in
theorem nestedSpecial_wrongKeyBot (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, (nestedSpecial E₁ E₂ n).WrongKeyBot (δ n) := by
  sorry
```

```lean
theorem uprob_not_good_le [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
    (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) :
    uprob (fun s : GarbleSeed Cc K ρ => ¬ Good M Cc s) ≤ 12 * Cc.gates.length * δ := by
  sorry
```

```lean
include hGE₁ hGE₂ in
theorem yaoSeed_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n := by
  sorry
```

```lean
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G := by
  sorry
```

- **`SpecialEncryptionSecurity.lean`** (namespace `TCSlib.Cryptography.SecureComputation`, under
  `open Complexity Turing TCSlib.Cryptography`): `specialScheme_multiMessageSecure` and `specialScheme_wrongKey` use
  the section variables `G` (length-doubling, `Fin (n + n)` outputs), `E`, `hE : PolyTimeComputable E` and `hGE`.
  `spDecStr_wrongKey` takes its own `ℓ`, `G'`, `E'`, `hGE'` and `hG'`; note that `E'` has **no**
  `PolyTimeComputable` hypothesis (use the evaluator of `hG'.easy`, which agrees with `E'` on canonical inputs).
- **`Garbling.lean`** (namespace `TCSlib.Cryptography.SecureComputation`, `open BoolCircuit TCSlib.Cryptography`):
  section variables `{K C ρ : Type} [Inhabited K] {n : ℕ} (M : MultiEnc K C ρ) (Cc : DAGCircuit n)`. `GarbleSeed` is
  an `abbrev` (notation): keys, row coins and row permutations.
- **`GarblingSecurity.lean`**: section variables `G₁`, `G₂` (`Fin ((PolyExpr.add .var innerLen).eval n)` outputs),
  `E₁`, `E₂`, `hGE₁`, `hGE₂`, with `include hGE₁ hGE₂ in`. The proved `garbling_good_whp` already consumes
  `nestedSpecial_wrongKeyBot` and `uprob_not_good_le`.
- **`Yao.lean`** (`section Security`): `yaoSeed_good_whp` with the same `G₁`, `G₂`, `hGE₁`, `hGE₂` and the file
  variables `Y`, `E₁`, `E₂`. `Y.fanin`, `Y.size_le`, `Y.outs_lt` and `Y.outs_sink` are its circuit facts.
- **`SpecialEncryptionMulti.lean`**: the definitions `sliceEnc`, `sliceMultiEncDist`, `SliceMultiMessageSecure`
  with their readers, the target, and the proved corollary `specialScheme_multiMessageSecure_of_joint` and bridges.

## Published interfaces

| Interface | Provider |
|---|---|
| **D1** `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` | `Pseudorandom/Functions/Asymptotic/Defs.lean` (#315) |
| **D2** `prfEncRealOut` (`prfEncRealOut_apply`), `otpEncOut` (`otpEncOut_apply`), `multiMsgAdvOut` (`eval_multiMsgAdvOut`, `multiMsgAdvOut_boundedBy`), `acceptProb_oracleDist_multiMsgAdvOut`, `prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_random_otp_le`, `acceptProb_otpEncOut`, `distAdv_prfEncRealOut_le` | `Encryption/PrivateKey/FromPRF/Hybrid.lean` (#315) |
| **D3** `MultiMsg.exists_queryChainOut_nuppt`, `MultiMsg.exists_oneQuery_nuppt` | `Encryption/PrivateKey/FromPRF/ReductionMachine.lean` (#315) |
| **D4** `encodeTupleOut` (`encodeTupleOut_eq`, `encodeTupleOut_eq_flatten`), `MultiMsg.encodeList_eq_flatMap`, `MultiMsg.exists_negligible_distAdv_prfEncRealOut` | `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean` (#315) |
| `MultiMsg.prfAdv_congr_equiv`, `MultiMsg.abs_uexp_sub_le_uprob`, `MultiMsg.negligible_choose_div_two_pow`, `uprob_not_injective_le`, `pushesUniform_comp_injective`, `MultiMsg.blockMapFun`, `MultiMsg.take_drop_ofFn_blocks` | `FromPRF/HybridLemmas.lean`, `FromPRF/Hybrid.lean`, `FromPRF/ReductionMachine.lean` |
| `OracleEnsemble.keyed_O`, `random_O`, `acceptProb_random_eq`, `acceptProb_random_eq_lazy`, `NUPPT.toOracleAdversary` readers | `Pseudorandom/Functions/Asymptotic/Defs.lean` |
| `PRFOut` (fields `easy`, `pseudorandom`), `prfOut_var_iff`, `specialScheme_gen/_enc/_dec` (`simps`) | `SecureComputation/SpecialEncryptionSecurity.lean` |
| `spEncStr_eq`, `spDecStr_eq`, `spDecStr_spEncStr`, `length_spEncStr`, `runAt_spEnc`, `runAt_spDec`, `polyTimeComputable_spEncFun` | `SecureComputation/SpecialEncryption.lean` |
| `sliceEnc_eq`, `sliceEnc_eq_spEncStr`, `sliceEnc_append_left/_right`, `sliceMultiEncDist_apply`, `sliceMultiMessageSecure_iff`, `specialScheme_multiMessageSecure_of_joint` | `SecureComputation/SpecialEncryptionMulti.lean` |
| `MultiEnc.decCorrect_iff`, `wrongKeyBot_iff`, `good_iff`, `keyAt_eq`, `argKeys_eq`, `garbledRow_eq`, `garbledTable_eq`, `tableAt_eq`, `tableAt_gate`, `gateOut_eq`, `GarbleSeed_eq` | `SecureComputation/Garbling.lean` |
| `nestedSpecial_enc`, `nestedSpecial_dec` (`simps`), `nestedSpecial_decCorrect`, `innerLen_eq` | `SecureComputation/GarblingSpecial.lean` |
| `yaoSeed_fst`, `yaoSeed_snd_fst`, `yaoSeed_snd_snd`, `keyAt_yaoSeed`, `readBits_apply`, `xorShift_apply`, `assignIdx_eq`, `yaoCoins_eval` | `SecureComputation/Yao.lean` |
| `runAt_coinKey`, `decodeFin_ofFn`, `PrivateKeyScheme.multiMessageSecure_iff`, `multiEncDist_apply`, `encodeList_nil/_cons`, `NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn`, `NUPPT.coinsCongr_ofFn` | `Encryption/PrivateKey/{FromPRG,EnsembleSecurity}.lean`, `Asymptotic/Adversary.lean`, `Complexity/Randomized/PPT.lean` |
| `NUPPT.exists_comp`, `NUPPT.exists_withAdvice`, `NUPPT.exists_split`, `NUPPT.distinguisherL` readers | `Complexity/Randomized/Closure.lean` and the `NUPPT` layer |
| `polyTimeComputable_blockMap`, `NMSim.chunkMap` (`polyTimeComputable_chunkMap`) | `Complexity/Randomized/Repetition.lean`, `Encryption/PublicKey/NonMalleability/Simulation/Generic.lean` |
| `uprob_mono`, `uprob_exists_le`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `uprob_le_one`, `uprob_nonneg`, `uprob_true`, `uprob_false`, `uprob_const`, `acceptProb_def`, `distAdv_def`, `acceptProb_comp_equiv`, `uprob_comp_eq_sum_map`, `distAdv_comp`, `OneWay.uprob_eq_one_div_card`, `OneWay.uexp_const`, `HardcoreBit.pushesUniform_restrict`, `Negligible.add`, `negligible_two_pow_neg`, `EnsembleLemmas.negligible_polyExpr_mul` | `Foundations/{Probability,Experiments,Negligible}.lean`, `Asymptotic/EnsemblesLemmas.lean`, `Pseudorandom/Indistinguishability.lean`, `OneWayFunctions/Basic.lean`, `HardcoreBit/Basic.lean` |

## Scope

**Owned files** (you prove their targets and may add to them):

| File | Lines at base | What changes |
|---|---|---|
| `SecureComputation/SpecialEncryptionSecurity.lean` | 157 | the proofs of `spDecStr_wrongKey`, `specialScheme_wrongKey` and `specialScheme_multiMessageSecure` and their sketch paragraphs; new public declarations (for example the coin-relabelling readers of `specialScheme`, see *The import direction*); the module title (drop "(statement phase)") and `## Main results`; imports of its helpers and of the D1–D4 modules |
| `SecureComputation/SpecialEncryptionMulti.lean` | 325 | the proof of `sliceMultiMessageSecure_of_prfOut` and its sketch; the title and `## Main results`; imports of its helpers |
| `SecureComputation/Garbling.lean` | 427 | the B2 lemma (new, beside the target); the proof of `uprob_not_good_le` from it and its sketch; the title and `## Main results`; imports of its helpers |
| `SecureComputation/GarblingSecurity.lean` | 87 | the proof of `nestedSpecial_wrongKeyBot` and its sketch; the title and `## Main results`; imports of its helpers |
| `SecureComputation/Yao.lean` (**shared** with `sc-yao`) | 942 | **only** the body of `yaoSeed_good_whp`, its `**Proof sketch.**` paragraph, and the `## Main results` bullet that lists it (split `yaoSeed_good_whp` out as proved). No import line, no new declaration, nothing else |

**New helper modules** are permitted in four directories, each imported by its file (after the facade-lint fix
#305 a helper under `X/` is covered as long as `X.lean` imports it, so `SecureComputation.lean` needs no edit):
- `SecureComputation/SpecialEncryptionSecurity/`, imported by `SpecialEncryptionSecurity.lean`: the PRF-facing parts
  of the wrong-key proof and the pad identities shared by the two multi-message proofs. They may import the D1–D4
  modules (`FromPRF/MultiMsgOut`, `FromPRF/ReductionMachine`, `FromPRF/Hybrid`, `Functions/Asymptotic/Defs`). State
  them on `PRFOut`'s clause (2) hypothesis
  `(OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ)`, as prf-long does, since
  `PRFOut` is defined in `SpecialEncryptionSecurity.lean` itself.
- `SecureComputation/SpecialEncryptionMulti/`, imported by `SpecialEncryptionMulti.lean`: the slice post-processor,
  its parser and the advice (B1 step 0). These cannot see `sliceEnc`; state them on `spEncStr` and the D4 objects,
  and assemble in `SpecialEncryptionMulti.lean`.
- `SecureComputation/Garbling/`, imported by `Garbling.lean`: **definition-free** probability helpers (the marginal
  of the keys at a `Nodup` argument list, the union-bound bookkeeping, the push-forward of a uniform string through
  disjoint blocks). `Garbling.lean` imports only `DAGCircuit`, two Mathlib modules and `Foundations.Probability`;
  keep these helpers as light. They are upstream of `Yao.lean`, so `yaoSeed_good_whp` can use them without a new
  import in `Yao.lean`.
- `SecureComputation/GarblingSecurity/`, imported by `GarblingSecurity.lean`: the relabelling for the nesting.

Check the import graph for cycles: a helper of a file never imports that file or anything downstream of it.

**The import direction (binding): `specialScheme_multiMessageSecure`.**
- The frozen target sits in `SpecialEncryptionSecurity.lean`, but the proved corollary
  `specialScheme_multiMessageSecure_of_joint` sits in `SpecialEncryptionMulti.lean`, which **imports**
  `SpecialEncryptionSecurity.lean`. So the target **cannot** be proved through that corollary in its own file; the B1
  docstring's "is `specialScheme_multiMessageSecure_of_joint G E hE hGE (sliceMultiMessageSecure_of_prfOut hG)`" holds
  only as a statement about the two results. Do not move either declaration (the frozen-statement rule).
- Prove it **directly from D4** in its own file: `ℓ = .add .var .var`, masks `w_i = 0^n ‖ m_i`, all slices `(0, n)`,
  so no post-map is needed (the window is all of `G_k(r_i)`). The scheme's sampler is then
  `encodeTupleOut ∘ prfEncRealOut (G n) w` up to the relabelling of `Gen`'s and `Enc`'s coins as an `n`-bit key and
  `n`-bit nonces (keeping their strings): `runAt_coinKey`, `runAt_spEnc`, `hGE`, and `spEncStr E k m r =
  ⟨r, (0^n ‖ m) ⊕ E(⟨k, r⟩)⟩` (`spEncStr_eq`), closed with `acceptProb_comp_equiv`.
- That relabelling repeats the **frozen private** helpers of `SpecialEncryptionMulti.lean`
  (`specialScheme_gen_runAt`, `specialScheme_enc_runAt`, `specialKeyEq`, `ofFn_specialKeyEq`, `specialNonceEq`,
  `ofFn_specialNonceEq`), which you may not make public or delete. Publish it **once**, as public readers in
  `SpecialEncryptionSecurity.lean` beside `specialScheme`, and disclose the overlap with the private copies as a
  **ledger** row in *Overlap and reuse* (the maintainer opens the ledger row; the private copies are removed in the
  cleanup). **Names:** the new public names must differ from those six private names and from
  `zipWith_xor_append_of_le`: a public declaration upstream with the same name makes the frozen private one fail to
  declare (the prf-long clash, DL-46). The name-clash scan (*Checks*) covers this.
- Put the pad identity that both multi-message proofs need (a special ciphertext from offset `o` equals the D4 entry
  `⟨r_i, w_i ⊕ G_k(r_i)⟩` cut by `P`) in a `SpecialEncryptionSecurity/` helper, so it is proved once.

**The frozen-statement rule (binding; checked).**
- **Headers.** Every declaration present at the issue base in the five owned files stays in the same file and the same
  order, with its header byte-identical. The header is the attributes and modifiers, the keyword, the name, the
  binders and the type, up to the `:=`, `by`, `where` or first `|` that begins the proof. `open … in`,
  `include … in` and `omit … in` prefixes count as part of the header.
- **Definitions are statements.** A `def`, `abbrev`, `structure`, `inductive`, `class` or `instance` stays
  byte-identical, body included. Delete nothing, private lemmas included.
- **What may change.** Only the proofs of the seven targets; their `**Proof sketch.**` paragraphs, rewritten to
  describe the delivered proof (the statement prose before the sketch stays); module docstrings (title, `## Main
  results`, `## Contents`; for `Yao.lean` only the one bullet); and, within the scope above, added imports and
  declarations. `set_option`s and attributes do not change.
- **`Yao.lean` is stricter:** apart from the `yaoSeed_good_whp` body, its sketch and its `## Main results` bullet,
  the file is byte-identical to the base.
- **Check.** Write a `python3 -I` script that extracts every declaration of the five files at the base and at the
  final and compares headers (and whole definitions) byte for byte, and checks that the base declarations appear in
  the same order; for `Yao.lean` also report the full diff and show it touches only the allowed lines. Deliver it and
  its output under `evidence/headers/`, with zero differences. Add a control: a copy with one header altered by one
  character must report exactly one difference. The prf-long review's checker counted 126 declarations; do not let
  private or unnamed declarations, `include … in` lines or match-arm headers escape the count.

**Everything else is frozen**, in particular `SpecialEncryption.lean`, `GarblingSpecial.lean`, the rest of
`Yao.lean`, `YaoReal.lean`, every prf-long file (*Base and parallel work*), `Pseudorandom/*`, `Encryption/*`,
`Games/*` (`Games/Efficiency.lean` is at 982 lines; do not add to it) and the circuit library.
- **Scope requests.** If the route needs any other change to a frozen file (a reader beside a foreign definition,
  an import or declaration in `Yao.lean`, a promotion, a change to a D1–D4 statement), stop that line of work. Ask
  Seyoon in your session, giving the exact file, the diff and the reason, and go ahead only on his approval. Record
  the request and his answer verbatim under `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. Seyoon
  prefers a route with no frozen-file edit where one exists.
- A lemma that belongs in an existing file goes in your helper module, with a promotion request.

## Proof route and checkpoints

1. **Checkpoint 1 · the wrong-key property.**
   - **`spDecStr_wrongKey`** (plan §2.3; its sketch).
     - *The event.* For every `n` and `m`, with `k, k', r` uniform: the length guard of `spDecStr` always passes on an
       honest ciphertext (`|k'| = |r| = n`, and `|c₂| = n + ℓ(n)` because `E'` outputs `n + ℓ(n)` bits by `hGE'`;
       `length_spEncStr`), so the decryption is `none` exactly when `G'_k(r)_{<n} ≠ G'_{k'}(r)_{<n}`. The event does
       not depend on `m`.
     - *The distinguisher.* `D` reads `⟨⟦r⟧, ⟦u⟧⟩`, draws `k'` from its coins, and accepts iff `u_{<n}` equals the
       first `n` bits of `E(⟨k', r⟩)`, where `E` is the polynomial-time evaluator of `hG'.easy` (it agrees with `E'`
       on canonical inputs through `hGE'`). `MultiMsg.exists_oneQuery_nuppt D (.add .var ℓ)` turns it into a
       one-query oracle machine `B` with coins `(r, c)` and the evaluation identity for every oracle.
     - *Against a random function* the acceptance probability is exactly `2^{-n}`: the answer `g(r)` is uniform and
       independent of `k'` and `r` (`OracleEnsemble.acceptProb_random_eq`/`_lazy`; `OneWay.uprob_eq_one_div_card`
       for the point probability). *Against `G'_k`* it is the success probability of the wrong key.
     - *The bound.* `hG'.pseudorandom.negligible_prfAdv B (.const 1)` (D1, budget `1`; `PolyExpr.eval_const`) makes
       the PRF advantage negligible. Take `ε n = prfAdv … + 2 · 2^{-n}`: the extra `2^{-n} > 0` gives the strict `<`.
   - **`specialScheme_wrongKey`** (plan §2.4): `spDecStr_wrongKey` at `ℓ = .var` with `G' = G` and `E' = E`, through
     `runAt_coinKey`, `runAt_spEnc`, `runAt_spDec` and `decodeFin_ofFn` (`1^{n+1}` decodes to no `n`-bit message; a
     `some` output has `n` bits); the `dec.Coins` factor has one element (`uprob_comp_equiv`, `uprob_fst`).
   - **`nestedSpecial_wrongKeyBot`** (plan §2.7; its sketch): the three cases (one position; two positions, first
     differs: `spDecStr_wrongKey` at `ℓ = innerLen` with `G₂`; first agrees, second differs: the outer layer opens by
     `spDecStr_spEncStr` and `length_spEncStr`, then `spDecStr_wrongKey` at `ℓ = .var` with `G₁`), the relabelling
     `(Fin len → Bool → K) × ρ ≃` (the used keys) × (the rest), and `δ = ε₁ + ε₂` (`Negligible.add`).
   - Send this checkpoint.
2. **Checkpoint 2 · the garbling bound (B2) and Yao's seed.**
   - **B2 (required, brief level).** `uprob_not_good_le` as frozen is about a uniform `GarbleSeed`, whose third
     component is a uniform `Equiv.Perm`, but `yaoSeed` uses XOR shifts, so it cannot be applied to Yao's seed (plan
     §2.8). Publish in `Garbling.lean`, beside the target, one stronger bound. The recommended form is the bound for
     **every fixed row-permutation family**; draft signature, binding unless the name clashes:

     ```lean
     theorem uprob_not_good_le_of_perm [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
         (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
         (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)) :
         uprob (fun t : (Fin Cc.size → Bool → K) ×
             ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
           ¬ Good M Cc (t.1, t.2, π)) ≤ 12 * Cc.gates.length * δ
     ```

     The allowed alternative is the bound for **every seed law whose keys and row coins are uniform and independent
     of the permutations**; if you choose it, give its signature in `REPORT.md` and say why. Either way it is one
     public declaration with a formula docstring, and:
     - **`uprob_not_good_le`** follows by averaging over the uniform permutations (reassociate the seed,
       `uprob_comp_equiv`, `uprob_prod`): a corollary, not a second proof;
     - the B2 proof is the target's sketch: correctness of the row of `a`; the arguments are distinct vertices below
       the gate's own (`IsFaninTwo`: `args.Nodup`, at most two arguments; `args_lt`), so the argument keys, the
       plaintext key and the row coin are independent; `WrongKeyBot` averaged over the plaintext and the coin; at
       most `4 · 3 = 12` events per gate; the union bound (`uprob_exists_le`). Constant gates add no event; the row
       order plays no role.
   - **`yaoSeed_good_whp`** (plan §2.8; its sketch) as a corollary of B2 and `nestedSpecial_wrongKeyBot` by
     push-forward: the keys, the row coins and the shifts of `yaoSeed` read disjoint blocks of Alice's coins
     (`yaoSeed_fst`, `yaoSeed_snd_fst`, `yaoSeed_snd_snd`, `readBits_apply`; the blocks fit in
     `yaoCoins = 10 S n + 2 S`, `assignIdx` injective below `4` for at most two positions, `|gates| ≤ size ≤ S`), so
     for each fixed shift block the keys and row coins are uniform; apply B2 with the XOR-shift family; add the output
     collision `outLen(n) · 2^{-n}` (two independent uniform keys per output vertex). `δ = 12 · S · δ₀ + outLen ·
     2^{-n}` is negligible (`EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`, `Negligible.add`).
     Keep the generic push-forward lemma in a `Garbling/` helper, so that `Yao.lean` changes only in this body.
   - Send this checkpoint.
3. **Final · the B1 statement and Claim 157.a (i).**
   - **`sliceMultiMessageSecure_of_prfOut`**, by the **B1 consumer map** (the prf-long review § *Content* and the
     prf-long worker's REPORT § *B1 consumer map*, both checked against the merged file):
     - **Step 0 · reduction to tuples (this unit's part).** Fix `D` and `q`. For a fitting slice vector
       (`o_i + n + ℓ_i ≤ ℓ(n)`) and messages `m`, the masks are
       `w_i = 0^{o_i + n} ‖ m_i ‖ 0^{ℓ(n) − o_i − n − ℓ_i} : Fin (ℓ.eval n) → Bool`, and the post-map
       `P_{o,ℓ} : (r, u) ↦ (r, (u.drop o_i).take (n + ℓ_i))` acts on each block inside `encodeList`. Prove pointwise,
       on the same seed space `(Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)` (no coin relabelling), that
       `P_{o,ℓ} (encodeTupleOut (prfEncRealOut (G n) w t)) = sliceMultiEncDist G n q o len m t`, reading
       `prfEncRealOut` only through `prfEncRealOut_apply`, `encodeTupleOut` through `encodeTupleOut_eq` or
       `encodeTupleOut_eq_flatten`, and the slice sampler through `sliceMultiEncDist_apply`, `sliceEnc_eq` and
       `spEncStr_eq`: within one ciphertext the revealed prefix `G_k(r)_{[o, o+n)}` and the masked message are
       disjoint windows of `w ⊕ G_k(r)`.
     - **The reduction `D' = D ∘ P`, with the slices as advice.** The advice at `n` encodes the maximizing slice
       vector (`q(n) + 1` pairs of numbers at most `ℓ(n)`: polynomial length); `P` is polynomial-time given the
       advice (a block parser: `polyTimeComputable_blockMap`, `NMSim.polyTimeComputable_chunkMap`, or the
       `encodeList` readers); `D'` comes from `NUPPT.exists_comp` and `NUPPT.exists_withAdvice`, with
       `D'.distinguisherL n z = D.distinguisherL n (P z)` read through the `NUPPT` readers.
     - **The maximization, with the empty-set convention.** Let `A(n)` be `D`'s largest advantage over the finitely
       many fitting slice vectors and message pairs, and `0` when no slice vector fits (for example when `ℓ(n) < n`;
       the advice is then arbitrary). D4's `ε` precedes the masks, so
       `MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q` bounds the maximizing pair's
       advantage, and every fitting `o, ℓ, m, m'` is at most `A(n) ≤ ε(n)` (`distAdv_comp` moves `P` into `D'`).
       `hG.pseudorandom` is literally D4's hypothesis (the prf-long worker's B1 probe and the review's consumer probe
       check this at the base).
     - **Steps 1–3** (the PRF step, the random function and collision, the total) are inside D4; do not repeat them.
   - **`specialScheme_multiMessageSecure`** directly from D4, as in *The import direction*.
   - **Gate 27's hand-off obligations for `sc-garble`** (`gates/27-b1-multimsg/resolutions-r1.md`; obligations, not
     findings). Your delivery must show each: (1) the maximizing advice, with the empty-set convention; (2) the slice
     post-processor; (3) the random-function slice law (here: inside D2/D4, the full `ℓ(n)`-bit pads are uniform, so
     every window is; say where your proof relies on it); (4) the triangle bound (inside D4); (5) the frozen theorem:
     `specialScheme_multiMessageSecure` proved (directly, by the import direction), with
     `specialScheme_multiMessageSecure_of_joint` staying proved beside B1; (6) B2. Map each to declarations in
     `REPORT.md` § *Gate 27 hand-off*.

Check the edge cases: `n = 0` (keys and nonces empty; the strict `<` of `spDecStr_wrongKey` at `2^{-0} = 1`);
`ℓ(n) = 0` and `ℓ(n) < n` (no slice fits; `A(n) = 0`); `q(n) = 0`; messages of length `0`; slices that fit exactly
(the outer slice `(2n, 4n + 2)` of Yao fits exactly); `len = 1` and `len = 2` in `WrongKeyBot` and constant gates;
gates with fewer than two arguments; the XOR shift at `len = 0`; `|gates| = 0`; output vertices that coincide
(`outs` need not be injective).

**Escalation.** If a sketch is wrong, a target is false as stated, or a D1–D4 statement does not fit, stop and
escalate with the exact obligation: a checkpoint with the counterexample or the missing fact. Do not weaken any
statement.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines. Keep
  `Yao.lean` (942 lines) at most 1000: `sc-yao` adds two large bodies to the same file after you; if the body
  cannot fit, make a scope request. Check both with a short `python3 -I` script before each push and include its
  output in `evidence/`.
- **Parallel fills.** See *Base and parallel work*. Edit only the files of *Scope*.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them.
  - **Probability, expectation and list identities first.** The undisclosed re-proofs that the last reviews and gates
    found were all of this kind:
    - prf-mac (F-01, a major): `hadv` re-proved `ETTGame.prfAdv_eq_expect` (`EncryptThenTag/Reduction.lean:347`;
      promoted as `TCSlib.Cryptography.prfAdv_eq_expect` in `Pseudorandom/Functions/Defs.lean` by #314, merged
      after your base);
    - learning: `uprob_eq_point` restated `OneWay.uprob_eq_one_div_card` (`OneWayFunctions/Basic.lean:144`), and an
      inline argument re-proved `MultiMsg.abs_uexp_sub_le_uprob` (`FromPRF/HybridLemmas.lean:61`);
    - Gate 29: `hj` re-proved `OneWay.uexp_const` (`OneWayFunctions/Basic.lean:69`; G29-01), and `firstBit_of_pos`
      re-proved `LamportFill.headD_drop_ofFn` (`Authentication/Signatures/Lamport/MachineSpec.lean:195`, outside
      your order; being promoted to a shared list layer, ruling G29-02).

    Before writing any advantage, expectation, uniform-projection, point-probability, push-forward or list-window
    lemma, search for `uprob_*` (`uprob_comp_equiv`, `uprob_prod`, `uprob_fst`, `uprob_exists_le`, `uprob_const`,
    `uprob_comp_eq_sum_map`, `uprob_eq_one_div_card`), `uexp_*` (`uexp_const`, `abs_uexp_sub_le_uprob`),
    `prfAdv_*` (`prfAdv_eq_expect`, `prfAdv_congr_equiv`), `acceptProb_*`, `distAdv_comp`, `pushesUniform_*`,
    `uprob_not_injective_le`, and for lists `ofFn_drop_take` (`Asymptotic/CollectionsHelpers.lean:210`),
    `take_ofFn_castLE` (`Asymptotic/ReductionSupport.lean:288`), `take_drop_ofFn_blocks`, `headD_drop_ofFn`,
    `zipWith_xor_*` (`HardcoreBit.zipWith_xor_ofFn_add`, the `MultiMsg.zipWith_xor_*` family), `encodeList_eq_flatMap`
    and Mathlib's `List.take_append_of_le_length`, `List.drop_append_of_le_length`, `List.ofFn_*`. Use
    `MultiMsg.encodeList_eq_flatMap` (public, D4); do not add a fourth copy (DL-46).
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it. The relabelling of *The import direction* is the one expected case.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration that
    restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its nearest
    relative (`path:line`), the relation, and why it is not reused. Disclose inline re-proofs inside a proof (`have`
    blocks) the same way. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23, 24 and 29 were
    undisclosed duplicates (G23-01, a private copy of `length_le_length_encodeLog`; G24-01, `inputWord_take`, which
    re-proves the public `take_ofFn_castLE`; G29-01 and G29-02 above), and so was prf-mac F-01.
  - **Nearest relatives here:**
    - the frozen private relabelling helpers of `SpecialEncryptionMulti.lean` (*The import direction*) and
      `prfScheme_coinsEquiv` (`Encryption/PrivateKey/FromPRF.lean`) for scheme coin relabellings;
    - D1–D4 themselves: do not rebuild a machine, a hybrid or a collision bound; `exists_oneQuery_nuppt` is the
      one-query machine, `exists_queryChainOut_nuppt` the chain;
    - `MultiMsg.blockMapFun`, `polyTimeComputable_blockMap`, `NMSim.chunkMap` for the block parser;
    - `Equiv.piEquivPiSubtypeProd`, `Equiv.sumArrowEquivProdArrow` and the `uprob` product lemmas for the marginals;
      `HardcoreBit.pushesUniform_restrict` for restrictions of uniform functions;
    - `sliceEnc_append_left/_right` for the two layers of `nestedSpecial`.
- **Docstrings and sketches.** The last batches' landing edits were mostly LE-doc (cca2-ett: 94 formulas and 15
  sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches; learning: 17 formulas; prf-long: 3) and
  LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a source tag where it comes from the source (`[PS10, §6.2.2, Algorithm 157.2]`,
    `[PS10, §6.2.3, Claim 159.a]`, `[PS10, Theorem 99.2, with slices]`);
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3); each target's sketch is rewritten to describe the delivered proof;
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public `abbrev` with
    an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections: for
    example `spEncStr` through `spEncStr_eq`, `spDecStr` through `spDecStr_eq`, `sliceEnc` through `sliceEnc_eq`,
    `Good` through `good_iff`, `WrongKeyBot` through `wrongKeyBot_iff`, `nestedSpecial` through its `simps` readers,
    `yaoSeed` through `yaoSeed_fst`/`_snd_fst`/`_snd_snd`, `readBits` through `readBits_apply`, `xorShift` through
    `xorShift_apply`, `prfEncRealOut` through `prfEncRealOut_apply`, `encodeTupleOut` through its two readers.
  - Each owned file and each helper module counts as foreign to the others; inside one owned file its own
    definitions may be read directly.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `GarbleSeed`, `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (166 modules) and the narrow `roots.txt` (71), following the addendum.
  - The order is the upstream closure of the modules downstream of the five owned files (root `TCSlib` excluded),
    and of the modules your helpers may import: the `FromPRF` facade (D2–D4 and `HybridLemmas`),
    `NonMalleability/Simulation/Generic` (`NMSim.chunkMap`) and `Games/Efficiency`. It contains `YaoReal` and the
    `SecureComputation` facade.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the five owned files and every helper, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (32 declarations in 15 modules). The only
    change must be the removal of the seven targets (25 in 11 modules: `Yao.lean` keeps
    `yaoHybrid_polyTime` and `yaoHybrid_simulators`).
  - **Name-clash scan.** No new public or private name may already be declared anywhere in `TCSlib/` at the issue
    base, with namespaces resolved; private names count (the frozen private helpers of `SpecialEncryptionMulti.lean`
    in particular). Deliver the script and its output under `evidence/clash/`.
- **Axioms.**
  - Print the axioms of the seven targets, of the B2 lemma and of every stored constant of the changed and new files.
    Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print, at base and final, the axioms of `garbling_good_whp` (it must become standard-only),
    `specialScheme_multiMessageSecure_of_joint`, `yaoHybrid_hbcSecure` and `yaoProtocol_hbcSecure`. The last two keep
    `sorryAx` through admissions outside this unit; say which.
- **Headers.** The check of *The frozen-statement rule*, with its control.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation). Report
    every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed, and attribute every seal-B failure by
    reading its raw log; do not summarize new B failures as "where the base fails" (Gate 31).
  - **Error counts (G26-N1), both forms.** Your runner must count both diagnostic forms, `error:` and `error(…)`,
    for example with `^\S+\.lean:\d+:\d+: error[:(]`, in every seal, control, sweep and probe log. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN**, re-run by the maintainer at `fbd37f44`.
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base, and the status of each target;
  - the changed and new files, with lines at base and final, and the sketch edits;
  - the new declarations with their final signatures, the B2 lemma in full;
  - **Gate 27 hand-off** (each obligation mapped to declarations);
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - the header-check script, its output and its control, and the name-clash scan;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's (top level and `evidence/`), with no
  leading `./`.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing, after #315
merges, on the then records tip (which includes #314).

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/fills/sc-garble/issued-r1/ruling-SG-1.md =====

# sc-garble · ruling SG-1: frozen-file exception (Seyoon, 2026-11-15)

Seyoon ruled this before dispatch, and it is part of the issued package. Where it differs from
[the brief](brief.md), the ruling takes precedence. It replaces the last two sentences of the third bullet of *The import
direction*: "which you may not make public or delete" and the ledger-row disclosure. Everything else in the brief
stands.

## The question
`specialScheme_multiMessageSecure` cannot be proved through `specialScheme_multiMessageSecure_of_joint`, because
`SpecialEncryptionMulti.lean` imports `SpecialEncryptionSecurity.lean`. The brief therefore proves it directly from
D4. That proof needs public coin-relabelling readers of `specialScheme` in `SpecialEncryptionSecurity.lean`, and
those readers repeat six frozen private helpers of `SpecialEncryptionMulti.lean`.

## The ruling: remove the private copies in this unit
Publish the relabelling **once**, as public readers beside `specialScheme` in `SpecialEncryptionSecurity.lean`, as
the brief says. Then, in `SpecialEncryptionMulti.lean`, you **may**:

1. **Delete** exactly these six private declarations:
   - `specialScheme_gen_runAt`
   - `specialScheme_enc_runAt`
   - `specialKeyEq`
   - `ofFn_specialKeyEq`
   - `specialNonceEq`
   - `ofFn_specialNonceEq`
2. **Re-prove `specialScheme_multiMessageSecure_of_joint`, proof only,** through the new public readers. Its header
   stays byte-identical. Its docstring, including the statement prose and the `**Proof sketch.**`, stays
   byte-identical unless the sketch names one of the deleted helpers. In that case, change only that name.
3. Make **no other change** to `SpecialEncryptionMulti.lean` beyond what the brief already allows: the proof of
   `sliceMultiMessageSecure_of_prfOut` and its sketch, the module docstring, and imports of its helpers. In
   particular, `zipWith_xor_append_of_le` and every other private declaration stay.

With the private copies gone, the overlap is not debt. Disclose the replacement in `REPORT.md` § *Overlap and reuse*:
which readers replace which private helpers, and the diff of `specialScheme_multiMessageSecure_of_joint`'s proof.
No ledger row is opened.

## Names
The new public names no longer have to avoid the six deleted names. They must still pass the name-clash scan
against everything else upstream and downstream, including `zipWith_xor_append_of_le` (the DL-46 clash class). Use
names that say what they relabel, under the `SecureComputation` namespace. Each name gets a formula docstring.

## Checks this changes
- **Header check** (*The frozen-statement rule*). The expected report for `SpecialEncryptionMulti.lean` is
  **exactly six REMOVED** (the names above) and **zero CHANGED**. Every other base declaration is present, in the
  same order, with its header byte-identical, and every definition body is byte-identical. Make the checker list
  these six as expected removals, so that anything else is still a difference. Keep the one-character control, and
  add a second control: deleting a seventh private declaration in a copy must report exactly one unexpected
  removal.
- **Proof changes outside the targets.** `specialScheme_multiMessageSecure_of_joint` is the only non-target
  declaration whose proof may change. Report its old and new proofs side by side under `evidence/headers/`.
- **Downstream.** The six helpers are private, so no other file can use them. Show this with a search over the
  project and `audits/`, and file it under `evidence/headers/`.
- **Rule 10.** Seal `specialScheme_multiMessageSecure_of_joint` with the new readers, in variants A and B, strict and
  coe, as for the targets.

Every other change to a frozen file still needs a scope request.

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
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `TCSlib.Cryptography.prfAdv_eq_expect` (published in #314, merge `59c2c1fb`); the list readers above; `GGMRed.tblEnc` | Open (F-01 paid) | F-01 **paid**: promoted in #314 (ETT re-derived, LE-gate30), prf-mac re-pointed by LE-reuse `590d1a56` (#317, Gate 33). F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). **sc-garble SG-F04 (ruling Seyoon 2026-11-15, ledger):** new inline getD/`List.ofFn` chain in `SecureComputation/Garbling/CoinBlocks.lean:73–74` (`getD_eq_getElem`, `getElem_ofFn`), same as Yao's private `getD_ofFn'`. | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. **Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger):** `OT.length_ofFn_coins` (`ObliviousTransfer/Simulators.lean:210–212`) is a verbatim copy of public `Composability.NMSim.length_ofFn_coins` (`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); direct reuse would add 69 NM modules to the OT closure. (G34-01, `OT.getD_zero_eq`/`OT.getD_one_eq'` re-proving `headD_drop`, is fixed by LE-gate34, not debt.) | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. G34-02 cleanup: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or `Randomized/NonUniform`) and re-point both copies. |
| DL-49 | sc-compose fill (delivery review 2026-11-15, SC-F01; disclosed in the checkpoint REPORTs): helpers under `SecureComputation/ComposeSecurity/` restate public lemmas because the brief's two extra imports were read as exhaustive: a third `negligible_polyExpr_mul`; `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`); `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family (from `Composability/ZeroKnowledge/ThreeColoring/Machines.lean`). | `EnsembleLemmas.negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`), `coinsEquiv`, `FunFamily.ofFn_blocks_symm`, the `ThreeColoring/Machines` helpers | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt. Cleanup: import the public lemmas (or promote the ThreeColoring helpers to a shared machine layer) and re-point the sc-compose copies proof-only. |

## ===== briefs/pass-shelat-ch5-8/fills/sc-garble/final-r1/landing/PROVENANCE.txt =====

sc-garble (PS10 §6.2.2-6.2.3: Claim 157.a (i)/(ii), Claim 159.a, Yao's seed, the B1 statement, requirement B2) maintainer delivery review r1, 2026-11-15 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Method: the common review brief ($SP/review-brief-common.md, Updates 1-3) with the sc-ot review as template (records
  briefs/pass-shelat-ch5-8/fills/sc-ot/final-r1/; its evidence dir $SP/dl-review/sc-ot-r1/), the canonizer review's full-file seal
  rule (-DmaxErrors=0, EOF record; C-F02) and the int-315 tools. Nothing pushed, no PR opened, the records checkout only read
  (git fetch and git worktree only). No lake build, no cache get. python3 -I throughout. One Lean process at a time, only on
  $SP/dl-oleans; dl-oleans-2 (the other review) was never touched; only my own PIDs were stopped (the control attempt 1 runner).

issue package: briefs/pass-shelat-ch5-8/fills/sc-garble/issued-r1/ (brief.md SHA-256 203d42ea… = dispatch.md; ruling-SG-1.md; copies
  in logs/). SHA256SUMS 8/8 OK (logs/issue-package-check.txt); SOURCE-SHA256SUMS 166/166 OK at the issue base
  fbd37f447596d4207c8d08b7ef7602f57fe95198 (logs/source-sums-check.txt). base-sorries.txt: 32 in 15 modules. The worker was Codex on
  Seyoon's Mac (host addendum codex-host-2026-11-15), though the brief names Claude.
delivery: exchange/pass-shelat-ch5-8 a73072f19787ee437f2201777711c7eb3154c714 ("fill sc-garble: final"; checkpoints 8313d3d2, 11b3b808).
  The three commits touch only inbox/fills/sc-garble/; no later exchange commit touches it (logs/exchange-commits*.txt). git archive into
  a fresh directory (removed after use); inventory logs/payload-inventory.sha256 (1279 files); cited extracts logs/delivery-extracts/
  (REPORT, both manifests, COMMITS.tsv, scope-request/, final-axiom-summary, seals B-attribution and final-summary, slots.log,
  preflight.log, checkpoint1-push-review, evidence/headers/), 61 files byte-equal to the payload (logs/delivery-extract-hashes.txt).
  Worker REPORT: logs/worker-REPORT.md.
integrity (logs/payload-check.txt, tools/mancheck.py, exact path-set equality):
  - top SHA256SUMS 1278/1278 OK (1279 delivered, manifest excluded); evidence/SHA256SUMS 1254/1254 OK; no missing, no extra, no "./".
  - git am of the 7 patches at fbd37f44 with committer name/email/date from patches/COMMITS.tsv and commit.gpgsign=false
    (logs/git-am-integrity.log): all 7 hashes reproduce (13f745ed … 81795f776e7de58a6ab112d12fbd5be4e7aaa2f8), tree 93f268a6. COMMITS.tsv
    has the signing column, "none" for every row (Update 3 / prf-long F-03 fixed).
  - The 14 changed paths are byte-identical to src/, which holds exactly these 14 files (logs/src-equality.txt): M the 5 owned files
    and M TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean (the approved reader, below); A 8 helpers (Garbling/{CoinBlocks,Probability},
    GarblingSecurity/{CoinMarginals,NestedBounds}, SpecialEncryptionMulti/{SliceParser,SliceReduction},
    SpecialEncryptionSecurity/{Pad,WrongKey}).
  - Codex host (Update 3): logs/delivery-extracts/evidence/logs/preflight.log: headroom 5.05 GiB >= 4 GiB, 219 GiB free; slots.log 543
    acquire/release pairs, all tag sc-garble, never two own holds at once, every lake call -k 3, no lake build. Environment notes
    (REPORT): the auto-approval rejection of the first checkpoint push, the overnight "best judgment" authorization
    (scope-request/autonomy.md): information, not findings.
olean tree: $SP/dl-oleans. tree/snapshot-pre.txt (tools/snapshot.py): 1230 files, 0 empty dirs, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = the required value (byte-equal to the sc-ot and canonizer
  post-restore snapshots); tree/base-records.jsonl copied from sc-ot-r1.
landing: branch land/pass-shelat-sc-garble (local, no upstream), worktree $SP/wt-land-sc-garble (sparse, briefs/ excluded; .lake/packages
  symlinked). The worker head 81795f77 rebased onto origin/cryptography/pass-shelat-ch2-4 1321b9cb358867f5b51974b8c5d0781519a9cfdb
  (#315 merged as 10b9be17, then #317 1d9b2ac3 and #316 1c09448c; landing/landing.log): rc 0, no conflict, range-diff 7/7 identical,
  the 14 paths equal the worker head. A first rebase made with commit.gpgsign=false (9ff9bec5) was discarded and redone with the
  environment's default signing, as for sc-ot. Origin Lean delta since the issue base: #314, #316, #317 (10 files, none a unit file;
  landing/origin-delta-since-issue-base.txt, origin-commits-since-issue-base.txt).
  FINAL head cd9a48438c2a6548fe9e246ce569be57c9df96b3, tree 13aa553d035fd55cf73c7123ebb73c1940019f1c (landing/commits.txt, series
  landing/series/0001-0008), 14 files +1901/-122 vs origin (landing/changed-paths-vs-origin.txt). Worker commits keep Seyoon's
  authorship (committer Claude); all 8 SSH-signed by the environment default:
    6b23a7b1 Prove special encryption and nested wrong-key security   69f7fc89 Prove permutation-independent garbling and Yao seed bounds
    2ca68a8e Prove slice multi-message security from the D4 total      60c71312 Wrap slice reduction proof within the source width limit
    f48ec526 Use explicit local coin-map aliases in the wrong-key proof 04adb34c Use the local prefix-test coin alias in the preservation proof
    e5cb6129 Reuse the published pair-state length bound in slice parsing
    cd9a4843 sc-garble landing edit LE-doc (Claude <noreply@anthropic.com>)
LE-doc (cd9a4843; tools/ledoc_sg.py, 3 exact replacements; landing/le-doc.diff; message landing/commit-msg-le-doc.txt): docstring-only.
  NestedBounds and WrongKey `## Main results` now list their main theorems (nestedSpecial_wrongKeyBot_of_string_bounds,
  uprob_not_good_distinct_le_of_uniform_data; exists_negligible_prefix_collision, spDecStr_none_iff_prefix_ne); the
  `**Proof sketch.**` of nestedSpecial_wrongKeyBot, left as issued by the worker, gains one sentence naming the delivered route.
  landing/le-doc-doconly.txt (tools/doconly_sg.py = doconly.py also stripping /-! -/): code-identical True in the 3 files, same
  docstring counts, 1 changed each, max width 98: RESULT OK. statements/frozen/frozen-check-le.txt: 0 differences after the edit.
build (order/ from tools/downorder.py against eff2dcd0 at the pre-edit head e5cb6129: changed 82 = 68 base delta + 14 unit; down 388 =
  the downstream through root TCSlib and both audits/{pass-shelat,garg-ch1-3}/Checks; DAGCircuit alone puts 273 modules downstream of
  the unit, order/unit-vs-origin/):
  - build/ (order/build-queue.txt, 388 modules, from the base tree): build/summary.txt 388/388 rc 0, 0 errors (G26-N1, both forms),
    substring "error" 0, 2322 s. Unit modules: 0 sorry; non-sorry warnings only SliceParser:168 and NestedBounds:89, both the
    unused-simp-argument linter (SG-F06). Sorry warnings elsewhere only in admitted modules.
  - edit-build/ (order/le-build-queue.txt, 9 modules: WrongKey, SpecialEncryptionSecurity, SpecialEncryptionMulti, NestedBounds,
    GarblingSecurity, Yao, YaoReal, SecureComputation, TCSlib): 9/9 rc 0, 0 errors.
  - Before building, the 330 base oleans the build overwrote were copied aside (tree/backed-up.txt, every hash = snapshot-pre) and the
    58 new ones listed (tree/new-oleans.txt). The tree itself was not copied.
  - tree/tree-check-head.txt (tools/treecheck.py; order/headfull-order.txt, 1257 modules; logs/records-head.jsonl = base records +
    build + edit-build): every module rc 0 at the final-head source with the tree's olean, no stray olean, no empty dir: RESULT OK.
statements (base fbd37f44; the 6 pre-existing files are byte-identical at fbd37f44 and 1321b9cb):
  - tools/frozencheck_sg.py (frozencheck.py + --expect-removed and a `remove` control): statements/frozen/frozen-check.txt (and
    frozen-check-le.txt at the final head): 139 base declarations of the 5 owned files (6+18+37+2+76; the worker's count) and the 72 of
    DAGCircuit: same file, kind, name and order; headers, statement prose and every definition body identical: 0 differences;
    SpecialEncryptionMulti: EXPECTED-REMOVED exactly the six SG-1 helpers (specialScheme_gen_runAt, specialScheme_enc_runAt,
    specialKeyEq, ofFn_specialKeyEq, specialNonceEq, ofFn_specialNonceEq), 6 of 6, zero CHANGED. Controls, each exactly 1 difference
    (statements/frozen/controls-summary.txt): one-character header of specialScheme_multiMessageSecure_of_joint; removal of a seventh
    private declaration (zipWith_xor_append_of_le) -> 1 MISSING; removal of sliceEnc; prose of of_joint; header of spDecStr_wrongKey;
    body of specialScheme; prose of uprob_not_good_le; body of GarbleSeed; header of nestedSpecial_wrongKeyBot; header of
    yaoSeed_good_whp; body of DAGCircuit.IsFaninTwo.
  - Raw diffs: statements/frozen/yao.diff (only the yaoSeed_good_whp body, its sketch and its Main-results bullet; Yao 970 lines),
    specialEncryptionMulti.diff (imports, title, Main results/Contents, the B1 proof and sketch, the six removals, of_joint proof only:
    four reader names and one re-wrap; its docstring untouched), dagcircuit.diff (= the approved fanin-reader.patch line for line).
  - statements/frozen/sg1-private-uses.txt: at fbd37f44 the six names occur only in SpecialEncryptionMulti.lean (project and audits/);
    at the head only the new public readers in SpecialEncryptionSecurity.lean and their uses.
  - statements/head/touched.tsv: 8 CHANGED (the 7 targets, proofs and sketches; of_joint, proof only), 6 REMOVED (SG-1), 15 ADDED,
    40 in new files, 197 UNCHANGED. decls2-vs-base.tsv: 55 ADDED, 0 CHANGED, 0 REMOVED (public). No @[simp], no instance, no abbrev.
  - docaudit: 55 OK, 8 NO-FORMULA = the 6 frozen target proses, of_joint (frozen docstring) and 2 Prop formulas without a relation
    symbol (nestedSpecial_wrongKeyBot_of_string_bounds, polyTimeComputable_slicePost; tool artifact). sketchaudit: 21 theorems with
    >= 15 proof lines, all with a sketch. sizes-widths: max width 100, 0 over 100, Yao 970 <= 1000, all files <= 659.
  - Name clash (clash/nameclash-head.txt, tools/nameclash.py over all TCSlib files at the head): 0 exact full-name clashes, private
    included; zipWith_xor_append_of_le occurs only in SpecialEncryptionMulti.lean. One short-name relative (SG-F07-note):
    SliceReduction.length_encodeList_le vs the private CircuitComplexity/Uniform.lean:208 one (different encodeList).
axioms: probe-sources/head/CensusHead.lean (tools/mkcensus_sg.py) -> probe-runs/ (tools/runner_full.py, nothing written to the tree):
  the 7 targets, uprob_not_good_le_of_perm (B2), uprob_not_good_le_of_uniform_data, uprob_not_good_distinct_le_of_uniform_data,
  garbling_good_whp, specialScheme_multiMessageSecure_of_joint and the helper endpoints: [propext, Classical.choice, Quot.sound];
  DAGCircuit.isFaninTwo_iff: no axioms. yaoHybrid_hbcSecure and yaoProtocol_hbcSecure keep sorryAx. probe-sources/head/DepTrace.lean
  (probe-runs/mods/PlProbe_H_DepTrace.log; its first attempt, a name clash, superseded in the same results.jsonl): the admitted
  declarations in their closures are yaoHybrid_polyTime, yaoHybrid_simulators (sc-yao) for both, plus otProtocol_polyTime,
  otProtocol_simulators (sc-ot, #318) and HybridProtocol.hbcSecure_compose (sc-compose) for yaoProtocol_hbcSecure; yaoSeed_good_whp
  is no longer among them. logs/census-summary.txt: 531 stored constants (= the worker's), sorryAx only in the three Yao hybrid
  constants above. Base: probe-sources/base/CensusBase.lean on the base-phase tree (below) -> base-probe-runs/: every target and
  garbling_good_whp had sorryAx; of_joint was standard. logs/census-base-vs-head.tsv (tools/censuscmp.py, name map
  statements/namemap-sg1.txt: specialKeyEq -> specialScheme_keyCoinsEquiv etc., 4/4 verified same type): removed = the SG-1 privates
  and their auxiliaries; specialScheme_gen_runAt/_enc_runAt moved private -> public with equal types; type-changed 0; axioms-changed
  8 (the 7 targets and garbling_good_whp: sorryAx dropped); added simp/instance/abbrev none.
admissions: logs/sorry-census.txt (tools/sorrycensus.py, records-head.jsonl): issued 32 in 15 modules -> 25 in 11: SpecialEncryptionSecurity
  3 -> 0, SpecialEncryptionMulti 1 -> 0, Garbling 1 -> 0, GarblingSecurity 1 -> 0, Yao 3 -> 2 (yaoHybrid_polyTime:869,
  yaoHybrid_simulators:935); every other issued module unchanged; outside the issued order no module whose source changed since the
  issue base differs.
Rule 10 (final head cd9a4843):
  - Collector probe-sources/head/CollectHead.lean (tools/mkcollect.py) -> probe-runs/. Seals tools/mkseals_ab.py (strict) -> seals/{A,B},
    tools/mkseals_coe.py (FinDist CoeFun instance as notation; canonical) -> seals-coe/{A,B}; logs/mkseals-*.log (requests 0 for
    DAGCircuit, whose closure has no TCSlib definition, up to 2106). 56 head probes seal-runs/ (order/seal-probes-head.txt), each run
    with lean -DmaxErrors=0 (tools/runner_full.py; C-F02); install and EOF records present in every probe.
  - Base: the six base files at the tip (= fbd37f44) need their own closure (a base SpecialEncryptionMulti cannot be sealed against the
    head SpecialEncryptionSecurity, whose public specialScheme_gen_runAt would clash with its private copy). Base phase: sparse
    worktree $SP/wt-sg-base at 1321b9cb (removed), base-build/ = order/base-phase/base-build-queue.txt (32 modules: DAGCircuit up to
    Yao and YaoReal; 32/32 rc 0), then CensusBase, CollectBase (base-probe-runs/), base seals base-seals{,-coe}/{A,B} and 24 probes
    base-seal-runs/ (order/seal-probes-base.txt).
  - logs/seal-head-*.tsv, seal-base-*.tsv (tools/sealsum.py), logs/seal-table-seals.txt and seal-table-seals-coe.txt
    (tools/sealtable.py): A (PolyExpr.eval notation, the canonical rule) head 14/14, base 6/6, strict and coe. B (PolyExpr.eval sealed,
    diagnostic): head 30 errors in 5 files, base 21 in 3 (GarblingSecurity 2, SpecialEncryptionSecurity 4, Yao 15), strict = coe.
    Every head B error read from the raw logs and attributed (logs/seal-B-attribution.txt): all PolyExpr.eval conversions; the 9 new
    ones are in new bodies (spDecStr_wrongKey, specialScheme_wrongKey and nestedSpecial_wrongKeyBot calls; WrongKey 5, NestedBounds 1),
    none a foreign-definition unfold; matches the worker's B-attribution.md.
  - SG-1: specialScheme_multiMessageSecure_of_joint passes A and B, strict and coe, with the new readers (SpecialEncryptionMulti seals).
  - Paired controls tools/mkctl_sg.py (rows PolyExpr.eval, the FinDist CoeFun instance, DAGCircuit.IsFaninTwo (the approved reader),
    spEncStr, Good, and the helper definitions sliceMask, SliceReduction.slicePost, SpecialWrongKey.prefixTest; negative = rfl/Iff.rfl
    unfolding, positive = published reader) -> controls/ (coe, 24 probes, 43 sealed negatives) and controls-strict/ (28, 57); runs
    control-runs/ (order/control-probes.txt). logs/ctlcheck.log: ALL_OK True. logs/ctlcheck-strict.log: every sealed negative fails
    exactly once and every unsealed probe passes; only ctlCoeReader fails in the 14 strict sealed probes (harness effect, as sc-ot
    F-09; logs/controls-strict-attribution.txt). Under the seal the Iff.rfl form of IsFaninTwo fails and isFaninTwo_iff passes: the new
    reader is needed and sufficient. controls-attempt1/, controls-strict-attempt1/, control-runs-attempt1/: the first attempt opened
    Turing in the Garbling probes, which Garbling's closure lacks (every Garbling control failed unsealed); superseded, the runner was
    stopped (my PID only) and the controls regenerated with per-row `open … in` prefixes.
  - Explicit-unfold scan (tools/scan1.py, scan2.py; probe-sources/head/ScanKindsHead.lean -> probe-runs/): scan/items-head.json,
    scan/explicit-head.json, logs/scan2-head.log: 774 items, 594 THEOREM, 31 OWNED_DEFINITION, 147 LOCAL_OR_UNRESOLVED, 2 flagged
    foreign, both local `let` binders (P, g) resolved to global names (logs/scan-attribution.txt): 0 foreign definitions.
lint (scripts/campaign_style_lint.py --check8b, #305 version, identical in the worktree and at the tip):
  - Cryptography: tip 1321b9cb 92 FAIL / 101 WARN (lint/lint-records-tip-1321b9cb.txt, from a git-archive export, removed), landing
    head 92/101 (lint/lint-landing-head.txt); identical line sets (lint/linediff.txt: only the file count 350 -> 358).
  - Complexity: 25 / 391 at both; the one changed line is DAGCircuit's check-8 WARN, which loses IsFaninTwo (it now has a reader).
  - Old lint for continuity (tools/campaign_style_lint_old_rooted.py, LINT_ROOT): 241/101 -> 249/101; the +8 are the facade class
    "SecureComputation.lean does not import child module …" for the 8 helpers (lint/oldlint-linediff.txt), fixed by #305: recorded.
content: every changed hunk and the helpers read. specialScheme_multiMessageSecure is proved directly from D4
  (MultiMsg.exists_negligible_distAdv_prfEncRealOut at masks 0^n ++ m_i, relabelled coins, acceptProb_comp_equiv), upstream of the
  corollary, as the import direction requires. spDecStr_wrongKey: hG'.easy's evaluator, exists_oneQuery_nuppt, D1 at budget 1
  (exists_negligible_prefix_collision: prfAdv + 2^-n), ε = that + 2^-n for the strict < (n = 0 included). specialScheme_wrongKey:
  the string bound at ℓ = n, coin relabelling, the dec coins averaged out (uprob_fst), the overlong failure word decodes to none.
  nestedSpecial_wrongKeyBot: two string bounds, δ = ε₁ + ε₂, the case analysis in nestedSpecial_wrongKeyBot_of_string_bounds
  (0, 1, 2 positions). B2 uprob_not_good_le_of_perm has the brief's exact signature; it is a corollary of the stronger
  uprob_not_good_le_of_uniform_data (uniform keys/row coins, permutations may depend on the seed), proved through
  good_of_no_crossOpening (correct row opens, no cross-opening => first success is the right key; row order irrelevant), 12 events per
  gate (arity <= 2, Finset count), uprob_exists_le twice. uprob_not_good_le averages B2 over uniform permutations. yaoSeed_good_whp
  uses the uniform-data form with Yao's XOR shifts as the seed-dependent permutations, pushesUniform_key_row_blocks for the disjoint
  key/row-coin blocks (b*S+v and 2S+2(4i+idx(a))+b, injective below 10S), and the output collision m/|K| = outLen·2^-n;
  δ = 12·S·δ₀ + outLen·2^-n. B1: Option of fitting configurations, none = 0 (empty-fit convention), unary slice advice, slicePost
  parser, D' = D ∘ P by exists_slicePost_nuppt, D4's ε before the masks, distAdv_comp and acceptProb_coins_equiv; the none branch
  uses D4 at equal zero masks for 0 <= ε. Gate 27 hand-off obligations (1)-(6) map as REPORT § Gate 27 says. Edge cases listed in
  the brief are covered (n = 0 strictness, no fitting slice, q = 0, empty messages, exact fits, arity 0/1/2, constant gates,
  |gates| = 0, repeated outputs).
duplication: logs/duplication-review.txt; dup/getd-headd-added-lines.txt. Findings SG-F04 (new undisclosed getD-of-ofFn chain,
  CoinBlocks:73), SG-F05 (placement), notes.
open PRs (logs/open-prs.txt, logs/open-pr-overlap.txt; heads fetched): #313 94b31964, #318 f62a25b3, #319 6421ac16 (#320 is the
  Arora-Barak Ladner PR, out of scope). git merge-tree --write-tree of the landing head (pre-edit e5cb6129) with each: clean (#313
  a345574e, #318 9fdd95fd, #319 a53254aa); no shared file; no PR-changed module in the unit's upstream closure; shared downstream
  #313: Randomness, Randomness/Learning, TCSlib; #318: YaoReal, SecureComputation, TCSlib; #319: 33 modules through DAGCircuit's
  downstream (CircuitComplexity, Randomized, Randomness, Asymptotic, audits/pass-shelat/Checks). No short-name coincidence with any PR's
  added declarations (clash/unit-new-short-names.txt). The merge trees were not built (integration builds are the maintainer's).
restore (restore/restore-log.txt, tools/restore.sh): 330 backups copied back (0 hash failures), 58 new oleans deleted, 10 emptied
  directories pruned (restore/empty-dirs-before-prune.txt); the base-phase oleans were among the 330. No probe olean was ever written
  (runner_full.py has no -o). tree/snapshot-post.txt: 1230 files, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f,
  byte-identical to tree/snapshot-pre.txt (SNAPSHOT EQUAL); tree/tree-check-post.txt: 1199 base modules at the eff2dcd0 source and
  record hashes, snapshot equal: RESULT OK.
tools/: sc-ot-r1 tools, plus canonizer's probefull.sh, fullsealmap.py, mkcensus_canon.py, mkctl_canon.py and int-315's buildset.py,
  bothdown.py, refunion.py, refcmp.py, restoreplan.py. New here: frozencheck_sg.py, mkcensus_sg.py, mkctl_sg.py, ledoc_sg.py,
  doconly_sg.py, runner_full.py (runner.py's records with lean -DmaxErrors=0 and no -o). runner.py unchanged (G26-N1).
cleanup: payload extraction, olean backups (bk-sg), the integrity worktree wt-sg-int and the base worktree wt-sg-base (git worktree
  remove --force), the tip lint export and the PlProbe/ directories removed. The landing worktree is clean at cd9a4843.
SHA256SUMS: every file here except itself (paths without "./"). ../sc-garble-r1-evidence.zip holds exactly the manifest's paths plus
  SHA256SUMS.

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

## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/pr-description.md =====

This is the landing PR for the Pass–shelat `sc-garble` fill (unit U1). It proves seven admitted statements of `SecureComputation/` [PS10, §6.2.2–6.2.3] and the stronger garbling bound B2.

**Head:** `cd9a48438c2a6548fe9e246ce569be57c9df96b3`. **Base:** `cryptography/pass-shelat-ch2-4` at `1321b9cb`, which includes #311 and #314–#317.

## Targets proved
- **In `SpecialEncryptionSecurity.lean`:** `spDecStr_wrongKey`, `specialScheme_wrongKey` and `specialScheme_multiMessageSecure`. The last is Claim 157.a (i), proved directly from prf-long's D4.
- **In `GarblingSecurity.lean`:** `nestedSpecial_wrongKeyBot`.
- **In `Garbling.lean`:** `uprob_not_good_le`, Claim 159.a. It is derived from B2, `uprob_not_good_le_of_perm`.
- **In `Yao.lean`:** `yaoSeed_good_whp`. Only its body changes; the file has 970 lines.
- **In `SpecialEncryptionMulti.lean`:** `sliceMultiMessageSecure_of_prfOut`, the B1 statement from #311.

## Changes
14 Lean files, +1901/−122:
- the five owned files;
- eight helpers under `Garbling/`, `GarblingSecurity/`, `SpecialEncryptionMulti/` and `SpecialEncryptionSecurity/`;
- `Complexity/CircuitComplexity/DAGCircuit.lean`, which gains the `Iff.rfl` reader `isFaninTwo_iff`. Seyoon approved this addition (SG-F01, 2026-11-15).

**Ruling SG-1** allows deleting six private relabelling helpers in `SpecialEncryptionMulti.lean`. Their work is now done by public readers beside `specialScheme`, and `specialScheme_multiMessageSecure_of_joint` is re-proved through those readers, changing the proof only.

**Commits:** seven Codex worker commits, then **LE-doc** `cd9a4843`. LE-doc fills in two `## Main results` sections and adds one sketch route note; it changes docstrings only.

## Review
The maintainer's review is in `briefs/pass-shelat-ch5-8/fills/sc-garble/final-r1/review.md`. Its verdict is **ACCEPT WITH LANDING EDITS**.
- **Statements:**
  - The frozen check finds 0 differences.
  - The SG-1 check finds exactly six REMOVED and nothing CHANGED. Both controls behave as expected, including the seventh-removal control.
  - decls2 gives 55 ADDED and 0 CHANGED.
  - There are no name clashes.
- **Axioms:** the seven targets, B2 and `of_joint` use only the standard three.
- **Build:** 388/388 modules give rc 0, with 0 errors in both forms. The whole-tree check covers 1257 modules: OK.
- **Rule 10:**
  - Seal A passes everywhere, strict and coe.
  - Seal B's 9 new errors are all `PolyExpr.eval` conversions.
  - The controls are ALL_OK, apart from the strict `ctlCoeReader`, which is a known harness effect.
- **Admissions:** 32 → 25.
- **Lint:** unchanged.
- **Ledger:** SG-F04, a new inline getD-of-`List.ofFn` chain in `Garbling/CoinBlocks.lean`, is added to DL-47 under Seyoon's ruling.

`yaoProtocol_hbcSecure` still depends on `sorryAx` through sc-yao (`yaoHybrid_*`), sc-ot (#318) and `hbcSecure_compose` (sc-compose).

A Codex gate follows. Seyoon merges.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/pr.diff.txt =====

diff --git a/TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean b/TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean
index 4bd1332fe..178ba19fc 100644
--- a/TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean
+++ b/TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean
@@ -507,6 +507,15 @@ def IsWellFormed : Prop :=
 def IsFaninTwo : Prop :=
   C.IsWellFormed ∧ ∀ g ∈ C.gates, g.args.length ≤ 2
 
+/-- A circuit is fan-in two exactly when each gate has distinct arguments, each negation
+gate has one argument, and every gate has at most two arguments:
+`C.IsFaninTwo ↔ (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
+  ∀ g ∈ C.gates, g.args.length ≤ 2`. [AB09, Definition 6.1] -/
+theorem isFaninTwo_iff :
+    C.IsFaninTwo ↔
+      (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
+        ∀ g ∈ C.gates, g.args.length ≤ 2 := Iff.rfl
+
 /-- The vertex-value list of a circuit has one entry per vertex: `n` inputs plus one per
 gate. -/
 @[simp] theorem length_values (x : Fin n → Bool) :
diff --git a/TCSlib/Cryptography/SecureComputation/Garbling.lean b/TCSlib/Cryptography/SecureComputation/Garbling.lean
index 21db7810b..55b29ba95 100644
--- a/TCSlib/Cryptography/SecureComputation/Garbling.lean
+++ b/TCSlib/Cryptography/SecureComputation/Garbling.lean
@@ -6,13 +6,15 @@ import TCSlib.Complexity.CircuitComplexity.DAGCircuit
 import Mathlib.Data.Fintype.Pi
 import Mathlib.Data.Fintype.Perm
 import TCSlib.Cryptography.Foundations.Probability
+import TCSlib.Cryptography.SecureComputation.Garbling.Probability
+import TCSlib.Cryptography.SecureComputation.Garbling.CoinBlocks
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Garbled circuits (statement phase)
+# Garbled circuits
 
 [PS10, §6.2.1–6.2.3]. Construction 158.a (inventory): to garble a circuit `C` with fan-in two,
 associate two random keys `k_w^0, k_w^1` to every wire `w`. Each gate becomes a table with one
@@ -65,8 +67,15 @@ The special encryption scheme of Algorithm 157.2 gives both, nested (`GarblingSp
   encoding.
 * `SecureComputation.garbledValues_getD`, `garbledOutput_eq` (Claim 159.a, deterministic part,
   proved): a good garbling evaluates to the keys of the circuit's values, and of `C(x)`.
-* `SecureComputation.uprob_not_good_le` (Claim 159.a, probabilistic part, stated; a `sorry` under
-  a sketch): a garbling is good except with probability `12 · |gates| · δ`.
+* `SecureComputation.uprob_not_good_le_of_perm` (B2): the failure bound holds for every
+  fixed row-permutation family; `uprob_not_good_le` averages this bound over uniform permutations.
+* `SecureComputation.uprob_not_good_le_of_uniform_data`: uniform keys and row coins suffice,
+  even when row permutations depend on the seed.
+
+## Contents
+
+* `Garbling.Probability`: independent marginals and the first successful opening.
+* `Garbling.CoinBlocks`: the joint uniform law of disjoint key and row-coin blocks.
 
 ## References
 
@@ -403,25 +412,248 @@ theorem garbledOutput_eq (s : GarbleSeed Cc K ρ) (hgood : Good M Cc s) (x : Fin
       ((DAGCircuit.size_eq Cc).symm ▸ Cc.output_lt)).trans
       (congrArg (keyAt Cc s Cc.output) (DAGCircuit.eval_eq Cc x).symm))
 
+/-- Correct rows and no successful cross-opening imply a good garbling:
+if `M` is correct, `Cc` is fan-in two, and for every gate and `a ≠ a'`,
+`M.dec (argKeys Cc s i a') (garbledRow M Cc s i a) = none`, then `Good M Cc s`.
+[PS10, §6.2.3, Claim 159.a]
+
+**Proof sketch.** The row for the current assignment opens by correctness. It occurs
+in the permuted table because the row permutation is surjective. Every other assignment's
+row fails by the cross-opening hypothesis. Thus each table has a successful row and every
+successful row gives the specified key, so its first successful opening is that key. -/
+theorem good_of_no_crossOpening (hdec : M.DecCorrect) (hC : Cc.IsFaninTwo)
+    (s : GarbleSeed Cc K ρ)
+    (hcross : ∀ (i : Fin Cc.gates.length)
+      (a a' : Fin (Cc.gates[i]).args.length → Bool), a ≠ a' →
+        M.dec (argKeys Cc s i a') (garbledRow M Cc s i a) = none) : Good M Cc s := by
+  classical
+  rw [good_iff]
+  intro i a
+  have hlen : (argKeys Cc s i a).length ≤ 2 := by
+    rw [argKeys_eq, List.length_ofFn]
+    exact ((DAGCircuit.isFaninTwo_iff Cc).mp hC).2 _ (List.getElem_mem i.isLt)
+  have hcorrect : M.dec (argKeys Cc s i a) (garbledRow M Cc s i a) =
+      some (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a)) := by
+    rw [garbledRow_eq]
+    exact (MultiEnc.decCorrect_iff M).mp hdec _ hlen _ _
+  rw [garbledTable_eq]
+  apply GarblingProbability.findSome_eq_some_of_dichotomy
+  · refine ⟨garbledRow M Cc s i a, ?_, hcorrect⟩
+    apply List.mem_map.mpr
+    refine ⟨(s.2.2 i).symm a, ?_, ?_⟩
+    · exact Finset.mem_toList.mpr (Finset.mem_univ _)
+    · rw [Equiv.apply_symm_apply]
+  · intro row hrow
+    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hrow
+    by_cases hba : s.2.2 i b = a
+    · right
+      rw [hba]
+      exact hcorrect
+    · exact Or.inl (hcross i (s.2.2 i b) a hba)
+
+/-- A wrong-key probability bound is nonnegative:
+`M.WrongKeyBot δ → 0 ≤ δ`. Use distinct choices at one position and any plaintext key. -/
+theorem wrongKeyBot_nonneg [Fintype K] [Fintype ρ] {δ : ℝ}
+    (hδ : M.WrongKeyBot δ) : 0 ≤ δ := by
+  have h := (MultiEnc.wrongKeyBot_iff M δ).mp hδ 1 (by decide)
+    (fun _ => false) (fun _ => true)
+    (by intro heq; have hbit := congrFun heq 0; cases hbit) default
+  exact (uprob_nonneg _).trans h
+
+/-- At a fixed gate, two distinct assignments cross-open with probability at most `δ`,
+for every fixed row-permutation family `π`:
+`Pr_t[(M.dec (argKeys Cc (t.1,t.2,π) i a')
+  (garbledRow M Cc (t.1,t.2,π) i a)).isSome = true] ≤ δ` when `a ≠ a'`.
+[PS10, §6.2.3, Claim 159.a]
+
+**Proof sketch.** The circuit's argument vertices are distinct and precede this gate's
+output vertex. Restrict the uniform key table to these vertices and the selected output
+key, and read the row's independent coins. This gives a uniform plaintext key, argument
+key table and row coin. Average `WrongKeyBot` over the plaintext key. The row order is
+unused by a cross-opening event. -/
+theorem uprob_crossOpening_le_of_perm [Fintype K] [Fintype ρ] {δ : ℝ}
+    (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
+    (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool))
+    (i : Fin Cc.gates.length) (a a' : Fin (Cc.gates[i]).args.length → Bool) (hne : a ≠ a') :
+    uprob (fun t : (Fin Cc.size → Bool → K) ×
+        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
+      (M.dec (argKeys Cc (t.1, t.2, π) i a')
+        (garbledRow M Cc (t.1, t.2, π) i a)).isSome = true) ≤ δ := by
+  classical
+  have hfan := (DAGCircuit.isFaninTwo_iff Cc).mp hC
+  have hmem : Cc.gates[i] ∈ Cc.gates := List.getElem_mem i.isLt
+  have hnodup := (hfan.1 _ hmem).1
+  have hlen := hfan.2 _ hmem
+  have hout : n + i < Cc.size := by rw [DAGCircuit.size_eq]; omega
+  have harglt : ∀ j : Fin (Cc.gates[i]).args.length,
+      (Cc.gates[i]).args[j] < n + i :=
+    fun j => Cc.args_lt i i.isLt _ (List.getElem_mem j.isLt)
+  have hargSize : ∀ j : Fin (Cc.gates[i]).args.length,
+      (Cc.gates[i]).args[j] < Cc.size := fun j => (harglt j).trans hout
+  let arg : Fin (Cc.gates[i]).args.length → Fin Cc.size :=
+    fun j => ⟨(Cc.gates[i]).args[j], hargSize j⟩
+  have hinj : Function.Injective arg := by
+    intro j k hjk
+    have hv := congrArg Fin.val hjk
+    change (Cc.gates[i]).args.get j = (Cc.gates[i]).args.get k at hv
+    exact hnodup.get_inj_iff.mp hv
+  let out : Fin Cc.size := ⟨n + i, hout⟩
+  have hnot : ∀ j, arg j ≠ out := fun j h =>
+    (Nat.ne_of_lt (harglt j)) (congrArg Fin.val h)
+  let R := (k : Fin Cc.gates.length) → (Fin (Cc.gates[k]).args.length → Bool) → ρ
+  have hlaw := GarblingProbability.pushesUniform_output_argKeys_row (K := K)
+    arg hinj out hnot
+    (gateOut (Cc.gates[i]) a) (fun r : R => r i a)
+    (GarblingProbability.pushesUniform_rowCoin
+      (A := fun k : Fin Cc.gates.length => Fin (Cc.gates[k]).args.length → Bool)
+      (ρ := ρ) i a)
+  let p : K × ((Fin (Cc.gates[i]).args.length → Bool → K) × ρ) → Prop := fun z =>
+    (M.dec (List.ofFn fun j => z.2.1 j (a' j))
+      (M.enc (List.ofFn fun j => z.2.1 j (a j)) z.1 z.2.2)).isSome = true
+  have hu := hlaw.uprob_eq p
+  calc
+    _ = uprob (fun t : (Fin Cc.size → Bool → K) × R =>
+        p (t.1 out (gateOut (Cc.gates[i]) a), (fun j => t.1 (arg j), t.2 i a))) := by
+      apply OneWay.uprob_congr
+      intro t
+      simp only [garbledRow_eq, argKeys_eq, keyAt_eq, hargSize, hout, dif_pos]
+      rfl
+    _ = uprob p := hu
+    _ ≤ δ := by
+      rw [uprob_prod]
+      exact (OneWay.uexp_mono (fun o : K =>
+        (MultiEnc.wrongKeyBot_iff M δ).mp hδ _ hlen a a' hne o)).trans
+          (OneWay.uexp_const δ).le
+
+/-- Uniform independent keys and row coins suffice for the garbling bound, with arbitrary
+row orders on the same seed space:
+`PushesUniform d → Pr_w[¬ Good M Cc ((d w).1,(d w).2,π w)] ≤ 12 * |Cc.gates| * δ`.
+The permutation `π w` may depend on any seed information; no independence from it is needed.
+[PS10, §6.2.3, Claim 159.a, strengthened seed-law form]
+
+**Proof sketch.** Goodness follows whenever no row cross-opens under a different assignment.
+Each cross-opening ignores row order, so its probability is transported by the uniform
+key/coin marginal and bounded by `WrongKeyBot`. A gate of arity at most two has at most
+four assignments and three different assignments per row. Apply the finite union bound
+within each gate and then over all gates. This proves the fixed-permutation B2 statement
+as a special case and also covers Yao's seed-dependent XOR shifts. -/
+theorem uprob_not_good_le_of_uniform_data [Fintype K] [Fintype ρ]
+    (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
+    {Ω : Type} [Fintype Ω]
+    (d : Ω → (Fin Cc.size → Bool → K) ×
+      ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ))
+    (hd : HardcoreBit.PushesUniform d)
+    (π : Ω → (i : Fin Cc.gates.length) →
+      Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)) :
+    uprob (fun w => ¬ Good M Cc ((d w).1, (d w).2, π w)) ≤
+      12 * Cc.gates.length * δ := by
+  classical
+  let event : (i : Fin Cc.gates.length) →
+      (Fin (Cc.gates[i]).args.length → Bool) →
+      (Fin (Cc.gates[i]).args.length → Bool) → Ω → Prop := fun i a a' w =>
+    (M.dec (argKeys Cc ((d w).1, (d w).2, π w) i a')
+      (garbledRow M Cc ((d w).1, (d w).2, π w) i a)).isSome = true
+  let gateBad : Fin Cc.gates.length → Ω → Prop := fun i w =>
+    ∃ a ∈ Finset.univ, ∃ a' ∈ Finset.univ.erase a, event i a a' w
+  have hpoint : ∀ i a a', a ≠ a' → uprob (event i a a') ≤ δ := by
+    intro i a a' hne
+    let π₀ : (i : Fin Cc.gates.length) →
+        Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool) := fun _ => Equiv.refl _
+    let p := fun t : (Fin Cc.size → Bool → K) ×
+        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
+      (M.dec (argKeys Cc (t.1, t.2, π₀) i a')
+        (garbledRow M Cc (t.1, t.2, π₀) i a)).isSome = true
+    have heq : event i a a' = fun w => p (d w) := rfl
+    rw [heq, hd.uprob_eq p]
+    exact uprob_crossOpening_le_of_perm M Cc hδ hC π₀ i a a' hne
+  have hbad : ∀ w, ¬ Good M Cc ((d w).1, (d w).2, π w) →
+      ∃ i ∈ Finset.univ, gateBad i w := by
+    intro w hw
+    by_contra hn
+    apply hw
+    apply good_of_no_crossOpening M Cc hdec hC
+    intro i a a' hne
+    apply Option.not_isSome_iff_eq_none.mp
+    intro hs
+    exact hn ⟨i, Finset.mem_univ _, a, Finset.mem_univ _, a',
+      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩, hs⟩
+  have hgate : ∀ i, uprob (gateBad i) ≤ 12 * δ := by
+    intro i
+    let A := Fin (Cc.gates[i]).args.length → Bool
+    have hlen : (Cc.gates[i]).args.length ≤ 2 :=
+      ((DAGCircuit.isFaninTwo_iff Cc).mp hC).2 (Cc.gates[i]) (List.getElem_mem i.isLt)
+    have hcardNat : Fintype.card A * (Fintype.card A - 1) ≤ 12 := by
+      simp only [A, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
+      have hcases : (Cc.gates[i]).args.length = 0 ∨ (Cc.gates[i]).args.length = 1 ∨
+          (Cc.gates[i]).args.length = 2 := by omega
+      rcases hcases with h0 | h1 | h2
+      · rw [h0]; decide
+      · rw [h1]; decide
+      · rw [h2]; decide
+    have hcard : ((Fintype.card A * (Fintype.card A - 1) : ℕ) : ℝ) ≤ 12 := by
+      exact_mod_cast hcardNat
+    have herase (a : A) : (Finset.univ.erase a).card = Fintype.card A - 1 := by
+      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
+    refine (uprob_exists_le (Finset.univ : Finset A)
+      (fun a w => ∃ a' ∈ Finset.univ.erase a, event i a a' w)).trans ?_
+    calc
+      _ ≤ ∑ a ∈ (Finset.univ : Finset A), ∑ a' ∈ Finset.univ.erase a, δ := by
+        apply Finset.sum_le_sum
+        intro a ha
+        refine (uprob_exists_le (Finset.univ.erase a) (fun a' w => event i a a' w)).trans ?_
+        exact Finset.sum_le_sum fun a' ha' =>
+          hpoint i a a' (Finset.mem_erase.mp ha').1.symm
+      _ = ((Fintype.card A * (Fintype.card A - 1) : ℕ) : ℝ) * δ := by
+        simp only [Finset.sum_const, herase, Finset.card_univ, nsmul_eq_mul,
+          Nat.cast_mul, mul_assoc]
+      _ ≤ 12 * δ := mul_le_mul_of_nonneg_right hcard (wrongKeyBot_nonneg M hδ)
+  calc
+    _ ≤ uprob (fun w => ∃ i ∈ Finset.univ, gateBad i w) := uprob_mono hbad
+    _ ≤ ∑ i ∈ Finset.univ, uprob (gateBad i) := uprob_exists_le _ _
+    _ ≤ ∑ i ∈ Finset.univ, 12 * δ := Finset.sum_le_sum fun i _ => hgate i
+    _ = 12 * Cc.gates.length * δ := by
+      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
+      rw [mul_left_comm, ← mul_assoc]
+
+/-- **B2: goodness for every fixed row-permutation family.** For uniform independent
+keys and row coins and any fixed `π`,
+`Pr_t[¬ Good M Cc (t.1,t.2,π)] ≤ 12 * Cc.gates.length * δ`.
+[PS10, §6.2.3, Claim 159.a, strengthened permutation form]
+
+**Proof sketch.** Apply the uniform-data bound to the identity map on the key/coin product
+and the constant row-permutation family. This is the prescribed fixed-permutation B2 API. -/
+theorem uprob_not_good_le_of_perm [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
+    (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
+    (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)) :
+    uprob (fun t : (Fin Cc.size → Bool → K) ×
+        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
+      ¬ Good M Cc (t.1, t.2, π)) ≤ 12 * Cc.gates.length * δ := by
+  exact uprob_not_good_le_of_uniform_data M Cc hdec hδ hC
+    (fun t => t) HardcoreBit.pushesUniform_id (fun _ => π)
+
 /-- **Claim 159.a, probabilistic part: a garbling is good with high probability** [PS10, §6.2.3,
 "all but one row will evaluate to `⊥`"]: for a fan-in-two circuit and a multi-key encryption
 that is correct and has the wrong-key property with error `δ`, a uniformly random garbling fails
 to be good with probability at most `12 · |gates| · δ`. The formal conclusion bounds failure
 of first-success correctness; it does not state the source's stronger unique-opening claim.
 
-**Proof sketch.** Fix a gate `i` and an assignment `a`.
-1. By correctness, the row of `a` decrypts under `a`'s keys to the right key. So `Good` can fail
-   at `(i, a)` only if another row, of an assignment `a'' ≠ a`, decrypts under `a`'s keys.
-2. The arguments are distinct vertices (`IsWellFormed`: no duplicates), and they precede the
-   gate's own vertex. So the keys of the argument positions are independent uniform pairs, and
-   the plaintext key and the row's coin are independent of them. By `WrongKeyBot`, averaged over
-   the plaintext and the coin, that event has probability at most `δ`.
-3. A gate has at most `2^2 = 4` assignments and `3` other rows each: at most `12` events per gate.
-   The union bound over the gates gives `12 · |gates| · δ`. The permutations play no role in
-   correctness. -/
+**Proof sketch.** Reassociate a uniform garbling seed as a permutation family and an
+independent key/coin pair. For each fixed permutation family apply the stronger B2 theorem
+`uprob_not_good_le_of_perm`. Average its constant bound with finite Fubini and the constant
+expectation identity. B2 itself bounds the at most twelve cross-opening events per gate. -/
 theorem uprob_not_good_le [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
     (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) :
     uprob (fun s : GarbleSeed Cc K ρ => ¬ Good M Cc s) ≤ 12 * Cc.gates.length * δ := by
-  sorry
+  let D := (Fin Cc.size → Bool → K) ×
+    ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ)
+  let P := (i : Fin Cc.gates.length) →
+    Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)
+  let e : GarbleSeed Cc K ρ ≃ P × D :=
+    (Equiv.prodAssoc (Fin Cc.size → Bool → K)
+      ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) P).symm.trans
+        (Equiv.prodComm D P)
+  rw [← uprob_comp_equiv e.symm, uprob_prod]
+  exact (OneWay.uexp_mono (fun π : P =>
+    uprob_not_good_le_of_perm M Cc hdec hδ hC π)).trans (OneWay.uexp_const _).le
 
 end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/Garbling/CoinBlocks.lean b/TCSlib/Cryptography/SecureComputation/Garbling/CoinBlocks.lean
new file mode 100644
index 000000000..71d4ecf56
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/Garbling/CoinBlocks.lean
@@ -0,0 +1,206 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.Garbling.Probability
+import Mathlib.Logic.Equiv.Fin.Basic
+import Mathlib.Data.List.GetD
+import Mathlib.Tactic.Ring
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Uniform key and row-coin blocks
+
+## Main definitions
+
+This module adds no definitions.
+
+## Main results
+
+* `GarblingProbability.pushesUniform_key_row_blocks`: the key and row-coin blocks used
+  by Yao have a uniform joint law, including zero-length blocks.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, §6.2.3, Claim 159.a.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.GarblingProbability
+
+open TCSlib.Cryptography
+
+/-- For `len ≤ 2`, the binary fold `a₀ + 2(a₁ + 2(⋯))` is below four and injective:
+`(∀ a, (List.ofFn a).foldr (fun b k => b.toNat + 2*k) 0 < 4) ∧
+  Function.Injective (fun a => (List.ofFn a).foldr (fun b k => b.toNat + 2*k) 0)`. -/
+theorem assignmentFold_small (len : ℕ) (hlen : len ≤ 2) :
+    (∀ a : Fin len → Bool, (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 4) ∧
+      Function.Injective (fun a : Fin len → Bool =>
+        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) := by
+  interval_cases len <;> decide
+
+/-- Selecting distinct blocks of `n` bits preserves the uniform law:
+`r ↦ (fun i t => (List.ofFn r).getD (c i * n + t) false)` pushes uniform to uniform,
+for an injection `c : I → Fin B` and any unused tail of length `tail`.
+
+**Proof sketch.** The product equivalence embeds a block and its bit into `Fin (B*n)`.
+Compose this injection with the inclusion into the raw coin space and restrict its uniform
+bit table. Currying the restricted table gives the claimed family of independent blocks. -/
+theorem pushesUniform_bits_of_blocks {I : Type} [Fintype I] [DecidableEq I]
+    {B n tail : ℕ} (c : I → Fin B) (hinj : Function.Injective c) :
+    HardcoreBit.PushesUniform (fun r : Fin (B * n + tail) → Bool =>
+      fun i (t : Fin n) => (List.ofFn r).getD ((c i : ℕ) * n + t) false) := by
+  let select : I × Fin n → Fin (B * n + tail) :=
+    fun p => Fin.castAdd tail (finProdFinEquiv (c p.1, p.2))
+  have hselect : Function.Injective select := by
+    intro x y hxy
+    have hp : (c x.1, x.2) = (c y.1, y.2) := by
+      apply (finProdFinEquiv (m := B) (n := n)).injective
+      apply Fin.castAdd_injective (B * n) tail
+      exact hxy
+    apply Prod.ext
+    · exact hinj (congrArg (fun p : Fin B × Fin n => p.1) hp)
+    · exact congrArg (fun p : Fin B × Fin n => p.2) hp
+  have h := (HardcoreBit.pushesUniform_restrict (O := Bool) hselect).comp
+    (HardcoreBit.pushesUniform_equiv (Equiv.curry I (Fin n) Bool))
+  convert h using 1
+  funext r i t
+  have heq : (select (i, t) : ℕ) = (c i : ℕ) * n + t := by
+    simp only [select, Fin.coe_castAdd, finProdFinEquiv_apply_val]
+    ring
+  rw [← heq, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact (select (i, t)).isLt),
+    List.getElem_ofFn]
+  rfl
+
+/-- Key blocks `b*S+v` and row-half blocks `2*S+2*(4*i+idx i a)+b` are distinct and below
+`10*S`, if `V,G ≤ S` and each `idx i` is an injection into `{0,1,2,3}`.
+
+**Proof sketch.** Key indices are below `2*S`; row indices start there. Within keys, the
+bit separates the two intervals. Within rows, bounds on the half-bit and assignment index
+recover first the gate, then the assignment, then the half-bit. -/
+theorem key_row_blocks_injective {S V G : ℕ} (hV : V ≤ S) (hG : G ≤ S)
+    {A : Fin G → Type} (idx : (i : Fin G) → A i → ℕ)
+    (hidx : ∀ i a, idx i a < 4) (hinj : ∀ i, Function.Injective (idx i)) :
+    let c : (Fin V × Bool) ⊕ ((Σ i, A i) × Bool) → ℕ :=
+      Sum.elim (fun p => p.2.toNat * S + p.1)
+        (fun p => 2 * S + (4 * p.1.1 + idx p.1.1 p.1.2) * 2 + p.2.toNat)
+    (∀ p, c p < 10 * S) ∧ Function.Injective c := by
+  dsimp only
+  have hb (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
+  have hk (p : Fin V × Bool) : p.2.toNat * S + p.1 < 2 * S := by
+    have hm := Nat.mul_le_mul_right S (hb p.2)
+    have hv := p.1.isLt
+    simp only [Nat.one_mul] at hm
+    omega
+  constructor
+  · intro p
+    cases p with
+    | inl p =>
+      simp only [Sum.elim_inl]
+      have hh := hk p
+      omega
+    | inr p =>
+      simp only [Sum.elim_inr]
+      have hi := p.1.1.isLt
+      have ha := hidx p.1.1 p.1.2
+      have hh := hb p.2
+      omega
+  · intro x y hxy
+    cases x with
+    | inl x =>
+      cases y with
+      | inl y =>
+        obtain ⟨x, b⟩ := x
+        obtain ⟨y, c⟩ := y
+        have hx := x.isLt
+        have hy := y.isLt
+        change b.toNat * S + x.val = c.toNat * S + y.val at hxy
+        have hbc : b = c := by
+          cases b <;> cases c <;> simp_all only [Bool.toNat_false, Bool.toNat_true,
+            Nat.zero_mul, Nat.one_mul] <;> omega
+        subst c
+        have hval : x.val = y.val := Nat.add_left_cancel hxy
+        exact congrArg Sum.inl (Prod.ext (Fin.ext hval) rfl)
+      | inr y =>
+        have hx := hk x
+        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
+        omega
+    | inr x =>
+      cases y with
+      | inl y =>
+        have hy := hk y
+        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
+        omega
+      | inr y =>
+        obtain ⟨⟨i, a⟩, b⟩ := x
+        obtain ⟨⟨j, a'⟩, c⟩ := y
+        have ha := hidx i a
+        have ha' := hidx j a'
+        have hbit := hb b
+        have hbit' := hb c
+        simp only [Sum.elim_inr] at hxy
+        have hij : i = j := Fin.ext (by omega)
+        subst j
+        have haa : a = a' := hinj i (by omega)
+        subst a'
+        have hbc : b = c := by cases b <;> cases c <;> simp_all
+        subst c
+        rfl
+
+/-- The joint key/row-coin law of Yao's block layout is uniform. For `V,G ≤ S`, row index
+injections `idx i : A i → {0,1,2,3}`, and uniform `10*S*n+2*S` bits, the keys read at
+`(b*S+v)*n` and the two row halves read at `2*S*n+(4*i+idx i a)*(2*n)` and that offset
+plus `n` form independent uniform tables. [PS10, §6.2.3, Claim 159.a]
+
+**Proof sketch.** Embed key blocks and row-half blocks into `Fin (10*S)` using their
+intervals, and restrict the raw uniform bit table to those blocks. Split the sum of the
+key and row indices. Curry the key indices, curry the row-half indices, turn each pair
+of Boolean-indexed row halves into a product, and curry the dependent row index. All
+these maps are equivalences, so the joint uniform law is preserved. -/
+theorem pushesUniform_key_row_blocks {S V G n : ℕ} (hV : V ≤ S) (hG : G ≤ S)
+    {A : Fin G → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
+    (idx : (i : Fin G) → A i → ℕ) (hidx : ∀ i a, idx i a < 4)
+    (hinj : ∀ i, Function.Injective (idx i)) :
+    HardcoreBit.PushesUniform (fun r : Fin (10 * S * n + 2 * S) → Bool =>
+      ((fun (v : Fin V) (b : Bool) (t : Fin n) =>
+          (List.ofFn r).getD ((b.toNat * S + v) * n + t) false),
+        fun i a =>
+          ((fun t : Fin n =>
+            (List.ofFn r).getD (2 * S * n + (4 * i + idx i a) * (2 * n) + t) false),
+           (fun t : Fin n =>
+            (List.ofFn r).getD (2 * S * n + (4 * i + idx i a) * (2 * n) + n + t)
+              false)))) := by
+  classical
+  let K := Fin n → Bool
+  let I := (Fin V × Bool) ⊕ ((Σ i, A i) × Bool)
+  let c : I → ℕ := Sum.elim (fun p => p.2.toNat * S + p.1)
+    (fun p => 2 * S + (4 * p.1.1 + idx p.1.1 p.1.2) * 2 + p.2.toNat)
+  have hc := key_row_blocks_injective hV hG idx hidx hinj
+  let c' : I → Fin (10 * S) := fun p => ⟨c p, hc.1 p⟩
+  have hc' : Function.Injective c' := fun x y h => hc.2 (congrArg Fin.val h)
+  let eK : (Fin V × Bool → K) ≃ (Fin V → Bool → K) := Equiv.curry _ _ _
+  let eR : ((Σ i, A i) × Bool → K) ≃ ((i : Fin G) → A i → K × K) :=
+    (Equiv.curry _ _ _).trans ((Equiv.piCongrRight fun _ =>
+      Equiv.boolArrowEquivProd K).trans (Equiv.piCurry fun i (_ : A i) => K × K))
+  have h := (pushesUniform_bits_of_blocks (n := n) (tail := 2 * S) c' hc').comp
+    ((HardcoreBit.pushesUniform_equiv
+      (Equiv.sumArrowEquivProdArrow (Fin V × Bool) ((Σ i, A i) × Bool) K)).comp
+      (HardcoreBit.pushesUniform_equiv (eK.prodCongr eR)))
+  convert h using 1
+  funext r
+  apply Prod.ext
+  · rfl
+  · funext i a
+    apply Prod.ext <;> funext t
+    · change (List.ofFn _).getD
+        (2 * S * n + (4 * i + idx i a) * (2 * n) + t) false =
+          (List.ofFn _).getD ((2 * S + (4 * i + idx i a) * 2 + 0) * n + t) false
+      congr 1; ring
+    · change (List.ofFn _).getD
+        (2 * S * n + (4 * i + idx i a) * (2 * n) + n + t) false =
+          (List.ofFn _).getD ((2 * S + (4 * i + idx i a) * 2 + 1) * n + t) false
+      congr 1; ring
+
+end TCSlib.Cryptography.SecureComputation.GarblingProbability
diff --git a/TCSlib/Cryptography/SecureComputation/Garbling/Probability.lean b/TCSlib/Cryptography/SecureComputation/Garbling/Probability.lean
new file mode 100644
index 000000000..8bcc5a5a4
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/Garbling/Probability.lean
@@ -0,0 +1,113 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.HardcoreBit.Basic
+import TCSlib.Cryptography.OneWayFunctions.Basic
+import Mathlib.Data.Fintype.Pi
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Independent marginals and first successful openings
+
+## Main definitions
+
+This module adds no definitions.
+
+## Main results
+
+* `SecureComputation.GarblingProbability.findSome_eq_some_of_dichotomy`: a successful
+  entry and no other successful value determine the first successful opening.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.3, Claim 159.a.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.GarblingProbability
+
+open TCSlib.Cryptography
+
+/-- If a list contains an entry mapped to `some b`, and every entry maps to either
+`none` or `some b`, its first successful image is `some b`:
+`(∃ a ∈ l, f a = some b) → (∀ a ∈ l, f a = none ∨ f a = some b) →
+  l.findSome? f = some b`. -/
+theorem findSome_eq_some_of_dichotomy {α β : Type} (l : List α) (f : α → Option β) (b : β)
+    (hex : ∃ a ∈ l, f a = some b)
+    (hall : ∀ a ∈ l, f a = none ∨ f a = some b) : l.findSome? f = some b := by
+  cases hfind : l.findSome? f with
+  | none =>
+    obtain ⟨a, ha, hfa⟩ := hex
+    have hn := List.findSome?_eq_none_iff.mp hfind a ha
+    cases hn.symm.trans hfa
+  | some c =>
+    obtain ⟨a, ha, hfa⟩ := List.exists_of_findSome?_eq_some hfind
+    rcases hall a ha with hn | hb
+    · cases hn.symm.trans hfa
+    · exact hfa.symm.trans hb
+
+/-- Distinct argument vertices and a different output vertex give an independent output
+key and argument-key table:
+`ks ↦ (ks out b, fun j => ks (arg j))` pushes uniform to uniform, if `arg` is injective
+and `arg j ≠ out` for every `j`.
+
+**Proof sketch.** Restrict the uniform vertex table to the injection from `J ⊕ Unit`
+which selects argument vertices on the left and the output vertex on the right. Split
+that restricted table along the sum, evaluate the unit coordinate and output bit, and
+swap the two resulting independent factors. -/
+theorem pushesUniform_output_argKeys {I J K : Type} [Fintype I] [DecidableEq I]
+    [Fintype J] [DecidableEq J] [Fintype K] [Nonempty K]
+    (arg : J → I) (hinj : Function.Injective arg) (out : I)
+    (hne : ∀ j, arg j ≠ out) (b : Bool) :
+    HardcoreBit.PushesUniform (fun ks : I → Bool → K =>
+      (ks out b, fun j => ks (arg j))) := by
+  let select : J ⊕ Unit → I := Sum.elim arg (fun _ => out)
+  have hselect : Function.Injective select := by
+    intro x y hxy
+    cases x with
+    | inl x =>
+      cases y with
+      | inl y => exact congrArg Sum.inl (hinj hxy)
+      | inr y => exact (hne x hxy).elim
+    | inr x =>
+      cases y with
+      | inl y => exact (hne y hxy.symm).elim
+      | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
+  -- Restrict, then split the argument and output coordinates.
+  have hrestrict := HardcoreBit.pushesUniform_restrict (O := Bool → K) hselect
+  have hsplit := hrestrict.comp (HardcoreBit.pushesUniform_equiv
+    (Equiv.sumArrowEquivProdArrow J Unit (Bool → K)))
+  have hout := (HardcoreBit.pushesUniform_eval (γ := Bool → K) ()).comp
+    (HardcoreBit.pushesUniform_eval (γ := K) b)
+  -- Evaluate only the output coordinate; retain the full argument-key table.
+  exact (hsplit.comp (HardcoreBit.pushesUniform_id.prodMap hout)).comp
+    (HardcoreBit.pushesUniform_equiv (Equiv.prodComm (J → Bool → K) K))
+
+/-- Reading one row of a uniform dependent family of coin tables is uniform:
+`r ↦ r i a : ((i : I) → A i → ρ) → ρ` pushes uniform to uniform. -/
+theorem pushesUniform_rowCoin {I : Type} [Fintype I] [DecidableEq I] {A : I → Type}
+    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] {ρ : Type} [Fintype ρ] (i : I) (a : A i) :
+    HardcoreBit.PushesUniform (fun r : (i : I) → A i → ρ => r i a) := by
+  classical
+  exact (HardcoreBit.pushesUniform_equiv (Equiv.piCurry (fun i (_ : A i) => ρ)).symm).comp
+    (HardcoreBit.pushesUniform_eval (γ := ρ) ⟨i, a⟩)
+
+/-- Independent uniform keys and a uniform row-coin map give their joint marginal:
+`(ks,r) ↦ (ks out b,(fun j => ks (arg j),coin r))` pushes uniform to uniform,
+if argument vertices are distinct and exclude `out`, and `coin` pushes uniform to uniform. -/
+theorem pushesUniform_output_argKeys_row {I J K R ρ : Type}
+    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
+    [Fintype K] [Nonempty K] [Fintype R] [Fintype ρ]
+    (arg : J → I) (hinj : Function.Injective arg) (out : I)
+    (hne : ∀ j, arg j ≠ out) (b : Bool) (coin : R → ρ)
+    (hcoin : HardcoreBit.PushesUniform coin) :
+    HardcoreBit.PushesUniform (fun t : (I → Bool → K) × R =>
+      (t.1 out b, (fun j => t.1 (arg j), coin t.2))) := by
+  exact ((pushesUniform_output_argKeys arg hinj out hne b).prodMap hcoin).comp
+    (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K (J → Bool → K) ρ))
+
+end TCSlib.Cryptography.SecureComputation.GarblingProbability
diff --git a/TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean b/TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean
index c7d45299f..f97ec66b3 100644
--- a/TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean
+++ b/TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean
@@ -4,13 +4,15 @@ Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.SecureComputation.GarblingSpecial
 import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
+import TCSlib.Cryptography.SecureComputation.GarblingSecurity.CoinMarginals
+import TCSlib.Cryptography.SecureComputation.GarblingSecurity.NestedBounds
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Garbled circuits from PRFs: Claim 159.a (statement phase)
+# Garbled circuits from PRFs: Claim 159.a
 
 [PS10, §6.2.2–6.2.3]: with the nested special encryption of `GarblingSpecial.lean`, built from two
 pseudorandom function families (`PRFOut`), a random garbling is good with high probability. This
@@ -24,12 +26,17 @@ wrong-key contracts `MultiEnc.DecCorrect` and `MultiEnc.WrongKeyBot` from `Garbl
 
 ## Main results
 
-* `SecureComputation.nestedSpecial_wrongKeyBot` (Claim 157.a (ii) for the nesting, stated; a
-  `sorry` under its sketch).
+* `SecureComputation.nestedSpecial_wrongKeyBot` (Claim 157.a (ii) for the nesting): the
+  wrong-key error is negligible.
 * `SecureComputation.garbling_good_whp` (Claim 159.a, proved from the previous results): a random
   garbling of a fan-in-two circuit is good except with probability `12 · |gates| · δ(n)`, `δ`
   negligible.
 
+## Contents
+
+* `GarblingSecurity.CoinMarginals`: independent key/nonce marginals and option probabilities.
+* `GarblingSecurity.NestedBounds`: the three concrete nesting cases.
+
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
@@ -62,11 +69,32 @@ nested special encryption has `WrongKeyBot` with a negligible error `δ(n)`.
   which is decrypted under an independent key: error `ε₁(n)`.
 
 So `δ = ε₁ + ε₂`, negligible (`Negligible.add`); `ε₁` and `ε₂` are averaged over the plaintext
-and the other layer's key and coins. -/
+and the other layer's key and coins. In the proof, `spDecStr_wrongKey` at `ℓ = n` (with `G₁`)
+and at `ℓ = innerLen` (with `G₂`) gives the two string success bounds
+(`GarblingCoins.uprob_isSome_lt_of_none`), and
+`GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds` carries out the case analysis,
+including the zero-position case, which has no distinct choices. -/
 theorem nestedSpecial_wrongKeyBot (hG₁ : PRFOut (.add .var .var) G₁)
     (hG₂ : PRFOut (.add .var innerLen) G₂) :
     ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, (nestedSpecial E₁ E₂ n).WrongKeyBot (δ n) := by
-  sorry
+  obtain ⟨ε₁, hε₁, hb₁⟩ := spDecStr_wrongKey .var G₁ E₁ hGE₁ hG₁
+  simp only [PolyExpr.eval_var] at hb₁
+  obtain ⟨ε₂, hε₂, hb₂⟩ := spDecStr_wrongKey innerLen G₂ E₂ hGE₂ hG₂
+  refine ⟨fun n => ε₁ n + ε₂ n, hε₁.add hε₂, fun n => ?_⟩
+  have hs₁ : ∀ m : Fin n → Bool,
+      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+        (spDecStr E₁ n n (List.ofFn t.2.1)
+          (spEncStr E₁ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₁ n :=
+    fun m => (GarblingCoins.uprob_isSome_lt_of_none _ (hb₁ n m)).le
+  have hs₂ : ∀ m : Fin (innerLen.eval n) → Bool,
+      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+        (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
+          (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₂ n :=
+    fun m => (GarblingCoins.uprob_isSome_lt_of_none _ (hb₂ n m)).le
+  have hε₁n : 0 ≤ ε₁ n := (uprob_nonneg _).trans (hs₁ (fun _ => false))
+  have hε₂n : 0 ≤ ε₂ n := (uprob_nonneg _).trans (hs₂ (fun _ => false))
+  exact GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds G₁ G₂ E₁ E₂
+    hGE₁ hGE₂ n hε₁n hε₂n hs₁ hs₂
 
 include hGE₁ hGE₂ in
 /-- **Claim 159.a: a random garbling is good with high probability** [PS10, §6.2.3, "all but one
diff --git a/TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean b/TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean
new file mode 100644
index 000000000..5a2d11439
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean
@@ -0,0 +1,58 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.HardcoreBit.Basic
+import TCSlib.Cryptography.OneWayFunctions.Basic
+import Mathlib.Data.Fin.Tuple.Basic
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Marginals of the keys and coins of nested encryption
+
+## Main definitions
+
+This module adds no definitions.
+
+## Main results
+
+* `SecureComputation.GarblingCoins.pushesUniform_position_keys_coin`: two distinct key
+  choices at one position and either nonce are an independent uniform triple.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.2, Claim 157.a (ii).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.GarblingCoins
+
+open TCSlib.Cryptography
+
+/-- Two distinct choices at one position and either coin form a uniform triple:
+`(ks,(r₀,r₁)) ↦ (ks j b,ks j b',if c then r₁ else r₀)` pushes uniform to uniform,
+for `b ≠ b'`. -/
+theorem pushesUniform_position_keys_coin {K : Type} [Fintype K] [Nonempty K]
+    {len : ℕ} (j : Fin len) {b b' : Bool} (hb : b ≠ b') (c : Bool) :
+    HardcoreBit.PushesUniform (fun t : (Fin len → Bool → K) × (K × K) =>
+      (t.1 j b, t.1 j b', if c then t.2.2 else t.2.1)) := by
+  have hk := (HardcoreBit.pushesUniform_eval j).comp
+    (HardcoreBit.pushesUniform_eval_pair (γ := K) hb)
+  cases c
+  · exact (hk.prodMap HardcoreBit.pushesUniform_fst).comp
+      (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))
+  · exact (hk.prodMap HardcoreBit.pushesUniform_snd).comp
+      (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))
+
+/-- A failure probability greater than `1-ε` bounds success strictly by `ε`:
+`1-ε < Pr[X = none] → Pr[X.isSome = true] < ε`. -/
+theorem uprob_isSome_lt_of_none {Ω α : Type} [Fintype Ω] [Nonempty Ω]
+    (X : Ω → Option α) {ε : ℝ} (h : 1 - ε < uprob (fun t => X t = none)) :
+    uprob (fun t => (X t).isSome = true) < ε := by
+  rw [OneWay.uprob_congr (fun t : Ω => Option.isSome_iff_ne_none), uprob_not]
+  linarith
+
+end TCSlib.Cryptography.SecureComputation.GarblingCoins
diff --git a/TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean b/TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean
new file mode 100644
index 000000000..26c0961fd
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean
@@ -0,0 +1,215 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.GarblingSpecial
+import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
+import TCSlib.Cryptography.SecureComputation.GarblingSecurity.CoinMarginals
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Concrete wrong-key bounds for nested special encryption
+
+## Main definitions
+
+This module adds no definitions.
+
+## Main results
+
+* `SecureComputation.GarblingCoins.length_nestedInner`: the inner ciphertext has `4n+2` bits.
+* `SecureComputation.GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds`: inner and outer
+  string success bounds `ε₁, ε₂` give `(nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂)`.
+* `SecureComputation.uprob_not_good_distinct_le_of_uniform_data`: with uniform keys and row
+  coins, goodness with distinct output keys fails with probability at most
+  `12 · |gates| · δ + m / |K|`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.2, Claim 157.a (ii).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.GarblingCoins
+
+open Complexity Turing TCSlib.Cryptography
+
+/-- A special ciphertext with an `n`-bit nonce, an `n`-bit message, and a `2n`-bit pad has
+`innerLen(n) = 4n+2` bits:
+`|spEncStr E ⟦k⟧ ⟦m⟧ ⟦r⟧| = innerLen.eval n`. -/
+theorem length_nestedInner
+    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
+    {E : List Bool → List Bool}
+    (hGE : ∀ n (k r : Fin n → Bool), E (pairEncode (List.ofFn k) (List.ofFn r)) =
+      List.ofFn (G n k r)) (n : ℕ) (k m r : Fin n → Bool) :
+    (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)).length = innerLen.eval n := by
+  rw [length_spEncStr E (by rw [hGE]; simp), List.length_ofFn, List.length_ofFn,
+    innerLen_eq, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+    PolyExpr.eval_var, PolyExpr.eval_const]
+  omega
+
+/-- Inner and outer string success bounds `ε₁, ε₂` give
+`(nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁+ε₂)`, provided both errors are nonnegative and
+the evaluators have the specified `2n` and `n+innerLen(n)` output lengths.
+[PS10, §6.2.2, Claim 157.a (ii)]
+
+**Proof sketch.** There are at most two key positions. With one position use the inner
+string bound and its uniform key/nonce marginal. With two positions, if the first key
+differs, condition on the second position's keys and inner nonce, and apply the outer
+bound to the resulting fixed inner ciphertext. If the first key agrees, correctness
+opens the outer layer and the inner key/nonce marginal gives the inner bound. Add the
+nonnegative unused error in each case. The zero-position case has no distinct choices. -/
+theorem nestedSpecial_wrongKeyBot_of_string_bounds
+    (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
+    (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
+      (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
+    (E₁ E₂ : List Bool → List Bool)
+    (hGE₁ : ∀ n (k r : Fin n → Bool), E₁ (pairEncode (List.ofFn k) (List.ofFn r)) =
+      List.ofFn (G₁ n k r))
+    (hGE₂ : ∀ n (k r : Fin n → Bool), E₂ (pairEncode (List.ofFn k) (List.ofFn r)) =
+      List.ofFn (G₂ n k r)) (n : ℕ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
+    (h₁ : ∀ m : Fin n → Bool,
+      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+        (spDecStr E₁ n n (List.ofFn t.2.1)
+          (spEncStr E₁ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₁)
+    (h₂ : ∀ m : Fin (innerLen.eval n) → Bool,
+      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+        (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
+          (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₂) :
+    (nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂) := by
+  rw [MultiEnc.wrongKeyBot_iff]
+  intro len hlen a a' hne o
+  have hcases : len = 0 ∨ len = 1 ∨ len = 2 := by omega
+  rcases hcases with rfl | rfl | rfl
+  · exact (hne (Subsingleton.elim a a')).elim
+  · have hab : a 0 ≠ a' 0 := fun h => hne (funext (Fin.forall_fin_one.mpr h))
+    have hu := (pushesUniform_position_keys_coin (K := Fin n → Bool) (0 : Fin 1)
+      hab false).uprob_eq (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+        (spDecStr E₁ n n (List.ofFn t.2.1)
+          (spEncStr E₁ (List.ofFn t.1) (List.ofFn o) (List.ofFn t.2.2))).isSome = true)
+    refine (uprob_mono (fun t ht => ?_)).trans
+      ((hu.trans_le (h₁ o)).trans (le_add_of_nonneg_right hε₂))
+    simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
+      nestedSpecial_enc, nestedSpecial_dec] at ht
+    exact Option.isSome_of_isSome_bind ht
+  · by_cases hfirst : a 0 = a' 0
+    · have hsecond : a 1 ≠ a' 1 := fun h =>
+        hne (funext (Fin.forall_fin_two.mpr ⟨hfirst, h⟩))
+      have hu := (pushesUniform_position_keys_coin (K := Fin n → Bool) (1 : Fin 2)
+        hsecond true).uprob_eq (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+          (spDecStr E₁ n n (List.ofFn t.2.1)
+            (spEncStr E₁ (List.ofFn t.1) (List.ofFn o) (List.ofFn t.2.2))).isSome = true)
+      refine (uprob_mono (fun t ht => ?_)).trans
+        ((hu.trans_le (h₁ o)).trans (le_add_of_nonneg_right hε₂))
+      simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
+      nestedSpecial_enc, nestedSpecial_dec] at ht
+      have hc := length_nestedInner hGE₁ n (t.1 1 (a 1)) o t.2.2
+      have hp : (E₂ (pairEncode (List.ofFn (t.1 0 (a 0))) (List.ofFn t.2.1))).length =
+          n + innerLen.eval n := by
+        rw [hGE₂, List.length_ofFn]
+        rfl
+      rw [← hfirst, spDecStr_spEncStr E₂ List.length_ofFn hc List.length_ofFn hp,
+        Option.bind_some] at ht
+      exact Option.isSome_of_isSome_bind ht
+    · let K := Fin n → Bool
+      let e : ((Fin 2 → Bool → K) × (K × K)) ≃
+          ((Bool → K) × K) × ((Bool → K) × K) :=
+        ((piFinTwoEquiv fun _ : Fin 2 => Bool → K).prodCongr (Equiv.refl (K × K))).trans
+          ((Equiv.prodProdProdComm (Bool → K) (Bool → K) K K).trans
+            (Equiv.prodComm ((Bool → K) × K) ((Bool → K) × K)))
+      rw [← uprob_comp_equiv e.symm, uprob_prod]
+      refine (OneWay.uexp_mono (g := fun _ => ε₂) (fun s => ?_)).trans ?_
+      · let c := spEncStr E₁ (List.ofFn (s.1 (a 1))) (List.ofFn o) (List.ofFn s.2)
+        have hc : c.length = innerLen.eval n := length_nestedInner hGE₁ n _ o _
+        let m := padFin (innerLen.eval n) c
+        have hm : List.ofFn m = c := ofFn_padFin_of_length hc
+        have hlaw : HardcoreBit.PushesUniform
+            (fun t : (Bool → K) × K => (t.1 (a 0), t.1 (a' 0), t.2)) :=
+          ((HardcoreBit.pushesUniform_eval_pair (γ := K) hfirst).prodMap
+            HardcoreBit.pushesUniform_id).comp
+              (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))
+        have hu := hlaw.uprob_eq (fun t : K × K × K =>
+          (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
+            (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true)
+        have hb := hu.trans_le (h₂ m)
+        rw [hm] at hb
+        refine (uprob_mono (fun t ht => ?_)).trans hb
+        simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
+      nestedSpecial_enc, nestedSpecial_dec] at ht
+        exact Option.isSome_of_isSome_bind ht
+      · simpa only [OneWay.uexp_const] using
+          (le_add_of_nonneg_left hε₁ : ε₂ ≤ ε₁ + ε₂)
+
+end TCSlib.Cryptography.SecureComputation.GarblingCoins
+
+namespace TCSlib.Cryptography.SecureComputation
+
+open BoolCircuit
+
+variable {K C ρ : Type} [Inhabited K] {n : ℕ} (M : MultiEnc K C ρ) (Cc : DAGCircuit n)
+
+/-- Uniform independent keys and row coins give goodness and distinct output keys:
+`Pr_w[¬ (Good M Cc (s w) ∧ ∀ j, keyAt Cc (s w) (out j) false ≠
+  keyAt Cc (s w) (out j) true)] ≤ 12*|Cc.gates|*δ + m/|K|`, if `out j < Cc.size`
+and `w ↦ ((s w).1,(s w).2.1)` pushes uniform to uniform.
+Outputs may coincide. [PS10, §6.2.3, Claim 159.a and Protocol 162.6]
+
+**Proof sketch.** Use the B2 uniform-data bound for goodness. At each output, the two
+keys are independent uniform elements of `K`, so their collision probability is `1/|K|`.
+The finite union bound over output positions does not require distinct output vertices.
+Add this collision bound to the goodness failure bound. -/
+theorem uprob_not_good_distinct_le_of_uniform_data [Fintype K] [Fintype ρ] [Nonempty ρ]
+    (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
+    {Ω : Type} [Fintype Ω] (s : Ω → GarbleSeed Cc K ρ)
+    (hs : HardcoreBit.PushesUniform (fun w => ((s w).1, (s w).2.1)))
+    {m : ℕ} (out : Fin m → ℕ) (hout : ∀ j, out j < Cc.size) :
+    uprob (fun w => ¬ (Good M Cc (s w) ∧ ∀ j,
+      keyAt Cc (s w) (out j) false ≠ keyAt Cc (s w) (out j) true)) ≤
+      12 * Cc.gates.length * δ + m * (1 / Fintype.card K) := by
+  classical
+  let collision : Fin m → Ω → Prop := fun j w =>
+    keyAt Cc (s w) (out j) false = keyAt Cc (s w) (out j) true
+  have hpoint (j : Fin m) : uprob (collision j) = 1 / Fintype.card K := by
+    let v : Fin Cc.size := ⟨out j, hout j⟩
+    have hkeys : HardcoreBit.PushesUniform (fun w => (s w).1) :=
+      hs.comp HardcoreBit.pushesUniform_fst
+    have hpair : HardcoreBit.PushesUniform (fun w => ((s w).1 v false, (s w).1 v true)) :=
+      (hkeys.comp (HardcoreBit.pushesUniform_eval (γ := Bool → K) v)).comp
+        (HardcoreBit.pushesUniform_eval_pair (γ := K) Bool.false_ne_true)
+    have hu := hpair.uprob_eq (fun z : K × K => z.1 = z.2)
+    calc
+      _ = uprob (fun w => (s w).1 v false = (s w).1 v true) := by
+        apply OneWay.uprob_congr
+        intro w
+        simp only [collision, keyAt_eq, dif_pos (hout j)]
+        rfl
+      _ = uprob (fun z : K × K => z.1 = z.2) := hu
+      _ = 1 / Fintype.card K := MultiMsg.uprob_eq_pair
+  have hcoll : uprob (fun w => ∃ j ∈ Finset.univ, collision j w) ≤
+      m * (1 / Fintype.card K) := by
+    refine (uprob_exists_le Finset.univ collision).trans ?_
+    simp only [hpoint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
+    exact le_rfl
+  have hbad : ∀ w, ¬ (Good M Cc (s w) ∧ ∀ j,
+      keyAt Cc (s w) (out j) false ≠ keyAt Cc (s w) (out j) true) →
+        ¬ Good M Cc (s w) ∨ ∃ j ∈ Finset.univ, collision j w := by
+    intro w hw
+    by_cases hg : Good M Cc (s w)
+    · right
+      have hj : ∃ j, collision j w := by simpa only [not_and, hg, true_implies,
+        not_forall, not_not, collision] using hw
+      obtain ⟨j, hj⟩ := hj
+      exact ⟨j, Finset.mem_univ _, hj⟩
+    · exact Or.inl hg
+  calc
+    _ ≤ uprob (fun w => ¬ Good M Cc (s w) ∨ ∃ j ∈ Finset.univ, collision j w) :=
+      uprob_mono hbad
+    _ ≤ uprob (fun w => ¬ Good M Cc (s w)) +
+        uprob (fun w => ∃ j ∈ Finset.univ, collision j w) := uprob_or_le _ _
+    _ ≤ 12 * Cc.gates.length * δ + m * (1 / Fintype.card K) :=
+      add_le_add (uprob_not_good_le_of_uniform_data M Cc hdec hδ hC
+        (fun w => ((s w).1, (s w).2.1)) hs (fun w => (s w).2.2)) hcoll
+
+end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean
index 0573d5333..3b6086515 100644
--- a/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean
+++ b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean
@@ -3,13 +3,15 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
+import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceParser
+import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceReduction
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Joint, length-generic multi-message security of special encryption (statement phase)
+# Joint, length-generic multi-message security of special encryption
 
 [PS10, Algorithm 157.2] encrypts `m` as `⟨r, (0^n ‖ m) ⊕ f_k(r)⟩`. Yao's protocol uses it in two
 layers with two pseudorandom families `G₁` (`2n`-bit outputs, `n`-bit messages) and `G₂`
@@ -44,14 +46,20 @@ byte-identical. It imports `SpecialEncryptionSecurity` for `PRFOut` and `special
 
 ## Main results
 
-* `SecureComputation.sliceMultiMessageSecure_of_prfOut` (stated; `sorry` under a sketch): every
-  `PRFOut` family is slice multi-message secure (ruling B1, 2026-11-14).
+* `SecureComputation.sliceMultiMessageSecure_of_prfOut` (proved): every `PRFOut` family is
+  slice multi-message secure (ruling B1, 2026-11-14).
 * `SecureComputation.specialScheme_multiMessageSecure_of_joint` (proved): the frozen Claim
   157.a (i) follows.
 * `SecureComputation.sliceEnc_eq_spEncStr`, `sliceEnc_append_left`, `sliceEnc_append_right`
   (proved): slice ciphertexts are special ciphertexts, in particular those of the two layers of
   `nestedSpecial` under `G₁ ‖ G₂`.
 
+## Contents
+
+* `SpecialEncryptionMulti.SliceParser`: the total efficient slice post-processor.
+* `SpecialEncryptionMulti.SliceReduction`: polynomial advice, the reduction machine and
+  the same-seed D4 tuple identity.
+
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
@@ -212,26 +220,103 @@ over `k, r_0, …, r_{q(n)} ← U_n`.
 length-generic and joint: the pads of different ciphertexts may come from different slices
 of one family under one key. The fit `o_i + n + ℓ_i ≤ ℓ(n)` keeps every pad inside `G_k(r_i)`.
 
-**Proof sketch.** As [PS10, Theorem 99.2] (`prfScheme_multiMessageSecure`), with `ℓ`-bit
-outputs. Fix `n` and let `A(n)` be `D`'s largest advantage over the finitely many fitting slice
-vectors and message pairs (each `o_i, ℓ_i ≤ ℓ(n)`).
-1. *PRF step.* For `b ∈ {0, 1}` the oracle machine `D_b` has as advice the maximizing slices and
-   the message vector `m` (`b = 0`) or `m'` (`b = 1`), all of polynomial length. It draws the
-   `r_i`, queries `O(r_i)` once each (`q(n) + 1` queries), forms each ciphertext from the slice
-   of the answer, and runs `D`. Against `G_k` it is the slice sampler; against a random function
-   `F` with `ℓ(n)`-bit outputs it is the same sampler for `F`. Its advantage is negligible by
-   `hG.pseudorandom`.
-2. *Random function.* If the `r_i` are distinct, the values `F(r_i)` are independent and uniform.
-   Within one ciphertext the revealed prefix and the mask are disjoint bits of the slice, so each
-   ciphertext is `⟨r_i, u_i⟩` with `u_i` uniform of length `n + ℓ_i`, whatever the message. The
-   laws for `m` and `m'` agree off the collision event, which has probability at most
-   `C(q(n) + 1, 2) · 2^{-n}` (`MultiMsg.negligible_choose_div_two_pow`).
-3. *Total.* `A(n) ≤ adv(D_0) + adv(D_1) + C(q(n) + 1, 2) · 2^{-n}`, which is negligible. Take
-   `ε = A`. The ℓ-output PRF hybrid machinery is supplied by `prf-long` (ruling B3). -/
+**Proof sketch.** Fix `D,q`. A configuration records fitting offsets and lengths bounded
+by `ℓ(n)`, together with two finite message vectors. Maximize the slice advantage over
+`Option` of these configurations, assigning `none` the value zero. This gives maximum zero
+when no slices fit. Encode the maximizing slice vector as polynomial-length unary advice.
+The total polynomial-time post-map parses descriptors and ciphertexts in parallel, keeping
+each nonce and taking `(body.drop o_i).take (n+len_i)`.
+
+For a fitting vector, use the full-width masks
+`0^{o_i+n} ++ m_i ++ 0^{ℓ(n)-(o_i+n+len_i)}`. The post-map of D4's encoded real tuple is
+pointwise the slice sampler on exactly the same key/nonce seed (`slicePost_tuple` and the
+shared `spEncStr_eq_sliceMask`). Precompose `D` with the parser and hard-wire its advice using
+the published NUPPT closure theorems. D4 supplies one negligible bound before these masks.
+The coin equivalence and `distAdv_comp` transfer it to the maximizing pair, which bounds all
+fitting choices. If the maximizing choice is `none`, D4 on equal zero masks supplies the
+required nonnegative error bound. The PRF step, uniform random pads, collision term and
+triangle bound all remain inside D4 and are not reconstructed here. -/
 theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
     {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
     SliceMultiMessageSecure G := by
-  sorry
+  classical
+  rw [sliceMultiMessageSecure_iff]
+  intro D q
+  -- A finite configuration stores bounded offsets and lengths, and its fit proof.
+  let Config : ℕ → Type := fun n =>
+    {c : (Fin (q.eval n + 1) → Fin (ℓ.eval n + 1)) ×
+      (Fin (q.eval n + 1) → Fin (ℓ.eval n + 1)) //
+        ∀ i, (c.1 i).val + n + (c.2 i).val ≤ ℓ.eval n}
+  let off (n : ℕ) (c : Config n) : Fin (q.eval n + 1) → ℕ := fun i => (c.1.1 i).val
+  let len (n : ℕ) (c : Config n) : Fin (q.eval n + 1) → ℕ := fun i => (c.1.2 i).val
+  let Msg (n : ℕ) (c : Config n) := (i : Fin (q.eval n + 1)) → Fin (len n c i) → Bool
+  let Pack (n : ℕ) := (c : Config n) × (Msg n c × Msg n c)
+  let adv (n : ℕ) (p : Option (Pack n)) : ℝ := p.elim 0 fun p =>
+    distAdv (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.1)
+      (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.2) (D.distinguisherL n)
+  -- Adding `none` with value zero implements the empty-fit-set convention.
+  have hmax : ∀ n, ∃ p : Option (Pack n), ∀ w, adv n w ≤ adv n p := by
+    intro n
+    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image Finset.univ (adv n) Finset.univ_nonempty
+    exact ⟨p, fun w => hmax w (Finset.mem_univ _)⟩
+  choose μ hμ using hmax
+  let β : ℕ → List Bool := fun n => (μ n).elim [] fun p =>
+    SliceReduction.sliceAdvice n (off n p.1) (len n p.1)
+  let b : PolyExpr := .mul (.add q (.const 1)) (.add (.mul (.const 6) ℓ) (.const 6))
+  have hβlen : ∀ n, (β n).length ≤ b.eval n := by
+    intro n
+    cases hc : μ n with
+    | none => simp only [β, hc, Option.elim_none, List.length_nil, Nat.zero_le]
+    | some p =>
+      have h := SliceReduction.length_sliceAdvice_le (ℓ.eval n) n
+        (off n p.1) (len n p.1) p.1.2
+      simpa only [β, hc, Option.elim_some, b, PolyExpr.eval_mul, PolyExpr.eval_add,
+        PolyExpr.eval_const] using h
+  obtain ⟨B, hB⟩ := SliceReduction.exists_slicePost_nuppt D β b hβlen
+  obtain ⟨ε, hε, hb⟩ := MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom B q
+  refine ⟨ε, hε, fun n o l hfit m m' => ?_⟩
+  let c : Config n := ⟨((fun i => ⟨o i, by have h := hfit i; omega⟩),
+    (fun i => ⟨l i, by have h := hfit i; omega⟩)), hfit⟩
+  have hdom := hμ n (some ⟨c, m, m'⟩)
+  change distAdv _ _ _ ≤ ε n
+  refine hdom.trans ?_
+  cases hc : μ n with
+  | none =>
+    have hz := hb n (fun _ _ => false) (fun _ _ => false)
+    rw [distAdv_def, sub_self, abs_zero] at hz
+    simpa only [adv, hc, Option.elim_none] using hz
+  | some p =>
+    obtain ⟨e, he⟩ := hB n
+    let P : List Bool → List Bool := fun z => SliceReduction.slicePost (pairEncode (β n) z)
+    let W : Msg n p.1 → Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool := fun v i =>
+      sliceMask (ℓ.eval n) n (off n p.1 i) (List.ofFn (v i))
+    let X (v : Msg n p.1) := fun t => encodeTupleOut (prfEncRealOut (G n) (W v) t)
+    have hadvice : β n = SliceReduction.sliceAdvice n (off n p.1) (len n p.1) := by
+      simp only [β, hc, Option.elim_some]
+    have hsampler (v : Msg n p.1) :
+        sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) v =
+          fun t => P (X v t) := by
+      funext t
+      rw [sliceMultiEncDist_apply]
+      dsimp only [P, X, W]
+      rw [hadvice, SliceReduction.slicePost_tuple (G n) _ _ p.1.2]
+      apply congrArg PrivateKeyScheme.encodeList
+      apply congrArg List.ofFn
+      funext i
+      rw [sliceEnc_eq]
+    have hcoin : ∀ z r, B.distinguisherL n z (e r) = D.distinguisherL n (P z) r := he
+    have hadv : distAdv (X p.2.1) (X p.2.2)
+        (fun z r => D.distinguisherL n (P z) r) =
+          distAdv (X p.2.1) (X p.2.2) (B.distinguisherL n) := by
+      symm
+      rw [distAdv_def, distAdv_def,
+        acceptProb_coins_equiv (X p.2.1) (B.distinguisherL n) _ e hcoin,
+        acceptProb_coins_equiv (X p.2.2) (B.distinguisherL n) _ e hcoin]
+    change distAdv (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.1)
+      (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.2)
+        (D.distinguisherL n) ≤ ε n
+    rw [hsampler p.2.1, hsampler p.2.2, ← distAdv_comp P, hadv]
+    exact hb n (W p.2.1) (W p.2.2)
 
 /-! ### The frozen Claim 157.a (i) as a corollary -/
 
@@ -242,49 +327,6 @@ variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) →
   (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
     List.ofFn (G n s x))
 
-/-- The key generator of `specialScheme` outputs its coins: `Gen(1^n; rg) = ⟦rg⟧`. -/
-private theorem specialScheme_gen_runAt (n : ℕ) :
-    ∀ rg : (specialScheme G E hE hGE).gen.Coins n,
-      (specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg := by
-  rw [specialScheme_gen]
-  intro rg
-  exact runAt_coinKey .var n rg
-
-/-- The encryption machine of `specialScheme` is `spEncStr` with its coins as the nonce. -/
-private theorem specialScheme_enc_runAt (n : ℕ) :
-    ∀ (k m : List Bool) (re : (specialScheme G E hE hGE).enc.Coins n),
-      (specialScheme G E hE hGE).enc.runAt n (pairEncode k m) re =
-        spEncStr E k m (List.ofFn re) := by
-  rw [specialScheme_enc]
-  intro k m re
-  exact runAt_spEnc hE .var n k m re
-
-/-- The key coins of `specialScheme` as an `n`-bit key, keeping the string. -/
-private noncomputable def specialKeyEq (n : ℕ) :
-    (specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool) :=
-  (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
-    ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
-      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))
-
-/-- `⟦specialKeyEq n rg⟧ = ⟦rg⟧`. -/
-private theorem ofFn_specialKeyEq (n : ℕ) (rg : (specialScheme G E hE hGE).gen.Coins n) :
-    List.ofFn (specialKeyEq G E hE hGE n rg) = List.ofFn rg := by
-  rw [specialKeyEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
-    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]
-
-/-- The encryption coins of `specialScheme` as an `n`-bit nonce, keeping the string. -/
-private noncomputable def specialNonceEq (n : ℕ) :
-    (specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool) :=
-  (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
-    ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
-      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))
-
-/-- `⟦specialNonceEq n re⟧ = ⟦re⟧`. -/
-private theorem ofFn_specialNonceEq (n : ℕ) (re : (specialScheme G E hE hGE).enc.Coins n) :
-    List.ofFn (specialNonceEq G E hE hGE n re) = List.ofFn re := by
-  rw [specialNonceEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
-    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]
-
 /-- **The frozen Claim 157.a (i) from the joint lemma** [PS10, §6.2.2, Definition 93.1]: if the
 length-doubling family `G` is slice multi-message secure, then `specialScheme G E hE hGE` is
 multi-message secure. With `sliceMultiMessageSecure_of_prfOut` this gives
@@ -305,8 +347,8 @@ theorem specialScheme_multiMessageSecure_of_joint (h : SliceMultiMessageSecure G
   let e : (specialScheme G E hE hGE).gen.Coins n ×
       (Fin (q.eval n + 1) → (specialScheme G E hE hGE).enc.Coins n) ≃
       (Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) :=
-    (specialKeyEq G E hE hGE n).prodCongr
-      (Equiv.piCongrRight fun _ => specialNonceEq G E hE hGE n)
+    (specialScheme_keyCoinsEquiv G E hE hGE n).prodCongr
+      (Equiv.piCongrRight fun _ => specialScheme_nonceCoinsEquiv G E hE hGE n)
   have hX : ∀ v : Fin (q.eval n + 1) → Fin n → Bool,
       (specialScheme G E hE hGE).multiEncDist n (q.eval n) v =
         fun t => sliceMultiEncDist G n (q.eval n) (fun _ => 0) (fun _ => n) v (e t) := by
@@ -316,7 +358,8 @@ theorem specialScheme_multiMessageSecure_of_joint (h : SliceMultiMessageSecure G
     refine congrArg PrivateKeyScheme.encodeList (congrArg List.ofFn (funext fun i => ?_))
     rw [specialScheme_gen_runAt, specialScheme_enc_runAt, sliceEnc_eq_spEncStr hGE]
     simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.piCongrRight_apply,
-      Pi.map_apply, List.drop_zero, ofFn_specialKeyEq, ofFn_specialNonceEq]
+      Pi.map_apply, List.drop_zero, specialScheme_keyCoinsEquiv_ofFn,
+      specialScheme_nonceCoinsEquiv_ofFn]
   rw [distAdv_def, hX m, hX m', acceptProb_comp_equiv, acceptProb_comp_equiv, ← distAdv_def]
   exact hb n (fun _ => 0) (fun _ => n) (fun _ => by show 0 + n + n ≤ n + n; omega) m m'
 
diff --git a/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceParser.lean b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceParser.lean
new file mode 100644
index 000000000..e1f19bbac
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceParser.lean
@@ -0,0 +1,180 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
+import TCSlib.Cryptography.Games.Efficiency
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The efficient slice post-processor
+
+## Main definitions
+
+* `SliceReduction.slicePost`: read slice descriptors and ciphertexts in parallel.
+
+## Main results
+
+* `SliceReduction.polyTimeComputable_slicePost`: the parser is polynomial-time on all words.
+* `SliceReduction.slicePost_encode`: its exact law on encoded descriptor/ciphertext pairs.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, Theorem 99.2 with slices.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.SliceReduction
+
+open Complexity Turing TCSlib.Cryptography
+
+/-- Drop one descriptor and one ciphertext from the paired parser state:
+`parserStep z = ⟨snd (fst z), snd (snd z)⟩`. -/
+def parserStep (z : List Bool) : List Bool :=
+  pairEncode (pairSndD (pairFstD z)) (pairSndD (pairSndD z))
+
+/-- `parserStep z = ⟨snd (fst z), snd (snd z)⟩`. -/
+theorem parserStep_eq (z : List Bool) :
+    parserStep z = pairEncode (pairSndD (pairFstD z)) (pairSndD (pairSndD z)) := rfl
+
+/-- Emit one slice ciphertext chunk. A descriptor `⟨u,v⟩` selects offset `|u|` and width
+`|v|`; on a state `⟨advice,ciphertexts⟩`, read both first entries, keep the nonce, cut the
+body, and emit `⟨⟨nonce,body.drop |u| |>.take |v|⟩,[]⟩`. Emit nothing if ciphertexts are empty. -/
+def parserEmit (z : List Bool) : List Bool :=
+  if pairSndD z = [] then [] else
+    pairEncode (pairEncode (pairFstD (pairFstD (pairSndD z)))
+      (((pairSndD (pairFstD (pairSndD z))).drop
+        (pairFstD (pairFstD (pairFstD z))).length).take
+          (pairSndD (pairFstD (pairFstD z))).length)) []
+
+/-- `parserEmit z` is empty if `snd z=[]`; otherwise it is the encoded chunk
+`⟨⟨fst (fst (snd z)),(snd (fst (snd z))).drop |fst (fst (fst z))|
+  |>.take |snd (fst (fst z))|⟩,[]⟩`. -/
+theorem parserEmit_eq (z : List Bool) :
+    parserEmit z = if pairSndD z = [] then [] else
+      pairEncode (pairEncode (pairFstD (pairFstD (pairSndD z)))
+        (((pairSndD (pairFstD (pairSndD z))).drop
+          (pairFstD (pairFstD (pairFstD z))).length).take
+            (pairSndD (pairFstD (pairFstD z))).length)) [] := rfl
+
+/-- The total slice parser runs `|z|+1` emissions:
+`slicePost z = Games.iterEmit parserStep parserEmit (z.length+1) z`. -/
+def slicePost (z : List Bool) : List Bool :=
+  Games.iterEmit parserStep parserEmit (z.length + 1) z
+
+/-- `slicePost z = Games.iterEmit parserStep parserEmit (z.length+1) z`. -/
+theorem slicePost_eq (z : List Bool) :
+    slicePost z = Games.iterEmit parserStep parserEmit (z.length + 1) z := rfl
+
+/-- Dropping both list heads never lengthens the state beyond the empty pair:
+`(parserStep z).length ≤ max z.length 2`.
+
+**Proof sketch.** Reuse the published pair-state bound after shortening the second
+component. Shortening the first component can only reduce its contribution to the public
+pairing length formula. -/
+theorem length_parserStep_le (z : List Bool) : (parserStep z).length ≤ max z.length 2 := by
+  rw [parserStep_eq]
+  have hf := length_pairSndD_le (pairFstD z)
+  have hs := OneWay.PosLoop.length_pairEncode_pairFstD_le z
+    (pairSndD (pairSndD z)) (length_pairSndD_le (pairSndD z))
+  refine le_trans ?_ hs
+  rw [length_pairEncode, length_pairEncode]
+  omega
+
+/-- The slice parser is polynomial-time on every input word:
+`PolyTimeComputable slicePost`.
+
+**Proof sketch.** Total pair projections read the current descriptor and ciphertext.
+The descriptor's two unary lengths drive the published polynomial-time drop and take
+operations. Pair the retained nonce and cut body and emit a self-delimited list chunk.
+The step drops both list heads and stays within `max |z| 2`, so the published iterate-and-emit
+host gives a polynomial-time parser, including malformed inputs. -/
+theorem polyTimeComputable_slicePost : PolyTimeComputable slicePost := by
+  have hf := polyTimeComputable_pairFstD
+  have hs := polyTimeComputable_pairSndD
+  have hadv := hf.comp' hf
+  have hct := hf.comp' hs
+  have ho := hf.comp' hadv
+  have hw := hs.comp' hadv
+  have hbody := hs.comp' hct
+  have hdrop := (polyTimeComputable_pairDropPoly .var).comp' (ho.pairEncode hbody)
+  have htake := (polyTimeComputable_pairTakePoly .var).comp' (hw.pairEncode hdrop)
+  have hemit : PolyTimeComputable parserEmit := by
+    have hnil := polyTimeComputable_isNil.comp' hs
+    have hout := ((hf.comp' hct).pairEncode htake).pairEncode (polyTimeComputable_const [])
+    convert polyTimeComputable_ite hnil (polyTimeComputable_const []) hout using 1
+    funext z
+    rw [parserEmit_eq]
+    simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
+    by_cases h : pairSndD z = []
+    · rw [if_pos h, decide_eq_true h]; rfl
+    · rw [if_neg h, decide_eq_false h]; rfl
+  exact Games.polyTimeComputable_iterEmit
+    ((hs.comp' hf).pairEncode (hs.comp' hs)) hemit 2 length_parserStep_le
+
+/-- Each encoded list has at least as many bits as entries:
+`l.length ≤ (PrivateKeyScheme.encodeList l).length`. -/
+theorem length_le_encodeList (l : List (List Bool)) :
+    l.length ≤ (PrivateKeyScheme.encodeList l).length := by
+  induction l with
+  | nil => rw [List.length_nil, PrivateKeyScheme.encodeList_nil, List.length_nil]
+  | cons a l ih =>
+    rw [List.length_cons, PrivateKeyScheme.encodeList_cons, length_pairEncode]
+    omega
+
+/-- On paired encoded lists of descriptors and ciphertexts, the parser cuts every body
+and keeps every nonce:
+`slicePost ⟨encodeList (l.map fst),encodeList (l.map snd)⟩ = encodeList
+  (l.map fun (d,c) => ⟨fst c,(snd c).drop |fst d| |>.take |snd d|⟩)`.
+[PS10, Theorem 99.2, with slices]
+
+**Proof sketch.** Regard the state as one encoding of a list of descriptor/ciphertext
+pairs. The step removes the two heads, the empty state is fixed, and emission reads the
+specified chunk of each ciphertext. The list encoding contains at least one bit per entry,
+so `|state|+1` iterations suffice. Apply the existing iterate-and-emit encoding theorem and
+the existing flat-map law for the ciphertext list encoding. -/
+theorem slicePost_encode (l : List (List Bool × List Bool)) :
+    slicePost (pairEncode (PrivateKeyScheme.encodeList (l.map Prod.fst))
+      (PrivateKeyScheme.encodeList (l.map Prod.snd))) =
+        PrivateKeyScheme.encodeList (l.map fun e => pairEncode (pairFstD e.2)
+          (((pairSndD e.2).drop (pairFstD e.1).length).take (pairSndD e.1).length)) := by
+  let enc : List (List Bool × List Bool) → List Bool := fun t =>
+    pairEncode (PrivateKeyScheme.encodeList (t.map Prod.fst))
+      (PrivateKeyScheme.encodeList (t.map Prod.snd))
+  let g : (List Bool × List Bool) → List Bool := fun e =>
+    pairEncode (pairEncode (pairFstD e.2)
+      (((pairSndD e.2).drop (pairFstD e.1).length).take (pairSndD e.1).length)) []
+  have hnil : enc [] = pairEncode [] [] := by
+    simp only [enc, List.map_nil, PrivateKeyScheme.encodeList_nil]
+  have hcons (e : List Bool × List Bool) (t : List (List Bool × List Bool)) :
+      enc (e :: t) = pairEncode
+        (pairEncode e.1 (PrivateKeyScheme.encodeList (t.map Prod.fst)))
+        (pairEncode e.2 (PrivateKeyScheme.encodeList (t.map Prod.snd))) := by
+    simp only [enc, List.map_cons, PrivateKeyScheme.encodeList_cons]
+  have hstep_nil : parserStep (enc []) = enc [] := by
+    rw [hnil, parserStep_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+    simp only [pairSndD_eq, pairDecode_nil, Option.map_none, Option.getD_none]
+  have hstep : ∀ e ∈ l, ∀ t, parserStep (enc (e :: t)) = enc t := by
+    intro e he t
+    rw [hcons, parserStep_eq]
+    simp only [pairFstD_pairEncode, pairSndD_pairEncode, enc]
+  have hemit_nil : parserEmit (enc []) = [] := by
+    rw [hnil, parserEmit_eq, pairSndD_pairEncode, if_pos rfl]
+  have hemit : ∀ e ∈ l, ∀ t, parserEmit (enc (e :: t)) = g e := by
+    intro e he t
+    rw [hcons, parserEmit_eq, pairSndD_pairEncode, if_neg (pairEncode_ne_nil _ _)]
+    simp only [pairFstD_pairEncode, pairSndD_pairEncode, g]
+  have hfuel : l.length ≤ (enc l).length + 1 := by
+    have h := length_le_encodeList (l.map Prod.snd)
+    rw [List.length_map] at h
+    dsimp only [enc]
+    rw [length_pairEncode]
+    omega
+  rw [slicePost_eq]
+  change Games.iterEmit parserStep parserEmit ((enc l).length + 1) (enc l) = _
+  rw [Games.iterEmit_encode parserStep parserEmit enc g l hstep_nil hstep
+    hemit_nil hemit _ hfuel, MultiMsg.encodeList_eq_flatMap, List.flatMap_map]
+
+end TCSlib.Cryptography.SecureComputation.SliceReduction
diff --git a/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceReduction.lean b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceReduction.lean
new file mode 100644
index 000000000..0847a5aca
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceReduction.lean
@@ -0,0 +1,150 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceParser
+import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Slice advice and the D4 consumer
+
+## Main definitions
+
+* `SliceReduction.sliceAdvice`: unary offsets and window widths in the list encoding.
+
+## Main results
+
+* `SliceReduction.exists_slicePost_nuppt`: hard-wire polynomial-length slice advice.
+* `SliceReduction.slicePost_tuple`: the same-seed identity with special slice ciphertexts.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, Theorem 99.2 with slices.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.SliceReduction
+
+open Complexity Turing TCSlib.Cryptography
+
+/-- Hard-wiring polynomial-length advice after the slice parser gives a PPT reduction:
+`∃ B, ∀ n, ∃ e : D.Coins n ≃ B.Coins n, ∀ y r,
+  B.distinguisherL n y (e r) = D.distinguisherL n (slicePost ⟨β n,y⟩) r`,
+provided `|β n| ≤ b(n)`. [PS10, Theorem 99.2, with slices]
+
+**Proof sketch.** Precompose `D` with the total polynomial-time slice parser, swapping the
+argument/advice pair into the parser's order. Hard-wire the extra advice with the published
+NUPPT closure theorem. Both operations preserve the coin polynomial; its canonical coin
+congruence preserves the raw coin string, so the activation and verdict equations hold
+pointwise, on arbitrary parser inputs. -/
+theorem exists_slicePost_nuppt (D : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
+    (hβ : ∀ n, (β n).length ≤ b.eval n) :
+    ∃ B : NUPPT, ∀ n, ∃ e : D.Coins n ≃ B.Coins n, ∀ y r,
+      B.distinguisherL n y (e r) =
+        D.distinguisherL n (slicePost (pairEncode (β n) y)) r := by
+  obtain ⟨A, hAc, -, -, hA⟩ := D.exists_comp
+    (polyTimeComputable_slicePost.comp'
+      (polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD))
+    polyTimeComputable_id
+  obtain ⟨B, hBc, hB⟩ := A.exists_withAdvice β b hβ
+  have hc : D.coins = B.coins := (hBc.trans hAc).symm
+  refine ⟨B, fun n => ⟨NUPPT.coinsCongr hc n, fun y r => ?_⟩⟩
+  rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq,
+    NUPPT.runAt_coinsCongr hc, hB, hA, pairFstD_pairEncode, pairSndD_pairEncode]
+  rw [NUPPT.runAt_eq]
+  rfl
+
+/-- The slice descriptor advice is the encoded list of unary offset/width pairs:
+`sliceAdvice n o len = encodeList (List.ofFn fun i => ⟨1^{o i},1^{n+len i}⟩)`. -/
+def sliceAdvice {Q : ℕ} (n : ℕ) (o len : Fin Q → ℕ) : List Bool :=
+  PrivateKeyScheme.encodeList (List.ofFn fun i =>
+    pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true))
+
+/-- `sliceAdvice n o len = encodeList (List.ofFn fun i => ⟨1^{o i},1^{n+len i}⟩)`. -/
+theorem sliceAdvice_eq {Q : ℕ} (n : ℕ) (o len : Fin Q → ℕ) :
+    sliceAdvice n o len = PrivateKeyScheme.encodeList (List.ofFn fun i =>
+      pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true)) := rfl
+
+/-- Uniformly bounded entries have a linearly bounded list encoding:
+`(∀ c ∈ l, c.length ≤ B) → (encodeList l).length ≤ l.length*(2*B+2)`. -/
+theorem length_encodeList_le (l : List (List Bool)) (B : ℕ)
+    (h : ∀ c ∈ l, c.length ≤ B) :
+    (PrivateKeyScheme.encodeList l).length ≤ l.length * (2 * B + 2) := by
+  induction l with
+  | nil =>
+    simp only [PrivateKeyScheme.encodeList_nil, List.length_nil, Nat.zero_mul, le_refl]
+  | cons c l ih =>
+    have hc := h c (List.mem_cons_self)
+    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
+    rw [PrivateKeyScheme.encodeList_cons, length_pairEncode, List.length_cons,
+      Nat.add_mul, Nat.one_mul]
+    omega
+
+/-- Fitting slice advice has polynomial length:
+`o i+n+len i ≤ L → |sliceAdvice n o len| ≤ Q*(6*L+6)`.
+This includes empty messages and slices that fit exactly.
+
+**Proof sketch.** Each descriptor has at most `3*L+2` bits by the fit inequality. Each
+encoded-list entry adds twice that length plus two delimiters. Apply the general list
+encoding length bound to its `Q` entries. -/
+theorem length_sliceAdvice_le {Q : ℕ} (L n : ℕ) (o len : Fin Q → ℕ)
+    (hfit : ∀ i, o i + n + len i ≤ L) :
+    (sliceAdvice n o len).length ≤ Q * (6 * L + 6) := by
+  rw [sliceAdvice_eq]
+  have h := length_encodeList_le (List.ofFn fun i =>
+    pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true)) (3 * L + 2)
+      (by
+        intro c hc
+        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
+        rw [length_pairEncode, List.length_replicate, List.length_replicate]
+        have hi := hfit i
+        omega)
+  have heq : 2 * (3 * L + 2) + 2 = 6 * L + 6 := by omega
+  simpa only [List.length_ofFn, heq] using h
+
+/-- On the same key/nonce seed, cutting a D4 tuple of full-width slice masks is the
+encoded tuple of special ciphertexts from those slices:
+`slicePost ⟨sliceAdvice n o len, encodeTupleOut (prfEncRealOut F masks t)⟩ =
+  encodeList (List.ofFn fun i => spEncStr (fun _ => ⟦F t.1 (t.2 i)⟧.drop (o i))
+    ⟦t.1⟧ ⟦m i⟧ ⟦t.2 i⟧)`, where `masks i = sliceMask L n (o i) ⟦m i⟧`
+and every `o i+n+len i ≤ L`. No relabelling of the encryption seed is used.
+[PS10, Theorem 99.2, with slices]
+
+**Proof sketch.** Apply the total parser's encoded-list law to the descriptor/ciphertext
+pairs from D4. Read the real tuple entrywise through its public reader. The pointwise XOR
+encoding and the shared special-encryption slice-mask identity identify each selected body.
+All equations preserve the input key and every nonce exactly. -/
+theorem slicePost_tuple {n L q : ℕ}
+    (F : (Fin n → Bool) → (Fin n → Bool) → (Fin L → Bool))
+    (o len : Fin (q + 1) → ℕ) (hfit : ∀ i, o i + n + len i ≤ L)
+    (m : (i : Fin (q + 1)) → Fin (len i) → Bool)
+    (t : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) :
+    slicePost (pairEncode (sliceAdvice n o len)
+      (encodeTupleOut (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t))) =
+        PrivateKeyScheme.encodeList (List.ofFn fun i =>
+          spEncStr (fun _ => (List.ofFn (F t.1 (t.2 i))).drop (o i))
+            (List.ofFn t.1) (List.ofFn (m i)) (List.ofFn (t.2 i))) := by
+  rw [sliceAdvice_eq, encodeTupleOut_eq]
+  have hp := slicePost_encode (List.ofFn fun i : Fin (q + 1) =>
+    (pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true),
+      pairEncode
+        (List.ofFn (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t i).1)
+        (List.ofFn (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t i).2)))
+  simp only [List.map_ofFn] at hp
+  refine hp.trans ?_
+  apply congrArg PrivateKeyScheme.encodeList
+  apply congrArg List.ofFn
+  funext i
+  dsimp only [Function.comp_apply]
+  rw [prfEncRealOut_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, List.length_replicate,
+    ← zipWith_xor_ofFn_add]
+  have h := spEncStr_eq_sliceMask L (o i) (List.ofFn (F t.1 (t.2 i)))
+    (List.ofFn t.1) (List.ofFn (m i)) (List.ofFn (t.2 i)) List.length_ofFn
+      (by simpa only [List.length_ofFn] using hfit i)
+  simpa only [List.length_ofFn] using h.symm
+
+end TCSlib.Cryptography.SecureComputation.SliceReduction
diff --git a/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
index f425de1fe..92b55b8be 100644
--- a/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
+++ b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean
@@ -3,6 +3,9 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.SecureComputation.SpecialEncryption
+import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad
+import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.WrongKey
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
 import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
 import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
 import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
@@ -13,7 +16,7 @@ set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# The special encryption scheme of Yao's protocol: security (statement phase)
+# The special encryption scheme of Yao's protocol: security
 
 [PS10, Algorithm 157.2] as a `PrivateKeyScheme`, and Claim 157.a (inventory): the scheme is
 multi-message secure, and a ciphertext decrypted under an independent key gives `⊥` except with
@@ -34,7 +37,13 @@ parameter; `OracleEnsemble.keyed` already allows any output length.
 ## Main results
 
 * `SecureComputation.specialScheme_multiMessageSecure`, `spDecStr_wrongKey`,
-  `specialScheme_wrongKey` (Claim 157.a, stated; `sorry`s under sketches).
+  `specialScheme_wrongKey` (Claim 157.a): multi-message security and the negligible
+  probability of successful decryption under an independent key.
+
+## Contents
+
+* `SpecialEncryptionSecurity.Pad`: the shared zero-prefix mask identity.
+* `SpecialEncryptionSecurity.WrongKey`: the efficient one-query test and prefix bound.
 
 ## References
 
@@ -100,30 +109,140 @@ noncomputable def specialScheme : PrivateKeyScheme where
     rw [spDecStr_spEncStr E hk (by simp) hr hp, Option.getD_some]
     exact decodeFin_ofFn m
 
+/-- The key generator of `specialScheme` outputs its coins: `Gen(1^n; rg) = ⟦rg⟧`. -/
+theorem specialScheme_gen_runAt (n : ℕ) :
+    ∀ rg : (specialScheme G E hE hGE).gen.Coins n,
+      (specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg := by
+  rw [specialScheme_gen]
+  intro rg
+  exact runAt_coinKey .var n rg
+
+/-- The encryption machine uses its coins as the nonce:
+`(specialScheme G E hE hGE).enc.runAt n ⟨k,m⟩ re = spEncStr E k m ⟦re⟧`. -/
+theorem specialScheme_enc_runAt (n : ℕ) :
+    ∀ (k m : List Bool) (re : (specialScheme G E hE hGE).enc.Coins n),
+      (specialScheme G E hE hGE).enc.runAt n (pairEncode k m) re =
+        spEncStr E k m (List.ofFn re) := by
+  rw [specialScheme_enc]
+  intro k m re
+  exact runAt_spEnc hE .var n k m re
+
+/-- Decryption of the special scheme is string decryption, with the overlong failure word:
+`(specialScheme G E hE hGE).dec.runAt n ⟨k,c⟩ rd =
+  (spDecStr E n n k c).getD (true :: 1^n)`. -/
+theorem specialScheme_dec_runAt (n : ℕ) :
+    ∀ (k c : List Bool) (rd : (specialScheme G E hE hGE).dec.Coins n),
+      (specialScheme G E hE hGE).dec.runAt n (pairEncode k c) rd =
+        (spDecStr E n n k c).getD (true :: List.replicate n true) := by
+  rw [specialScheme_dec]
+  intro k c rd
+  exact runAt_spDec hE (.const 0) n k c rd
+
+/-- The key-coin relabelling is an equivalence
+`specialScheme_keyCoinsEquiv G E hE hGE n : (specialScheme G E hE hGE).gen.Coins n ≃
+  (Fin n → Bool)`, preserving the coin string. -/
+noncomputable def specialScheme_keyCoinsEquiv (n : ℕ) :
+    (specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool) :=
+  (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
+    ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
+      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))
+
+/-- The key-coin relabelling is its published composite:
+`specialScheme_keyCoinsEquiv G E hE hGE n = coinsCongr ... ≪≫
+  coinsEquiv_ofPolyTimeUniform ... ≪≫ arrowCongr (finCongr ...) (refl Bool)`. -/
+theorem specialScheme_keyCoinsEquiv_eq (n : ℕ) :
+    specialScheme_keyCoinsEquiv G E hE hGE n =
+      (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
+        ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
+          (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))) := rfl
+
+/-- `⟦specialScheme_keyCoinsEquiv n rg⟧ = ⟦rg⟧`. -/
+theorem specialScheme_keyCoinsEquiv_ofFn (n : ℕ) (rg : (specialScheme G E hE hGE).gen.Coins n) :
+    List.ofFn (specialScheme_keyCoinsEquiv G E hE hGE n rg) = List.ofFn rg := by
+  rw [specialScheme_keyCoinsEquiv, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
+    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]
+
+/-- The nonce-coin relabelling is an equivalence
+`specialScheme_nonceCoinsEquiv G E hE hGE n : (specialScheme G E hE hGE).enc.Coins n ≃
+  (Fin n → Bool)`, preserving the coin string. -/
+noncomputable def specialScheme_nonceCoinsEquiv (n : ℕ) :
+    (specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool) :=
+  (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
+    ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
+      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))
+
+/-- The nonce-coin relabelling is its published composite:
+`specialScheme_nonceCoinsEquiv G E hE hGE n = coinsCongr ... ≪≫
+  coinsEquiv_ofPolyTimeUniform ... ≪≫ arrowCongr (finCongr ...) (refl Bool)`. -/
+theorem specialScheme_nonceCoinsEquiv_eq (n : ℕ) :
+    specialScheme_nonceCoinsEquiv G E hE hGE n =
+      (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
+        ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
+          (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))) := rfl
+
+/-- `⟦specialScheme_nonceCoinsEquiv n re⟧ = ⟦re⟧`. -/
+theorem specialScheme_nonceCoinsEquiv_ofFn (n : ℕ) (re : (specialScheme G E hE hGE).enc.Coins n) :
+    List.ofFn (specialScheme_nonceCoinsEquiv G E hE hGE n re) = List.ofFn re := by
+  rw [specialScheme_nonceCoinsEquiv, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
+    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]
+
 /-! ### Claim 157.a -/
 
 /-- **Claim 157.a (i): the special scheme is multi-message secure** [PS10, §6.2.2, "it is easy to
 modify construction 99.1"] when `G` is a length-doubling PRF.
 
-**Proof sketch.** As [PS10, Theorem 99.2] for Algorithm 99.1 (`prfScheme_multiMessageSecure`):
-replace `f_k` by a random function with `2n`-bit outputs (PRF security, one oracle query per
-ciphertext); then the pads of distinct `r`'s are independent uniform `2n`-bit strings, so the
-ciphertexts are independent of the messages unless two `r`'s collide, with probability at most
-`C(q(n)+1, 2) · 2^{-n}`. The zero prefix `0^n` is masked like the message. -/
+**Proof sketch.** Use the output-length-generic total of [PS10, Theorem 99.2]
+with the masks `0^n ++ m_i`. The full pad is used, so there is no slice post-processor.
+Relabel the scheme's key and nonce coins as uniform `n`-bit words, preserving their strings.
+The shared zero-prefix identity identifies each ciphertext with the corresponding masked
+PRF tuple entry. Relabelling preserves both acceptance probabilities, and the D4 bound
+applies to every pair of mask vectors. This uses D4 directly in this upstream module. -/
 theorem specialScheme_multiMessageSecure (hG : PRFOut (.add .var .var) G) :
     (specialScheme G E hE hGE).MultiMessageSecure := by
-  sorry
+  rw [PrivateKeyScheme.multiMessageSecure_iff]
+  intro D q
+  obtain ⟨ε, hε, hb⟩ := MultiMsg.exists_negligible_distAdv_prfEncRealOut
+    hG.pseudorandom D q
+  refine ⟨ε, hε, fun n m m' => ?_⟩
+  let e : (specialScheme G E hE hGE).gen.Coins n ×
+      (Fin (q.eval n + 1) → (specialScheme G E hE hGE).enc.Coins n) ≃
+      (Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) :=
+    (specialScheme_keyCoinsEquiv G E hE hGE n).prodCongr
+      (Equiv.piCongrRight fun _ => specialScheme_nonceCoinsEquiv G E hE hGE n)
+  have hX : ∀ v : Fin (q.eval n + 1) → Fin n → Bool,
+      (specialScheme G E hE hGE).multiEncDist n (q.eval n) v =
+        fun t => encodeTupleOut (prfEncRealOut (G n)
+          (fun i => Fin.append (fun _ : Fin n => false) (v i)) (e t)) := by
+    intro v
+    funext t
+    rw [PrivateKeyScheme.multiEncDist_apply, encodeTupleOut_eq]
+    refine congrArg PrivateKeyScheme.encodeList (congrArg List.ofFn (funext fun i => ?_))
+    rw [specialScheme_gen_runAt, specialScheme_enc_runAt, prfEncRealOut_apply]
+    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
+      Equiv.piCongrRight_apply, Pi.map_apply]
+    rw [← specialScheme_keyCoinsEquiv_ofFn G E hE hGE n t.1,
+      ← specialScheme_nonceCoinsEquiv_ofFn G E hE hGE n (t.2 i)]
+    rw [spEncStr_eq_zeroPrefixMask E _ _ _ (by rw [hGE]; simp), hGE,
+      ← zipWith_xor_ofFn_add, List.ofFn_fin_append, List.ofFn_const, List.length_ofFn]
+  rw [distAdv_def, hX m, hX m',
+    acceptProb_comp_equiv e (fun z => encodeTupleOut (prfEncRealOut (G n)
+      (fun i => Fin.append (fun _ : Fin n => false) (m i)) z)),
+    acceptProb_comp_equiv e (fun z => encodeTupleOut (prfEncRealOut (G n)
+      (fun i => Fin.append (fun _ : Fin n => false) (m' i)) z)), ← distAdv_def]
+  exact hb n _ _
 
 /-- **Claim 157.a (ii), on strings: a wrong key gives `⊥`** [PS10, §6.2.2, "the extra property"]
 for any polynomial message length `ℓ`: for `G` a PRF with `n + ℓ(n)`-bit outputs and every
 `ℓ(n)`-bit message, encrypting under `k` and decrypting under an independent `k'` gives `⊥`
 except with negligible probability.
 
-**Proof sketch.** Decryption under `k'` succeeds only if `f_k(r)_{<n} = f_{k'}(r)_{<n}`. The
-distinguisher with oracle `O` samples `k'` and `r`, queries `O(r)`, and accepts iff the first `n`
-bits agree with `f_{k'}(r)`. Against a random function this has probability `2^{-n}`, so against
-`f_k` it has probability at most `2^{-n}` plus the PRF advantage: negligible. The guard does not
-fire on honest ciphertexts. -/
+**Proof sketch.** The polynomial-time evaluator supplied by PRF clause (1) agrees
+with `E'` on every canonical key/nonce pair. Its prefix test is run through the published
+one-query machine. Real acceptance is the equal-prefix event; random acceptance is `2^{-n}`
+by the uniform evaluation and restriction laws and point probability. The budget-one PRF
+advantage plus `2^{-n}` bounds prefix collision. Honest ciphertexts pass the length guard,
+and decryption fails exactly off that collision. Add one further positive `2^{-n}` to
+obtain the required strict inequality, including at `n = 0`. -/
 theorem spDecStr_wrongKey (ℓ : PolyExpr)
     (G' : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
     (E' : List Bool → List Bool)
@@ -134,14 +253,36 @@ theorem spDecStr_wrongKey (ℓ : PolyExpr)
       1 - ε n < uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
         spDecStr E' n (ℓ.eval n) (List.ofFn t.2.1)
           (spEncStr E' (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none) := by
-  sorry
+  obtain ⟨E₀, hE₀, hGE₀⟩ := hG'.easy
+  obtain ⟨ε, hε, hb⟩ := SpecialWrongKey.exists_negligible_prefix_collision
+    ℓ G' E₀ hE₀ hGE₀ hG'.pseudorandom
+  refine ⟨fun n => ε n + (2 : ℝ)⁻¹ ^ n, hε.add negligible_two_pow_neg, fun n m => ?_⟩
+  have hevent :
+      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+        spDecStr E' n (ℓ.eval n) (List.ofFn t.2.1)
+          (spEncStr E' (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none) =
+        1 - uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+          (List.ofFn (G' n t.1 t.2.2)).take n =
+            (List.ofFn (G' n t.2.1 t.2.2)).take n) := by
+    rw [OneWay.uprob_congr (fun t :
+        (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+      SpecialWrongKey.spDecStr_none_iff_prefix_ne
+      (G' n) E' (hGE' n) t.1 t.2.1 t.2.2 m), uprob_not]
+  rw [hevent]
+  have hpos : 0 < (2 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n
+  have hbound := hb n
+  dsimp only
+  linarith
 
 /-- **Claim 157.a (ii) for the scheme**: under an independent key, `Dec` returns `⊥` (an output
 that decodes to no `n`-bit message) except with negligible probability, the source's
 `Pr[k, k' ← Gen(1^n), c ← Enc_k(m) : Dec_{k'}(c) = ⊥] > 1 − ε(n)`.
 
-**Proof sketch.** `runAt_spEnc` and `runAt_spDec` reduce it to `spDecStr_wrongKey` at `ℓ = n`;
-the `⊥` string `1^{n+1}` decodes to no `n`-bit message, and a `some` output has `n` bits. -/
+**Proof sketch.** Apply the string bound at message length `n`. Relabel the two
+key coin strings and the nonce as independent uniform `n`-bit words. Average over the
+unused decryption coins. The public activation readers identify string encryption and
+decryption. String failure produces the overlong word `1^{n+1}`, which decodes to `none`;
+monotonicity therefore transfers the string lower bound to the scheme's failure event. -/
 theorem specialScheme_wrongKey (hG : PRFOut (.add .var .var) G) :
     ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin n → Bool),
       1 - ε n < uprob (fun t : (specialScheme G E hE hGE).gen.Coins n ×
@@ -152,6 +293,40 @@ theorem specialScheme_wrongKey (hG : PRFOut (.add .var .var) G) :
             ((specialScheme G E hE hGE).enc.runAt n
               (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.1) (List.ofFn m)) t.2.2.1))
           t.2.2.2) = none) := by
-  sorry
+  obtain ⟨ε, hε, hb⟩ := spDecStr_wrongKey .var G E hGE hG
+  simp only [PolyExpr.eval_var] at hb
+  refine ⟨ε, hε, fun n m => ?_⟩
+  let K := Fin n → Bool
+  let ek := specialScheme_keyCoinsEquiv G E hE hGE n
+  let er := specialScheme_nonceCoinsEquiv G E hE hGE n
+  let e : (specialScheme G E hE hGE).gen.Coins n ×
+      (specialScheme G E hE hGE).gen.Coins n ×
+      (specialScheme G E hE hGE).enc.Coins n × (specialScheme G E hE hGE).dec.Coins n ≃
+      (K × K × K) × (specialScheme G E hE hGE).dec.Coins n :=
+    { toFun := fun t => ((ek t.1, ek t.2.1, er t.2.2.1), t.2.2.2)
+      invFun := fun t => (ek.symm t.1.1, ek.symm t.1.2.1, er.symm t.1.2.2, t.2)
+      left_inv := by intro t; simp
+      right_inv := by intro t; simp }
+  have hk : ∀ k : K, List.ofFn (ek.symm k) = List.ofFn k := by
+    intro k
+    simpa only [ek, Equiv.apply_symm_apply] using
+      (specialScheme_keyCoinsEquiv_ofFn G E hE hGE n (ek.symm k)).symm
+  have hr : ∀ r : K, List.ofFn (er.symm r) = List.ofFn r := by
+    intro r
+    simpa only [er, Equiv.apply_symm_apply] using
+      (specialScheme_nonceCoinsEquiv_ofFn G E hE hGE n (er.symm r)).symm
+  refine (hb n m).trans_le ?_
+  rw [← uprob_comp_equiv e.symm]
+  rw [← uprob_fst (β := (specialScheme G E hE hGE).dec.Coins n)
+    (fun t : K × K × K => spDecStr E n n (List.ofFn t.2.1)
+      (spEncStr E (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none)]
+  apply uprob_mono
+  intro t ht
+  rw [specialScheme_gen_runAt, specialScheme_gen_runAt, specialScheme_enc_runAt,
+    specialScheme_dec_runAt]
+  change decodeFin n ((spDecStr E n n (List.ofFn (ek.symm t.1.2.1))
+    (spEncStr E (List.ofFn (ek.symm t.1.1)) (List.ofFn m)
+      (List.ofFn (er.symm t.1.2.2)))).getD (true :: List.replicate n true)) = none
+  rw [hk, hk, hr, ht, Option.getD_none, decodeFin_eq, dif_neg (by simp)]
 
 end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/Pad.lean b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/Pad.lean
new file mode 100644
index 000000000..45c8573c8
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/Pad.lean
@@ -0,0 +1,116 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.SpecialEncryption
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Zero-prefix and slice masks of special encryption
+
+## Main definitions
+
+* `SecureComputation.sliceMask`: the zero/message/zero full-width mask for a fitting slice.
+
+## Main results
+
+* `SecureComputation.spEncStr_eq_zeroPrefixMask`: the full ciphertext body is the XOR of
+  a zero-prefix message with the pad.
+* `SecureComputation.spEncStr_eq_sliceMask`: cutting a full masked pad gives a slice ciphertext.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.2, Algorithm 157.2.
+-/
+
+namespace TCSlib.Cryptography.SecureComputation
+
+open Complexity Turing TCSlib.Cryptography
+
+/-- Special encryption masks the zero-prefix message:
+`spEncStr E k m r = ⟨r, (0^{|r|} ++ m) ⊕ E(⟨k,r⟩)⟩`, whenever the pad has at least
+`|r| + |m|` bits. [PS10, §6.2.2, Algorithm 157.2]
+
+**Proof sketch.** Split the pad after the nonce length. Split XOR at the same boundary;
+its prefix is unchanged by the zero mask, and its suffix is the encrypted message.
+The pad-length hypothesis makes the prefix exactly as long as the nonce. -/
+theorem spEncStr_eq_zeroPrefixMask (E : List Bool → List Bool) (k m r : List Bool)
+    (hp : r.length + m.length ≤ (E (pairEncode k r)).length) :
+    spEncStr E k m r = pairEncode r
+      (List.zipWith xor (List.replicate r.length false ++ m) (E (pairEncode k r))) := by
+  rw [spEncStr_eq]
+  congr 1
+  have hlen : ((E (pairEncode k r)).take r.length).length = r.length := by
+    rw [List.length_take, Nat.min_eq_left (by omega)]
+  conv_rhs => rw [← List.take_append_drop r.length (E (pairEncode k r))]
+  rw [List.zipWith_append (by rw [List.length_replicate, hlen])]
+  congr 1
+  rw [List.zipWith_comm_of_comm Bool.xor_comm]
+  simpa only [hlen] using
+    (MultiMsg.zipWith_xor_replicate_false ((E (pairEncode k r)).take r.length)).symm
+
+/-- A full-width slice mask, padded with zeros:
+`sliceMask L n o m = padFin L (0^{o+n} ++ m ++ 0^{L-(o+n+|m|)})`.
+[PS10, Theorem 99.2 with slices] -/
+def sliceMask (L n o : ℕ) (m : List Bool) : Fin L → Bool :=
+  padFin L (List.replicate (o + n) false ++ m ++
+    List.replicate (L - (o + n + m.length)) false)
+
+/-- `sliceMask L n o m = padFin L (0^{o+n} ++ m ++ 0^{L-(o+n+|m|)})`. -/
+theorem sliceMask_eq (L n o : ℕ) (m : List Bool) :
+    sliceMask L n o m = padFin L (List.replicate (o + n) false ++ m ++
+      List.replicate (L - (o + n + m.length)) false) := rfl
+
+/-- A fitting slice mask has its specified full-width word:
+`⟦sliceMask L n o m⟧ = 0^{o+n} ++ m ++ 0^{L-(o+n+|m|)}` if `o+n+|m| ≤ L`. -/
+theorem ofFn_sliceMask (L n o : ℕ) (m : List Bool) (h : o + n + m.length ≤ L) :
+    List.ofFn (sliceMask L n o m) = List.replicate (o + n) false ++ m ++
+      List.replicate (L - (o + n + m.length)) false := by
+  rw [sliceMask_eq]
+  apply ofFn_padFin_of_length
+  simp only [List.length_append, List.length_replicate]
+  omega
+
+/-- Cutting a masked full-width pad gives special encryption from that slice:
+`spEncStr (fun _ => pad.drop o) k m r =
+  ⟨r, ((⟦sliceMask L |r| o m⟧ ⊕ pad).drop o).take (|r|+|m|)⟩`,
+if `|pad|=L` and `o+|r|+|m| ≤ L`. [PS10, §6.2.2, Algorithm 157.2, with slices]
+
+**Proof sketch.** The fitting mask has the exact zero/message/zero word. Drop the leading
+offset and take the nonce/message width using the existing zip-with window identities.
+The selected mask is precisely `0^{|r|} ++ m`. The zero-prefix special-encryption identity
+then gives the ciphertext; zip-with truncation discards the unused remainder of the pad. -/
+theorem spEncStr_eq_sliceMask (L o : ℕ) (pad k m r : List Bool)
+    (hp : pad.length = L) (hfit : o + r.length + m.length ≤ L) :
+    spEncStr (fun _ => pad.drop o) k m r = pairEncode r
+      (((List.zipWith xor (List.ofFn (sliceMask L r.length o m)) pad).drop o).take
+        (r.length + m.length)) := by
+  have hdrop : r.length + m.length ≤ (pad.drop o).length := by
+    rw [List.length_drop, hp]
+    omega
+  rw [spEncStr_eq_zeroPrefixMask _ _ _ _ hdrop, ofFn_sliceMask _ _ _ _ hfit]
+  congr 1
+  rw [List.drop_zipWith, List.take_zipWith]
+  have hmask : ((List.replicate (o + r.length) false ++ m ++
+      List.replicate (L - (o + r.length + m.length)) false).drop o).take
+        (r.length + m.length) = List.replicate r.length false ++ m := by
+    rw [List.append_assoc, List.drop_append_of_le_length (by simp),
+      List.drop_replicate]
+    have ho : o + r.length - o = r.length := by omega
+    rw [ho, ← List.append_assoc]
+    have hl : (List.replicate r.length false ++ m).length = r.length + m.length := by
+      rw [List.length_append, List.length_replicate]
+    rw [← hl, List.take_left]
+  rw [hmask]
+  have ht := List.zipWith_eq_zipWith_take_min
+    (f := xor) (l₁ := List.replicate r.length false ++ m) (l₂ := pad.drop o)
+  have hlen : (List.replicate r.length false ++ m).length = r.length + m.length := by
+    rw [List.length_append, List.length_replicate]
+  simpa only [hlen, Nat.min_eq_left hdrop, List.take_of_length_le hlen.le] using ht
+
+end TCSlib.Cryptography.SecureComputation
diff --git a/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean
new file mode 100644
index 000000000..b05c49664
--- /dev/null
+++ b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean
@@ -0,0 +1,226 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The one-query test for a wrong encryption key
+
+## Main definitions
+
+* `SecureComputation.SpecialWrongKey.prefixTest`: compare an oracle answer's prefix with
+  the evaluator's prefix under an independent key.
+
+## Main results
+
+* `SecureComputation.SpecialWrongKey.polyTimeComputable_prefixTest`: efficiency of the test.
+* `SecureComputation.SpecialWrongKey.exists_negligible_prefix_collision`: two independent keys
+  give equal `n`-bit pad prefixes on a common nonce with negligible probability.
+* `SecureComputation.SpecialWrongKey.spDecStr_none_iff_prefix_ne`: an honest ciphertext
+  decrypts to `⊥` under a second key exactly when the two pad prefixes differ.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.2.2, Claim 157.a (ii).
+-/
+
+namespace TCSlib.Cryptography.SecureComputation.SpecialWrongKey
+
+open Complexity Turing TCSlib.Cryptography
+
+/-- On layout `⟨⟨⟨1^n,⟨r,u⟩⟩,α⟩,k'⟩`, return
+`[decide (u.take n = (E ⟨k',r⟩).take n)]`. [PS10, §6.2.2, Claim 157.a (ii)] -/
+def prefixTest (E : List Bool → List Bool) (z : List Bool) : List Bool :=
+  [decide ((pairSndD (NUPPT.inArg z)).take (NUPPT.inParam z).length =
+    (E (pairEncode (NUPPT.inCoins z) (pairFstD (NUPPT.inArg z)))).take
+      (NUPPT.inParam z).length)]
+
+/-- The test is the singleton comparison word:
+`prefixTest E z = [decide ((snd (inArg z)).take |inParam z| =
+  (E ⟨inCoins z,fst (inArg z)⟩).take |inParam z|)]`. -/
+theorem prefixTest_eq (E : List Bool → List Bool) (z : List Bool) :
+    prefixTest E z =
+      [decide ((pairSndD (NUPPT.inArg z)).take (NUPPT.inParam z).length =
+        (E (pairEncode (NUPPT.inCoins z) (pairFstD (NUPPT.inArg z)))).take
+          (NUPPT.inParam z).length)] := rfl
+
+/-- A polynomial-time evaluator gives a polynomial-time prefix test:
+`PolyTimeComputable E → PolyTimeComputable (prefixTest E)`.
+
+**Proof sketch.** Read the unary parameter, argument components, and independent key.
+Evaluate the family, take both prefixes, and compare them with the polynomial-time
+string equality test. All operations are compositions of published polynomial-time maps. -/
+theorem polyTimeComputable_prefixTest {E : List Bool → List Bool}
+    (hE : PolyTimeComputable E) : PolyTimeComputable (prefixTest E) := by
+  have hp := NUPPT.polyTimeComputable_inParam
+  have hr := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
+  have hu := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
+  have hv := hE.comp (NUPPT.polyTimeComputable_inCoins.pairEncode hr)
+  have hleft := (polyTimeComputable_pairTakePoly .var).comp (hp.pairEncode hu)
+  have hright := (polyTimeComputable_pairTakePoly .var).comp (hp.pairEncode hv)
+  have h := polyTimeComputable_pairEq.comp (hleft.pairEncode hright)
+  refine (congrArg PolyTimeComputable (?_ : prefixTest E = _)).mpr h
+  funext z
+  simp only [prefixTest_eq, Function.comp_apply, pairFstD_pairEncode,
+    pairSndD_pairEncode, PolyExpr.eval_var]
+
+/-- Reading `n` fixed coordinates of one random-function answer hits any fixed `n`-bit
+word with probability `2^{-n}`:
+`Pr_R[(⟦R r⟧).take n = ⟦v⟧] = (2⁻¹)^n`, for `n ≤ L`. -/
+theorem uprob_random_prefix {n L : ℕ} (h : n ≤ L) (r v : Fin n → Bool) :
+    uprob (fun R : (Fin n → Bool) → (Fin L → Bool) =>
+      (List.ofFn (R r)).take n = List.ofFn v) = (2 : ℝ)⁻¹ ^ n := by
+  rw [(HardcoreBit.pushesUniform_eval r).uprob_eq
+    (fun u : Fin L → Bool => (List.ofFn u).take n = List.ofFn v)]
+  have hcast := Fin.castLE_injective h
+  have hprob := (HardcoreBit.pushesUniform_restrict (O := Bool) hcast).uprob_eq
+    (fun u : Fin n → Bool => u = v)
+  rw [OneWay.uprob_congr (fun u => by rw [take_ofFn_castLE h, List.ofFn_inj])]
+  rw [hprob, OneWay.uprob_eq_one_div_card]
+  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
+    Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow]
+
+/-- For a pseudorandom family with `n + ℓ(n)` output bits and a polynomial-time evaluator,
+independent keys have equal `n`-bit output prefixes at one uniform point with negligible
+probability: `∃ ε, Negligible ε ∧ ∀ n, Pr_{k,k',r}[F_k(r)_{<n} = F_{k'}(r)_{<n}] ≤ ε(n)`.
+[PS10, §6.2.2, Claim 157.a (ii)]
+
+**Proof sketch.** Use the published one-query machine with the efficient prefix test and
+one query. Relabel its coins as the query point and an independent key. Its real acceptance
+probability is the prefix collision probability; its random acceptance probability is
+`2^{-n}` by uniform evaluation, restriction, and point probability. The difference is at
+most its PRF advantage. The budget-one advantage and `2^{-n}` are negligible. -/
+theorem exists_negligible_prefix_collision (ℓ : PolyExpr)
+    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
+      (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
+    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
+    (hFE : ∀ n (k r : Fin n → Bool), E (pairEncode (List.ofFn k) (List.ofFn r)) =
+      List.ofFn (F n k r))
+    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .add .var ℓ) F).Indist
+      (OracleEnsemble.random .var (.add .var ℓ))) :
+    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
+      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+        (List.ofFn (F n t.1 t.2.2)).take n =
+          (List.ofFn (F n t.2.1 t.2.2)).take n) ≤ ε n := by
+  let htest := polyTimeComputable_prefixTest hE
+  let D := NUPPT.ofPolyTimeUniform htest .var
+  obtain ⟨B, hB⟩ := MultiMsg.exists_oneQuery_nuppt D (.add .var ℓ)
+  refine ⟨fun n => prfAdv (F n) (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1) +
+      (2 : ℝ)⁻¹ ^ n, ?_, fun n => ?_⟩
+  · simpa only [PolyExpr.eval_const] using
+      (hF.negligible_prfAdv B (.const 1)).add negligible_two_pow_neg
+  · obtain ⟨φ, hφ⟩ := hB n
+    let eD := NUPPT.coinsEquiv_ofPolyTimeUniform htest .var n
+    let χ : ((Fin n → Bool) × (Fin n → Bool)) ≃ B.Coins n :=
+      ((Equiv.refl (Fin n → Bool)).prodCongr eD.symm).trans φ
+    have hχ : ∀ (g : (Fin n → Bool) →
+        (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) (r k : Fin n → Bool),
+        (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 (χ (r, k))).eval g =
+          decide ((List.ofFn (g r)).take n = (List.ofFn (F n k r)).take n) := by
+      intro g r k
+      have hcoins : List.ofFn (eD.symm k) = List.ofFn k := by
+        simpa only [eD, Equiv.apply_symm_apply] using
+          (NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn htest .var n (eD.symm k)).symm
+      rw [show χ (r, k) = φ (r, eD.symm k) from rfl, hφ]
+      have hrun : D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) (eD.symm k) =
+          [decide ((List.ofFn (g r)).take n = (List.ofFn (F n k r)).take n)] := by
+        rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
+        simp only [prefixTest_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
+          NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+          List.length_replicate, hcoins, hFE]
+      rw [hrun]
+      simp only [List.cons.injEq, and_true, decide_eq_true_eq]
+    have hreal :
+        uprob (fun z : (Fin n → Bool) × B.Coins n =>
+          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 z.2).eval (F n z.1) = true) =
+        uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+          (List.ofFn (F n t.1 t.2.2)).take n =
+            (List.ofFn (F n t.2.1 t.2.2)).take n) := by
+      let e : ((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) ≃
+          ((Fin n → Bool) × B.Coins n) :=
+        (Equiv.refl (Fin n → Bool)).prodCongr
+          ((Equiv.prodComm (Fin n → Bool) (Fin n → Bool)).trans χ)
+      rw [← uprob_comp_equiv e]
+      apply OneWay.uprob_congr
+      intro t
+      change (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1
+        (χ (t.2.2, t.2.1))).eval (F n t.1) = true ↔ _
+      rw [hχ, decide_eq_true_eq]
+    have hrandom :
+        uprob (fun z : ((Fin n → Bool) →
+            (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) × B.Coins n =>
+          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 z.2).eval z.1 = true) =
+            (2 : ℝ)⁻¹ ^ n := by
+      let e := (Equiv.refl ((Fin n → Bool) →
+        (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))).prodCongr χ
+      rw [← uprob_comp_equiv e]
+      have he : ∀ z : ((Fin n → Bool) →
+          (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) ×
+            ((Fin n → Bool) × (Fin n → Bool)),
+          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 (e z).2).eval (e z).1 = true ↔
+            (List.ofFn (z.1 z.2.1)).take n =
+              (List.ofFn (F n z.2.2 z.2.1)).take n := by
+        intro z
+        change (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1
+          (χ (z.2.1, z.2.2))).eval z.1 = true ↔ _
+        rw [hχ, decide_eq_true_eq]
+      rw [OneWay.uprob_congr he,
+        ← uprob_comp_equiv (Equiv.prodComm
+          ((Fin n → Bool) × (Fin n → Bool))
+          ((Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))), uprob_prod]
+      have hn : n ≤ (PolyExpr.add .var ℓ).eval n := by
+        simp only [PolyExpr.eval_add, PolyExpr.eval_var]
+        omega
+      have hp : ∀ t : (Fin n → Bool) × (Fin n → Bool),
+          uprob (fun R : (Fin n → Bool) →
+              (Fin ((PolyExpr.add .var ℓ).eval n) → Bool) =>
+            (List.ofFn (R t.1)).take n =
+              (List.ofFn (F n t.2 t.1)).take n) = (2 : ℝ)⁻¹ ^ n := by
+        intro t
+        rw [take_ofFn_castLE hn]
+        exact uprob_random_prefix hn t.1 _
+      exact (congrArg uexp (funext hp)).trans (OneWay.uexp_const _)
+    have ha := le_abs_self
+      (uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
+        (List.ofFn (F n t.1 t.2.2)).take n =
+          (List.ofFn (F n t.2.1 t.2.2)).take n) - (2 : ℝ)⁻¹ ^ n)
+    dsimp only
+    rw [prfAdv_eq, hreal, hrandom]
+    linarith
+
+/-- Honest string ciphertexts fail under a second key exactly when the pad prefixes
+differ:
+`spDecStr E n l ⟦k'⟧ (spEncStr E ⟦k⟧ ⟦m⟧ ⟦r⟧) = none ↔
+  (⟦F k r⟧).take n ≠ (⟦F k' r⟧).take n`, when `E` evaluates `F` with `n+l` output bits.
+[PS10, §6.2.2, Claim 157.a (ii)]
+
+**Proof sketch.** The honest nonce and key lengths pass the length guard. The pad prefix
+has `n` bits and the masked suffix has `l` bits, so the ciphertext length also passes.
+Its first `n` bits are the first pad's prefix; decryption tests exactly its equality
+with the second pad's prefix. -/
+theorem spDecStr_none_iff_prefix_ne {n l : ℕ}
+    (F : (Fin n → Bool) → (Fin n → Bool) → (Fin (n + l) → Bool))
+    (E : List Bool → List Bool)
+    (hFE : ∀ k r, E (pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (F k r))
+    (k k' r : Fin n → Bool) (m : Fin l → Bool) :
+    spDecStr E n l (List.ofFn k')
+      (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)) = none ↔
+        (List.ofFn (F k r)).take n ≠ (List.ofFn (F k' r)).take n := by
+  have ht : ((List.ofFn (F k r)).take n).length = n := by
+    rw [List.length_take, List.length_ofFn, Nat.min_eq_left (by omega)]
+  have hz : (List.zipWith xor (List.ofFn m) ((List.ofFn (F k r)).drop n)).length = l := by
+    rw [List.length_zipWith, List.length_ofFn, List.length_drop, List.length_ofFn]
+    omega
+  simp only [spDecStr_eq, spEncStr_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    List.length_ofFn, hFE]
+  rw [if_pos ⟨trivial, trivial, by rw [List.length_append, ht, hz]⟩, List.take_left' ht]
+  by_cases h : (List.ofFn (F k r)).take n = (List.ofFn (F k' r)).take n <;> simp [h]
+
+end TCSlib.Cryptography.SecureComputation.SpecialWrongKey
diff --git a/TCSlib/Cryptography/SecureComputation/Yao.lean b/TCSlib/Cryptography/SecureComputation/Yao.lean
index e4a546c2d..a8d89e096 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao.lean
@@ -93,9 +93,10 @@ coins (`yaoSeed`): the keys, `2n` coins per row, and a shift `λ_i` per gate.
 * `SecureComputation.yaoHybrid_answersB_getD` (proved): Bob's OT answers are his keys.
 * `SecureComputation.yaoHybrid_correct` (proved): both parties output `f(x, y)` in the hybrid
   execution when the garbling is good with distinct output keys.
-* `SecureComputation.yaoSeed_good_whp`, `yaoHybrid_polyTime`, `yaoHybrid_simulators` (stated;
-  `sorry`s under sketches): the garbling is good w.h.p., the protocol is efficient, and the
-  simulators of Theorem 163.7.
+* `SecureComputation.yaoSeed_good_whp` (proved): the garbling is good with distinct output keys
+  except with negligible probability.
+* `SecureComputation.yaoHybrid_polyTime`, `yaoHybrid_simulators` (stated; `sorry`s under sketches):
+  the protocol is efficient, and the simulators of Theorem 163.7.
 * `SecureComputation.yaoHybrid_hbcSecure` (Theorem 163.7 in the OT-hybrid model, proved from the
   two previous results).
 
@@ -795,29 +796,56 @@ PRFs `G₁`, `G₂` evaluated by `E₁`, `E₂`, there is a negligible `δ` such
 uniform coins for Alice, the garbling `yaoSeed` fails to be good, or gives some output vertex two
 equal keys, with probability at most `δ(n)`.
 
-**Proof sketch.** Write `S = sizeBound(n)`.
-1. *The coin blocks are disjoint.* Vertices are below `size(C_n) ≤ S`, gates below `S`, and a
-   fan-in-two gate has at most four assignments, with indices below `4` (`assignIdx`). So the
-   keys, the row coins and the shifts of `yaoSeed` read disjoint blocks of Alice's coins: the keys
-   and row coins are independent and uniform, and independent of the shifts.
-2. *Goodness.* The argument of `uprob_not_good_le` applies to this distribution. At gate `i` and
-   assignment `a`, the row of `a` decrypts under `a`'s keys to the right key
-   (`nestedSpecial_decCorrect`), so `Good` fails there only if the row of some `a'' ≠ a`
-   decrypts under `a`'s keys. The arguments are distinct vertices below the gate's own, so that
-   row's keys, plaintext and coins are independent and uniform. By `nestedSpecial_wrongKeyBot`
-   the event has probability at most `δ₀(n)`, whatever the row order. At most `12` such events
-   per gate and `S` gates give `12 · S · δ₀(n)`.
-3. *Distinct output keys.* The two keys of an output vertex are independent uniform `n`-bit
-   strings, equal with probability `2^{-n}`: at most `outLen(n) · 2^{-n}` in all.
-4. `δ(n) = 12 · S(n) · δ₀(n) + outLen(n) · 2^{-n}` is negligible (a polynomial times a negligible
-   function, `Negligible.add`). -/
+**Proof sketch.** Write `S = sizeBound(n)`. Distinct blocks contain all vertex keys and
+row coins: vertices and gates are below `S`, and binary assignment indices are injective
+below four for fan-in at most two. The generic block restriction theorem gives their joint
+uniform law, including zero-length blocks. Apply the strengthened B2 uniform-data bound
+with `nestedSpecial_wrongKeyBot` and correctness; this bound permits arbitrary seed-dependent
+row permutations, including the XOR shifts. Each output's two keys coincide with probability
+`2^{-n}`. The output union bound allows repeated vertices. Thus failure is at most
+`12*S(n)*δ₀(n) + outLen(n)*2^{-n}`, a sum of polynomial multiples of negligible functions. -/
 theorem yaoSeed_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
     (hG₂ : PRFOut (.add .var innerLen) G₂) :
     ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
       ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
         ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
           keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n := by
-  sorry
+  classical
+  obtain ⟨δ₀, hδ₀, hbot⟩ :=
+    nestedSpecial_wrongKeyBot G₁ G₂ E₁ E₂ hGE₁ hGE₂ hG₁ hG₂
+  refine ⟨fun n => 12 * (Y.sizeBound.eval n : ℝ) * δ₀ n +
+    (Y.outLen.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n, ?_, fun n => ?_⟩
+  · simpa only [PolyExpr.eval_mul, PolyExpr.eval_const, Nat.cast_mul, Nat.cast_ofNat] using
+      (EnsembleLemmas.negligible_polyExpr_mul (.mul (.const 12) Y.sizeBound) hδ₀).add
+        (EnsembleLemmas.negligible_polyExpr_mul Y.outLen negligible_two_pow_neg)
+  · have hg : (Y.circ n).gates.length ≤ Y.sizeBound.eval n := by
+      have hs := Y.size_le n
+      rw [DAGCircuit.size_eq] at hs
+      omega
+    have hsmall (i : Fin (Y.circ n).gates.length) :=
+      GarblingProbability.assignmentFold_small ((Y.circ n).gates[i]).args.length
+        (((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
+          (List.getElem_mem i.isLt))
+    have hlaw : HardcoreBit.PushesUniform
+        (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
+          ((yaoSeed Y n (List.ofFn r)).1, (yaoSeed Y n (List.ofFn r)).2.1)) := by
+      simp only [yaoCoins_eval]
+      convert GarblingProbability.pushesUniform_key_row_blocks (n := n)
+        (A := fun i : Fin (Y.circ n).gates.length => Fin ((Y.circ n).gates[i]).args.length → Bool)
+        (Y.size_le n) hg
+        (fun i a => assignIdx a)
+        (fun i a => by change assignIdx a < 4; rw [assignIdx_eq]; exact (hsmall i).1 a)
+        (fun i => by simpa only [assignIdx_eq] using (hsmall i).2) using 1
+    have hb := uprob_not_good_distinct_le_of_uniform_data
+      (nestedSpecial E₁ E₂ n) (Y.circ n)
+      (nestedSpecial_decCorrect G₁ G₂ E₁ E₂ hGE₁ hGE₂ n) (hbot n) (Y.fanin n)
+      (fun r => yaoSeed Y n (List.ofFn r)) hlaw (Y.outs n) (Y.outs_lt n)
+    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
+      Nat.cast_ofNat, one_div, ← inv_pow] at hb
+    refine hb.trans (add_le_add_right ?_ _)
+    exact mul_le_mul_of_nonneg_right
+      (mul_le_mul_of_nonneg_left (by exact_mod_cast hg) (by norm_num))
+      (wrongKeyBot_nonneg (nestedSpecial E₁ E₂ n) (hbot n))
 
 /-- **Protocol 162.6 in the OT-hybrid model runs in polynomial time** (the efficiency clause of
 [PS10, Definition 155.1], `HybridProtocol.PolyTime`, ruling of 2026-11-05) when `E₁` and `E₂`

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.WrongKey
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The special encryption scheme of Yao's protocol: security

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
  `specialScheme_wrongKey` (Claim 157.a): multi-message security and the negligible
  probability of successful decryption under an independent key.

## Contents

* `SpecialEncryptionSecurity.Pad`: the shared zero-prefix mask identity.
* `SpecialEncryptionSecurity.WrongKey`: the efficient one-query test and prefix bound.

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

/-- The key generator of `specialScheme` outputs its coins: `Gen(1^n; rg) = ⟦rg⟧`. -/
theorem specialScheme_gen_runAt (n : ℕ) :
    ∀ rg : (specialScheme G E hE hGE).gen.Coins n,
      (specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg := by
  rw [specialScheme_gen]
  intro rg
  exact runAt_coinKey .var n rg

/-- The encryption machine uses its coins as the nonce:
`(specialScheme G E hE hGE).enc.runAt n ⟨k,m⟩ re = spEncStr E k m ⟦re⟧`. -/
theorem specialScheme_enc_runAt (n : ℕ) :
    ∀ (k m : List Bool) (re : (specialScheme G E hE hGE).enc.Coins n),
      (specialScheme G E hE hGE).enc.runAt n (pairEncode k m) re =
        spEncStr E k m (List.ofFn re) := by
  rw [specialScheme_enc]
  intro k m re
  exact runAt_spEnc hE .var n k m re

/-- Decryption of the special scheme is string decryption, with the overlong failure word:
`(specialScheme G E hE hGE).dec.runAt n ⟨k,c⟩ rd =
  (spDecStr E n n k c).getD (true :: 1^n)`. -/
theorem specialScheme_dec_runAt (n : ℕ) :
    ∀ (k c : List Bool) (rd : (specialScheme G E hE hGE).dec.Coins n),
      (specialScheme G E hE hGE).dec.runAt n (pairEncode k c) rd =
        (spDecStr E n n k c).getD (true :: List.replicate n true) := by
  rw [specialScheme_dec]
  intro k c rd
  exact runAt_spDec hE (.const 0) n k c rd

/-- The key-coin relabelling is an equivalence
`specialScheme_keyCoinsEquiv G E hE hGE n : (specialScheme G E hE hGE).gen.Coins n ≃
  (Fin n → Bool)`, preserving the coin string. -/
noncomputable def specialScheme_keyCoinsEquiv (n : ℕ) :
    (specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- The key-coin relabelling is its published composite:
`specialScheme_keyCoinsEquiv G E hE hGE n = coinsCongr ... ≪≫
  coinsEquiv_ofPolyTimeUniform ... ≪≫ arrowCongr (finCongr ...) (refl Bool)`. -/
theorem specialScheme_keyCoinsEquiv_eq (n : ℕ) :
    specialScheme_keyCoinsEquiv G E hE hGE n =
      (NUPPT.coinsCongr (by rw [specialScheme_gen]) n).trans
        ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
          (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))) := rfl

/-- `⟦specialScheme_keyCoinsEquiv n rg⟧ = ⟦rg⟧`. -/
theorem specialScheme_keyCoinsEquiv_ofFn (n : ℕ) (rg : (specialScheme G E hE hGE).gen.Coins n) :
    List.ofFn (specialScheme_keyCoinsEquiv G E hE hGE n rg) = List.ofFn rg := by
  rw [specialScheme_keyCoinsEquiv, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- The nonce-coin relabelling is an equivalence
`specialScheme_nonceCoinsEquiv G E hE hGE n : (specialScheme G E hE hGE).enc.Coins n ≃
  (Fin n → Bool)`, preserving the coin string. -/
noncomputable def specialScheme_nonceCoinsEquiv (n : ℕ) :
    (specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- The nonce-coin relabelling is its published composite:
`specialScheme_nonceCoinsEquiv G E hE hGE n = coinsCongr ... ≪≫
  coinsEquiv_ofPolyTimeUniform ... ≪≫ arrowCongr (finCongr ...) (refl Bool)`. -/
theorem specialScheme_nonceCoinsEquiv_eq (n : ℕ) :
    specialScheme_nonceCoinsEquiv G E hE hGE n =
      (NUPPT.coinsCongr (by rw [specialScheme_enc]) n).trans
        ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_spEncFun hE) .var n).trans
          (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))) := rfl

/-- `⟦specialScheme_nonceCoinsEquiv n re⟧ = ⟦re⟧`. -/
theorem specialScheme_nonceCoinsEquiv_ofFn (n : ℕ) (re : (specialScheme G E hE hGE).enc.Coins n) :
    List.ofFn (specialScheme_nonceCoinsEquiv G E hE hGE n re) = List.ofFn re := by
  rw [specialScheme_nonceCoinsEquiv, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-! ### Claim 157.a -/

/-- **Claim 157.a (i): the special scheme is multi-message secure** [PS10, §6.2.2, "it is easy to
modify construction 99.1"] when `G` is a length-doubling PRF.

**Proof sketch.** Use the output-length-generic total of [PS10, Theorem 99.2]
with the masks `0^n ++ m_i`. The full pad is used, so there is no slice post-processor.
Relabel the scheme's key and nonce coins as uniform `n`-bit words, preserving their strings.
The shared zero-prefix identity identifies each ciphertext with the corresponding masked
PRF tuple entry. Relabelling preserves both acceptance probabilities, and the D4 bound
applies to every pair of mask vectors. This uses D4 directly in this upstream module. -/
theorem specialScheme_multiMessageSecure (hG : PRFOut (.add .var .var) G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  rw [PrivateKeyScheme.multiMessageSecure_iff]
  intro D q
  obtain ⟨ε, hε, hb⟩ := MultiMsg.exists_negligible_distAdv_prfEncRealOut
    hG.pseudorandom D q
  refine ⟨ε, hε, fun n m m' => ?_⟩
  let e : (specialScheme G E hE hGE).gen.Coins n ×
      (Fin (q.eval n + 1) → (specialScheme G E hE hGE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) :=
    (specialScheme_keyCoinsEquiv G E hE hGE n).prodCongr
      (Equiv.piCongrRight fun _ => specialScheme_nonceCoinsEquiv G E hE hGE n)
  have hX : ∀ v : Fin (q.eval n + 1) → Fin n → Bool,
      (specialScheme G E hE hGE).multiEncDist n (q.eval n) v =
        fun t => encodeTupleOut (prfEncRealOut (G n)
          (fun i => Fin.append (fun _ : Fin n => false) (v i)) (e t)) := by
    intro v
    funext t
    rw [PrivateKeyScheme.multiEncDist_apply, encodeTupleOut_eq]
    refine congrArg PrivateKeyScheme.encodeList (congrArg List.ofFn (funext fun i => ?_))
    rw [specialScheme_gen_runAt, specialScheme_enc_runAt, prfEncRealOut_apply]
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Equiv.piCongrRight_apply, Pi.map_apply]
    rw [← specialScheme_keyCoinsEquiv_ofFn G E hE hGE n t.1,
      ← specialScheme_nonceCoinsEquiv_ofFn G E hE hGE n (t.2 i)]
    rw [spEncStr_eq_zeroPrefixMask E _ _ _ (by rw [hGE]; simp), hGE,
      ← zipWith_xor_ofFn_add, List.ofFn_fin_append, List.ofFn_const, List.length_ofFn]
  rw [distAdv_def, hX m, hX m',
    acceptProb_comp_equiv e (fun z => encodeTupleOut (prfEncRealOut (G n)
      (fun i => Fin.append (fun _ : Fin n => false) (m i)) z)),
    acceptProb_comp_equiv e (fun z => encodeTupleOut (prfEncRealOut (G n)
      (fun i => Fin.append (fun _ : Fin n => false) (m' i)) z)), ← distAdv_def]
  exact hb n _ _

/-- **Claim 157.a (ii), on strings: a wrong key gives `⊥`** [PS10, §6.2.2, "the extra property"]
for any polynomial message length `ℓ`: for `G` a PRF with `n + ℓ(n)`-bit outputs and every
`ℓ(n)`-bit message, encrypting under `k` and decrypting under an independent `k'` gives `⊥`
except with negligible probability.

**Proof sketch.** The polynomial-time evaluator supplied by PRF clause (1) agrees
with `E'` on every canonical key/nonce pair. Its prefix test is run through the published
one-query machine. Real acceptance is the equal-prefix event; random acceptance is `2^{-n}`
by the uniform evaluation and restriction laws and point probability. The budget-one PRF
advantage plus `2^{-n}` bounds prefix collision. Honest ciphertexts pass the length guard,
and decryption fails exactly off that collision. Add one further positive `2^{-n}` to
obtain the required strict inequality, including at `n = 0`. -/
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
  obtain ⟨E₀, hE₀, hGE₀⟩ := hG'.easy
  obtain ⟨ε, hε, hb⟩ := SpecialWrongKey.exists_negligible_prefix_collision
    ℓ G' E₀ hE₀ hGE₀ hG'.pseudorandom
  refine ⟨fun n => ε n + (2 : ℝ)⁻¹ ^ n, hε.add negligible_two_pow_neg, fun n m => ?_⟩
  have hevent :
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        spDecStr E' n (ℓ.eval n) (List.ofFn t.2.1)
          (spEncStr E' (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none) =
        1 - uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
          (List.ofFn (G' n t.1 t.2.2)).take n =
            (List.ofFn (G' n t.2.1 t.2.2)).take n) := by
    rw [OneWay.uprob_congr (fun t :
        (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
      SpecialWrongKey.spDecStr_none_iff_prefix_ne
      (G' n) E' (hGE' n) t.1 t.2.1 t.2.2 m), uprob_not]
  rw [hevent]
  have hpos : 0 < (2 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n
  have hbound := hb n
  dsimp only
  linarith

/-- **Claim 157.a (ii) for the scheme**: under an independent key, `Dec` returns `⊥` (an output
that decodes to no `n`-bit message) except with negligible probability, the source's
`Pr[k, k' ← Gen(1^n), c ← Enc_k(m) : Dec_{k'}(c) = ⊥] > 1 − ε(n)`.

**Proof sketch.** Apply the string bound at message length `n`. Relabel the two
key coin strings and the nonce as independent uniform `n`-bit words. Average over the
unused decryption coins. The public activation readers identify string encryption and
decryption. String failure produces the overlong word `1^{n+1}`, which decodes to `none`;
monotonicity therefore transfers the string lower bound to the scheme's failure event. -/
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
  obtain ⟨ε, hε, hb⟩ := spDecStr_wrongKey .var G E hGE hG
  simp only [PolyExpr.eval_var] at hb
  refine ⟨ε, hε, fun n m => ?_⟩
  let K := Fin n → Bool
  let ek := specialScheme_keyCoinsEquiv G E hE hGE n
  let er := specialScheme_nonceCoinsEquiv G E hE hGE n
  let e : (specialScheme G E hE hGE).gen.Coins n ×
      (specialScheme G E hE hGE).gen.Coins n ×
      (specialScheme G E hE hGE).enc.Coins n × (specialScheme G E hE hGE).dec.Coins n ≃
      (K × K × K) × (specialScheme G E hE hGE).dec.Coins n :=
    { toFun := fun t => ((ek t.1, ek t.2.1, er t.2.2.1), t.2.2.2)
      invFun := fun t => (ek.symm t.1.1, ek.symm t.1.2.1, er.symm t.1.2.2, t.2)
      left_inv := by intro t; simp
      right_inv := by intro t; simp }
  have hk : ∀ k : K, List.ofFn (ek.symm k) = List.ofFn k := by
    intro k
    simpa only [ek, Equiv.apply_symm_apply] using
      (specialScheme_keyCoinsEquiv_ofFn G E hE hGE n (ek.symm k)).symm
  have hr : ∀ r : K, List.ofFn (er.symm r) = List.ofFn r := by
    intro r
    simpa only [er, Equiv.apply_symm_apply] using
      (specialScheme_nonceCoinsEquiv_ofFn G E hE hGE n (er.symm r)).symm
  refine (hb n m).trans_le ?_
  rw [← uprob_comp_equiv e.symm]
  rw [← uprob_fst (β := (specialScheme G E hE hGE).dec.Coins n)
    (fun t : K × K × K => spDecStr E n n (List.ofFn t.2.1)
      (spEncStr E (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none)]
  apply uprob_mono
  intro t ht
  rw [specialScheme_gen_runAt, specialScheme_gen_runAt, specialScheme_enc_runAt,
    specialScheme_dec_runAt]
  change decodeFin n ((spDecStr E n n (List.ofFn (ek.symm t.1.2.1))
    (spEncStr E (List.ofFn (ek.symm t.1.1)) (List.ofFn m)
      (List.ofFn (er.symm t.1.2.2)))).getD (true :: List.replicate n true)) = none
  rw [hk, hk, hr, ht, Option.getD_none, decodeFin_eq, dif_neg (by simp)]

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/Pad.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-prefix and slice masks of special encryption

## Main definitions

* `SecureComputation.sliceMask`: the zero/message/zero full-width mask for a fitting slice.

## Main results

* `SecureComputation.spEncStr_eq_zeroPrefixMask`: the full ciphertext body is the XOR of
  a zero-prefix message with the pad.
* `SecureComputation.spEncStr_eq_sliceMask`: cutting a full masked pad gives a slice ciphertext.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Algorithm 157.2.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-- Special encryption masks the zero-prefix message:
`spEncStr E k m r = ⟨r, (0^{|r|} ++ m) ⊕ E(⟨k,r⟩)⟩`, whenever the pad has at least
`|r| + |m|` bits. [PS10, §6.2.2, Algorithm 157.2]

**Proof sketch.** Split the pad after the nonce length. Split XOR at the same boundary;
its prefix is unchanged by the zero mask, and its suffix is the encrypted message.
The pad-length hypothesis makes the prefix exactly as long as the nonce. -/
theorem spEncStr_eq_zeroPrefixMask (E : List Bool → List Bool) (k m r : List Bool)
    (hp : r.length + m.length ≤ (E (pairEncode k r)).length) :
    spEncStr E k m r = pairEncode r
      (List.zipWith xor (List.replicate r.length false ++ m) (E (pairEncode k r))) := by
  rw [spEncStr_eq]
  congr 1
  have hlen : ((E (pairEncode k r)).take r.length).length = r.length := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  conv_rhs => rw [← List.take_append_drop r.length (E (pairEncode k r))]
  rw [List.zipWith_append (by rw [List.length_replicate, hlen])]
  congr 1
  rw [List.zipWith_comm_of_comm Bool.xor_comm]
  simpa only [hlen] using
    (MultiMsg.zipWith_xor_replicate_false ((E (pairEncode k r)).take r.length)).symm

/-- A full-width slice mask, padded with zeros:
`sliceMask L n o m = padFin L (0^{o+n} ++ m ++ 0^{L-(o+n+|m|)})`.
[PS10, Theorem 99.2 with slices] -/
def sliceMask (L n o : ℕ) (m : List Bool) : Fin L → Bool :=
  padFin L (List.replicate (o + n) false ++ m ++
    List.replicate (L - (o + n + m.length)) false)

/-- `sliceMask L n o m = padFin L (0^{o+n} ++ m ++ 0^{L-(o+n+|m|)})`. -/
theorem sliceMask_eq (L n o : ℕ) (m : List Bool) :
    sliceMask L n o m = padFin L (List.replicate (o + n) false ++ m ++
      List.replicate (L - (o + n + m.length)) false) := rfl

/-- A fitting slice mask has its specified full-width word:
`⟦sliceMask L n o m⟧ = 0^{o+n} ++ m ++ 0^{L-(o+n+|m|)}` if `o+n+|m| ≤ L`. -/
theorem ofFn_sliceMask (L n o : ℕ) (m : List Bool) (h : o + n + m.length ≤ L) :
    List.ofFn (sliceMask L n o m) = List.replicate (o + n) false ++ m ++
      List.replicate (L - (o + n + m.length)) false := by
  rw [sliceMask_eq]
  apply ofFn_padFin_of_length
  simp only [List.length_append, List.length_replicate]
  omega

/-- Cutting a masked full-width pad gives special encryption from that slice:
`spEncStr (fun _ => pad.drop o) k m r =
  ⟨r, ((⟦sliceMask L |r| o m⟧ ⊕ pad).drop o).take (|r|+|m|)⟩`,
if `|pad|=L` and `o+|r|+|m| ≤ L`. [PS10, §6.2.2, Algorithm 157.2, with slices]

**Proof sketch.** The fitting mask has the exact zero/message/zero word. Drop the leading
offset and take the nonce/message width using the existing zip-with window identities.
The selected mask is precisely `0^{|r|} ++ m`. The zero-prefix special-encryption identity
then gives the ciphertext; zip-with truncation discards the unused remainder of the pad. -/
theorem spEncStr_eq_sliceMask (L o : ℕ) (pad k m r : List Bool)
    (hp : pad.length = L) (hfit : o + r.length + m.length ≤ L) :
    spEncStr (fun _ => pad.drop o) k m r = pairEncode r
      (((List.zipWith xor (List.ofFn (sliceMask L r.length o m)) pad).drop o).take
        (r.length + m.length)) := by
  have hdrop : r.length + m.length ≤ (pad.drop o).length := by
    rw [List.length_drop, hp]
    omega
  rw [spEncStr_eq_zeroPrefixMask _ _ _ _ hdrop, ofFn_sliceMask _ _ _ _ hfit]
  congr 1
  rw [List.drop_zipWith, List.take_zipWith]
  have hmask : ((List.replicate (o + r.length) false ++ m ++
      List.replicate (L - (o + r.length + m.length)) false).drop o).take
        (r.length + m.length) = List.replicate r.length false ++ m := by
    rw [List.append_assoc, List.drop_append_of_le_length (by simp),
      List.drop_replicate]
    have ho : o + r.length - o = r.length := by omega
    rw [ho, ← List.append_assoc]
    have hl : (List.replicate r.length false ++ m).length = r.length + m.length := by
      rw [List.length_append, List.length_replicate]
    rw [← hl, List.take_left]
  rw [hmask]
  have ht := List.zipWith_eq_zipWith_take_min
    (f := xor) (l₁ := List.replicate r.length false ++ m) (l₂ := pad.drop o)
  have hlen : (List.replicate r.length false ++ m).length = r.length + m.length := by
    rw [List.length_append, List.length_replicate]
  simpa only [hlen, Nat.min_eq_left hdrop, List.take_of_length_le hlen.le] using ht

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The one-query test for a wrong encryption key

## Main definitions

* `SecureComputation.SpecialWrongKey.prefixTest`: compare an oracle answer's prefix with
  the evaluator's prefix under an independent key.

## Main results

* `SecureComputation.SpecialWrongKey.polyTimeComputable_prefixTest`: efficiency of the test.
* `SecureComputation.SpecialWrongKey.exists_negligible_prefix_collision`: two independent keys
  give equal `n`-bit pad prefixes on a common nonce with negligible probability.
* `SecureComputation.SpecialWrongKey.spDecStr_none_iff_prefix_ne`: an honest ciphertext
  decrypts to `⊥` under a second key exactly when the two pad prefixes differ.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Claim 157.a (ii).
-/

namespace TCSlib.Cryptography.SecureComputation.SpecialWrongKey

open Complexity Turing TCSlib.Cryptography

/-- On layout `⟨⟨⟨1^n,⟨r,u⟩⟩,α⟩,k'⟩`, return
`[decide (u.take n = (E ⟨k',r⟩).take n)]`. [PS10, §6.2.2, Claim 157.a (ii)] -/
def prefixTest (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  [decide ((pairSndD (NUPPT.inArg z)).take (NUPPT.inParam z).length =
    (E (pairEncode (NUPPT.inCoins z) (pairFstD (NUPPT.inArg z)))).take
      (NUPPT.inParam z).length)]

/-- The test is the singleton comparison word:
`prefixTest E z = [decide ((snd (inArg z)).take |inParam z| =
  (E ⟨inCoins z,fst (inArg z)⟩).take |inParam z|)]`. -/
theorem prefixTest_eq (E : List Bool → List Bool) (z : List Bool) :
    prefixTest E z =
      [decide ((pairSndD (NUPPT.inArg z)).take (NUPPT.inParam z).length =
        (E (pairEncode (NUPPT.inCoins z) (pairFstD (NUPPT.inArg z)))).take
          (NUPPT.inParam z).length)] := rfl

/-- A polynomial-time evaluator gives a polynomial-time prefix test:
`PolyTimeComputable E → PolyTimeComputable (prefixTest E)`.

**Proof sketch.** Read the unary parameter, argument components, and independent key.
Evaluate the family, take both prefixes, and compare them with the polynomial-time
string equality test. All operations are compositions of published polynomial-time maps. -/
theorem polyTimeComputable_prefixTest {E : List Bool → List Bool}
    (hE : PolyTimeComputable E) : PolyTimeComputable (prefixTest E) := by
  have hp := NUPPT.polyTimeComputable_inParam
  have hr := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hu := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hv := hE.comp (NUPPT.polyTimeComputable_inCoins.pairEncode hr)
  have hleft := (polyTimeComputable_pairTakePoly .var).comp (hp.pairEncode hu)
  have hright := (polyTimeComputable_pairTakePoly .var).comp (hp.pairEncode hv)
  have h := polyTimeComputable_pairEq.comp (hleft.pairEncode hright)
  refine (congrArg PolyTimeComputable (?_ : prefixTest E = _)).mpr h
  funext z
  simp only [prefixTest_eq, Function.comp_apply, pairFstD_pairEncode,
    pairSndD_pairEncode, PolyExpr.eval_var]

/-- Reading `n` fixed coordinates of one random-function answer hits any fixed `n`-bit
word with probability `2^{-n}`:
`Pr_R[(⟦R r⟧).take n = ⟦v⟧] = (2⁻¹)^n`, for `n ≤ L`. -/
theorem uprob_random_prefix {n L : ℕ} (h : n ≤ L) (r v : Fin n → Bool) :
    uprob (fun R : (Fin n → Bool) → (Fin L → Bool) =>
      (List.ofFn (R r)).take n = List.ofFn v) = (2 : ℝ)⁻¹ ^ n := by
  rw [(HardcoreBit.pushesUniform_eval r).uprob_eq
    (fun u : Fin L → Bool => (List.ofFn u).take n = List.ofFn v)]
  have hcast := Fin.castLE_injective h
  have hprob := (HardcoreBit.pushesUniform_restrict (O := Bool) hcast).uprob_eq
    (fun u : Fin n → Bool => u = v)
  rw [OneWay.uprob_congr (fun u => by rw [take_ofFn_castLE h, List.ofFn_inj])]
  rw [hprob, OneWay.uprob_eq_one_div_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow]

/-- For a pseudorandom family with `n + ℓ(n)` output bits and a polynomial-time evaluator,
independent keys have equal `n`-bit output prefixes at one uniform point with negligible
probability: `∃ ε, Negligible ε ∧ ∀ n, Pr_{k,k',r}[F_k(r)_{<n} = F_{k'}(r)_{<n}] ≤ ε(n)`.
[PS10, §6.2.2, Claim 157.a (ii)]

**Proof sketch.** Use the published one-query machine with the efficient prefix test and
one query. Relabel its coins as the query point and an independent key. Its real acceptance
probability is the prefix collision probability; its random acceptance probability is
`2^{-n}` by uniform evaluation, restriction, and point probability. The difference is at
most its PRF advantage. The budget-one advantage and `2^{-n}` are negligible. -/
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
          (List.ofFn (F n t.2.1 t.2.2)).take n) ≤ ε n := by
  let htest := polyTimeComputable_prefixTest hE
  let D := NUPPT.ofPolyTimeUniform htest .var
  obtain ⟨B, hB⟩ := MultiMsg.exists_oneQuery_nuppt D (.add .var ℓ)
  refine ⟨fun n => prfAdv (F n) (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1) +
      (2 : ℝ)⁻¹ ^ n, ?_, fun n => ?_⟩
  · simpa only [PolyExpr.eval_const] using
      (hF.negligible_prfAdv B (.const 1)).add negligible_two_pow_neg
  · obtain ⟨φ, hφ⟩ := hB n
    let eD := NUPPT.coinsEquiv_ofPolyTimeUniform htest .var n
    let χ : ((Fin n → Bool) × (Fin n → Bool)) ≃ B.Coins n :=
      ((Equiv.refl (Fin n → Bool)).prodCongr eD.symm).trans φ
    have hχ : ∀ (g : (Fin n → Bool) →
        (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) (r k : Fin n → Bool),
        (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 (χ (r, k))).eval g =
          decide ((List.ofFn (g r)).take n = (List.ofFn (F n k r)).take n) := by
      intro g r k
      have hcoins : List.ofFn (eD.symm k) = List.ofFn k := by
        simpa only [eD, Equiv.apply_symm_apply] using
          (NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn htest .var n (eD.symm k)).symm
      rw [show χ (r, k) = φ (r, eD.symm k) from rfl, hφ]
      have hrun : D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) (eD.symm k) =
          [decide ((List.ofFn (g r)).take n = (List.ofFn (F n k r)).take n)] := by
        rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
        simp only [prefixTest_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
          NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate, hcoins, hFE]
      rw [hrun]
      simp only [List.cons.injEq, and_true, decide_eq_true_eq]
    have hreal :
        uprob (fun z : (Fin n → Bool) × B.Coins n =>
          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 z.2).eval (F n z.1) = true) =
        uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
          (List.ofFn (F n t.1 t.2.2)).take n =
            (List.ofFn (F n t.2.1 t.2.2)).take n) := by
      let e : ((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) ≃
          ((Fin n → Bool) × B.Coins n) :=
        (Equiv.refl (Fin n → Bool)).prodCongr
          ((Equiv.prodComm (Fin n → Bool) (Fin n → Bool)).trans χ)
      rw [← uprob_comp_equiv e]
      apply OneWay.uprob_congr
      intro t
      change (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1
        (χ (t.2.2, t.2.1))).eval (F n t.1) = true ↔ _
      rw [hχ, decide_eq_true_eq]
    have hrandom :
        uprob (fun z : ((Fin n → Bool) →
            (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) × B.Coins n =>
          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 z.2).eval z.1 = true) =
            (2 : ℝ)⁻¹ ^ n := by
      let e := (Equiv.refl ((Fin n → Bool) →
        (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))).prodCongr χ
      rw [← uprob_comp_equiv e]
      have he : ∀ z : ((Fin n → Bool) →
          (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) ×
            ((Fin n → Bool) × (Fin n → Bool)),
          (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 (e z).2).eval (e z).1 = true ↔
            (List.ofFn (z.1 z.2.1)).take n =
              (List.ofFn (F n z.2.2 z.2.1)).take n := by
        intro z
        change (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1
          (χ (z.2.1, z.2.2))).eval z.1 = true ↔ _
        rw [hχ, decide_eq_true_eq]
      rw [OneWay.uprob_congr he,
        ← uprob_comp_equiv (Equiv.prodComm
          ((Fin n → Bool) × (Fin n → Bool))
          ((Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))), uprob_prod]
      have hn : n ≤ (PolyExpr.add .var ℓ).eval n := by
        simp only [PolyExpr.eval_add, PolyExpr.eval_var]
        omega
      have hp : ∀ t : (Fin n → Bool) × (Fin n → Bool),
          uprob (fun R : (Fin n → Bool) →
              (Fin ((PolyExpr.add .var ℓ).eval n) → Bool) =>
            (List.ofFn (R t.1)).take n =
              (List.ofFn (F n t.2 t.1)).take n) = (2 : ℝ)⁻¹ ^ n := by
        intro t
        rw [take_ofFn_castLE hn]
        exact uprob_random_prefix hn t.1 _
      exact (congrArg uexp (funext hp)).trans (OneWay.uexp_const _)
    have ha := le_abs_self
      (uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (List.ofFn (F n t.1 t.2.2)).take n =
          (List.ofFn (F n t.2.1 t.2.2)).take n) - (2 : ℝ)⁻¹ ^ n)
    dsimp only
    rw [prfAdv_eq, hreal, hrandom]
    linarith

/-- Honest string ciphertexts fail under a second key exactly when the pad prefixes
differ:
`spDecStr E n l ⟦k'⟧ (spEncStr E ⟦k⟧ ⟦m⟧ ⟦r⟧) = none ↔
  (⟦F k r⟧).take n ≠ (⟦F k' r⟧).take n`, when `E` evaluates `F` with `n+l` output bits.
[PS10, §6.2.2, Claim 157.a (ii)]

**Proof sketch.** The honest nonce and key lengths pass the length guard. The pad prefix
has `n` bits and the masked suffix has `l` bits, so the ciphertext length also passes.
Its first `n` bits are the first pad's prefix; decryption tests exactly its equality
with the second pad's prefix. -/
theorem spDecStr_none_iff_prefix_ne {n l : ℕ}
    (F : (Fin n → Bool) → (Fin n → Bool) → (Fin (n + l) → Bool))
    (E : List Bool → List Bool)
    (hFE : ∀ k r, E (pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (F k r))
    (k k' r : Fin n → Bool) (m : Fin l → Bool) :
    spDecStr E n l (List.ofFn k')
      (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)) = none ↔
        (List.ofFn (F k r)).take n ≠ (List.ofFn (F k' r)).take n := by
  have ht : ((List.ofFn (F k r)).take n).length = n := by
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left (by omega)]
  have hz : (List.zipWith xor (List.ofFn m) ((List.ofFn (F k r)).drop n)).length = l := by
    rw [List.length_zipWith, List.length_ofFn, List.length_drop, List.length_ofFn]
    omega
  simp only [spDecStr_eq, spEncStr_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_ofFn, hFE]
  rw [if_pos ⟨trivial, trivial, by rw [List.length_append, ht, hz]⟩, List.take_left' ht]
  by_cases h : (List.ofFn (F k r)).take n = (List.ofFn (F k' r)).take n <;> simp [h]

end TCSlib.Cryptography.SecureComputation.SpecialWrongKey

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceParser
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joint, length-generic multi-message security of special encryption

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

* `SecureComputation.sliceMultiMessageSecure_of_prfOut` (proved): every `PRFOut` family is
  slice multi-message secure (ruling B1, 2026-11-14).
* `SecureComputation.specialScheme_multiMessageSecure_of_joint` (proved): the frozen Claim
  157.a (i) follows.
* `SecureComputation.sliceEnc_eq_spEncStr`, `sliceEnc_append_left`, `sliceEnc_append_right`
  (proved): slice ciphertexts are special ciphertexts, in particular those of the two layers of
  `nestedSpecial` under `G₁ ‖ G₂`.

## Contents

* `SpecialEncryptionMulti.SliceParser`: the total efficient slice post-processor.
* `SpecialEncryptionMulti.SliceReduction`: polynomial advice, the reduction machine and
  the same-seed D4 tuple identity.

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

**Proof sketch.** Fix `D,q`. A configuration records fitting offsets and lengths bounded
by `ℓ(n)`, together with two finite message vectors. Maximize the slice advantage over
`Option` of these configurations, assigning `none` the value zero. This gives maximum zero
when no slices fit. Encode the maximizing slice vector as polynomial-length unary advice.
The total polynomial-time post-map parses descriptors and ciphertexts in parallel, keeping
each nonce and taking `(body.drop o_i).take (n+len_i)`.

For a fitting vector, use the full-width masks
`0^{o_i+n} ++ m_i ++ 0^{ℓ(n)-(o_i+n+len_i)}`. The post-map of D4's encoded real tuple is
pointwise the slice sampler on exactly the same key/nonce seed (`slicePost_tuple` and the
shared `spEncStr_eq_sliceMask`). Precompose `D` with the parser and hard-wire its advice using
the published NUPPT closure theorems. D4 supplies one negligible bound before these masks.
The coin equivalence and `distAdv_comp` transfer it to the maximizing pair, which bounds all
fitting choices. If the maximizing choice is `none`, D4 on equal zero masks supplies the
required nonnegative error bound. The PRF step, uniform random pads, collision term and
triangle bound all remain inside D4 and are not reconstructed here. -/
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G := by
  classical
  rw [sliceMultiMessageSecure_iff]
  intro D q
  -- A finite configuration stores bounded offsets and lengths, and its fit proof.
  let Config : ℕ → Type := fun n =>
    {c : (Fin (q.eval n + 1) → Fin (ℓ.eval n + 1)) ×
      (Fin (q.eval n + 1) → Fin (ℓ.eval n + 1)) //
        ∀ i, (c.1 i).val + n + (c.2 i).val ≤ ℓ.eval n}
  let off (n : ℕ) (c : Config n) : Fin (q.eval n + 1) → ℕ := fun i => (c.1.1 i).val
  let len (n : ℕ) (c : Config n) : Fin (q.eval n + 1) → ℕ := fun i => (c.1.2 i).val
  let Msg (n : ℕ) (c : Config n) := (i : Fin (q.eval n + 1)) → Fin (len n c i) → Bool
  let Pack (n : ℕ) := (c : Config n) × (Msg n c × Msg n c)
  let adv (n : ℕ) (p : Option (Pack n)) : ℝ := p.elim 0 fun p =>
    distAdv (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.1)
      (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.2) (D.distinguisherL n)
  -- Adding `none` with value zero implements the empty-fit-set convention.
  have hmax : ∀ n, ∃ p : Option (Pack n), ∀ w, adv n w ≤ adv n p := by
    intro n
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image Finset.univ (adv n) Finset.univ_nonempty
    exact ⟨p, fun w => hmax w (Finset.mem_univ _)⟩
  choose μ hμ using hmax
  let β : ℕ → List Bool := fun n => (μ n).elim [] fun p =>
    SliceReduction.sliceAdvice n (off n p.1) (len n p.1)
  let b : PolyExpr := .mul (.add q (.const 1)) (.add (.mul (.const 6) ℓ) (.const 6))
  have hβlen : ∀ n, (β n).length ≤ b.eval n := by
    intro n
    cases hc : μ n with
    | none => simp only [β, hc, Option.elim_none, List.length_nil, Nat.zero_le]
    | some p =>
      have h := SliceReduction.length_sliceAdvice_le (ℓ.eval n) n
        (off n p.1) (len n p.1) p.1.2
      simpa only [β, hc, Option.elim_some, b, PolyExpr.eval_mul, PolyExpr.eval_add,
        PolyExpr.eval_const] using h
  obtain ⟨B, hB⟩ := SliceReduction.exists_slicePost_nuppt D β b hβlen
  obtain ⟨ε, hε, hb⟩ := MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom B q
  refine ⟨ε, hε, fun n o l hfit m m' => ?_⟩
  let c : Config n := ⟨((fun i => ⟨o i, by have h := hfit i; omega⟩),
    (fun i => ⟨l i, by have h := hfit i; omega⟩)), hfit⟩
  have hdom := hμ n (some ⟨c, m, m'⟩)
  change distAdv _ _ _ ≤ ε n
  refine hdom.trans ?_
  cases hc : μ n with
  | none =>
    have hz := hb n (fun _ _ => false) (fun _ _ => false)
    rw [distAdv_def, sub_self, abs_zero] at hz
    simpa only [adv, hc, Option.elim_none] using hz
  | some p =>
    obtain ⟨e, he⟩ := hB n
    let P : List Bool → List Bool := fun z => SliceReduction.slicePost (pairEncode (β n) z)
    let W : Msg n p.1 → Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool := fun v i =>
      sliceMask (ℓ.eval n) n (off n p.1 i) (List.ofFn (v i))
    let X (v : Msg n p.1) := fun t => encodeTupleOut (prfEncRealOut (G n) (W v) t)
    have hadvice : β n = SliceReduction.sliceAdvice n (off n p.1) (len n p.1) := by
      simp only [β, hc, Option.elim_some]
    have hsampler (v : Msg n p.1) :
        sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) v =
          fun t => P (X v t) := by
      funext t
      rw [sliceMultiEncDist_apply]
      dsimp only [P, X, W]
      rw [hadvice, SliceReduction.slicePost_tuple (G n) _ _ p.1.2]
      apply congrArg PrivateKeyScheme.encodeList
      apply congrArg List.ofFn
      funext i
      rw [sliceEnc_eq]
    have hcoin : ∀ z r, B.distinguisherL n z (e r) = D.distinguisherL n (P z) r := he
    have hadv : distAdv (X p.2.1) (X p.2.2)
        (fun z r => D.distinguisherL n (P z) r) =
          distAdv (X p.2.1) (X p.2.2) (B.distinguisherL n) := by
      symm
      rw [distAdv_def, distAdv_def,
        acceptProb_coins_equiv (X p.2.1) (B.distinguisherL n) _ e hcoin,
        acceptProb_coins_equiv (X p.2.2) (B.distinguisherL n) _ e hcoin]
    change distAdv (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.1)
      (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.2)
        (D.distinguisherL n) ≤ ε n
    rw [hsampler p.2.1, hsampler p.2.2, ← distAdv_comp P, hadv]
    exact hb n (W p.2.1) (W p.2.2)

/-! ### The frozen Claim 157.a (i) as a corollary -/

section Corollary

variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G n s x))

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
    (specialScheme_keyCoinsEquiv G E hE hGE n).prodCongr
      (Equiv.piCongrRight fun _ => specialScheme_nonceCoinsEquiv G E hE hGE n)
  have hX : ∀ v : Fin (q.eval n + 1) → Fin n → Bool,
      (specialScheme G E hE hGE).multiEncDist n (q.eval n) v =
        fun t => sliceMultiEncDist G n (q.eval n) (fun _ => 0) (fun _ => n) v (e t) := by
    intro v
    funext t
    rw [PrivateKeyScheme.multiEncDist_apply, sliceMultiEncDist_apply]
    refine congrArg PrivateKeyScheme.encodeList (congrArg List.ofFn (funext fun i => ?_))
    rw [specialScheme_gen_runAt, specialScheme_enc_runAt, sliceEnc_eq_spEncStr hGE]
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.piCongrRight_apply,
      Pi.map_apply, List.drop_zero, specialScheme_keyCoinsEquiv_ofFn,
      specialScheme_nonceCoinsEquiv_ofFn]
  rw [distAdv_def, hX m, hX m', acceptProb_comp_equiv, acceptProb_comp_equiv, ← distAdv_def]
  exact hb n (fun _ => 0) (fun _ => n) (fun _ => by show 0 + n + n ≤ n + n; omega) m m'

end Corollary

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceParser.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficient slice post-processor

## Main definitions

* `SliceReduction.slicePost`: read slice descriptors and ciphertexts in parallel.

## Main results

* `SliceReduction.polyTimeComputable_slicePost`: the parser is polynomial-time on all words.
* `SliceReduction.slicePost_encode`: its exact law on encoded descriptor/ciphertext pairs.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, Theorem 99.2 with slices.
-/

namespace TCSlib.Cryptography.SecureComputation.SliceReduction

open Complexity Turing TCSlib.Cryptography

/-- Drop one descriptor and one ciphertext from the paired parser state:
`parserStep z = ⟨snd (fst z), snd (snd z)⟩`. -/
def parserStep (z : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD z)) (pairSndD (pairSndD z))

/-- `parserStep z = ⟨snd (fst z), snd (snd z)⟩`. -/
theorem parserStep_eq (z : List Bool) :
    parserStep z = pairEncode (pairSndD (pairFstD z)) (pairSndD (pairSndD z)) := rfl

/-- Emit one slice ciphertext chunk. A descriptor `⟨u,v⟩` selects offset `|u|` and width
`|v|`; on a state `⟨advice,ciphertexts⟩`, read both first entries, keep the nonce, cut the
body, and emit `⟨⟨nonce,body.drop |u| |>.take |v|⟩,[]⟩`. Emit nothing if ciphertexts are empty. -/
def parserEmit (z : List Bool) : List Bool :=
  if pairSndD z = [] then [] else
    pairEncode (pairEncode (pairFstD (pairFstD (pairSndD z)))
      (((pairSndD (pairFstD (pairSndD z))).drop
        (pairFstD (pairFstD (pairFstD z))).length).take
          (pairSndD (pairFstD (pairFstD z))).length)) []

/-- `parserEmit z` is empty if `snd z=[]`; otherwise it is the encoded chunk
`⟨⟨fst (fst (snd z)),(snd (fst (snd z))).drop |fst (fst (fst z))|
  |>.take |snd (fst (fst z))|⟩,[]⟩`. -/
theorem parserEmit_eq (z : List Bool) :
    parserEmit z = if pairSndD z = [] then [] else
      pairEncode (pairEncode (pairFstD (pairFstD (pairSndD z)))
        (((pairSndD (pairFstD (pairSndD z))).drop
          (pairFstD (pairFstD (pairFstD z))).length).take
            (pairSndD (pairFstD (pairFstD z))).length)) [] := rfl

/-- The total slice parser runs `|z|+1` emissions:
`slicePost z = Games.iterEmit parserStep parserEmit (z.length+1) z`. -/
def slicePost (z : List Bool) : List Bool :=
  Games.iterEmit parserStep parserEmit (z.length + 1) z

/-- `slicePost z = Games.iterEmit parserStep parserEmit (z.length+1) z`. -/
theorem slicePost_eq (z : List Bool) :
    slicePost z = Games.iterEmit parserStep parserEmit (z.length + 1) z := rfl

/-- Dropping both list heads never lengthens the state beyond the empty pair:
`(parserStep z).length ≤ max z.length 2`.

**Proof sketch.** Reuse the published pair-state bound after shortening the second
component. Shortening the first component can only reduce its contribution to the public
pairing length formula. -/
theorem length_parserStep_le (z : List Bool) : (parserStep z).length ≤ max z.length 2 := by
  rw [parserStep_eq]
  have hf := length_pairSndD_le (pairFstD z)
  have hs := OneWay.PosLoop.length_pairEncode_pairFstD_le z
    (pairSndD (pairSndD z)) (length_pairSndD_le (pairSndD z))
  refine le_trans ?_ hs
  rw [length_pairEncode, length_pairEncode]
  omega

/-- The slice parser is polynomial-time on every input word:
`PolyTimeComputable slicePost`.

**Proof sketch.** Total pair projections read the current descriptor and ciphertext.
The descriptor's two unary lengths drive the published polynomial-time drop and take
operations. Pair the retained nonce and cut body and emit a self-delimited list chunk.
The step drops both list heads and stays within `max |z| 2`, so the published iterate-and-emit
host gives a polynomial-time parser, including malformed inputs. -/
theorem polyTimeComputable_slicePost : PolyTimeComputable slicePost := by
  have hf := polyTimeComputable_pairFstD
  have hs := polyTimeComputable_pairSndD
  have hadv := hf.comp' hf
  have hct := hf.comp' hs
  have ho := hf.comp' hadv
  have hw := hs.comp' hadv
  have hbody := hs.comp' hct
  have hdrop := (polyTimeComputable_pairDropPoly .var).comp' (ho.pairEncode hbody)
  have htake := (polyTimeComputable_pairTakePoly .var).comp' (hw.pairEncode hdrop)
  have hemit : PolyTimeComputable parserEmit := by
    have hnil := polyTimeComputable_isNil.comp' hs
    have hout := ((hf.comp' hct).pairEncode htake).pairEncode (polyTimeComputable_const [])
    convert polyTimeComputable_ite hnil (polyTimeComputable_const []) hout using 1
    funext z
    rw [parserEmit_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
    by_cases h : pairSndD z = []
    · rw [if_pos h, decide_eq_true h]; rfl
    · rw [if_neg h, decide_eq_false h]; rfl
  exact Games.polyTimeComputable_iterEmit
    ((hs.comp' hf).pairEncode (hs.comp' hs)) hemit 2 length_parserStep_le

/-- Each encoded list has at least as many bits as entries:
`l.length ≤ (PrivateKeyScheme.encodeList l).length`. -/
theorem length_le_encodeList (l : List (List Bool)) :
    l.length ≤ (PrivateKeyScheme.encodeList l).length := by
  induction l with
  | nil => rw [List.length_nil, PrivateKeyScheme.encodeList_nil, List.length_nil]
  | cons a l ih =>
    rw [List.length_cons, PrivateKeyScheme.encodeList_cons, length_pairEncode]
    omega

/-- On paired encoded lists of descriptors and ciphertexts, the parser cuts every body
and keeps every nonce:
`slicePost ⟨encodeList (l.map fst),encodeList (l.map snd)⟩ = encodeList
  (l.map fun (d,c) => ⟨fst c,(snd c).drop |fst d| |>.take |snd d|⟩)`.
[PS10, Theorem 99.2, with slices]

**Proof sketch.** Regard the state as one encoding of a list of descriptor/ciphertext
pairs. The step removes the two heads, the empty state is fixed, and emission reads the
specified chunk of each ciphertext. The list encoding contains at least one bit per entry,
so `|state|+1` iterations suffice. Apply the existing iterate-and-emit encoding theorem and
the existing flat-map law for the ciphertext list encoding. -/
theorem slicePost_encode (l : List (List Bool × List Bool)) :
    slicePost (pairEncode (PrivateKeyScheme.encodeList (l.map Prod.fst))
      (PrivateKeyScheme.encodeList (l.map Prod.snd))) =
        PrivateKeyScheme.encodeList (l.map fun e => pairEncode (pairFstD e.2)
          (((pairSndD e.2).drop (pairFstD e.1).length).take (pairSndD e.1).length)) := by
  let enc : List (List Bool × List Bool) → List Bool := fun t =>
    pairEncode (PrivateKeyScheme.encodeList (t.map Prod.fst))
      (PrivateKeyScheme.encodeList (t.map Prod.snd))
  let g : (List Bool × List Bool) → List Bool := fun e =>
    pairEncode (pairEncode (pairFstD e.2)
      (((pairSndD e.2).drop (pairFstD e.1).length).take (pairSndD e.1).length)) []
  have hnil : enc [] = pairEncode [] [] := by
    simp only [enc, List.map_nil, PrivateKeyScheme.encodeList_nil]
  have hcons (e : List Bool × List Bool) (t : List (List Bool × List Bool)) :
      enc (e :: t) = pairEncode
        (pairEncode e.1 (PrivateKeyScheme.encodeList (t.map Prod.fst)))
        (pairEncode e.2 (PrivateKeyScheme.encodeList (t.map Prod.snd))) := by
    simp only [enc, List.map_cons, PrivateKeyScheme.encodeList_cons]
  have hstep_nil : parserStep (enc []) = enc [] := by
    rw [hnil, parserStep_eq, pairFstD_pairEncode, pairSndD_pairEncode]
    simp only [pairSndD_eq, pairDecode_nil, Option.map_none, Option.getD_none]
  have hstep : ∀ e ∈ l, ∀ t, parserStep (enc (e :: t)) = enc t := by
    intro e he t
    rw [hcons, parserStep_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, enc]
  have hemit_nil : parserEmit (enc []) = [] := by
    rw [hnil, parserEmit_eq, pairSndD_pairEncode, if_pos rfl]
  have hemit : ∀ e ∈ l, ∀ t, parserEmit (enc (e :: t)) = g e := by
    intro e he t
    rw [hcons, parserEmit_eq, pairSndD_pairEncode, if_neg (pairEncode_ne_nil _ _)]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, g]
  have hfuel : l.length ≤ (enc l).length + 1 := by
    have h := length_le_encodeList (l.map Prod.snd)
    rw [List.length_map] at h
    dsimp only [enc]
    rw [length_pairEncode]
    omega
  rw [slicePost_eq]
  change Games.iterEmit parserStep parserEmit ((enc l).length + 1) (enc l) = _
  rw [Games.iterEmit_encode parserStep parserEmit enc g l hstep_nil hstep
    hemit_nil hemit _ hfuel, MultiMsg.encodeList_eq_flatMap, List.flatMap_map]

end TCSlib.Cryptography.SecureComputation.SliceReduction

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceReduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceParser
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity.Pad

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Slice advice and the D4 consumer

## Main definitions

* `SliceReduction.sliceAdvice`: unary offsets and window widths in the list encoding.

## Main results

* `SliceReduction.exists_slicePost_nuppt`: hard-wire polynomial-length slice advice.
* `SliceReduction.slicePost_tuple`: the same-seed identity with special slice ciphertexts.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, Theorem 99.2 with slices.
-/

namespace TCSlib.Cryptography.SecureComputation.SliceReduction

open Complexity Turing TCSlib.Cryptography

/-- Hard-wiring polynomial-length advice after the slice parser gives a PPT reduction:
`∃ B, ∀ n, ∃ e : D.Coins n ≃ B.Coins n, ∀ y r,
  B.distinguisherL n y (e r) = D.distinguisherL n (slicePost ⟨β n,y⟩) r`,
provided `|β n| ≤ b(n)`. [PS10, Theorem 99.2, with slices]

**Proof sketch.** Precompose `D` with the total polynomial-time slice parser, swapping the
argument/advice pair into the parser's order. Hard-wire the extra advice with the published
NUPPT closure theorem. Both operations preserve the coin polynomial; its canonical coin
congruence preserves the raw coin string, so the activation and verdict equations hold
pointwise, on arbitrary parser inputs. -/
theorem exists_slicePost_nuppt (D : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, ∀ n, ∃ e : D.Coins n ≃ B.Coins n, ∀ y r,
      B.distinguisherL n y (e r) =
        D.distinguisherL n (slicePost (pairEncode (β n) y)) r := by
  obtain ⟨A, hAc, -, -, hA⟩ := D.exists_comp
    (polyTimeComputable_slicePost.comp'
      (polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD))
    polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := A.exists_withAdvice β b hβ
  have hc : D.coins = B.coins := (hBc.trans hAc).symm
  refine ⟨B, fun n => ⟨NUPPT.coinsCongr hc n, fun y r => ?_⟩⟩
  rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq,
    NUPPT.runAt_coinsCongr hc, hB, hA, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [NUPPT.runAt_eq]
  rfl

/-- The slice descriptor advice is the encoded list of unary offset/width pairs:
`sliceAdvice n o len = encodeList (List.ofFn fun i => ⟨1^{o i},1^{n+len i}⟩)`. -/
def sliceAdvice {Q : ℕ} (n : ℕ) (o len : Fin Q → ℕ) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun i =>
    pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true))

/-- `sliceAdvice n o len = encodeList (List.ofFn fun i => ⟨1^{o i},1^{n+len i}⟩)`. -/
theorem sliceAdvice_eq {Q : ℕ} (n : ℕ) (o len : Fin Q → ℕ) :
    sliceAdvice n o len = PrivateKeyScheme.encodeList (List.ofFn fun i =>
      pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true)) := rfl

/-- Uniformly bounded entries have a linearly bounded list encoding:
`(∀ c ∈ l, c.length ≤ B) → (encodeList l).length ≤ l.length*(2*B+2)`. -/
theorem length_encodeList_le (l : List (List Bool)) (B : ℕ)
    (h : ∀ c ∈ l, c.length ≤ B) :
    (PrivateKeyScheme.encodeList l).length ≤ l.length * (2 * B + 2) := by
  induction l with
  | nil =>
    simp only [PrivateKeyScheme.encodeList_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons c l ih =>
    have hc := h c (List.mem_cons_self)
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    rw [PrivateKeyScheme.encodeList_cons, length_pairEncode, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

/-- Fitting slice advice has polynomial length:
`o i+n+len i ≤ L → |sliceAdvice n o len| ≤ Q*(6*L+6)`.
This includes empty messages and slices that fit exactly.

**Proof sketch.** Each descriptor has at most `3*L+2` bits by the fit inequality. Each
encoded-list entry adds twice that length plus two delimiters. Apply the general list
encoding length bound to its `Q` entries. -/
theorem length_sliceAdvice_le {Q : ℕ} (L n : ℕ) (o len : Fin Q → ℕ)
    (hfit : ∀ i, o i + n + len i ≤ L) :
    (sliceAdvice n o len).length ≤ Q * (6 * L + 6) := by
  rw [sliceAdvice_eq]
  have h := length_encodeList_le (List.ofFn fun i =>
    pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true)) (3 * L + 2)
      (by
        intro c hc
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        rw [length_pairEncode, List.length_replicate, List.length_replicate]
        have hi := hfit i
        omega)
  have heq : 2 * (3 * L + 2) + 2 = 6 * L + 6 := by omega
  simpa only [List.length_ofFn, heq] using h

/-- On the same key/nonce seed, cutting a D4 tuple of full-width slice masks is the
encoded tuple of special ciphertexts from those slices:
`slicePost ⟨sliceAdvice n o len, encodeTupleOut (prfEncRealOut F masks t)⟩ =
  encodeList (List.ofFn fun i => spEncStr (fun _ => ⟦F t.1 (t.2 i)⟧.drop (o i))
    ⟦t.1⟧ ⟦m i⟧ ⟦t.2 i⟧)`, where `masks i = sliceMask L n (o i) ⟦m i⟧`
and every `o i+n+len i ≤ L`. No relabelling of the encryption seed is used.
[PS10, Theorem 99.2, with slices]

**Proof sketch.** Apply the total parser's encoded-list law to the descriptor/ciphertext
pairs from D4. Read the real tuple entrywise through its public reader. The pointwise XOR
encoding and the shared special-encryption slice-mask identity identify each selected body.
All equations preserve the input key and every nonce exactly. -/
theorem slicePost_tuple {n L q : ℕ}
    (F : (Fin n → Bool) → (Fin n → Bool) → (Fin L → Bool))
    (o len : Fin (q + 1) → ℕ) (hfit : ∀ i, o i + n + len i ≤ L)
    (m : (i : Fin (q + 1)) → Fin (len i) → Bool)
    (t : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) :
    slicePost (pairEncode (sliceAdvice n o len)
      (encodeTupleOut (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t))) =
        PrivateKeyScheme.encodeList (List.ofFn fun i =>
          spEncStr (fun _ => (List.ofFn (F t.1 (t.2 i))).drop (o i))
            (List.ofFn t.1) (List.ofFn (m i)) (List.ofFn (t.2 i))) := by
  rw [sliceAdvice_eq, encodeTupleOut_eq]
  have hp := slicePost_encode (List.ofFn fun i : Fin (q + 1) =>
    (pairEncode (List.replicate (o i) true) (List.replicate (n + len i) true),
      pairEncode
        (List.ofFn (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t i).1)
        (List.ofFn (prfEncRealOut F (fun i => sliceMask L n (o i) (List.ofFn (m i))) t i).2)))
  simp only [List.map_ofFn] at hp
  refine hp.trans ?_
  apply congrArg PrivateKeyScheme.encodeList
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [prfEncRealOut_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, List.length_replicate,
    ← zipWith_xor_ofFn_add]
  have h := spEncStr_eq_sliceMask L (o i) (List.ofFn (F t.1 (t.2 i)))
    (List.ofFn t.1) (List.ofFn (m i)) (List.ofFn (t.2 i)) List.length_ofFn
      (by simpa only [List.length_ofFn] using hfit i)
  simpa only [List.length_ofFn] using h.symm

end TCSlib.Cryptography.SecureComputation.SliceReduction

## ===== TCSlib/Cryptography/SecureComputation/Garbling.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.SecureComputation.Garbling.Probability
import TCSlib.Cryptography.SecureComputation.Garbling.CoinBlocks

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Garbled circuits

[PS10, §6.2.1–6.2.3]. Construction 158.a (inventory): to garble a circuit `C` with fan-in two,
associate two random keys `k_w^0, k_w^1` to every wire `w`. Each gate becomes a table with one
row per assignment of its input bits; the row encrypts the key of the gate's output value under
the keys of its inputs. The rows are randomly permuted, so the position of the row that
decrypts does not reveal the inputs. Claim 159.a (inventory): given the input keys, evaluating
the garbled circuit opens exactly one row per gate, with high probability, and ends with the key
of `C(x)` on the output wire.

**The construction on `main`'s circuits** (route note `design/S3b-yao-runWith.md`).
- The circuit is `main`'s `BoolCircuit.DAGCircuit`, with vertices numbered topologically.
- Garbled evaluation is a second instance of `DAGCircuit.runWith`, whose gate function reads its
  vertex from the length of the data so far.
- Its correctness is the simulation lemma `runWith_sim` (proved; the route probe's lemma), which
  relates the two runs through the wire keys.

**The encryption, abstracted.** The rows are built and opened through an interface `MultiEnc`:
encryption and decryption under a list of keys. A row with two inputs is doubly encrypted, one
with a single input singly encrypted, and a constant gate's row is in the clear. Its two
properties:
- `MultiEnc.DecCorrect`: decryption inverts encryption;
- `MultiEnc.WrongKeyBot δ`: under independent uniform keys, a row decrypted with a different key
  list gives `⊥` except with probability `δ`. This is [PS10]'s "the extra property" (§6.2.2).

The special encryption scheme of Algorithm 157.2 gives both, nested (`GarblingSpecial.lean`).

**Deviations.**
- **Gates of any fan-in up to two.** Each table has `2^{|args|} ∈ {1, 2, 4}` rows (`¬` gates and
  constant gates included); [PS10] describes the two-input case.
- **The row order.** A table lists its rows in a fixed enumeration of the assignments, composed
  with the gate's random permutation.
- **The evaluator** opens the first row that decrypts (`List.findSome?`). The formal `Good`
  invariant and the probability theorems below assert correctness of that first opening for
  every assignment. They do not assert the source's stronger unique-opening conclusion.
  Several rows may open to the same correct label, for example when wire labels coincide.
  The cross-opening union-bound sketch proves a sufficient stronger event for this target.

## Main definitions

* `SecureComputation.MultiEnc`, `MultiEnc.DecCorrect`, `MultiEnc.WrongKeyBot`.
* `SecureComputation.gateOut`: a gate's output on an assignment of its argument positions.
* `SecureComputation.GarbleSeed`, `garbledTable`, `inputKeys`, `garbledValues`,
  `garbledOutput`: Construction 158.a and its evaluation.
* `SecureComputation.Good`: every table's first successful opening, under every assignment's
  keys, gives the right key; uniqueness is not part of this invariant.

## Main results

* `SecureComputation.runWith_sim` (proved): two `runWith` runs agree through a per-vertex
  encoding.
* `SecureComputation.garbledValues_getD`, `garbledOutput_eq` (Claim 159.a, deterministic part,
  proved): a good garbling evaluates to the keys of the circuit's values, and of `C(x)`.
* `SecureComputation.uprob_not_good_le_of_perm` (B2): the failure bound holds for every
  fixed row-permutation family; `uprob_not_good_le` averages this bound over uniform permutations.
* `SecureComputation.uprob_not_good_le_of_uniform_data`: uniform keys and row coins suffice,
  even when row permutations depend on the seed.

## Contents

* `Garbling.Probability`: independent marginals and the first successful opening.
* `Garbling.CoinBlocks`: the joint uniform law of disjoint key and row-coin blocks.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.1–6.2.3 (book pp. 156–160).
-/

namespace TCSlib.Cryptography.SecureComputation

open BoolCircuit TCSlib.Cryptography

/-! ### Simulation of `runWith` -/

/-- **Indexed simulation of `runWith`.** If the second evaluator, at gate `i`, maps data that
encode the first evaluator's data (vertex by vertex, through `W v`) on the gate's inputs to the
encoding of the first evaluator's output, then the two runs agree through `W` at every
vertex.

**Proof sketch.** Use strong induction on the vertex number. At an input vertex, the claim is
the initial correspondence. At a gate vertex, both runs read their inputs from the preceding
prefix, whose length identifies this gate's vertex. Acyclicity puts every argument at a smaller
vertex, so the induction hypothesis relates the two argument lists. Reading an earlier vertex
is unchanged by the later gates; the gate simulation hypothesis therefore gives the required
correspondence for the newly appended value. -/
theorem runWith_sim {α β : Type} (fA : DAGGate → List α → α) (fB : ℕ → DAGGate → List β → β)
    (W : ℕ → α → β) (dA : α) (dB : β) (gs : List DAGGate) (initA : List α) (initB : List β)
    (hlen : initB.length = initA.length)
    (hinit : ∀ v < initA.length, initB.getD v dB = W v (initA.getD v dA))
    (hacyc : ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < initA.length + i)
    (hgate : ∀ (i : ℕ) (h : i < gs.length) (vA : List α) (vB : List β),
       vA.length = initA.length + i → vB.length = initA.length + i →
       (∀ a ∈ (gs[i]).args, vB.getD a dB = W a (vA.getD a dA)) →
       fB (initA.length + i) gs[i] vB = W (initA.length + i) (fA gs[i] vA)) :
    ∀ v < initA.length + gs.length,
      (runWith (fun g vs => fB vs.length g vs) gs initB).getD v dB =
        W v ((runWith fA gs initA).getD v dA) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hlt : v < initA.length
    · rw [runWith_getD_of_lt _ _ _ (hlen ▸ hlt), runWith_getD_of_lt _ _ _ hlt]
      exact hinit v hlt
    · obtain ⟨i, rfl⟩ : ∃ i, v = initA.length + i := ⟨v - initA.length, by omega⟩
      have hi : i < gs.length := by omega
      have hB := runWith_getD_gate (fun g vs => fB vs.length g vs) gs initB hi dB
      have hA := runWith_getD_gate fA gs initA hi dA
      rw [hlen] at hB
      rw [hB, hA, length_runWith, List.length_take_of_le hi.le, hlen]
      refine hgate i hi _ _ (by rw [length_runWith, List.length_take_of_le hi.le])
        (by rw [length_runWith, List.length_take_of_le hi.le, hlen]) fun a ha => ?_
      have ha' := hacyc i hi a ha
      rw [runWith_getD_take _ gs initB hi.le (by omega),
        runWith_getD_take _ gs initA hi.le ha']
      exact ih a ha' (by omega)

/-! ### Multi-key encryption -/

/-- **Encryption under a list of keys**: `enc ks o r` encrypts the key `o` under the keys `ks`
with coins `r`, and `dec ks c` decrypts, with `none` for `⊥`. -/
structure MultiEnc (K C ρ : Type) where
  /-- Encryption under a list of keys. -/
  enc : List K → K → ρ → C
  /-- Decryption under a list of keys; `none` is `⊥`. -/
  dec : List K → C → Option K

namespace MultiEnc

variable {K C ρ : Type}

/-- **Correctness**: decryption under at most two keys inverts encryption under them. -/
def DecCorrect (M : MultiEnc K C ρ) : Prop :=
  ∀ ks : List K, ks.length ≤ 2 → ∀ (o : K) (r : ρ), M.dec ks (M.enc ks o r) = some o

/-- `DecCorrect M` holds exactly when decryption inverts encryption under every list of at
most two keys, for every plaintext key and coin. -/
theorem decCorrect_iff (M : MultiEnc K C ρ) :
    M.DecCorrect ↔
      ∀ ks : List K, ks.length ≤ 2 → ∀ (o : K) (r : ρ),
        M.dec ks (M.enc ks o r) = some o := Iff.rfl

/-- **The wrong-key property with error `δ`** [PS10, §6.2.2, "the extra property"]: for at most
two positions, two independent uniform keys per position, and two different choices `a ≠ a'` of
key per position, a ciphertext of any key `o` under the `a`-keys decrypts to `⊥` under the
`a'`-keys, except with probability `δ` over the keys and the coins. -/
def WrongKeyBot [Fintype K] [Fintype ρ] (M : MultiEnc K C ρ) (δ : ℝ) : Prop :=
  ∀ (len : ℕ), len ≤ 2 → ∀ (a a' : Fin len → Bool), a ≠ a' → ∀ o : K,
    uprob (fun t : (Fin len → Bool → K) × ρ =>
      (M.dec (List.ofFn fun j => t.1 j (a' j))
        (M.enc (List.ofFn fun j => t.1 j (a j)) o t.2)).isSome = true) ≤ δ

/-- `WrongKeyBot M δ` holds exactly when each pair of distinct assignments to at most two
key positions gives successful wrong-key decryption probability at most `δ`, uniformly in
the plaintext key, with independent uniform key pairs and coins. -/
theorem wrongKeyBot_iff [Fintype K] [Fintype ρ] (M : MultiEnc K C ρ) (δ : ℝ) :
    M.WrongKeyBot δ ↔
      ∀ (len : ℕ), len ≤ 2 → ∀ (a a' : Fin len → Bool), a ≠ a' → ∀ o : K,
        uprob (fun t : (Fin len → Bool → K) × ρ =>
          (M.dec (List.ofFn fun j => t.1 j (a' j))
            (M.enc (List.ofFn fun j => t.1 j (a j)) o t.2)).isSome = true) ≤ δ := Iff.rfl

end MultiEnc

/-! ### Gates on assignments -/

/-- **A gate's output on an assignment of its argument positions**: the gate's kind applied to
the bits `ass 0, …, ass (|args| − 1)`. -/
def gateOut (g : DAGGate) (ass : Fin g.args.length → Bool) : Bool :=
  (DAGGate.mk g.kind (List.range g.args.length)).eval (List.ofFn ass)

/-- On any assignment of argument positions, `gateOut` evaluates the gate's kind on the
assignment list, with arguments replaced by their consecutive positions. -/
theorem gateOut_eq_eval (g : DAGGate) (ass : Fin g.args.length → Bool) :
    gateOut g ass =
      (DAGGate.mk g.kind (List.range g.args.length)).eval (List.ofFn ass) := rfl

/-- Reading a list of values at a gate's arguments is the `ofFn` of the positions. -/
theorem map_args_eq_ofFn {β : Type} (g : DAGGate) (f : ℕ → β) :
    g.args.map f = List.ofFn fun t : Fin g.args.length => f (g.args[t]) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp

/-- The range positions read the assignment back. -/
private theorem map_range_getD_ofFn {len : ℕ} (ass : Fin len → Bool) :
    (List.range len).map (fun a => (List.ofFn ass).getD a false) = List.ofFn ass := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa using h₂)]
  simp

/-- **The assignment read from the circuit's values gives the gate's value**: `gateOut` at the
bits of the arguments is `DAGGate.eval`. -/
theorem gateOut_eq (g : DAGGate) (vals : List Bool) :
    gateOut g (fun t => vals.getD (g.args[t]) false) = g.eval vals := by
  have hA := map_range_getD_ofFn (fun t : Fin g.args.length => vals.getD (g.args[t]) false)
  have hB := map_args_eq_ofFn g (fun a => vals.getD a false)
  have hall : ∀ (l : List ℕ) (p : ℕ → Bool), l.all p = (l.map p).all id := by
    intro l p; rw [List.all_map]; rfl
  have hany : ∀ (l : List ℕ) (p : ℕ → Bool), l.any p = (l.map p).any id := by
    intro l p; rw [List.any_map]; rfl
  unfold gateOut
  simp only [DAGGate.eval_eq]
  cases g.kind <;> simp only [hall, hany, hA, hB]

/-! ### The garbling -/

variable {K C ρ : Type} [Inhabited K] {n : ℕ}

/-- **The randomness of a garbling** of `Cc`: two keys per vertex, a coin per table row, and a
permutation of each gate's rows. -/
abbrev GarbleSeed (Cc : DAGCircuit n) (K ρ : Type) : Type :=
  (Fin Cc.size → Bool → K) ×
    ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) ×
    ((i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool))

/-- A garbling seed is the product of the two-key function at each vertex, the coin function
for each gate assignment, and the row permutation at each gate. -/
theorem GarbleSeed_eq (Cc : DAGCircuit n) (K ρ : Type) :
    GarbleSeed Cc K ρ =
      ((Fin Cc.size → Bool → K) ×
        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) ×
        ((i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool))) := rfl

variable (M : MultiEnc K C ρ) (Cc : DAGCircuit n)

/-- The key of vertex `v` for the bit `b` (a default beyond the circuit). -/
def keyAt (s : GarbleSeed Cc K ρ) (v : ℕ) (b : Bool) : K :=
  if h : v < Cc.size then s.1 ⟨v, h⟩ b else default

/-- The key at `v` for bit `b` is the seed's key when `v < Cc.size`, and `default` otherwise. -/
theorem keyAt_eq (s : GarbleSeed Cc K ρ) (v : ℕ) (b : Bool) :
    keyAt Cc s v b = if h : v < Cc.size then s.1 ⟨v, h⟩ b else default := rfl

/-- The keys of gate `i`'s arguments under the assignment `a` of its positions. -/
def argKeys (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length)
    (a : Fin (Cc.gates[i]).args.length → Bool) : List K :=
  List.ofFn fun t => keyAt Cc s ((Cc.gates[i]).args[t]) (a t)

/-- The argument-key list of gate `i` enumerates the wire key selected by `a t` at each
argument vertex `(Cc.gates[i]).args[t]`. -/
theorem argKeys_eq (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length)
    (a : Fin (Cc.gates[i]).args.length → Bool) :
    argKeys Cc s i a = List.ofFn fun t => keyAt Cc s ((Cc.gates[i]).args[t]) (a t) := rfl

/-- **The row of gate `i` for the assignment `a`** [PS10, §6.2.3]: the key of the gate's output
on `a`, encrypted under the keys of its arguments on `a`. -/
def garbledRow (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length)
    (a : Fin (Cc.gates[i]).args.length → Bool) : C :=
  M.enc (argKeys Cc s i a) (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a)) (s.2.1 i a)

/-- A garbled row encrypts the output wire key for `gateOut (Cc.gates[i]) a` under
`argKeys Cc s i a`, using that row's seed coins. -/
theorem garbledRow_eq (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length)
    (a : Fin (Cc.gates[i]).args.length → Bool) :
    garbledRow M Cc s i a =
      M.enc (argKeys Cc s i a) (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a)) (s.2.1 i a) := rfl

/-- **The garbled table of gate `i`** [PS10, §6.2.3, "the rows … must be randomly shuffled"]: the
rows in a fixed enumeration of the assignments, composed with the gate's random permutation. -/
noncomputable def garbledTable (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length) : List C :=
  (Finset.univ : Finset (Fin (Cc.gates[i]).args.length → Bool)).toList.map
    fun a => garbledRow M Cc s i (s.2.2 i a)

/-- Gate `i`'s table enumerates its assignments through `Finset.univ.toList` and applies the
seed's permutation before forming each garbled row. -/
theorem garbledTable_eq (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length) :
    garbledTable M Cc s i =
      (Finset.univ : Finset (Fin (Cc.gates[i]).args.length → Bool)).toList.map
        fun a => garbledRow M Cc s i (s.2.2 i a) := rfl

/-- The garbled table at vertex `v` (none at the inputs). -/
noncomputable def tableAt (s : GarbleSeed Cc K ρ) (v : ℕ) : List C :=
  if h : n ≤ v ∧ v - n < Cc.gates.length then garbledTable M Cc s ⟨v - n, h.2⟩ else []

/-- The table at `v` is gate `v - n`'s garbled table when `v` names a gate vertex, and is
empty otherwise, including input vertices and vertices beyond the circuit. -/
theorem tableAt_eq (s : GarbleSeed Cc K ρ) (v : ℕ) :
    tableAt M Cc s v = if h : n ≤ v ∧ v - n < Cc.gates.length then
      garbledTable M Cc s ⟨v - n, h.2⟩ else [] := rfl

/-- The table at the vertex of gate `i` is its garbled table. -/
theorem tableAt_gate (s : GarbleSeed Cc K ρ) {i : ℕ} (hi : i < Cc.gates.length) :
    tableAt M Cc s (n + i) = garbledTable M Cc s ⟨i, hi⟩ := by
  unfold tableAt
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  exact Fin.ext (by simp)

/-- **The evaluator at a gate** [PS10, §6.2.3, "the evaluating player can attempt to decrypt all
four rows"]: the first row of the vertex's table that decrypts under the keys of the gate's
arguments (a default if none does). -/
def evalGate (T : ℕ → List C) (v : ℕ) (g : DAGGate) (vs : List K) : K :=
  ((T v).findSome? (M.dec (g.args.map fun a => vs.getD a default))).getD default

/-- Evaluating gate `g` at `v` decrypts the first successful row of `T v` under its argument
keys from `vs`, with `default` when no row decrypts. -/
theorem evalGate_eq (T : ℕ → List C) (v : ℕ) (g : DAGGate) (vs : List K) :
    evalGate M T v g vs =
      ((T v).findSome? (M.dec (g.args.map fun a => vs.getD a default))).getD default := rfl

/-- **The input keys**: the key of each input bit of `x`. -/
def inputKeys (s : GarbleSeed Cc K ρ) (x : Fin n → Bool) : List K :=
  List.ofFn fun i : Fin n => keyAt Cc s i (x i)

/-- The input-key list enumerates `keyAt Cc s i (x i)` over all input positions `i`. -/
theorem inputKeys_eq (s : GarbleSeed Cc K ρ) (x : Fin n → Bool) :
    inputKeys Cc s x = List.ofFn fun i : Fin n => keyAt Cc s i (x i) := rfl

/-- **Garbled evaluation**: `runWith` over the circuit's gates from the input keys, each gate
opened by `evalGate` at its vertex. -/
noncomputable def garbledValues (s : GarbleSeed Cc K ρ) (init : List K) : List K :=
  runWith (fun g vs => evalGate M (tableAt M Cc s) vs.length g vs) Cc.gates init

/-- Garbled evaluation runs `runWith` from `init` over `Cc.gates`, opening each gate at the
vertex given by the current value-list length. -/
theorem garbledValues_eq (s : GarbleSeed Cc K ρ) (init : List K) :
    garbledValues M Cc s init =
      runWith (fun g vs => evalGate M (tableAt M Cc s) vs.length g vs) Cc.gates init := rfl

/-- **The garbled output** on input `x`: the key reached at the output vertex. -/
noncomputable def garbledOutput (s : GarbleSeed Cc K ρ) (x : Fin n → Bool) : K :=
  (garbledValues M Cc s (inputKeys Cc s x)).getD Cc.output default

/-- The garbled output reads the value at `Cc.output` after garbled evaluation from the
input keys, using `default` for a missing value. -/
theorem garbledOutput_eq_getD (s : GarbleSeed Cc K ρ) (x : Fin n → Bool) :
    garbledOutput M Cc s x =
      (garbledValues M Cc s (inputKeys Cc s x)).getD Cc.output default := rfl

/-- **A good garbling**: at every gate, under the keys of every assignment of its arguments, the
first row of the table that decrypts gives the key of the gate's output on that assignment.
This is first-success correctness, not uniqueness of the row that can decrypt. -/
def Good (s : GarbleSeed Cc K ρ) : Prop :=
  ∀ (i : Fin Cc.gates.length) (a : Fin (Cc.gates[i]).args.length → Bool),
    (garbledTable M Cc s i).findSome? (M.dec (argKeys Cc s i a)) =
      some (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a))

/-- `Good M Cc s` holds exactly when every gate table, under every assignment's argument
keys, first decrypts to the key of that gate's output on the assignment. -/
theorem good_iff (s : GarbleSeed Cc K ρ) :
    Good M Cc s ↔
      ∀ (i : Fin Cc.gates.length) (a : Fin (Cc.gates[i]).args.length → Bool),
        (garbledTable M Cc s i).findSome? (M.dec (argKeys Cc s i a)) =
          some (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a)) := Iff.rfl

/-- **Claim 159.a, deterministic part: a good garbling evaluates to the keys of the circuit's
values** [PS10, §6.2.3]: at every vertex, garbled evaluation from the input keys of `x` reaches
the key of the vertex's value on `x` (`runWith_sim`, with the encoding `keyAt`).

**Proof sketch.** Apply indexed simulation with each Boolean wire value encoded by its
corresponding wire key. The input-key list gives the initial correspondence, and the circuit's
topological ordering supplies acyclicity. At a gate, the correspondence on its arguments makes
the supplied keys exactly those for their Boolean assignment. Goodness says that the first
decrypting row returns the key of this assignment's output. The Boolean gate equation identifies
that output with the value in the ordinary circuit run, completing the simulation. -/
theorem garbledValues_getD (s : GarbleSeed Cc K ρ) (hgood : Good M Cc s) (x : Fin n → Bool) :
    ∀ v < Cc.size, (garbledValues M Cc s (inputKeys Cc s x)).getD v default =
      keyAt Cc s v ((Cc.values x).getD v false) := by
  intro v hv
  have hlenA : (List.ofFn x).length = n := List.length_ofFn
  rw [garbledValues_eq, DAGCircuit.values_eq]
  refine runWith_sim DAGGate.eval (fun v g vs => evalGate M (tableAt M Cc s) v g vs)
    (keyAt Cc s) false default Cc.gates (List.ofFn x) (inputKeys Cc s x)
    (by simp [inputKeys]) ?_ ?_ ?_ v
    (by simpa only [hlenA, DAGCircuit.size_eq] using hv)
  · intro w hw
    rw [hlenA] at hw
    have h1 : w < (inputKeys Cc s x).length := by simp [inputKeys, hw]
    have h2 : w < (List.ofFn x).length := by simp [hw]
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
    simp [inputKeys]
  · intro i hi a ha
    rw [hlenA]
    exact Cc.args_lt i hi a ha
  · intro i hi vA vB _ _ hargs
    rw [hlenA]
    show evalGate M (tableAt M Cc s) (n + i) (Cc.gates[i]) vB = _
    simp only [evalGate]
    rw [tableAt_gate M Cc s hi]
    have hkeys : (Cc.gates[i]).args.map (fun a => vB.getD a default) =
        argKeys Cc s ⟨i, hi⟩ (fun t => vA.getD ((Cc.gates[i]).args[t]) false) := by
      rw [List.map_congr_left hargs, map_args_eq_ofFn]
      rfl
    rw [hkeys, hgood ⟨i, hi⟩]
    simp only [Option.getD_some]
    exact congrArg (keyAt Cc s (n + i)) (gateOut_eq (Cc.gates[i]) vA)

/-- **Claim 159.a, deterministic part, at the output**: a good garbling's output on `x` is the
key of `C(x)` on the output wire. -/
theorem garbledOutput_eq (s : GarbleSeed Cc K ρ) (hgood : Good M Cc s) (x : Fin n → Bool) :
    garbledOutput M Cc s x = keyAt Cc s Cc.output (Cc.eval x) :=
  (garbledOutput_eq_getD M Cc s x).trans
    ((garbledValues_getD M Cc s hgood x Cc.output
      ((DAGCircuit.size_eq Cc).symm ▸ Cc.output_lt)).trans
      (congrArg (keyAt Cc s Cc.output) (DAGCircuit.eval_eq Cc x).symm))

/-- Correct rows and no successful cross-opening imply a good garbling:
if `M` is correct, `Cc` is fan-in two, and for every gate and `a ≠ a'`,
`M.dec (argKeys Cc s i a') (garbledRow M Cc s i a) = none`, then `Good M Cc s`.
[PS10, §6.2.3, Claim 159.a]

**Proof sketch.** The row for the current assignment opens by correctness. It occurs
in the permuted table because the row permutation is surjective. Every other assignment's
row fails by the cross-opening hypothesis. Thus each table has a successful row and every
successful row gives the specified key, so its first successful opening is that key. -/
theorem good_of_no_crossOpening (hdec : M.DecCorrect) (hC : Cc.IsFaninTwo)
    (s : GarbleSeed Cc K ρ)
    (hcross : ∀ (i : Fin Cc.gates.length)
      (a a' : Fin (Cc.gates[i]).args.length → Bool), a ≠ a' →
        M.dec (argKeys Cc s i a') (garbledRow M Cc s i a) = none) : Good M Cc s := by
  classical
  rw [good_iff]
  intro i a
  have hlen : (argKeys Cc s i a).length ≤ 2 := by
    rw [argKeys_eq, List.length_ofFn]
    exact ((DAGCircuit.isFaninTwo_iff Cc).mp hC).2 _ (List.getElem_mem i.isLt)
  have hcorrect : M.dec (argKeys Cc s i a) (garbledRow M Cc s i a) =
      some (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a)) := by
    rw [garbledRow_eq]
    exact (MultiEnc.decCorrect_iff M).mp hdec _ hlen _ _
  rw [garbledTable_eq]
  apply GarblingProbability.findSome_eq_some_of_dichotomy
  · refine ⟨garbledRow M Cc s i a, ?_, hcorrect⟩
    apply List.mem_map.mpr
    refine ⟨(s.2.2 i).symm a, ?_, ?_⟩
    · exact Finset.mem_toList.mpr (Finset.mem_univ _)
    · rw [Equiv.apply_symm_apply]
  · intro row hrow
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hrow
    by_cases hba : s.2.2 i b = a
    · right
      rw [hba]
      exact hcorrect
    · exact Or.inl (hcross i (s.2.2 i b) a hba)

/-- A wrong-key probability bound is nonnegative:
`M.WrongKeyBot δ → 0 ≤ δ`. Use distinct choices at one position and any plaintext key. -/
theorem wrongKeyBot_nonneg [Fintype K] [Fintype ρ] {δ : ℝ}
    (hδ : M.WrongKeyBot δ) : 0 ≤ δ := by
  have h := (MultiEnc.wrongKeyBot_iff M δ).mp hδ 1 (by decide)
    (fun _ => false) (fun _ => true)
    (by intro heq; have hbit := congrFun heq 0; cases hbit) default
  exact (uprob_nonneg _).trans h

/-- At a fixed gate, two distinct assignments cross-open with probability at most `δ`,
for every fixed row-permutation family `π`:
`Pr_t[(M.dec (argKeys Cc (t.1,t.2,π) i a')
  (garbledRow M Cc (t.1,t.2,π) i a)).isSome = true] ≤ δ` when `a ≠ a'`.
[PS10, §6.2.3, Claim 159.a]

**Proof sketch.** The circuit's argument vertices are distinct and precede this gate's
output vertex. Restrict the uniform key table to these vertices and the selected output
key, and read the row's independent coins. This gives a uniform plaintext key, argument
key table and row coin. Average `WrongKeyBot` over the plaintext key. The row order is
unused by a cross-opening event. -/
theorem uprob_crossOpening_le_of_perm [Fintype K] [Fintype ρ] {δ : ℝ}
    (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
    (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool))
    (i : Fin Cc.gates.length) (a a' : Fin (Cc.gates[i]).args.length → Bool) (hne : a ≠ a') :
    uprob (fun t : (Fin Cc.size → Bool → K) ×
        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
      (M.dec (argKeys Cc (t.1, t.2, π) i a')
        (garbledRow M Cc (t.1, t.2, π) i a)).isSome = true) ≤ δ := by
  classical
  have hfan := (DAGCircuit.isFaninTwo_iff Cc).mp hC
  have hmem : Cc.gates[i] ∈ Cc.gates := List.getElem_mem i.isLt
  have hnodup := (hfan.1 _ hmem).1
  have hlen := hfan.2 _ hmem
  have hout : n + i < Cc.size := by rw [DAGCircuit.size_eq]; omega
  have harglt : ∀ j : Fin (Cc.gates[i]).args.length,
      (Cc.gates[i]).args[j] < n + i :=
    fun j => Cc.args_lt i i.isLt _ (List.getElem_mem j.isLt)
  have hargSize : ∀ j : Fin (Cc.gates[i]).args.length,
      (Cc.gates[i]).args[j] < Cc.size := fun j => (harglt j).trans hout
  let arg : Fin (Cc.gates[i]).args.length → Fin Cc.size :=
    fun j => ⟨(Cc.gates[i]).args[j], hargSize j⟩
  have hinj : Function.Injective arg := by
    intro j k hjk
    have hv := congrArg Fin.val hjk
    change (Cc.gates[i]).args.get j = (Cc.gates[i]).args.get k at hv
    exact hnodup.get_inj_iff.mp hv
  let out : Fin Cc.size := ⟨n + i, hout⟩
  have hnot : ∀ j, arg j ≠ out := fun j h =>
    (Nat.ne_of_lt (harglt j)) (congrArg Fin.val h)
  let R := (k : Fin Cc.gates.length) → (Fin (Cc.gates[k]).args.length → Bool) → ρ
  have hlaw := GarblingProbability.pushesUniform_output_argKeys_row (K := K)
    arg hinj out hnot
    (gateOut (Cc.gates[i]) a) (fun r : R => r i a)
    (GarblingProbability.pushesUniform_rowCoin
      (A := fun k : Fin Cc.gates.length => Fin (Cc.gates[k]).args.length → Bool)
      (ρ := ρ) i a)
  let p : K × ((Fin (Cc.gates[i]).args.length → Bool → K) × ρ) → Prop := fun z =>
    (M.dec (List.ofFn fun j => z.2.1 j (a' j))
      (M.enc (List.ofFn fun j => z.2.1 j (a j)) z.1 z.2.2)).isSome = true
  have hu := hlaw.uprob_eq p
  calc
    _ = uprob (fun t : (Fin Cc.size → Bool → K) × R =>
        p (t.1 out (gateOut (Cc.gates[i]) a), (fun j => t.1 (arg j), t.2 i a))) := by
      apply OneWay.uprob_congr
      intro t
      simp only [garbledRow_eq, argKeys_eq, keyAt_eq, hargSize, hout, dif_pos]
      rfl
    _ = uprob p := hu
    _ ≤ δ := by
      rw [uprob_prod]
      exact (OneWay.uexp_mono (fun o : K =>
        (MultiEnc.wrongKeyBot_iff M δ).mp hδ _ hlen a a' hne o)).trans
          (OneWay.uexp_const δ).le

/-- Uniform independent keys and row coins suffice for the garbling bound, with arbitrary
row orders on the same seed space:
`PushesUniform d → Pr_w[¬ Good M Cc ((d w).1,(d w).2,π w)] ≤ 12 * |Cc.gates| * δ`.
The permutation `π w` may depend on any seed information; no independence from it is needed.
[PS10, §6.2.3, Claim 159.a, strengthened seed-law form]

**Proof sketch.** Goodness follows whenever no row cross-opens under a different assignment.
Each cross-opening ignores row order, so its probability is transported by the uniform
key/coin marginal and bounded by `WrongKeyBot`. A gate of arity at most two has at most
four assignments and three different assignments per row. Apply the finite union bound
within each gate and then over all gates. This proves the fixed-permutation B2 statement
as a special case and also covers Yao's seed-dependent XOR shifts. -/
theorem uprob_not_good_le_of_uniform_data [Fintype K] [Fintype ρ]
    (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
    {Ω : Type} [Fintype Ω]
    (d : Ω → (Fin Cc.size → Bool → K) ×
      ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ))
    (hd : HardcoreBit.PushesUniform d)
    (π : Ω → (i : Fin Cc.gates.length) →
      Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)) :
    uprob (fun w => ¬ Good M Cc ((d w).1, (d w).2, π w)) ≤
      12 * Cc.gates.length * δ := by
  classical
  let event : (i : Fin Cc.gates.length) →
      (Fin (Cc.gates[i]).args.length → Bool) →
      (Fin (Cc.gates[i]).args.length → Bool) → Ω → Prop := fun i a a' w =>
    (M.dec (argKeys Cc ((d w).1, (d w).2, π w) i a')
      (garbledRow M Cc ((d w).1, (d w).2, π w) i a)).isSome = true
  let gateBad : Fin Cc.gates.length → Ω → Prop := fun i w =>
    ∃ a ∈ Finset.univ, ∃ a' ∈ Finset.univ.erase a, event i a a' w
  have hpoint : ∀ i a a', a ≠ a' → uprob (event i a a') ≤ δ := by
    intro i a a' hne
    let π₀ : (i : Fin Cc.gates.length) →
        Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool) := fun _ => Equiv.refl _
    let p := fun t : (Fin Cc.size → Bool → K) ×
        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
      (M.dec (argKeys Cc (t.1, t.2, π₀) i a')
        (garbledRow M Cc (t.1, t.2, π₀) i a)).isSome = true
    have heq : event i a a' = fun w => p (d w) := rfl
    rw [heq, hd.uprob_eq p]
    exact uprob_crossOpening_le_of_perm M Cc hδ hC π₀ i a a' hne
  have hbad : ∀ w, ¬ Good M Cc ((d w).1, (d w).2, π w) →
      ∃ i ∈ Finset.univ, gateBad i w := by
    intro w hw
    by_contra hn
    apply hw
    apply good_of_no_crossOpening M Cc hdec hC
    intro i a a' hne
    apply Option.not_isSome_iff_eq_none.mp
    intro hs
    exact hn ⟨i, Finset.mem_univ _, a, Finset.mem_univ _, a',
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩, hs⟩
  have hgate : ∀ i, uprob (gateBad i) ≤ 12 * δ := by
    intro i
    let A := Fin (Cc.gates[i]).args.length → Bool
    have hlen : (Cc.gates[i]).args.length ≤ 2 :=
      ((DAGCircuit.isFaninTwo_iff Cc).mp hC).2 (Cc.gates[i]) (List.getElem_mem i.isLt)
    have hcardNat : Fintype.card A * (Fintype.card A - 1) ≤ 12 := by
      simp only [A, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      have hcases : (Cc.gates[i]).args.length = 0 ∨ (Cc.gates[i]).args.length = 1 ∨
          (Cc.gates[i]).args.length = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · rw [h0]; decide
      · rw [h1]; decide
      · rw [h2]; decide
    have hcard : ((Fintype.card A * (Fintype.card A - 1) : ℕ) : ℝ) ≤ 12 := by
      exact_mod_cast hcardNat
    have herase (a : A) : (Finset.univ.erase a).card = Fintype.card A - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    refine (uprob_exists_le (Finset.univ : Finset A)
      (fun a w => ∃ a' ∈ Finset.univ.erase a, event i a a' w)).trans ?_
    calc
      _ ≤ ∑ a ∈ (Finset.univ : Finset A), ∑ a' ∈ Finset.univ.erase a, δ := by
        apply Finset.sum_le_sum
        intro a ha
        refine (uprob_exists_le (Finset.univ.erase a) (fun a' w => event i a a' w)).trans ?_
        exact Finset.sum_le_sum fun a' ha' =>
          hpoint i a a' (Finset.mem_erase.mp ha').1.symm
      _ = ((Fintype.card A * (Fintype.card A - 1) : ℕ) : ℝ) * δ := by
        simp only [Finset.sum_const, herase, Finset.card_univ, nsmul_eq_mul,
          Nat.cast_mul, mul_assoc]
      _ ≤ 12 * δ := mul_le_mul_of_nonneg_right hcard (wrongKeyBot_nonneg M hδ)
  calc
    _ ≤ uprob (fun w => ∃ i ∈ Finset.univ, gateBad i w) := uprob_mono hbad
    _ ≤ ∑ i ∈ Finset.univ, uprob (gateBad i) := uprob_exists_le _ _
    _ ≤ ∑ i ∈ Finset.univ, 12 * δ := Finset.sum_le_sum fun i _ => hgate i
    _ = 12 * Cc.gates.length * δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_left_comm, ← mul_assoc]

/-- **B2: goodness for every fixed row-permutation family.** For uniform independent
keys and row coins and any fixed `π`,
`Pr_t[¬ Good M Cc (t.1,t.2,π)] ≤ 12 * Cc.gates.length * δ`.
[PS10, §6.2.3, Claim 159.a, strengthened permutation form]

**Proof sketch.** Apply the uniform-data bound to the identity map on the key/coin product
and the constant row-permutation family. This is the prescribed fixed-permutation B2 API. -/
theorem uprob_not_good_le_of_perm [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
    (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
    (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)) :
    uprob (fun t : (Fin Cc.size → Bool → K) ×
        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
      ¬ Good M Cc (t.1, t.2, π)) ≤ 12 * Cc.gates.length * δ := by
  exact uprob_not_good_le_of_uniform_data M Cc hdec hδ hC
    (fun t => t) HardcoreBit.pushesUniform_id (fun _ => π)

/-- **Claim 159.a, probabilistic part: a garbling is good with high probability** [PS10, §6.2.3,
"all but one row will evaluate to `⊥`"]: for a fan-in-two circuit and a multi-key encryption
that is correct and has the wrong-key property with error `δ`, a uniformly random garbling fails
to be good with probability at most `12 · |gates| · δ`. The formal conclusion bounds failure
of first-success correctness; it does not state the source's stronger unique-opening claim.

**Proof sketch.** Reassociate a uniform garbling seed as a permutation family and an
independent key/coin pair. For each fixed permutation family apply the stronger B2 theorem
`uprob_not_good_le_of_perm`. Average its constant bound with finite Fubini and the constant
expectation identity. B2 itself bounds the at most twelve cross-opening events per gate. -/
theorem uprob_not_good_le [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
    (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) :
    uprob (fun s : GarbleSeed Cc K ρ => ¬ Good M Cc s) ≤ 12 * Cc.gates.length * δ := by
  let D := (Fin Cc.size → Bool → K) ×
    ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ)
  let P := (i : Fin Cc.gates.length) →
    Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)
  let e : GarbleSeed Cc K ρ ≃ P × D :=
    (Equiv.prodAssoc (Fin Cc.size → Bool → K)
      ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) P).symm.trans
        (Equiv.prodComm D P)
  rw [← uprob_comp_equiv e.symm, uprob_prod]
  exact (OneWay.uexp_mono (fun π : P =>
    uprob_not_good_le_of_perm M Cc hdec hδ hC π)).trans (OneWay.uexp_const _).le

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/Garbling/CoinBlocks.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Garbling.Probability
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform key and row-coin blocks

## Main definitions

This module adds no definitions.

## Main results

* `GarblingProbability.pushesUniform_key_row_blocks`: the key and row-coin blocks used
  by Yao have a uniform joint law, including zero-length blocks.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, §6.2.3, Claim 159.a.
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingProbability

open TCSlib.Cryptography

/-- For `len ≤ 2`, the binary fold `a₀ + 2(a₁ + 2(⋯))` is below four and injective:
`(∀ a, (List.ofFn a).foldr (fun b k => b.toNat + 2*k) 0 < 4) ∧
  Function.Injective (fun a => (List.ofFn a).foldr (fun b k => b.toNat + 2*k) 0)`. -/
theorem assignmentFold_small (len : ℕ) (hlen : len ≤ 2) :
    (∀ a : Fin len → Bool, (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 4) ∧
      Function.Injective (fun a : Fin len → Bool =>
        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) := by
  interval_cases len <;> decide

/-- Selecting distinct blocks of `n` bits preserves the uniform law:
`r ↦ (fun i t => (List.ofFn r).getD (c i * n + t) false)` pushes uniform to uniform,
for an injection `c : I → Fin B` and any unused tail of length `tail`.

**Proof sketch.** The product equivalence embeds a block and its bit into `Fin (B*n)`.
Compose this injection with the inclusion into the raw coin space and restrict its uniform
bit table. Currying the restricted table gives the claimed family of independent blocks. -/
theorem pushesUniform_bits_of_blocks {I : Type} [Fintype I] [DecidableEq I]
    {B n tail : ℕ} (c : I → Fin B) (hinj : Function.Injective c) :
    HardcoreBit.PushesUniform (fun r : Fin (B * n + tail) → Bool =>
      fun i (t : Fin n) => (List.ofFn r).getD ((c i : ℕ) * n + t) false) := by
  let select : I × Fin n → Fin (B * n + tail) :=
    fun p => Fin.castAdd tail (finProdFinEquiv (c p.1, p.2))
  have hselect : Function.Injective select := by
    intro x y hxy
    have hp : (c x.1, x.2) = (c y.1, y.2) := by
      apply (finProdFinEquiv (m := B) (n := n)).injective
      apply Fin.castAdd_injective (B * n) tail
      exact hxy
    apply Prod.ext
    · exact hinj (congrArg (fun p : Fin B × Fin n => p.1) hp)
    · exact congrArg (fun p : Fin B × Fin n => p.2) hp
  have h := (HardcoreBit.pushesUniform_restrict (O := Bool) hselect).comp
    (HardcoreBit.pushesUniform_equiv (Equiv.curry I (Fin n) Bool))
  convert h using 1
  funext r i t
  have heq : (select (i, t) : ℕ) = (c i : ℕ) * n + t := by
    simp only [select, Fin.coe_castAdd, finProdFinEquiv_apply_val]
    ring
  rw [← heq, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact (select (i, t)).isLt),
    List.getElem_ofFn]
  rfl

/-- Key blocks `b*S+v` and row-half blocks `2*S+2*(4*i+idx i a)+b` are distinct and below
`10*S`, if `V,G ≤ S` and each `idx i` is an injection into `{0,1,2,3}`.

**Proof sketch.** Key indices are below `2*S`; row indices start there. Within keys, the
bit separates the two intervals. Within rows, bounds on the half-bit and assignment index
recover first the gate, then the assignment, then the half-bit. -/
theorem key_row_blocks_injective {S V G : ℕ} (hV : V ≤ S) (hG : G ≤ S)
    {A : Fin G → Type} (idx : (i : Fin G) → A i → ℕ)
    (hidx : ∀ i a, idx i a < 4) (hinj : ∀ i, Function.Injective (idx i)) :
    let c : (Fin V × Bool) ⊕ ((Σ i, A i) × Bool) → ℕ :=
      Sum.elim (fun p => p.2.toNat * S + p.1)
        (fun p => 2 * S + (4 * p.1.1 + idx p.1.1 p.1.2) * 2 + p.2.toNat)
    (∀ p, c p < 10 * S) ∧ Function.Injective c := by
  dsimp only
  have hb (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  have hk (p : Fin V × Bool) : p.2.toNat * S + p.1 < 2 * S := by
    have hm := Nat.mul_le_mul_right S (hb p.2)
    have hv := p.1.isLt
    simp only [Nat.one_mul] at hm
    omega
  constructor
  · intro p
    cases p with
    | inl p =>
      simp only [Sum.elim_inl]
      have hh := hk p
      omega
    | inr p =>
      simp only [Sum.elim_inr]
      have hi := p.1.1.isLt
      have ha := hidx p.1.1 p.1.2
      have hh := hb p.2
      omega
  · intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        obtain ⟨x, b⟩ := x
        obtain ⟨y, c⟩ := y
        have hx := x.isLt
        have hy := y.isLt
        change b.toNat * S + x.val = c.toNat * S + y.val at hxy
        have hbc : b = c := by
          cases b <;> cases c <;> simp_all only [Bool.toNat_false, Bool.toNat_true,
            Nat.zero_mul, Nat.one_mul] <;> omega
        subst c
        have hval : x.val = y.val := Nat.add_left_cancel hxy
        exact congrArg Sum.inl (Prod.ext (Fin.ext hval) rfl)
      | inr y =>
        have hx := hk x
        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        omega
    | inr x =>
      cases y with
      | inl y =>
        have hy := hk y
        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        omega
      | inr y =>
        obtain ⟨⟨i, a⟩, b⟩ := x
        obtain ⟨⟨j, a'⟩, c⟩ := y
        have ha := hidx i a
        have ha' := hidx j a'
        have hbit := hb b
        have hbit' := hb c
        simp only [Sum.elim_inr] at hxy
        have hij : i = j := Fin.ext (by omega)
        subst j
        have haa : a = a' := hinj i (by omega)
        subst a'
        have hbc : b = c := by cases b <;> cases c <;> simp_all
        subst c
        rfl

/-- The joint key/row-coin law of Yao's block layout is uniform. For `V,G ≤ S`, row index
injections `idx i : A i → {0,1,2,3}`, and uniform `10*S*n+2*S` bits, the keys read at
`(b*S+v)*n` and the two row halves read at `2*S*n+(4*i+idx i a)*(2*n)` and that offset
plus `n` form independent uniform tables. [PS10, §6.2.3, Claim 159.a]

**Proof sketch.** Embed key blocks and row-half blocks into `Fin (10*S)` using their
intervals, and restrict the raw uniform bit table to those blocks. Split the sum of the
key and row indices. Curry the key indices, curry the row-half indices, turn each pair
of Boolean-indexed row halves into a product, and curry the dependent row index. All
these maps are equivalences, so the joint uniform law is preserved. -/
theorem pushesUniform_key_row_blocks {S V G n : ℕ} (hV : V ≤ S) (hG : G ≤ S)
    {A : Fin G → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (idx : (i : Fin G) → A i → ℕ) (hidx : ∀ i a, idx i a < 4)
    (hinj : ∀ i, Function.Injective (idx i)) :
    HardcoreBit.PushesUniform (fun r : Fin (10 * S * n + 2 * S) → Bool =>
      ((fun (v : Fin V) (b : Bool) (t : Fin n) =>
          (List.ofFn r).getD ((b.toNat * S + v) * n + t) false),
        fun i a =>
          ((fun t : Fin n =>
            (List.ofFn r).getD (2 * S * n + (4 * i + idx i a) * (2 * n) + t) false),
           (fun t : Fin n =>
            (List.ofFn r).getD (2 * S * n + (4 * i + idx i a) * (2 * n) + n + t)
              false)))) := by
  classical
  let K := Fin n → Bool
  let I := (Fin V × Bool) ⊕ ((Σ i, A i) × Bool)
  let c : I → ℕ := Sum.elim (fun p => p.2.toNat * S + p.1)
    (fun p => 2 * S + (4 * p.1.1 + idx p.1.1 p.1.2) * 2 + p.2.toNat)
  have hc := key_row_blocks_injective hV hG idx hidx hinj
  let c' : I → Fin (10 * S) := fun p => ⟨c p, hc.1 p⟩
  have hc' : Function.Injective c' := fun x y h => hc.2 (congrArg Fin.val h)
  let eK : (Fin V × Bool → K) ≃ (Fin V → Bool → K) := Equiv.curry _ _ _
  let eR : ((Σ i, A i) × Bool → K) ≃ ((i : Fin G) → A i → K × K) :=
    (Equiv.curry _ _ _).trans ((Equiv.piCongrRight fun _ =>
      Equiv.boolArrowEquivProd K).trans (Equiv.piCurry fun i (_ : A i) => K × K))
  have h := (pushesUniform_bits_of_blocks (n := n) (tail := 2 * S) c' hc').comp
    ((HardcoreBit.pushesUniform_equiv
      (Equiv.sumArrowEquivProdArrow (Fin V × Bool) ((Σ i, A i) × Bool) K)).comp
      (HardcoreBit.pushesUniform_equiv (eK.prodCongr eR)))
  convert h using 1
  funext r
  apply Prod.ext
  · rfl
  · funext i a
    apply Prod.ext <;> funext t
    · change (List.ofFn _).getD
        (2 * S * n + (4 * i + idx i a) * (2 * n) + t) false =
          (List.ofFn _).getD ((2 * S + (4 * i + idx i a) * 2 + 0) * n + t) false
      congr 1; ring
    · change (List.ofFn _).getD
        (2 * S * n + (4 * i + idx i a) * (2 * n) + n + t) false =
          (List.ofFn _).getD ((2 * S + (4 * i + idx i a) * 2 + 1) * n + t) false
      congr 1; ring

end TCSlib.Cryptography.SecureComputation.GarblingProbability

## ===== TCSlib/Cryptography/SecureComputation/Garbling/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Independent marginals and first successful openings

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.GarblingProbability.findSome_eq_some_of_dichotomy`: a successful
  entry and no other successful value determine the first successful opening.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.3, Claim 159.a.
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingProbability

open TCSlib.Cryptography

/-- If a list contains an entry mapped to `some b`, and every entry maps to either
`none` or `some b`, its first successful image is `some b`:
`(∃ a ∈ l, f a = some b) → (∀ a ∈ l, f a = none ∨ f a = some b) →
  l.findSome? f = some b`. -/
theorem findSome_eq_some_of_dichotomy {α β : Type} (l : List α) (f : α → Option β) (b : β)
    (hex : ∃ a ∈ l, f a = some b)
    (hall : ∀ a ∈ l, f a = none ∨ f a = some b) : l.findSome? f = some b := by
  cases hfind : l.findSome? f with
  | none =>
    obtain ⟨a, ha, hfa⟩ := hex
    have hn := List.findSome?_eq_none_iff.mp hfind a ha
    cases hn.symm.trans hfa
  | some c =>
    obtain ⟨a, ha, hfa⟩ := List.exists_of_findSome?_eq_some hfind
    rcases hall a ha with hn | hb
    · cases hn.symm.trans hfa
    · exact hfa.symm.trans hb

/-- Distinct argument vertices and a different output vertex give an independent output
key and argument-key table:
`ks ↦ (ks out b, fun j => ks (arg j))` pushes uniform to uniform, if `arg` is injective
and `arg j ≠ out` for every `j`.

**Proof sketch.** Restrict the uniform vertex table to the injection from `J ⊕ Unit`
which selects argument vertices on the left and the output vertex on the right. Split
that restricted table along the sum, evaluate the unit coordinate and output bit, and
swap the two resulting independent factors. -/
theorem pushesUniform_output_argKeys {I J K : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [Nonempty K]
    (arg : J → I) (hinj : Function.Injective arg) (out : I)
    (hne : ∀ j, arg j ≠ out) (b : Bool) :
    HardcoreBit.PushesUniform (fun ks : I → Bool → K =>
      (ks out b, fun j => ks (arg j))) := by
  let select : J ⊕ Unit → I := Sum.elim arg (fun _ => out)
  have hselect : Function.Injective select := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (hinj hxy)
      | inr y => exact (hne x hxy).elim
    | inr x =>
      cases y with
      | inl y => exact (hne y hxy.symm).elim
      | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  -- Restrict, then split the argument and output coordinates.
  have hrestrict := HardcoreBit.pushesUniform_restrict (O := Bool → K) hselect
  have hsplit := hrestrict.comp (HardcoreBit.pushesUniform_equiv
    (Equiv.sumArrowEquivProdArrow J Unit (Bool → K)))
  have hout := (HardcoreBit.pushesUniform_eval (γ := Bool → K) ()).comp
    (HardcoreBit.pushesUniform_eval (γ := K) b)
  -- Evaluate only the output coordinate; retain the full argument-key table.
  exact (hsplit.comp (HardcoreBit.pushesUniform_id.prodMap hout)).comp
    (HardcoreBit.pushesUniform_equiv (Equiv.prodComm (J → Bool → K) K))

/-- Reading one row of a uniform dependent family of coin tables is uniform:
`r ↦ r i a : ((i : I) → A i → ρ) → ρ` pushes uniform to uniform. -/
theorem pushesUniform_rowCoin {I : Type} [Fintype I] [DecidableEq I] {A : I → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] {ρ : Type} [Fintype ρ] (i : I) (a : A i) :
    HardcoreBit.PushesUniform (fun r : (i : I) → A i → ρ => r i a) := by
  classical
  exact (HardcoreBit.pushesUniform_equiv (Equiv.piCurry (fun i (_ : A i) => ρ)).symm).comp
    (HardcoreBit.pushesUniform_eval (γ := ρ) ⟨i, a⟩)

/-- Independent uniform keys and a uniform row-coin map give their joint marginal:
`(ks,r) ↦ (ks out b,(fun j => ks (arg j),coin r))` pushes uniform to uniform,
if argument vertices are distinct and exclude `out`, and `coin` pushes uniform to uniform. -/
theorem pushesUniform_output_argKeys_row {I J K R ρ : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [Nonempty K] [Fintype R] [Fintype ρ]
    (arg : J → I) (hinj : Function.Injective arg) (out : I)
    (hne : ∀ j, arg j ≠ out) (b : Bool) (coin : R → ρ)
    (hcoin : HardcoreBit.PushesUniform coin) :
    HardcoreBit.PushesUniform (fun t : (I → Bool → K) × R =>
      (t.1 out b, (fun j => t.1 (arg j), coin t.2))) := by
  exact ((pushesUniform_output_argKeys arg hinj out hne b).prodMap hcoin).comp
    (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K (J → Bool → K) ρ))

end TCSlib.Cryptography.SecureComputation.GarblingProbability

## ===== TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.GarblingSecurity.CoinMarginals
import TCSlib.Cryptography.SecureComputation.GarblingSecurity.NestedBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Garbled circuits from PRFs: Claim 159.a

[PS10, §6.2.2–6.2.3]: with the nested special encryption of `GarblingSpecial.lean`, built from two
pseudorandom function families (`PRFOut`), a random garbling is good with high probability. This
combines Claim 157.a's wrong-key property (here for the nesting) with the union bound of
`Garbling.lean`.

## Main definitions

The imported `SecureComputation.nestedSpecial` construction uses the correctness and
wrong-key contracts `MultiEnc.DecCorrect` and `MultiEnc.WrongKeyBot` from `Garbling.lean`.

## Main results

* `SecureComputation.nestedSpecial_wrongKeyBot` (Claim 157.a (ii) for the nesting): the
  wrong-key error is negligible.
* `SecureComputation.garbling_good_whp` (Claim 159.a, proved from the previous results): a random
  garbling of a fan-in-two circuit is good except with probability `12 · |gates| · δ(n)`, `δ`
  negligible.

## Contents

* `GarblingSecurity.CoinMarginals`: independent key/nonce marginals and option probabilities.
* `GarblingSecurity.NestedBounds`: the three concrete nesting cases.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2–6.2.3 (book pp. 156–160).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Claim 157.a (ii) for the nesting: the wrong-key property with negligible error**
[PS10, §6.2.2]: for length-doubling `G₁` and `G₂` with `n + (4n + 2)`-bit outputs, both PRFs,
nested special encryption has `WrongKeyBot` with a negligible error `δ(n)`.

**Proof sketch.** Let `a ≠ a'` be the key choices on at most two positions.
- **One position:** the ciphertext under `k_a` is decrypted under the independent `k_{a'}`, which
  is `spDecStr_wrongKey` at `ℓ = n`: error `ε₁(n)`.
- **Two positions, first differs:** the outer layer is decrypted under an independent key, which
  is `spDecStr_wrongKey` at `ℓ = 4n + 2`: error `ε₂(n)`.
- **Two positions, first agrees, second differs:** the outer layer opens to the inner ciphertext,
  which is decrypted under an independent key: error `ε₁(n)`.

So `δ = ε₁ + ε₂`, negligible (`Negligible.add`); `ε₁` and `ε₂` are averaged over the plaintext
and the other layer's key and coins. In the proof, `spDecStr_wrongKey` at `ℓ = n` (with `G₁`)
and at `ℓ = innerLen` (with `G₂`) gives the two string success bounds
(`GarblingCoins.uprob_isSome_lt_of_none`), and
`GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds` carries out the case analysis,
including the zero-position case, which has no distinct choices. -/
theorem nestedSpecial_wrongKeyBot (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, (nestedSpecial E₁ E₂ n).WrongKeyBot (δ n) := by
  obtain ⟨ε₁, hε₁, hb₁⟩ := spDecStr_wrongKey .var G₁ E₁ hGE₁ hG₁
  simp only [PolyExpr.eval_var] at hb₁
  obtain ⟨ε₂, hε₂, hb₂⟩ := spDecStr_wrongKey innerLen G₂ E₂ hGE₂ hG₂
  refine ⟨fun n => ε₁ n + ε₂ n, hε₁.add hε₂, fun n => ?_⟩
  have hs₁ : ∀ m : Fin n → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₁ n n (List.ofFn t.2.1)
          (spEncStr E₁ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₁ n :=
    fun m => (GarblingCoins.uprob_isSome_lt_of_none _ (hb₁ n m)).le
  have hs₂ : ∀ m : Fin (innerLen.eval n) → Bool,
      uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
          (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true) ≤ ε₂ n :=
    fun m => (GarblingCoins.uprob_isSome_lt_of_none _ (hb₂ n m)).le
  have hε₁n : 0 ≤ ε₁ n := (uprob_nonneg _).trans (hs₁ (fun _ => false))
  have hε₂n : 0 ≤ ε₂ n := (uprob_nonneg _).trans (hs₂ (fun _ => false))
  exact GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds G₁ G₂ E₁ E₂
    hGE₁ hGE₂ n hε₁n hε₂n hs₁ hs₂

include hGE₁ hGE₂ in
/-- **Claim 159.a: a random garbling is good with high probability** [PS10, §6.2.3, "all but one
row will evaluate to `⊥`"]: with the nested special encryption from two PRFs, there is a
negligible `δ` such that, for every parameter `n` and every fan-in-two circuit, a uniformly
random garbling is good, and so evaluates correctly (`garbledOutput_eq`), except with
probability at most `12 · |gates| · δ(n)`. Goodness here concerns the first successful opening
for every assignment; the stronger source assertion of unique opening is not this conclusion. -/
theorem garbling_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ (n m : ℕ) (Cc : DAGCircuit m), Cc.IsFaninTwo →
      uprob (fun s : GarbleSeed Cc (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) =>
        ¬ Good (nestedSpecial E₁ E₂ n) Cc s) ≤ 12 * Cc.gates.length * δ n := by
  obtain ⟨δ, hδ, hbot⟩ := nestedSpecial_wrongKeyBot G₁ G₂ E₁ E₂ hGE₁ hGE₂ hG₁ hG₂
  exact ⟨δ, hδ, fun n m Cc hC => uprob_not_good_le (nestedSpecial E₁ E₂ n) Cc
    (nestedSpecial_decCorrect G₁ G₂ E₁ E₂ hGE₁ hGE₂ n) (hbot n) hC⟩

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Marginals of the keys and coins of nested encryption

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.GarblingCoins.pushesUniform_position_keys_coin`: two distinct key
  choices at one position and either nonce are an independent uniform triple.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Claim 157.a (ii).
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingCoins

open TCSlib.Cryptography

/-- Two distinct choices at one position and either coin form a uniform triple:
`(ks,(r₀,r₁)) ↦ (ks j b,ks j b',if c then r₁ else r₀)` pushes uniform to uniform,
for `b ≠ b'`. -/
theorem pushesUniform_position_keys_coin {K : Type} [Fintype K] [Nonempty K]
    {len : ℕ} (j : Fin len) {b b' : Bool} (hb : b ≠ b') (c : Bool) :
    HardcoreBit.PushesUniform (fun t : (Fin len → Bool → K) × (K × K) =>
      (t.1 j b, t.1 j b', if c then t.2.2 else t.2.1)) := by
  have hk := (HardcoreBit.pushesUniform_eval j).comp
    (HardcoreBit.pushesUniform_eval_pair (γ := K) hb)
  cases c
  · exact (hk.prodMap HardcoreBit.pushesUniform_fst).comp
      (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))
  · exact (hk.prodMap HardcoreBit.pushesUniform_snd).comp
      (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))

/-- A failure probability greater than `1-ε` bounds success strictly by `ε`:
`1-ε < Pr[X = none] → Pr[X.isSome = true] < ε`. -/
theorem uprob_isSome_lt_of_none {Ω α : Type} [Fintype Ω] [Nonempty Ω]
    (X : Ω → Option α) {ε : ℝ} (h : 1 - ε < uprob (fun t => X t = none)) :
    uprob (fun t => (X t).isSome = true) < ε := by
  rw [OneWay.uprob_congr (fun t : Ω => Option.isSome_iff_ne_none), uprob_not]
  linarith

end TCSlib.Cryptography.SecureComputation.GarblingCoins

## ===== TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.GarblingSecurity.CoinMarginals

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete wrong-key bounds for nested special encryption

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.GarblingCoins.length_nestedInner`: the inner ciphertext has `4n+2` bits.
* `SecureComputation.GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds`: inner and outer
  string success bounds `ε₁, ε₂` give `(nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂)`.
* `SecureComputation.uprob_not_good_distinct_le_of_uniform_data`: with uniform keys and row
  coins, goodness with distinct output keys fails with probability at most
  `12 · |gates| · δ + m / |K|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Claim 157.a (ii).
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingCoins

open Complexity Turing TCSlib.Cryptography

/-- A special ciphertext with an `n`-bit nonce, an `n`-bit message, and a `2n`-bit pad has
`innerLen(n) = 4n+2` bits:
`|spEncStr E ⟦k⟧ ⟦m⟧ ⟦r⟧| = innerLen.eval n`. -/
theorem length_nestedInner
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {E : List Bool → List Bool}
    (hGE : ∀ n (k r : Fin n → Bool), E (pairEncode (List.ofFn k) (List.ofFn r)) =
      List.ofFn (G n k r)) (n : ℕ) (k m r : Fin n → Bool) :
    (spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)).length = innerLen.eval n := by
  rw [length_spEncStr E (by rw [hGE]; simp), List.length_ofFn, List.length_ofFn,
    innerLen_eq, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var, PolyExpr.eval_const]
  omega

/-- Inner and outer string success bounds `ε₁, ε₂` give
`(nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁+ε₂)`, provided both errors are nonnegative and
the evaluators have the specified `2n` and `n+innerLen(n)` output lengths.
[PS10, §6.2.2, Claim 157.a (ii)]

**Proof sketch.** There are at most two key positions. With one position use the inner
string bound and its uniform key/nonce marginal. With two positions, if the first key
differs, condition on the second position's keys and inner nonce, and apply the outer
bound to the resulting fixed inner ciphertext. If the first key agrees, correctness
opens the outer layer and the inner key/nonce marginal gives the inner bound. Add the
nonnegative unused error in each case. The zero-position case has no distinct choices. -/
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
    (nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂) := by
  rw [MultiEnc.wrongKeyBot_iff]
  intro len hlen a a' hne o
  have hcases : len = 0 ∨ len = 1 ∨ len = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (hne (Subsingleton.elim a a')).elim
  · have hab : a 0 ≠ a' 0 := fun h => hne (funext (Fin.forall_fin_one.mpr h))
    have hu := (pushesUniform_position_keys_coin (K := Fin n → Bool) (0 : Fin 1)
      hab false).uprob_eq (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        (spDecStr E₁ n n (List.ofFn t.2.1)
          (spEncStr E₁ (List.ofFn t.1) (List.ofFn o) (List.ofFn t.2.2))).isSome = true)
    refine (uprob_mono (fun t ht => ?_)).trans
      ((hu.trans_le (h₁ o)).trans (le_add_of_nonneg_right hε₂))
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
      nestedSpecial_enc, nestedSpecial_dec] at ht
    exact Option.isSome_of_isSome_bind ht
  · by_cases hfirst : a 0 = a' 0
    · have hsecond : a 1 ≠ a' 1 := fun h =>
        hne (funext (Fin.forall_fin_two.mpr ⟨hfirst, h⟩))
      have hu := (pushesUniform_position_keys_coin (K := Fin n → Bool) (1 : Fin 2)
        hsecond true).uprob_eq (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
          (spDecStr E₁ n n (List.ofFn t.2.1)
            (spEncStr E₁ (List.ofFn t.1) (List.ofFn o) (List.ofFn t.2.2))).isSome = true)
      refine (uprob_mono (fun t ht => ?_)).trans
        ((hu.trans_le (h₁ o)).trans (le_add_of_nonneg_right hε₂))
      simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
      nestedSpecial_enc, nestedSpecial_dec] at ht
      have hc := length_nestedInner hGE₁ n (t.1 1 (a 1)) o t.2.2
      have hp : (E₂ (pairEncode (List.ofFn (t.1 0 (a 0))) (List.ofFn t.2.1))).length =
          n + innerLen.eval n := by
        rw [hGE₂, List.length_ofFn]
        rfl
      rw [← hfirst, spDecStr_spEncStr E₂ List.length_ofFn hc List.length_ofFn hp,
        Option.bind_some] at ht
      exact Option.isSome_of_isSome_bind ht
    · let K := Fin n → Bool
      let e : ((Fin 2 → Bool → K) × (K × K)) ≃
          ((Bool → K) × K) × ((Bool → K) × K) :=
        ((piFinTwoEquiv fun _ : Fin 2 => Bool → K).prodCongr (Equiv.refl (K × K))).trans
          ((Equiv.prodProdProdComm (Bool → K) (Bool → K) K K).trans
            (Equiv.prodComm ((Bool → K) × K) ((Bool → K) × K)))
      rw [← uprob_comp_equiv e.symm, uprob_prod]
      refine (OneWay.uexp_mono (g := fun _ => ε₂) (fun s => ?_)).trans ?_
      · let c := spEncStr E₁ (List.ofFn (s.1 (a 1))) (List.ofFn o) (List.ofFn s.2)
        have hc : c.length = innerLen.eval n := length_nestedInner hGE₁ n _ o _
        let m := padFin (innerLen.eval n) c
        have hm : List.ofFn m = c := ofFn_padFin_of_length hc
        have hlaw : HardcoreBit.PushesUniform
            (fun t : (Bool → K) × K => (t.1 (a 0), t.1 (a' 0), t.2)) :=
          ((HardcoreBit.pushesUniform_eval_pair (γ := K) hfirst).prodMap
            HardcoreBit.pushesUniform_id).comp
              (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))
        have hu := hlaw.uprob_eq (fun t : K × K × K =>
          (spDecStr E₂ n (innerLen.eval n) (List.ofFn t.2.1)
            (spEncStr E₂ (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2))).isSome = true)
        have hb := hu.trans_le (h₂ m)
        rw [hm] at hb
        refine (uprob_mono (fun t ht => ?_)).trans hb
        simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
      nestedSpecial_enc, nestedSpecial_dec] at ht
        exact Option.isSome_of_isSome_bind ht
      · simpa only [OneWay.uexp_const] using
          (le_add_of_nonneg_left hε₁ : ε₂ ≤ ε₁ + ε₂)

end TCSlib.Cryptography.SecureComputation.GarblingCoins

namespace TCSlib.Cryptography.SecureComputation

open BoolCircuit

variable {K C ρ : Type} [Inhabited K] {n : ℕ} (M : MultiEnc K C ρ) (Cc : DAGCircuit n)

/-- Uniform independent keys and row coins give goodness and distinct output keys:
`Pr_w[¬ (Good M Cc (s w) ∧ ∀ j, keyAt Cc (s w) (out j) false ≠
  keyAt Cc (s w) (out j) true)] ≤ 12*|Cc.gates|*δ + m/|K|`, if `out j < Cc.size`
and `w ↦ ((s w).1,(s w).2.1)` pushes uniform to uniform.
Outputs may coincide. [PS10, §6.2.3, Claim 159.a and Protocol 162.6]

**Proof sketch.** Use the B2 uniform-data bound for goodness. At each output, the two
keys are independent uniform elements of `K`, so their collision probability is `1/|K|`.
The finite union bound over output positions does not require distinct output vertices.
Add this collision bound to the goodness failure bound. -/
theorem uprob_not_good_distinct_le_of_uniform_data [Fintype K] [Fintype ρ] [Nonempty ρ]
    (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
    {Ω : Type} [Fintype Ω] (s : Ω → GarbleSeed Cc K ρ)
    (hs : HardcoreBit.PushesUniform (fun w => ((s w).1, (s w).2.1)))
    {m : ℕ} (out : Fin m → ℕ) (hout : ∀ j, out j < Cc.size) :
    uprob (fun w => ¬ (Good M Cc (s w) ∧ ∀ j,
      keyAt Cc (s w) (out j) false ≠ keyAt Cc (s w) (out j) true)) ≤
      12 * Cc.gates.length * δ + m * (1 / Fintype.card K) := by
  classical
  let collision : Fin m → Ω → Prop := fun j w =>
    keyAt Cc (s w) (out j) false = keyAt Cc (s w) (out j) true
  have hpoint (j : Fin m) : uprob (collision j) = 1 / Fintype.card K := by
    let v : Fin Cc.size := ⟨out j, hout j⟩
    have hkeys : HardcoreBit.PushesUniform (fun w => (s w).1) :=
      hs.comp HardcoreBit.pushesUniform_fst
    have hpair : HardcoreBit.PushesUniform (fun w => ((s w).1 v false, (s w).1 v true)) :=
      (hkeys.comp (HardcoreBit.pushesUniform_eval (γ := Bool → K) v)).comp
        (HardcoreBit.pushesUniform_eval_pair (γ := K) Bool.false_ne_true)
    have hu := hpair.uprob_eq (fun z : K × K => z.1 = z.2)
    calc
      _ = uprob (fun w => (s w).1 v false = (s w).1 v true) := by
        apply OneWay.uprob_congr
        intro w
        simp only [collision, keyAt_eq, dif_pos (hout j)]
        rfl
      _ = uprob (fun z : K × K => z.1 = z.2) := hu
      _ = 1 / Fintype.card K := MultiMsg.uprob_eq_pair
  have hcoll : uprob (fun w => ∃ j ∈ Finset.univ, collision j w) ≤
      m * (1 / Fintype.card K) := by
    refine (uprob_exists_le Finset.univ collision).trans ?_
    simp only [hpoint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_rfl
  have hbad : ∀ w, ¬ (Good M Cc (s w) ∧ ∀ j,
      keyAt Cc (s w) (out j) false ≠ keyAt Cc (s w) (out j) true) →
        ¬ Good M Cc (s w) ∨ ∃ j ∈ Finset.univ, collision j w := by
    intro w hw
    by_cases hg : Good M Cc (s w)
    · right
      have hj : ∃ j, collision j w := by simpa only [not_and, hg, true_implies,
        not_forall, not_not, collision] using hw
      obtain ⟨j, hj⟩ := hj
      exact ⟨j, Finset.mem_univ _, hj⟩
    · exact Or.inl hg
  calc
    _ ≤ uprob (fun w => ¬ Good M Cc (s w) ∨ ∃ j ∈ Finset.univ, collision j w) :=
      uprob_mono hbad
    _ ≤ uprob (fun w => ¬ Good M Cc (s w)) +
        uprob (fun w => ∃ j ∈ Finset.univ, collision j w) := uprob_or_le _ _
    _ ≤ 12 * Cc.gates.length * δ + m * (1 / Fintype.card K) :=
      add_le_add (uprob_not_good_le_of_uniform_data M Cc hdec hδ hC
        (fun w => ((s w).1, (s w).2.1)) hs (fun w => (s w).2.2)) hcoll

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/Yao.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.GarblingSecurity
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Yao's protocol in the OT-hybrid model (statement phase)

[PS10, Protocol 162.6]: Alice garbles a circuit for `f` and sends it with the keys of her input
bits; for each of Bob's input bits the parties run an oblivious transfer in which Bob obtains the
key of his bit; Bob evaluates the garbled circuit, sends the result to Alice, and both output it.
[PS10, Theorem 163.7]: the protocol is honest-but-curious secure. By the ruling of 2026-11-05,
both are stated here in the OT-hybrid model of [Gol04, §7.3] (`HybridProtocol otFunctionality`,
`Hybrid.lean`); the real protocol follows by composition with Protocol 160.4, which is not in
this file.

**The circuits** (`YaoCircuit`). The source garbles "a canonical circuit representation of `f`".
Here that is a uniform family of fan-in-two circuits `C_n` (`DAGCircuit`) of polynomial size, on
`inA(n) + inB(n)` inputs, with a list of `outLen(n)` output vertices. Alice's input bits are
vertices `0, …, inA − 1`, Bob's are vertices `inA, …, inA + inB − 1`. Uniformity (a
polynomial-time map from `1^n` to the description `encodeCircuit`) is what lets Alice, Bob and
the simulators build the circuit in polynomial time. The functionality gives both parties the
values of `C_n(x, y)` at the output vertices (`yaoFunctionality`).

**The garbling** is Construction 158.a of `Garbling.lean` with nested special encryption
(`GarblingSpecial.lean`), keys of `n` bits, and the randomness read from fixed blocks of Alice's
coins (`yaoSeed`): the keys, `2n` coins per row, and a shift `λ_i` per gate.

**The protocol** (`yaoHybrid`). `inB(n) · n` ideal bit-OTs, then two messages:
- call `(i, t)` gives Bob bit `t` of the key of his wire `inA + i` for his bit `y_i`;
- Alice sends the garbled tables, the keys of her input bits, and the key pair `(k⁰, k¹)` of every
  output vertex;
- Bob evaluates the garbled circuit with `runWith` and `evalGate`, decodes each output key by
  comparison with its pair, and sends the bits; under D8 the last mover's message is its output,
  and Alice outputs the message she received.

**Deviations from [PS10].**
- **The OT-hybrid model** (ruling of 2026-11-05), with the ideal calls first (`Hybrid.lean`). The
  source's proof simulates the OT transcripts with Proposition 161.5's simulators; here a party's
  view holds its OT outputs instead, and the composition theorem supplies the rest.
- **Bit OTs.** `otFunctionality` transfers one bit, so the source's OT of a key pair `(k_{i,0},
  k_{i,1})` is `n` bit OTs with the same choice bit `y_i` (the source: "it is straightforward to
  generalize this construction to handle `n`-bit values").
- **The row order: a random XOR shift.** Row `a` of gate `i` sits at the position of `a ⊕ λ_i`
  in a fixed enumeration of the assignments, for a uniform `λ_i` (`xorShift`). The source shuffles
  each table uniformly, but the `24` orders of four rows cannot be sampled exactly from a fixed
  number of coin bits. A uniform shift makes the position of the row that opens uniform and
  independent of the inputs, which is what the simulation uses (the point-and-permute idea of
  [BMR90]).
- **Output decoding.** The source does not say how Bob reads the output from the output keys.
  Here Alice sends each output vertex's key pair, and Bob maps `k⁰ ↦ 0`, `k¹ ↦ 1` (`decodeOut`).
- **Output vertices are sinks** (`YaoCircuit.outs_sink`). The decoding pairs reveal both keys of
  every output vertex, so if a gate read an output vertex `o`, Bob could open its table on both
  values of `o`. For `f(x) = (x₀, x₀ ∧ x₁)` with output vertices `x₀` and `g = x₀ ∧ x₁`, Bob
  holds both keys of `x₀`, opens the row `(1, x₁)` of `g`, and decodes `x₁` even when `x₀ = 0`.
  One identity gate per output brings any circuit to this form.
- **Lengths.** Inputs and outputs have polynomial lengths `inA(n)`, `inB(n)`, `outLen(n)` (the
  source: `x, y ∈ {0,1}^n`); the security parameter `n` is the key length.
- **Correctness** needs, besides a good garbling, distinct keys on each output vertex
  (`yaoHybrid_correct`); both hold except with negligible probability (`yaoSeed_good_whp`).
- **A joint PRF.** The two encryption layers use two PRFs `G₁`, `G₂` (`GarblingSpecial.lean`), and
  a wire's key can key both. The security theorem assumes the pair is pseudorandom under one key
  (`yaoHybrid_simulators`); the source uses one scheme for both layers.

## Main definitions

* `SecureComputation.encodeCircuit`: the description of a circuit with an output list.
* `SecureComputation.YaoCircuit`, `YaoCircuit.output`, `yaoFunctionality`: the circuit family and
  the functionality it computes.
* `SecureComputation.readBits`, `assignIdx`, `xorShift`, `yaoCoins`, `yaoSeed`: the garbling's
  randomness from Alice's coins.
* `SecureComputation.decodeMsgs`: the inverse of `Strategy.encodeMsgs`.
* `SecureComputation.yaoTables`, `yaoKeysA`, `yaoPairs`, `yaoMsg`: Alice's message.
* `SecureComputation.yaoBobTables`, `yaoBobInit`, `yaoBobValues`, `decodeOut`, `yaoBobOut`: Bob's
  evaluation.
* `SecureComputation.yaoAlice`, `yaoBob`, `yaoMain`, `yaoCall`, `yaoHybrid`: Protocol 162.6 in the
  OT-hybrid model.

## Main results

* `SecureComputation.encodeCircuit_injective`, `decodeMsgs_encodeMsgs` (proved): the encodings.
* `SecureComputation.yaoBobOut_yaoMsg` (proved): Bob's evaluation of a good garbling with distinct
  output keys gives `f(x, y)`.
* `SecureComputation.yaoHybrid_answersB_getD` (proved): Bob's OT answers are his keys.
* `SecureComputation.yaoHybrid_correct` (proved): both parties output `f(x, y)` in the hybrid
  execution when the garbling is good with distinct output keys.
* `SecureComputation.yaoSeed_good_whp` (proved): the garbling is good with distinct output keys
  except with negligible probability.
* `SecureComputation.yaoHybrid_polyTime`, `yaoHybrid_simulators` (stated; `sorry`s under sketches):
  the protocol is efficient, and the simulators of Theorem 163.7.
* `SecureComputation.yaoHybrid_hbcSecure` (Theorem 163.7 in the OT-hybrid model, proved from the
  two previous results).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Protocol 162.6 and Theorem 163.7 (book pp. 156–164).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3 (oracle-aided protocols and their composition).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*, STOC 1990,
  pp. 503–513 (the point-and-permute row order).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party computation*,
  Journal of Cryptology 22(2), 2009, pp. 161–188 (the simulator with one active key per wire).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

/-! ### Circuit descriptions with an output list -/

/-- **The description of a circuit with an output list** [PS10, Protocol 162.6, "a canonical
circuit representation of `f`"]: the pair of the circuit's description `DAGCircuit.encode` (the
number of inputs, the gates and the output vertex, numbers in unary) and the encoded list of the
output vertices in unary, `⟨C, ⟨o₀, ⟨o₁, …⟩⟩⟩`. The gates are encoded by `DAGGate.encode`. -/
def encodeCircuit {m k : ℕ} (C : DAGCircuit m) (outs : Fin k → ℕ) : List Bool :=
  pairEncode C.encode (Strategy.encodeMsgs (List.ofFn fun j => encodeNat (outs j)))

/-- The description of a circuit with an output list is
`⟨encode C, encodeMsgs [encodeNat o₀, …, encodeNat o_{k−1}]⟩`. -/
theorem encodeCircuit_eq {m k : ℕ} (C : DAGCircuit m) (outs : Fin k → ℕ) :
    encodeCircuit C outs =
      pairEncode C.encode (Strategy.encodeMsgs (List.ofFn fun j => encodeNat (outs j))) := rfl

/-- Encoded message lists of equal length are equal only if the lists are. -/
private theorem encodeMsgs_inj : ∀ {l l' : List (List Bool)}, l.length = l'.length →
    Strategy.encodeMsgs l = Strategy.encodeMsgs l' → l = l'
  | [], [], _, _ => rfl
  | a :: l, b :: l', hlen, h => by
    rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons] at h
    have h₁ := congrArg pairFstD h
    have h₂ := congrArg pairSndD h
    rw [pairFstD_pairEncode, pairFstD_pairEncode] at h₁
    rw [pairSndD_pairEncode, pairSndD_pairEncode] at h₂
    rw [h₁, encodeMsgs_inj (by simpa using hlen) h₂]

/-- The unary code is injective (`decodeNat_encodeNat`). -/
private theorem encodeNat_inj {a b : ℕ} (h : encodeNat a = encodeNat b) : a = b := by
  have ha := decodeNat_encodeNat a []
  have hb := decodeNat_encodeNat b []
  rw [h, hb] at ha
  exact (Prod.mk.inj (Option.some.inj ha)).1.symm

/-- **The description of a circuit with an output list is injective**: equal descriptions come
from equal circuits and equal output lists (`DAGCircuit.encode_injective`, the injectivity of the
pairing and of the unary code). -/
theorem encodeCircuit_injective {m k : ℕ} {C C' : DAGCircuit m} {outs outs' : Fin k → ℕ}
    (h : encodeCircuit C outs = encodeCircuit C' outs') : C = C' ∧ outs = outs' := by
  have h₁ := congrArg pairFstD h
  have h₂ := congrArg pairSndD h
  rw [encodeCircuit_eq, encodeCircuit_eq, pairFstD_pairEncode, pairFstD_pairEncode] at h₁
  rw [encodeCircuit_eq, encodeCircuit_eq, pairSndD_pairEncode, pairSndD_pairEncode] at h₂
  refine ⟨DAGCircuit.encode_injective m h₁, funext fun j => encodeNat_inj ?_⟩
  have h₃ := List.ofFn_injective (encodeMsgs_inj (by simp) h₂)
  exact congrFun h₃ j

/-! ### Uniform circuit families with output lists -/

/-- **A uniform circuit family for Yao's protocol** [PS10, Protocol 162.6, "a canonical circuit
representation of `f`"; §6.2.1, fan-in two]: for each `n`, a fan-in-two circuit `C_n` on
`inA(n) + inB(n)` inputs (Alice's input bits first, then Bob's) with `outLen(n)` output vertices,
none of them read by a gate, of size at most `sizeBound(n)`; and a polynomial-time map sends `1^n`
to the description of `C_n` with its output list. The circuit's own `output` field is not used.

**Deviations.** The output vertices must be sinks (see the module docstring: the decoding pairs
reveal both keys of an output vertex). Uniformity makes the parties efficient; the source fixes a
circuit for `f` without discussing how it is computed. -/
structure YaoCircuit where
  /-- Alice's input length. -/
  inA : PolyExpr
  /-- Bob's input length. -/
  inB : PolyExpr
  /-- The output length. -/
  outLen : PolyExpr
  /-- A polynomial bound on the circuits' sizes. -/
  sizeBound : PolyExpr
  /-- The circuit at parameter `n`: Alice's inputs are vertices `0, …, inA − 1`, Bob's follow. -/
  circ : ∀ n, DAGCircuit (inA.eval n + inB.eval n)
  /-- The output vertices at parameter `n`. -/
  outs : ∀ n, Fin (outLen.eval n) → ℕ
  /-- The output vertices are vertices of the circuit. -/
  outs_lt : ∀ n j, outs n j < (circ n).size
  /-- No gate reads an output vertex. -/
  outs_sink : ∀ n j, ∀ g ∈ (circ n).gates, outs n j ∉ g.args
  /-- The circuits have fan-in two (and are well formed). -/
  fanin : ∀ n, (circ n).IsFaninTwo
  /-- The circuits have polynomial size. -/
  size_le : ∀ n, (circ n).size ≤ sizeBound.eval n
  /-- The family is uniform: a polynomial-time map sends `1^n` to the description of `C_n`. -/
  uniform : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n, E (List.replicate n true) = encodeCircuit (circ n) (outs n)

namespace YaoCircuit

variable (Y : YaoCircuit)

/-- **The function computed by the family**: on Alice's input `x` and Bob's input `y`, bit `j` is
the value of `C_n(x, y)` at the output vertex `o_j`. -/
def output (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) :
    Fin (Y.outLen.eval n) → Bool :=
  fun j => ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false

/-- Bit `j` of the output is the value of `C_n(x, y)` at the output vertex `o_j`. -/
theorem output_apply (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (j : Fin (Y.outLen.eval n)) :
    Y.output n x y j = ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false := rfl

end YaoCircuit

/-- **The functionality of a Yao circuit family** [PS10, Protocol 162.6, "A and B output the
result `f(x, y)`"]: Alice's input has `inA(n)` bits, Bob's `inB(n)`, and both parties receive the
`outLen(n)` bits `C_n(x, y)` at the output vertices. Its field equations are
`yaoFunctionality_inA`, …, `yaoFunctionality_f`. -/
def yaoFunctionality (Y : YaoCircuit) : Functionality where
  inA := Y.inA
  inB := Y.inB
  outA := Y.outLen
  outB := Y.outLen
  f n x y := (Y.output n x y, Y.output n x y)

attribute [simps (config := { isSimp := false }) inA inB outA outB f] yaoFunctionality

/-! ### The garbling from Alice's coins -/

/-- **`len` bits of a string from position `off`**: bit `t` is the string's bit `off + t`, or
`false` past its end. -/
def readBits (w : List Bool) (off len : ℕ) : Fin len → Bool := fun t => w.getD (off + t) false

/-- Bit `t` of `readBits w off len` is bit `off + t` of `w` (`false` past its end). -/
theorem readBits_apply (w : List Bool) (off len : ℕ) (t : Fin len) :
    readBits w off len t = w.getD (off + t) false := rfl

/-- **The index of an assignment**: the assignment `a` of `len` positions read as a binary number,
position `0` the least significant bit, `Σ_t a_t · 2^t`. It is below `4` for at most two
positions. -/
def assignIdx {len : ℕ} (a : Fin len → Bool) : ℕ :=
  (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0

/-- The index of an assignment is the fold `b₀ + 2 (b₁ + 2 (⋯))` of its bits. -/
theorem assignIdx_eq {len : ℕ} (a : Fin len → Bool) :
    assignIdx a = (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 := rfl

/-- **The XOR shift by `λ`**: the permutation `a ↦ a ⊕ λ` of the assignments of `len` positions,
an involution. It is the row order of the garbled tables ([BMR90]'s point-and-permute; declared
deviation from [PS10, §6.2.3]'s uniform shuffle, see the module docstring). -/
def xorShift {len : ℕ} (l : Fin len → Bool) : Equiv.Perm (Fin len → Bool) :=
  Function.Involutive.toPerm (fun a p => xor (a p) (l p)) fun a => funext fun p => by
    show xor (xor (a p) (l p)) (l p) = a p
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The XOR shift by `λ` maps `a` to `a ⊕ λ`, position by position. -/
theorem xorShift_apply {len : ℕ} (l a : Fin len → Bool) :
    xorShift l a = fun p => xor (a p) (l p) := rfl

/-- The inverse XOR shift is the same pointwise XOR operation. -/
theorem xorShift_symm_apply {len : ℕ} (l a : Fin len → Bool) :
    (xorShift l).symm a = fun p => xor (a p) (l p) := rfl

/-- **Alice's number of coins**: `10 · S(n) · n + 2 · S(n)` for the size bound `S`; `2 · S(n) · n`
for the keys, `8 · S(n) · n` for the row coins (at most four rows of `2n` coins per gate), and
`2 · S(n)` for the shifts. -/
def yaoCoins (Y : YaoCircuit) : PolyExpr :=
  .add (.mul (.mul (.const 10) Y.sizeBound) .var) (.mul (.const 2) Y.sizeBound)

/-- Alice's coin-count expression is `10 S(n)n + 2 S(n)` syntactically. -/
theorem yaoCoins_eq (Y : YaoCircuit) :
    yaoCoins Y = .add (.mul (.mul (.const 10) Y.sizeBound) .var)
      (.mul (.const 2) Y.sizeBound) := rfl

/-- Alice has `10 · S(n) · n + 2 · S(n)` coins. -/
theorem yaoCoins_eval (Y : YaoCircuit) (n : ℕ) :
    (yaoCoins Y).eval n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n := rfl

/-- **The garbling's randomness from Alice's coins** [PS10, §6.2.2–6.2.3: random key pairs,
encryption coins, shuffled rows], at key length `n`, with `S = sizeBound(n)`:
- the key of vertex `v` for the bit `b`: the `n` coins from `(b · S + v) · n`;
- the coins of row `a` of gate `i`: the `2n` coins from `2 S n + (4 i + idx(a)) · 2n`, split in
  halves (the outer and inner layer's coins);
- the row order of gate `i`: the XOR shift by the coins from `10 S n + 2 i`.

For a fan-in-two circuit of size at most `S` these blocks are disjoint, so uniform coins give
independent uniform keys and row coins, and uniform shifts.

**Deviation.** The row order is a uniform XOR shift, not a uniform permutation (module docstring).
-/
def yaoSeed (Y : YaoCircuit) (n : ℕ) (r : List Bool) :
    GarbleSeed (Y.circ n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) :=
  (fun v b => readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n,
    fun i a => (readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n)) n,
      readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n) + n) n),
    fun i => xorShift (readBits r (10 * Y.sizeBound.eval n * n + 2 * i) _))

/-- The key of vertex `v` for the bit `b` is the `n` coins from `(b · S + v) · n`. -/
theorem yaoSeed_fst (Y : YaoCircuit) (n : ℕ) (r : List Bool) (v : Fin (Y.circ n).size)
    (b : Bool) :
    (yaoSeed Y n r).1 v b = readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n := rfl

/-- The coins of row `a` of gate `i` are the two `n`-bit halves of the `2n` coins from
`2 S n + (4 i + idx(a)) · 2n`. -/
theorem yaoSeed_snd_fst (Y : YaoCircuit) (n : ℕ) (r : List Bool)
    (i : Fin (Y.circ n).gates.length) (a : Fin ((Y.circ n).gates[i]).args.length → Bool) :
    (yaoSeed Y n r).2.1 i a =
      (readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n)) n,
        readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n) + n) n) := rfl

/-- The row order of gate `i` is the XOR shift by the coins from `10 S n + 2 i`. -/
theorem yaoSeed_snd_snd (Y : YaoCircuit) (n : ℕ) (r : List Bool)
    (i : Fin (Y.circ n).gates.length) :
    (yaoSeed Y n r).2.2 i = xorShift (readBits r (10 * Y.sizeBound.eval n * n + 2 * i) _) := rfl

/-- The key of a vertex `v` of the circuit for the bit `b` is the `n` coins from
`(b · S + v) · n`. -/
theorem keyAt_yaoSeed (Y : YaoCircuit) (n : ℕ) (r : List Bool) {v : ℕ}
    (hv : v < (Y.circ n).size) (b : Bool) :
    keyAt (Y.circ n) (yaoSeed Y n r) v b =
      readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n := by
  rw [keyAt_eq, dif_pos hv, yaoSeed_fst]

/-! ### Message lists -/

/-- **Decoding a message list**, the inverse of `Strategy.encodeMsgs`: the first component of the
string, then the decoding of the second, until the empty string (at most `|w|` components).
Delegates to the public word-list decoder, including on malformed words. -/
def decodeMsgs (w : List Bool) : List (List Bool) := BinArith.decWords w

/-- Decoding any word gives `[]` when the word is empty, and otherwise its first pair
component followed by the decoding of its second component, including on malformed words.

**Proof sketch.** Apply the public empty or nonempty equation of `BinArith.decWords`, according
to whether the input word is empty. -/
theorem decodeMsgs_eq (w : List Bool) :
    decodeMsgs w = if w = [] then [] else pairFstD w :: decodeMsgs (pairSndD w) :=
  if hw : w = [] then
    (congrArg decodeMsgs hw).trans (BinArith.decWords_nil.trans (if_pos hw).symm)
  else
    (BinArith.decWords_of_ne hw).trans (if_neg hw).symm

/-- **Decoding inverts the message-list encoding**: `decodeMsgs (encodeMsgs l) = l`.

**Proof sketch.** The public nil and cons equations identify `Strategy.encodeMsgs` with
`BinArith.encWords` by list recursion. Apply `BinArith.decWords_encWords`. -/
theorem decodeMsgs_encodeMsgs (l : List (List Bool)) :
    decodeMsgs (Strategy.encodeMsgs l) = l := by
  have henc : ∀ ms : List (List Bool), Strategy.encodeMsgs ms = BinArith.encWords ms :=
    List.rec (motive := fun ms : List (List Bool) =>
      Strategy.encodeMsgs ms = BinArith.encWords ms)
      (Strategy.encodeMsgs_nil.trans BinArith.encWords_nil.symm)
      (fun m ms ih => (Strategy.encodeMsgs_cons m ms).trans
        ((congrArg (pairEncode m) ih).trans (BinArith.encWords_cons m ms).symm))
  exact (congrArg BinArith.decWords (henc l)).trans (BinArith.decWords_encWords l)

/-- The empty string decodes to the empty list. -/
theorem decodeMsgs_nil : decodeMsgs [] = [] := BinArith.decWords_nil

/-! ### Alice's message -/

variable (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)

/-- **The garbled tables** [PS10, Protocol 162.6, "A generates a garbled circuit … and sends the
circuit"]: gate by gate, the garbled table of `yaoSeed` with nested special encryption, each
table an encoded list of rows, and the tables an encoded list. -/
noncomputable def yaoTables (n : ℕ) (r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun i : Fin (Y.circ n).gates.length =>
    Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) i))

/-- The garbled tables are the encoded list of the encoded garbled tables. -/
theorem yaoTables_eq (n : ℕ) (r : List Bool) :
    yaoTables Y E₁ E₂ n r = Strategy.encodeMsgs (List.ofFn fun i : Fin (Y.circ n).gates.length =>
      Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) i)) :=
  rfl

/-- **Alice's input keys** [PS10, Protocol 162.6, "the input keys corresponding to the bits of
`x`"]: the encoded list of the keys `k_v^{x_v}` of her input vertices `v < inA(n)`, for her
input `xs`. -/
def yaoKeysA (n : ℕ) (xs r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun v : Fin (Y.inA.eval n) =>
    List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) v (xs.getD v false)))

/-- Alice's input keys are the encoded list of `k_v^{x_v}` for `v < inA(n)`. -/
theorem yaoKeysA_eq (n : ℕ) (xs r : List Bool) :
    yaoKeysA Y n xs r = Strategy.encodeMsgs (List.ofFn fun v : Fin (Y.inA.eval n) =>
      List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) v (xs.getD v false))) := rfl

/-- **The decoding pairs**: for each output index `j`, the pair `⟨k_{o_j}^0, k_{o_j}^1⟩` of the
keys of the output vertex `o_j`, as an encoded list.

**Deviation.** Not in [PS10], which does not say how Bob reads the output (module docstring). -/
def yaoPairs (n : ℕ) (r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun j : Fin (Y.outLen.eval n) =>
    pairEncode (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false))
      (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true)))

/-- The decoding pairs are the encoded list of `⟨k_{o_j}^0, k_{o_j}^1⟩`. -/
theorem yaoPairs_eq (n : ℕ) (r : List Bool) :
    yaoPairs Y n r = Strategy.encodeMsgs (List.ofFn fun j : Fin (Y.outLen.eval n) =>
      pairEncode (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false))
        (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true))) := rfl

/-- **Alice's message** [PS10, Protocol 162.6, first step]: `⟨tables, ⟨her input keys, decoding
pairs⟩⟩`, for her input `xs` and her coins `r`. -/
noncomputable def yaoMsg (n : ℕ) (xs r : List Bool) : List Bool :=
  pairEncode (yaoTables Y E₁ E₂ n r) (pairEncode (yaoKeysA Y n xs r) (yaoPairs Y n r))

/-- Alice's message is `⟨tables, ⟨input keys, decoding pairs⟩⟩`. -/
theorem yaoMsg_eq (n : ℕ) (xs r : List Bool) :
    yaoMsg Y E₁ E₂ n xs r =
      pairEncode (yaoTables Y E₁ E₂ n r) (pairEncode (yaoKeysA Y n xs r) (yaoPairs Y n r)) := rfl

/-! ### Bob's evaluation -/

/-- **The tables Bob reads**: at a gate vertex `v ≥ inA + inB`, the decoded list of rows of the
`(v − inA − inB)`-th encoded table of the message; none at an input vertex. -/
def yaoBobTables (n : ℕ) (msg : List Bool) (v : ℕ) : List (List Bool) :=
  if Y.inA.eval n + Y.inB.eval n ≤ v then
    decodeMsgs ((decodeMsgs (pairFstD msg)).getD (v - (Y.inA.eval n + Y.inB.eval n)) [])
  else []

/-- Bob's table at `v` is the decoded `(v − inA − inB)`-th table at a gate vertex, and empty at
an input vertex. -/
theorem yaoBobTables_eq (n : ℕ) (msg : List Bool) (v : ℕ) :
    yaoBobTables Y n msg v = if Y.inA.eval n + Y.inB.eval n ≤ v then
      decodeMsgs ((decodeMsgs (pairFstD msg)).getD (v - (Y.inA.eval n + Y.inB.eval n)) [])
    else [] := rfl

/-- **Bob's input keys** [PS10, Protocol 162.6, "using the keys for all input wires"]: at Alice's
vertex `v < inA(n)`, the `v`-th key of the message; at his vertex `inA(n) + i`, bits `i · n` to
`i · n + n − 1` of his OT answers `ans`. -/
def yaoBobInit (n : ℕ) (msg ans : List Bool) : List (Fin n → Bool) :=
  List.ofFn fun v : Fin (Y.inA.eval n + Y.inB.eval n) =>
    if (v : ℕ) < Y.inA.eval n then padFin n ((decodeMsgs (pairFstD (pairSndD msg))).getD v [])
    else readBits ans (((v : ℕ) - Y.inA.eval n) * n) n

/-- Bob's input keys: Alice's `v`-th key from the message at `v < inA`, his answer bits from
`(v − inA) · n` otherwise. -/
theorem yaoBobInit_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobInit Y n msg ans = List.ofFn fun v : Fin (Y.inA.eval n + Y.inB.eval n) =>
      if (v : ℕ) < Y.inA.eval n then padFin n ((decodeMsgs (pairFstD (pairSndD msg))).getD v [])
      else readBits ans (((v : ℕ) - Y.inA.eval n) * n) n := rfl

/-- **Bob's garbled evaluation** [PS10, Protocol 162.6, "B evaluates the circuit"; §6.2.3, "attempt
to decrypt all four rows"]: `runWith` over the gates of `C_n` from his input keys, each gate opened
by `evalGate` on the table he read at its vertex. -/
def yaoBobValues (n : ℕ) (msg ans : List Bool) : List (Fin n → Bool) :=
  runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ n) (yaoBobTables Y n msg) vs.length g vs)
    (Y.circ n).gates (yaoBobInit Y n msg ans)

/-- Bob's garbled evaluation is `runWith` of `evalGate` on his tables from his input keys. -/
theorem yaoBobValues_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobValues Y E₁ E₂ n msg ans =
      runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ n) (yaoBobTables Y n msg) vs.length g vs)
        (Y.circ n).gates (yaoBobInit Y n msg ans) := rfl

/-- **Decoding an output key** by its pair `p = ⟨k⁰, k¹⟩`: `k⁰ ↦ false`, `k¹ ↦ true`, anything
else `↦ false`.

**Deviation.** Not in [PS10] (module docstring). -/
def decodeOut (k p : List Bool) : Bool :=
  if k = pairFstD p then false else decide (k = pairSndD p)

/-- Decoding an output key: `false` if it is the first key of the pair, otherwise whether it is
the second. -/
theorem decodeOut_eq (k p : List Bool) :
    decodeOut k p = if k = pairFstD p then false else decide (k = pairSndD p) := rfl

/-- The first key of a pair decodes to `false`. -/
theorem decodeOut_fst (k₀ k₁ : List Bool) : decodeOut k₀ (pairEncode k₀ k₁) = false := by
  rw [decodeOut, pairFstD_pairEncode, if_pos rfl]

/-- The second key of a pair of distinct keys decodes to `true`. -/
theorem decodeOut_snd (k₀ k₁ : List Bool) (h : k₁ ≠ k₀) :
    decodeOut k₁ (pairEncode k₀ k₁) = true := by
  rw [decodeOut, pairFstD_pairEncode, pairSndD_pairEncode, if_neg h, decide_eq_true rfl]

/-- **Bob's result** [PS10, Protocol 162.6, last step]: for each output index `j`, the key his
evaluation reaches at the output vertex `o_j`, decoded by the `j`-th pair of the message. -/
def yaoBobOut (n : ℕ) (msg ans : List Bool) : List Bool :=
  List.ofFn fun j : Fin (Y.outLen.eval n) =>
    decodeOut (List.ofFn ((yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
      ((decodeMsgs (pairSndD (pairSndD msg))).getD j [])

/-- Bob's result: bit `j` decodes the key at `o_j` by the `j`-th decoding pair. -/
theorem yaoBobOut_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobOut Y E₁ E₂ n msg ans = List.ofFn fun j : Fin (Y.outLen.eval n) =>
      decodeOut (List.ofFn ((yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
        ((decodeMsgs (pairSndD (pairSndD msg))).getD j []) := rfl

/-! ### The protocol -/

/-- **Alice in Protocol 162.6** [PS10] (the prover's role, `Defs.lean`'s convention), on common
input `1^n`, private input `⟨x, answers⟩` (her answers are empty: OT gives the sender `⊥`) and
coins `r`: on the empty history, her message `yaoMsg`; on a nonempty history, its first message,
which is her output ("A and B output the result"). Her coins are `yaoCoins`. -/
noncomputable def yaoAlice : Strategy where
  next x z r hist := match hist with
    | [] => yaoMsg Y E₁ E₂ x.length (pairFstD z) r
    | m :: _ => m
  coins := yaoCoins Y

/-- On the empty history Alice sends `yaoMsg` at `|x|` for her input `pairFstD z`. -/
theorem yaoAlice_next_nil (x z r : List Bool) :
    (yaoAlice Y E₁ E₂).next x z r [] = yaoMsg Y E₁ E₂ x.length (pairFstD z) r := rfl

/-- On a nonempty history Alice returns its first message. -/
theorem yaoAlice_next_cons (x z r m : List Bool) (hist : List (List Bool)) :
    (yaoAlice Y E₁ E₂).next x z r (m :: hist) = m := rfl

/-- Alice's coin polynomial is `yaoCoins`. -/
theorem yaoAlice_coins : (yaoAlice Y E₁ E₂).coins = yaoCoins Y := rfl

/-- **Bob in Protocol 162.6** [PS10] (the verifier's role), on common input `1^n` and private
input `⟨y, answers⟩`: his result `yaoBobOut` on the first message received and his answers. He
moves last, so his message is also his output. He uses no coins. -/
def yaoBob : Strategy where
  next x z _ hist := yaoBobOut Y E₁ E₂ x.length (hist.headD []) (pairSndD z)
  coins := .const 0

/-- Bob's message is `yaoBobOut` at `|x|` on the first message received and his answers. -/
theorem yaoBob_next (x z r : List Bool) (hist : List (List Bool)) :
    (yaoBob Y E₁ E₂).next x z r hist =
      yaoBobOut Y E₁ E₂ x.length (hist.headD []) (pairSndD z) := rfl

/-- Bob uses no coins. -/
theorem yaoBob_coins : (yaoBob Y E₁ E₂).coins = .const 0 := rfl

/-- **The message phase of Protocol 162.6** [PS10]: two messages, Alice first; Alice sends the
garbled circuit and her keys, Bob returns `f(x, y)`. Its fields are `yaoMain_P`, …,
`yaoMain_verifierFirst`. -/
noncomputable def yaoMain : Protocol where
  P := yaoAlice Y E₁ E₂
  V := yaoBob Y E₁ E₂
  rounds := .const 2
  verifierFirst := false

attribute [simps (config := { isSimp := false }) P V rounds verifierFirst] yaoMain

/-- **Bob's output in the message phase**: Bob's result on Alice's message and his answers. -/
theorem yaoMain_outV (w zA zB : List Bool)
    (r : (yaoMain Y E₁ E₂).ExecCoins (yaoMain Y E₁ E₂).P w) :
    (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P w zA zB r =
      yaoBobOut Y E₁ E₂ w.length (yaoMsg Y E₁ E₂ w.length (pairFstD zA) (List.ofFn r.1))
        (pairSndD zB) := by
  simp [Protocol.outV_eq, Protocol.transcriptWith_eq, yaoMain_P, yaoMain_V,
    yaoMain_rounds, yaoMain_verifierFirst, PolyExpr.eval_const, exec_succ, exec_zero,
    moverIsV_false, yaoAlice_next_nil, yaoBob_next]

/-- **Alice's output in the message phase**: the message Bob sent, his result. -/
theorem yaoMain_outP (w zA zB : List Bool)
    (r : (yaoMain Y E₁ E₂).ExecCoins (yaoMain Y E₁ E₂).P w) :
    (yaoMain Y E₁ E₂).outP w zA zB r =
      yaoBobOut Y E₁ E₂ w.length (yaoMsg Y E₁ E₂ w.length (pairFstD zA) (List.ofFn r.1))
        (pairSndD zB) := by
  simp [Protocol.outP_eq, Protocol.transcriptWith_eq, yaoMain_P, yaoMain_V,
    yaoMain_rounds, yaoMain_verifierFirst, PolyExpr.eval_const, exec_succ, exec_zero,
    moverIsV_false, yaoAlice_next_nil, yaoAlice_next_cons, yaoBob_next]

/-- **The OT call index**: call `j < inB(n) · n` transfers bit `t` of the keys of Bob's wire
`inA + i`, for `(i, t) = finProdFinEquiv⁻¹ j`, that is `j = i · n + t`. -/
def yaoCall (n : ℕ) (j : Fin (Y.inB.eval n * n)) : Fin (Y.inB.eval n) × Fin n :=
  finProdFinEquiv.symm j

/-- The OT call index is `finProdFinEquiv⁻¹`. -/
theorem yaoCall_eq (n : ℕ) (j : Fin (Y.inB.eval n * n)) :
    yaoCall Y n j = finProdFinEquiv.symm j := rfl

/-- Call `finProdFinEquiv (i, t)` (that is `i · n + t`) has index `(i, t)`. -/
theorem yaoCall_finProdFinEquiv (n : ℕ) (i : Fin (Y.inB.eval n)) (t : Fin n) :
    yaoCall Y n (finProdFinEquiv (i, t)) = (i, t) := by
  rw [yaoCall, Equiv.symm_apply_apply]

/-- **Protocol 162.6 in the OT-hybrid model** [PS10, Protocol 162.6; Gol04, §7.3]: `inB(n) · n`
ideal bit OTs, then `yaoMain`. In call `(i, t)` Alice's input is bit `t` of the two keys of
Bob's wire `inA + i` (from her coins, through `yaoSeed`), Bob's is his bit `y_i`. Its fields are
`yaoHybrid_main`, `yaoHybrid_calls`, `yaoHybrid_callA`, `yaoHybrid_callB`.

**Deviation.** The source's OT of a key pair is `n` bit OTs with the same choice bit (module
docstring). -/
noncomputable def yaoHybrid : HybridProtocol otFunctionality where
  main := yaoMain Y E₁ E₂
  calls := .mul Y.inB .var
  callA n _ r j c := keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + (yaoCall Y n j).1)
    (decide ((c : ℕ) = 1)) (yaoCall Y n j).2
  callB n y _ j _ := y.getD (yaoCall Y n j).1 false

attribute [simps (config := { isSimp := false }) main calls] yaoHybrid

/-- Alice's input to call `j = (i, t)` is `c ↦ k_{inA + i}^{c = 1}[t]`. -/
theorem yaoHybrid_callA (n : ℕ) (xs r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 2) :
    (yaoHybrid Y E₁ E₂).callA n xs r j
        (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inA).trans
          (PolyExpr.eval_const 2 n)).symm c) =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + (yaoCall Y n j).1) (decide ((c : ℕ) = 1))
        (yaoCall Y n j).2 := rfl

/-- Bob's input to call `j = (i, t)` is his bit `y_i`. -/
theorem yaoHybrid_callB (n : ℕ) (ys r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 1) :
    (yaoHybrid Y E₁ E₂).callB n ys r j
        (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inB).trans
          (PolyExpr.eval_const 1 n)).symm c) = ys.getD (yaoCall Y n j).1 false := rfl

/-! ### Correctness -/

/-- Reading a list of a function at an index of the function's domain. -/
private theorem getD_ofFn' {α : Type} {k : ℕ} (f : Fin k → α) (i : Fin k) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **Bob reads the garbled tables**: on Alice's message, the tables Bob reads are the garbled
tables `tableAt` of her garbling, at every vertex. -/
theorem yaoBobTables_yaoMsg (n : ℕ) (xs r : List Bool) :
    yaoBobTables Y n (yaoMsg Y E₁ E₂ n xs r) =
      tableAt (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) := by
  funext v
  rw [tableAt_eq, yaoBobTables_eq, yaoMsg_eq, yaoTables_eq, pairFstD_pairEncode,
    decodeMsgs_encodeMsgs]
  by_cases h1 : Y.inA.eval n + Y.inB.eval n ≤ v
  · rw [if_pos h1]
    by_cases h2 : v - (Y.inA.eval n + Y.inB.eval n) < (Y.circ n).gates.length
    · rw [dif_pos ⟨h1, h2⟩, List.getD_eq_getElem _ _ (by simpa using h2), List.getElem_ofFn,
        decodeMsgs_encodeMsgs]
    · rw [dif_neg (fun h => h2 h.2), List.getD_eq_default _ _ (by simp; omega), decodeMsgs_nil]
  · rw [if_neg h1, dif_neg (fun h => h1 h.1)]

/-- **Bob's input keys are the input keys of `(x, y)`**: on Alice's message for `x`, and answers
that hold, at bits `i · n + t`, the bits of the keys `k_{inA + i}^{y_i}`, Bob's input keys are
`inputKeys` of `x ‖ y`.

**Proof sketch.** Vertex by vertex. At Alice's vertex `v < inA`, the second component of the
message decodes to her keys (`decodeMsgs_encodeMsgs`), and its `v`-th entry is `k_v^{x_v}`
(`padFin_ofFn`), with `x_v = (x ‖ y)_v` (`Fin.append_left`). At Bob's vertex `inA + i`, the
answer bits `i · n + t` are the bits of `k_{inA + i}^{y_i}` by hypothesis, with
`y_i = (x ‖ y)_{inA + i}` (`Fin.append_right`). -/
theorem yaoBobInit_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t) :
    yaoBobInit Y n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      inputKeys (Y.circ n) (yaoSeed Y n r) (Fin.append x y) := by
  rw [inputKeys_eq, yaoBobInit_eq]
  congr 1
  funext v
  rw [yaoMsg_eq, pairSndD_pairEncode, pairFstD_pairEncode, yaoKeysA_eq, decodeMsgs_encodeMsgs]
  by_cases hv : (v : ℕ) < Y.inA.eval n
  · rw [if_pos hv, getD_ofFn' _ ⟨v, hv⟩, padFin_ofFn, getD_ofFn' x ⟨v, hv⟩]
    have hx := Fin.append_left x y ⟨v, hv⟩
    rw [show Fin.castAdd (Y.inB.eval n) ⟨(v : ℕ), hv⟩ = v from Fin.ext rfl] at hx
    rw [hx]
  · rw [if_neg hv]
    have hi : (v : ℕ) - Y.inA.eval n < Y.inB.eval n := by omega
    have hy := Fin.append_right x y ⟨v - Y.inA.eval n, hi⟩
    rw [show Fin.natAdd (Y.inA.eval n) ⟨(v : ℕ) - Y.inA.eval n, hi⟩ = v from
      Fin.ext (by simp; omega)] at hy
    rw [hy]
    funext t
    have hv' : Y.inA.eval n + ((v : ℕ) - Y.inA.eval n) = v := by omega
    rw [readBits_apply, hans ⟨v - Y.inA.eval n, hi⟩ t, Fin.val_mk, hv']

/-- **Bob's evaluation is the garbled evaluation**: on Alice's message and answers holding the
keys of Bob's bits, Bob's values are `garbledValues` of her garbling from the input keys of
`x ‖ y`. -/
theorem yaoBobValues_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t) :
    yaoBobValues Y E₁ E₂ n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      garbledValues (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r)
        (inputKeys (Y.circ n) (yaoSeed Y n r) (Fin.append x y)) := by
  rw [yaoBobValues_eq, yaoBobTables_yaoMsg, yaoBobInit_yaoMsg Y E₁ E₂ n x y r ans hans,
    garbledValues_eq]

/-- **Bob computes `f(x, y)`** [PS10, Protocol 162.6, "B evaluates the circuit to compute the
output `f(x, y)`"; Claim 159.a]: on Alice's message for `x`, with answers holding the keys of
Bob's bits `y`, if the garbling is good and every output vertex has two distinct keys, Bob's
result is `C_n(x, y)` at the output vertices.

**Proof sketch.** Bob's tables are the garbled tables and his input keys those of `x ‖ y`
(`yaoBobTables_yaoMsg`, `yaoBobInit_yaoMsg`), so his evaluation is `garbledValues`
(`yaoBobValues_yaoMsg`). By `garbledValues_getD` it reaches the key `k_o^{v_o}` of each output
vertex `o`'s value. The `j`-th decoding pair is `⟨k_o^0, k_o^1⟩`, and with distinct keys
`decodeOut` returns `v_o` (`decodeOut_fst`, `decodeOut_snd`). -/
theorem yaoBobOut_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true) :
    yaoBobOut Y E₁ E₂ n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans = List.ofFn (Y.output n x y) := by
  rw [yaoBobOut_eq, yaoBobValues_yaoMsg Y E₁ E₂ n x y r ans hans]
  congr 1
  funext j
  rw [garbledValues_getD _ _ _ hgood _ _ (Y.outs_lt n j), yaoMsg_eq, pairSndD_pairEncode,
    pairSndD_pairEncode, yaoPairs_eq, decodeMsgs_encodeMsgs, getD_ofFn', YaoCircuit.output_apply]
  cases ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false
  · exact decodeOut_fst _ _
  · exact decodeOut_snd _ _ fun h => hdist j (List.ofFn_injective h).symm

/-- **Bob's OT answers are the keys of his bits**: in the hybrid execution, bit `i · n + t` of
Bob's answers is bit `t` of the key `k_{inA + i}^{y_i}` of his wire `inA + i` for his bit `y_i`
(`otFunctionality_f_snd`). -/
theorem yaoHybrid_answersB_getD (n : ℕ) (xs ys rA rB : List Bool) (i : Fin (Y.inB.eval n))
    (t : Fin n) :
    ((yaoHybrid Y E₁ E₂).answersB n xs ys rA rB).getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n rA) (Y.inA.eval n + i) (ys.getD i false) t := by
  have h := flatten_ofFn_one (k := Y.inB.eval n * n) (l := otFunctionality.outB.eval n)
    ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_outB).trans
      (PolyExpr.eval_const 1 n))
    fun j => (otFunctionality.f n ((yaoHybrid Y E₁ E₂).callA n xs rA j)
      ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2
  have hj : i * n + t = (finProdFinEquiv (i, t) : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  rw [HybridProtocol.answersB_eq]
  -- Normalize the owner-local hybrid call count in the list binder before using `h`.
  change (List.ofFn (fun j : Fin (Y.inB.eval n * n) =>
    List.ofFn ((otFunctionality.f n ((yaoHybrid Y E₁ E₂).callA n xs rA j)
      ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2))).flatten.getD (i * n + t) false = _
  rw [h, hj, getD_ofFn', otFunctionality_f_snd_apply,
    yaoHybrid_callA, yaoHybrid_callB, yaoCall_finProdFinEquiv]
  cases ys.getD i false <;> rfl

/-- `yaoBobOut_yaoMsg` at a parameter `L` equal to `n` (for the common input `1^n`, whose length
is `n` only propositionally). -/
private theorem yaoBobOut_yaoMsg_of_eq {L n : ℕ} (hL : L = n) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true) :
    yaoBobOut Y E₁ E₂ L (yaoMsg Y E₁ E₂ L (List.ofFn x) r) ans = List.ofFn (Y.output n x y) := by
  subst hL
  exact yaoBobOut_yaoMsg Y E₁ E₂ L x y r ans hans hgood hdist

/-- **Correctness of Protocol 162.6 in the OT-hybrid model** [PS10, Protocol 162.6, "A and B
output the result `f(x, y)`"; the output clause of Theorem 163.7]: in the hybrid execution with
common input `1^n`, inputs `x`, `y` and coins `r`, if Alice's garbling is good and every output
vertex has two distinct keys, Bob's output and Alice's output are both `f(x, y)`.

**Deviation.** The source needs no hypothesis on the output keys, since it does not say how Bob
decodes them. Equal keys on an output vertex (probability `2^{-n}` each) make the decoding
ambiguous; `yaoSeed_good_whp` bounds both failure events.

**Proof sketch.** Bob's answers hold the keys of his bits (`yaoHybrid_answersB_getD`), and his
private input decodes to them (`HybridProtocol.pairSndD_privB`), Alice's to `x`. The message
phase gives Bob the output `yaoBobOut` on Alice's message (`yaoMain_outV`), which is `f(x, y)`
(`yaoBobOut_yaoMsg`, transported along `|1^n| = n`), and Alice outputs what Bob sent
(`yaoMain_outP`). -/
theorem yaoHybrid_correct (n : ℕ) (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
    (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool) (r : (yaoHybrid Y E₁ E₂).Coins n)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r.1)))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) true) :
    (yaoHybrid Y E₁ E₂).main.outV (yaoHybrid Y E₁ E₂).main.P (List.replicate n true)
        ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        r = List.ofFn ((yaoFunctionality Y).f n x y).2 ∧
      (yaoHybrid Y E₁ E₂).main.outP (List.replicate n true)
        ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        r = List.ofFn ((yaoFunctionality Y).f n x y).1 := by
  have key := yaoBobOut_yaoMsg_of_eq Y E₁ E₂ (List.length_replicate (n := n) (a := true)) x y
    (List.ofFn r.1)
    ((yaoHybrid Y E₁ E₂).answersB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
    (fun i t => by rw [yaoHybrid_answersB_getD, getD_ofFn']) hgood hdist
  refine ⟨?_, ?_⟩
  · show (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P (List.replicate n true) _ _ r = _
    rw [yaoMain_outV, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB]
    exact key
  · show (yaoMain Y E₁ E₂).outP (List.replicate n true) _ _ r = _
    rw [yaoMain_outP, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB]
    exact key

/-! ### Theorem 163.7 in the OT-hybrid model -/

section Security

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Alice's garbling is good, with distinct output keys, with high probability** [PS10, §6.2.3,
"all but one row will evaluate to `⊥`" (Claim 159.a)]: with nested special encryption from two
PRFs `G₁`, `G₂` evaluated by `E₁`, `E₂`, there is a negligible `δ` such that for every `n`, on
uniform coins for Alice, the garbling `yaoSeed` fails to be good, or gives some output vertex two
equal keys, with probability at most `δ(n)`.

**Proof sketch.** Write `S = sizeBound(n)`. Distinct blocks contain all vertex keys and
row coins: vertices and gates are below `S`, and binary assignment indices are injective
below four for fan-in at most two. The generic block restriction theorem gives their joint
uniform law, including zero-length blocks. Apply the strengthened B2 uniform-data bound
with `nestedSpecial_wrongKeyBot` and correctness; this bound permits arbitrary seed-dependent
row permutations, including the XOR shifts. Each output's two keys coincide with probability
`2^{-n}`. The output union bound allows repeated vertices. Thus failure is at most
`12*S(n)*δ₀(n) + outLen(n)*2^{-n}`, a sum of polynomial multiples of negligible functions. -/
theorem yaoSeed_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n := by
  classical
  obtain ⟨δ₀, hδ₀, hbot⟩ :=
    nestedSpecial_wrongKeyBot G₁ G₂ E₁ E₂ hGE₁ hGE₂ hG₁ hG₂
  refine ⟨fun n => 12 * (Y.sizeBound.eval n : ℝ) * δ₀ n +
    (Y.outLen.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n, ?_, fun n => ?_⟩
  · simpa only [PolyExpr.eval_mul, PolyExpr.eval_const, Nat.cast_mul, Nat.cast_ofNat] using
      (EnsembleLemmas.negligible_polyExpr_mul (.mul (.const 12) Y.sizeBound) hδ₀).add
        (EnsembleLemmas.negligible_polyExpr_mul Y.outLen negligible_two_pow_neg)
  · have hg : (Y.circ n).gates.length ≤ Y.sizeBound.eval n := by
      have hs := Y.size_le n
      rw [DAGCircuit.size_eq] at hs
      omega
    have hsmall (i : Fin (Y.circ n).gates.length) :=
      GarblingProbability.assignmentFold_small ((Y.circ n).gates[i]).args.length
        (((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
          (List.getElem_mem i.isLt))
    have hlaw : HardcoreBit.PushesUniform
        (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
          ((yaoSeed Y n (List.ofFn r)).1, (yaoSeed Y n (List.ofFn r)).2.1)) := by
      simp only [yaoCoins_eval]
      convert GarblingProbability.pushesUniform_key_row_blocks (n := n)
        (A := fun i : Fin (Y.circ n).gates.length => Fin ((Y.circ n).gates[i]).args.length → Bool)
        (Y.size_le n) hg
        (fun i a => assignIdx a)
        (fun i a => by change assignIdx a < 4; rw [assignIdx_eq]; exact (hsmall i).1 a)
        (fun i => by simpa only [assignIdx_eq] using (hsmall i).2) using 1
    have hb := uprob_not_good_distinct_le_of_uniform_data
      (nestedSpecial E₁ E₂ n) (Y.circ n)
      (nestedSpecial_decCorrect G₁ G₂ E₁ E₂ hGE₁ hGE₂ n) (hbot n) (Y.fanin n)
      (fun r => yaoSeed Y n (List.ofFn r)) hlaw (Y.outs n) (Y.outs_lt n)
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat, one_div, ← inv_pow] at hb
    refine hb.trans (add_le_add_right ?_ _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hg) (by norm_num))
      (wrongKeyBot_nonneg (nestedSpecial E₁ E₂ n) (hbot n))

/-- **Protocol 162.6 in the OT-hybrid model runs in polynomial time** (the efficiency clause of
[PS10, Definition 155.1], `HybridProtocol.PolyTime`, ruling of 2026-11-05) when `E₁` and `E₂`
are polynomial-time.

**Proof sketch.** Write `S = sizeBound(n)`.
1. *Alice* (`Strategy.Efficient`). On the empty history: compute the description of `C_n` from
   `1^n` by the uniformity map and decode it; read keys, row coins and shifts from her coins;
   encrypt at most four rows per gate with `E₁` and `E₂`; pair the tables, her input keys and the
   decoding pairs. The enumeration `Finset.univ.toList` of the assignments of at most two
   positions is a constant table. On a nonempty history: copy the first message. A uniform
   machine with coin polynomial `yaoCoins` computes this.
2. *Bob.* Decode the three lists (`decodeMsgs`), recompute `C_n`, and run `runWith` with
   `evalGate`: each decryption checks lengths before calling `E₁` or `E₂` (`spDecStr`), and each
   output key is compared with its pair. This is polynomial in `n` and the message length.
3. *The calls.* Alice's input to call `(i, t)` is two coins at positions computed from `n`,
   `inA(n)` and `S` (`keyAt_yaoSeed`); Bob's is one bit of his input.
4. *The messages.* Whatever `E₁`, `E₂` return, a row has at most `7n + 4` bits (`take` and
   `zipWith` cap the pads), so Alice's message has `O((S + inA(n) + outLen(n)) · n)` bits after
   the pairings; Bob's has `outLen(n)` bits. Neither depends on the answers. -/
theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    (yaoHybrid Y E₁ E₂).PolyTime (yaoFunctionality Y) := by
  sorry

include hGE₁ hGE₂ in
/-- **The simulators of Theorem 163.7, in the OT-hybrid model** [PS10, Theorem 163.7]: with
nested special encryption from two PRFs `G₁`, `G₂` with polynomial-time evaluators `E₁`, `E₂`,
which are also jointly pseudorandom under one key, there are non-uniform PPT simulators `S_A`,
`S_B` such that for every non-uniform PPT distinguisher there is a negligible `ε` bounding, for
all `n`, `x`, `y`, its advantage between the hybrid real and ideal samplers on both sides.

**Deviation: the joint PRF hypothesis `hG₁₂`** (the pair `k ↦ (G₁(k, ·), G₂(k, ·))` is one PRF;
it implies `hG₁` and `hG₂`). [PS10] doubly encrypts with one scheme. Here the two layers use two
PRFs (`nestedSpecial`), and a wire's key keys `G₂` where the wire is a first argument and `G₁`
where it is a second or only one. The hybrid of step 3 then needs encryptions of both schemes
under one unknown key. A reduction to the security of `G₁` alone cannot produce the `G₂`-pads
under that key, nor conversely; the two separate PRF assumptions do not give their security
under a shared key in general.

**Proof sketch.** Write `f = f(x, y)`. Alice's view in the hybrid execution is
`⟨1^n, ⟨x, []⟩, r_A, [m_B]⟩` (her OT answers are empty), Bob's is `⟨1^n, ⟨y, ans⟩, [], [m_A]⟩`
with `ans` the bits of the keys `k_{inA + i}^{y_i}` (`yaoHybrid_answersB_getD`). Let `Bad` be the
event that the garbling is not good or some output vertex has two equal keys; by
`yaoSeed_good_whp` it has probability at most `δ(n)`, and off `Bad` both outputs are `f`
(`yaoHybrid_correct`).
1. *`S_A(1^n, ⟨x, f⟩)`*, with `yaoCoins(n)` coins `r`: the view `⟨1^n, ⟨x, []⟩, r, [f]⟩`. The
   source's `S_A` also simulates the OT transcripts with Proposition 161.5's simulator; in the
   hybrid model there are none. Off `Bad`, `m_B = f` and Bob outputs `f`, so the real and ideal
   samplers agree outside an event of probability at most `δ(n)`; every distinguisher has
   advantage at most `δ(n)`, for all inputs.
2. *`S_B(1^n, ⟨y, f⟩)`*, with `yaoCoins(n)` coins: read a seed `s = yaoSeed` and let the active
   key of every wire be `k_w = k_w^0`. The fake garbled circuit has the real enumeration and
   shifts, but every row of gate `i` encrypts the active key `k_{inA + inB + i}` under that row's
   argument keys. Alice's input keys are the active keys, and so are Bob's answers. The pair of
   output `j` is `⟨k_o^0, k_o^1⟩` if `f_j = 0` and `⟨k_o^1, k_o^0⟩` otherwise, so the active key
   decodes to `f_j`. This is the source's "garbled circuit that always outputs `f(x, y)`", in the
   one-active-key form of [LP09]. `S_B` outputs `⟨1^n, ⟨y, ans'⟩, [], [m'_A]⟩`.
3. *Bob's side, the hybrid over gates* [PS10, "using a hybrid argument …"].
   - `H₀` is the real sampler.
   - In `H₁`, wire `w` with value `v_w` on `(x, y)` has active key `a_w = k_w^{v_w}` and inactive
     key `ι_w = k_w^{1−v_w}`, and gate `i` the shift `λ_i ⊕ v_{args}`. This is a bijection of
     Alice's coins, so `H₁ = H₀`. In these terms the opened row of every gate is the row of the
     all-active assignment; its position is uniform, given by the shift. Bob holds only active
     keys, and the active key of output `j` decodes to `f_j`.
   - `H₂,ᵢ` makes the rows of the gates below `i` encrypt the active output key. Then
     `H₂,₀ = H₁`, and `H₂,|gates|` is `S_B`'s output up to renaming the keys.
   - `H₂,ᵢ ≈ H₂,ᵢ₊₁`: the rows that change are encrypted under an inactive key `ι_u` of an
     argument `u` of gate `i`: in the outer layer if `u` is the first argument, else in the inner
     one. In `H₂,ᵢ`, `ι_u` is only an encryption key, of rows of the gates that read `u`:
     - it is no plaintext: if `u` is a gate, it precedes gate `i` and its table is already fake;
     - it is in no decoding pair: no gate reads an output vertex (`YaoCircuit.outs_sink`);
     - it is not among Alice's keys or Bob's answers, which are active.

     A distinguisher between the two gives one against the multi-message security of
     Algorithm 157.2 under `ι_u`: the reduction samples everything else and obtains the rows
     under `ι_u` from its challenge, with plaintexts `ι_{inA + inB + i}` versus
     `a_{inA + inB + i}` for the changed rows. For the inner layer this is Claim 157.a (i)
     (`specialScheme_multiMessageSecure`, `n`-bit messages with `G₁`). For the outer layer it is
     the same claim for `(4n + 2)`-bit messages with `G₂`. Since `ι_u` may key both layers, the
     reduction needs the two schemes' ciphertexts under one key: the same proof, with the
     joint PRF `hG₁₂` replaced by a random function (not yet stated in the library).
   - The reductions are non-uniform: their advice at `n` is the worst inputs `(x, y)` and the
     hybrid index. This makes the bound `2 · S(n) · ε_MM(n)` uniform over the inputs.
   - Bob's real output pair adds `Bad`: the total is `δ(n) + 2 · S(n) · ε_MM(n)`, negligible.
4. *Efficiency of the simulators.* `S_A` copies its input and coins. `S_B` builds `C_n` with the
   uniformity map and encrypts with `E₁` and `E₂`; both are uniform PPT machines. -/
theorem yaoHybrid_simulators (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
        (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool),
        distAdv ((yaoHybrid Y E₁ E₂).realA (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv ((yaoHybrid Y E₁ E₂).realB (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  sorry

include hGE₁ hGE₂ in
/-- **Theorem 163.7 in the OT-hybrid model** [PS10, Theorem 163.7; Gol04, §7.3]: for a uniform
fan-in-two circuit family whose output vertices are sinks, and nested special encryption from two
pseudorandom function families `G₁`, `G₂` with polynomial-time evaluators `E₁`, `E₂`, jointly
pseudorandom under one key, Protocol 162.6 in the OT-hybrid model is an honest-but-curious secure
protocol for the family's functionality. The real protocol (composition with Protocol 160.4) is
not in this file.

**Deviation.** The joint PRF hypothesis `hG₁₂` (see `yaoHybrid_simulators`).

Proved from `yaoHybrid_polyTime` and `yaoHybrid_simulators`. -/
theorem yaoHybrid_hbcSecure (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    (yaoHybrid Y E₁ E₂).HBCSecure (yaoFunctionality Y) :=
  (HybridProtocol.hbcSecure_iff (yaoHybrid Y E₁ E₂) (yaoFunctionality Y)).mpr
    ⟨yaoHybrid_polyTime Y E₁ E₂ hE₁ hE₂,
      yaoHybrid_simulators Y E₁ E₂ G₁ G₂ hGE₁ hGE₂ hE₁ hE₂ hG₁ hG₂ hG₁₂⟩

end Security

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

## ===== TCSlib/Cryptography/SecureComputation/GarblingSpecial.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Garbling
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Garbled circuits from the special encryption scheme (statement phase)

[PS10, §6.2.2–6.2.3]: the garbled rows are encrypted with Algorithm 157.2, "doubly encrypting each
row". This module instantiates the multi-key encryption interface of `Garbling.lean` with nested
special encryption, and proves it correct. Its wrong-key property and the combination with
Claim 159.a are in `GarblingSecurity.lean`.

**Nesting and lengths.** A row with two inputs encrypts the output key (`n` bits) under the
second input's key, then encrypts that ciphertext under the first input's key. The inner
ciphertext `⟨r, c⟩` has `2n + 2 + 2n = 4n + 2` bits (`length_spEncStr`), so the outer layer encrypts
`(4n + 2)`-bit messages, with a pad of `n + (4n + 2)` bits. [PS10] encrypts
`n`-bit messages only and leaves the nesting's lengths implicit; this is a declared deviation. A
single-input row is singly encrypted, and a constant gate's row is in the clear.

## Main definitions

* `SecureComputation.innerLen`: the inner ciphertext length `4n + 2`.
* `SecureComputation.nestedSpecial`: nested special encryption as a `MultiEnc` at parameter `n`.

## Main results

* `SecureComputation.nestedSpecial_decCorrect` (proved): nested special encryption is correct.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2–6.2.3 (book pp. 156–160).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

/-- The inner ciphertext length `4n + 2` of a nested row. -/
def innerLen : PolyExpr := .add (.mul (.const 4) .var) (.const 2)

/-- The inner ciphertext length expression is `4n+2`. -/
theorem innerLen_eq : innerLen = .add (.mul (.const 4) .var) (.const 2) := rfl

/-- **Nested special encryption at parameter `n`**: no key, the plaintext; one key,
Algorithm 157.2 with the pad `E₁` (`2n` bits); two keys, Algorithm 157.2 under the second key
with `E₁`, then under the first key with `E₂` (`n + (4n + 2)` bits). Longer key lists are
unused. -/
@[simps (config := { isSimp := false }) enc dec]
def nestedSpecial (E₁ E₂ : List Bool → List Bool) (n : ℕ) :
    MultiEnc (Fin n → Bool) (List Bool) ((Fin n → Bool) × (Fin n → Bool)) where
  enc ks o r := match ks with
    | [] => List.ofFn o
    | [k] => spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1)
    | [k₁, k₂] => spEncStr E₂ (List.ofFn k₁)
        (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)) (List.ofFn r.1)
    | _ => []
  dec ks c := match ks with
    | [] => decodeFin n c
    | [k] => (spDecStr E₁ n n (List.ofFn k) c).bind (decodeFin n)
    | [k₁, k₂] => (spDecStr E₂ n (innerLen.eval n) (List.ofFn k₁) c).bind fun c' =>
        (spDecStr E₁ n n (List.ofFn k₂) c').bind (decodeFin n)
    | _ => none

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Nested special encryption is correct**: decryption under at most two keys inverts
encryption under them (`spDecStr_spEncStr` at each layer, with the inner ciphertext's length
`4n + 2`).

**Proof sketch.** Split by the number of keys. With no key, decoding the encoded plaintext
returns the plaintext. With one key, the evaluator specification gives a pad of length `2n`,
so special-encryption correctness removes the encryption before decoding. With two keys, the
inner ciphertext has length `4n + 2`; the second evaluator provides the pad of length
`n + (4n + 2)` required by the outer layer. Remove the outer layer, then the inner layer, and
decode the original plaintext. Longer key lists are excluded by the correctness contract. -/
theorem nestedSpecial_decCorrect (n : ℕ) : (nestedSpecial E₁ E₂ n).DecCorrect := by
  rw [MultiEnc.decCorrect_iff]
  intro ks hks o r
  have hlen : ∀ v : Fin n → Bool, (List.ofFn v).length = n := fun v => List.length_ofFn
  match ks, hks with
  | [], _ =>
    show decodeFin n (List.ofFn o) = some o
    exact decodeFin_ofFn o
  | [k], _ =>
    show (spDecStr E₁ n n (List.ofFn k)
      (spEncStr E₁ (List.ofFn k) (List.ofFn o) (List.ofFn r.1))).bind (decodeFin n) = some o
    have hp : (E₁ (pairEncode (List.ofFn k) (List.ofFn r.1))).length = n + n := by
      rw [hGE₁ n k r.1, List.length_ofFn]
    rw [spDecStr_spEncStr E₁ (hlen k) (hlen o) (hlen r.1) hp]
    exact decodeFin_ofFn o
  | [k₁, k₂], _ =>
    show (spDecStr E₂ n (innerLen.eval n) (List.ofFn k₁)
      (spEncStr E₂ (List.ofFn k₁) (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2))
        (List.ofFn r.1))).bind (fun c' =>
          (spDecStr E₁ n n (List.ofFn k₂) c').bind (decodeFin n)) = some o
    have hp₁ : (E₁ (pairEncode (List.ofFn k₂) (List.ofFn r.2))).length = n + n := by
      rw [hGE₁ n k₂ r.2, List.length_ofFn]
    have hc : (spEncStr E₁ (List.ofFn k₂) (List.ofFn o) (List.ofFn r.2)).length =
        innerLen.eval n := by
      rw [length_spEncStr E₁ (by rw [hp₁, hlen, hlen]), hlen, hlen]
      simp only [innerLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
        PolyExpr.eval_var]
      ring
    have hp₂ : (E₂ (pairEncode (List.ofFn k₁) (List.ofFn r.1))).length =
        n + innerLen.eval n := by
      rw [hGE₂ n k₁ r.1, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_var]
    rw [spDecStr_spEncStr E₂ (hlen k₁) hc (hlen r.1) hp₂, Option.bind_some,
      spDecStr_spEncStr E₁ (hlen k₂) (hlen o) (hlen r.2) hp₁]
    exact decodeFin_ofFn o
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

end TCSlib.Cryptography.SecureComputation

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
