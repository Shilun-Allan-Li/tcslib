# Loop bank-frame factoring: passed cumulative proposal, not applied

One private theorem, `emCall_bank_embed`, replaces the substantial repeated configuration/frame
case scaffold of `emCall_bank_initial` and `emCall_bank_final`. It uses the **already published**
`Turing.embedEmitCfg_mapState_eq` rather than re-proving the general R1 configuration identity.
Both old private declarations retain their complete exact statements, including the top-level
`let frame := …`; their old labels `0` and `3`, input/head/output data, and call witnesses are fixed.

The complete source to consider is **`Loop-cumulative-proposed-v2.lean.txt`**, 290330 bytes,
SHA-256 **`3ea69f4bf1ad933c4b3dc33debc4611d187dcae244b7938ae7f7f7c10e8472b8`**.
It includes the prior immutable passed terminal-certificate proposal. **No actual source was
edited.** The live source still matched the archived original at the final evidence check.

| Exact patch | Base | SHA-256 |
|---|---|---|
| `Loop-bank-only-v2.patch` (3 hunks) | Passed terminal proposal `2908372c…` | `33dde2b7a217923cfc9cc6267caf8cf6b2a84677500a13da2395076d03620f77` |
| `Loop-cumulative-v2.patch` (7 hunks) | Actual source `0e2e7ed7…` | `79831bdee8f0e7c48fbe24fa41fc8dcc7854b3aa82f67cbaec3143e10e5b7cc4` |

Both patches independently reconstruct the complete proposed source without using Git or patch
execution. Full hashes and source pins are in `summary-v4.json` and `context.json`.

## Semantic boundary and exact freeze

The new helper permits a target cleaned prefix `j` and cleaner state `q`, assuming every bank
other than `i` has the same cleaned-prefix membership as at prefix `i.val`. Its cleaner supplies
the target bank's exact three tapes and common head. The public relabelled reconstruction lemma
handles the whole configuration. The selected triple is read through the existing local layout
equation; the outside-layout split is proved **once**, with tape and head equality together.

The initial wrapper specializes `j = i.val`, `q = 0`, and reflexive membership equivalence.
The final wrapper specializes `j = i.val + 1`, `q = 3`; distinct finite indices have distinct
values, so `l < i+1 ↔ l < i` for each other bank. Thus the two wrappers preserve precisely their
different mathematical boundary conditions. Their proof bodies shrink from **3089 / 3685
characters (60 / 64 lines)** to **135 / 214 characters (4 / 7 lines)**, excluding the unchanged
headers/docs. These are literal source sizes, not a new copy-text screen.

Against the passed terminal milestone, only these **two** old proof bodies change and one new
private proof theorem is added. Against the original actual source, exactly **five** old proof
bodies change and two private proof helpers are added (the earlier terminal helper and this bank
helper). All **208** original declaration headers/docs, visibility, relative order, executable
definitions/tables/types, imports, coefficients and every other declaration body are literal-equal.
Public source declarations remain **21 → 21**; private **187 → 189**. The terminal helper and its
three consumers are byte-identical to the passed terminal proposal. No new public API, import,
host, executable definition or admission is introduced.

The v2 delimiter check distinguishes a statement's depth-zero `let … :=` from its eventual
`:= by`. Additionally, `let-header-witnesses.json` independently checks both complete old headers
against their exact old `:= by`/`dsimp only`/`Cfg.ext` proof marker. This guards against the
specific truncation mistake in failed v1; no header claim depends solely on the parser.

## Executed checks and controls

All runs used plain managed `leanelab.sh`, one sequential wrapper at a time, local budget three,
the parent's read-only complete `oleans-mig1-preflight-current2`, and temporary `/private/tmp`
sources. Exact commands, raw outputs, receipts and hashes are retained. No `.olean`, shared
snapshot or cache was written. Owner/import `.olean` pins are in `compiled-input-pins.json`.

| Check | Result |
|---|---|
| Complete cumulative source, native v2 | PASS, 0 errors, 12.41 s |
| Seven complete changed/new regions, strict v2 with original 30 guards | PASS, 0 errors, 14.03 s; superseded by stronger v4 |
| Seven complete regions, final strict **v4 with 31 guards** | PASS, 0 errors, 15.35 s |
| Seven roots and all eleven compiled descendants | All **18** use only standard axioms `propext`, `Classical.choice`, `Quot.sound` or subsets |
| Original 30 guards, 60 point/abstract pairs | Reused freshly executed, exact-checked evidence from immutable terminal milestone, same current2 context |
| Additional `Turing.FinTM.tapeBlocks`, both modes | Fresh positive PASS/0 errors; sealed expected FAIL/exactly 2 identified diagnostics; checker negative cases rejected |

All seven guards start **before docs and headers**, including let-bearing headers. The final
31-definition set is in `seal-coverage-v4.json`. The three default simp definitions `Action.apply`,
`Cfg.init` and `MultiTapeTM.initCfg` are disabled in every region. Exact instrumentation removal
recovers the proposed source bytes. No unsafe reducibility is used. Unchanged legacy helper
proofs remain outside the guards and are consumed opaquely.

The fresh inventory inspects all seven roots' compiled types/values and all eleven descendants:
six direct foreign ordinary definitions are all guarded. It separately inspects immediate foreign
definitions in the seven unchanged configuration/layout bridges used by the bank proof; this adds
`Cfg.mapState`, `bufferedCompTM`, `embedEmitCfg` and **`FinTM.tapeBlocks`**. All ten ordinary
definitions in this union are guarded. Reducible projections are explicitly classified as
abbreviations. Imported theorem proofs and other legacy helper proofs are not recursively audited.

Control reuse is exact-scoped in `controls-reuse.json`, including hashes of both original control
inputs, outputs, receipts and checker. Those 60 controls were run under the original 30-guard set;
the new definition has its own two fresh controls, rather than a claim that all 62 were rerun
together. The full 31-guard consumer check is fresh. The unrelated ineffective generated
`rewind_scan.match_1` remains outside this effective seal claim.

Manual inspection of the new helper and all five changed complete old proof regions finds no
explicit foreign-definition `simp`/`rw`/`unfold` argument. The helper unfolds only unchanged
same-home configuration/embedding wrappers and uses existing `emCall_layout_pair/triple` and
`embedEmitCfg_mapState_eq`. Its state/input/output reflexivity uses same-home constructors and
projections, and passes with all relevant ordinary foreign definitions sealed, including nested
`tapeBlocks`. Core/Mathlib entries are equations or theorems, not definition unfolding arguments.

## T3 disposition and limits

This proposal removes the identified **whole bank-initial/bank-final repeated scaffold**, rather
than stopping after the earlier twelve side-proof extraction. The earlier two selector
disjointness helpers remain unchanged. It does **not** assert that all T3 duplication, all Loop
families or the campaign's screen candidates are retired. No new screen ran here; the parent/C
classification and eventual actual-source screen remain separate. No debt acknowledgment or
external gate acceptance is granted. Parent applies only after its running replay ends and owns
the subsequent actual-source replay, source accounting and audit packet.

Failed attempts are retained. Native v1 failed (nine diagnostics): the same-home embedding
coercion needed to be exposed, and the initial builder mistakenly cut at the statement's `let`;
its freeze claim is **invalid for those headers**. V2 rebuilt from the immutable terminal base
and fixed both issues. Extra-guard v3 and its first controls failed only because the instrumentation
spelled `Turing.tapeBlocks` instead of the actual compiled `Turing.FinTM.tapeBlocks`; the checker
rejected those records. V4 uses the exact environment name and passes. There was also a setup
`__file__` assertion error before any proposal/Lean generation. No failed run is called a seal,
and the failed v1 compiler-generated `sorryAx` output is not evidence about the passed v2 source.

No Git mutation, source write, screen, snapshot/cache write, replay, commit or push was performed.
