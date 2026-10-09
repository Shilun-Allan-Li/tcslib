# External audit pack — chapter-1/2 retrofit, epoch R1 boundary

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4d).
Epoch R1 = the three conservative retrofit batches, integrated and merged:
RB1 (`Build/Loop.lean`, PR #10), RB2 (`Build/Primitives.lean`, PR #9, plus
the maintainer's E1-resolution commit approved by the user's merge), RB3
(`CookLevin/Hardness.lean`, PR #10). This is the epoch-boundary audit the
workflow and the duplication governance require (`workflow.md` §4; audit
template failure mode 5). The gate closes on zero blockers and zero
majors; a debt major closes only by explicit human acknowledgment.

Audited at commit `c43f3a53` (branch `complexity/arora-barak-ch3-4`; the
tree also carries the out-of-scope §13 statement work — `Build/Zone.lean`,
`Codes2Tape.lean`, `Build/VirtualInput.lean`, the `Simulation`/`Embed`/
`Robustness` additions — which has its own gates and is **not** this
audit's object). **Every change is kernel-checked** (maintainer replay
evidence below); the audit object is the retrofit's **discipline**: that
deletions deleted only dead material, that public surfaces are
byte-identical, that every replacement is the strict simplification its
brief claimed, and that the epoch's duplication ledger is honest.

## Brief for the auditor

1. **Re-verify the freezes from the patches.** The three attached patch
   series are the complete change (plus the maintainer's E1 commit, whose
   diff is quoted below). Verify: every removed line lies inside a deleted
   `private` declaration (with its docstring), an authorized comment
   block, or a named re-pointed use line inside a `private` proof body —
   with exactly **one** exception, the E1 line (item 3). The public
   declarations of all three files must be reconstructible byte-for-byte
   from base `5588628c`; the maintainer's declaration-level comparisons
   attested 18/18, 9/9 (8 + `stateWord`), and 5/5 — re-establish
   independently.
2. **Audit the deletions as deletions of dead code**: 62 (Primitives) +
   8 (Loop) + 6 (Hardness) + the 2 Encoding-duplicate privates + the H4
   pair + `clCompute_comp`/`clBuffer_append_bit`/`clA5_pt_unaryLength`/
   `catalogPair_length`. The compile is the base safety argument (a live
   deletion fails loudly); your added value is the converse check — flag
   any deleted declaration that a *pending* consumer (the §4d plan, the
   12.2c dedup maps, the §13 layer) expected to survive.
3. **The E1 exception (human-approved).** RB2's agent correctly escalated:
   `catalogPair_inverse`'s last use sat in the public proof body of
   `computesFunInTime_stripLast`, which the batch freeze forbids touching.
   The maintainer's commit swapped that one line,
   `rw [catalogPair_inverse x u v hd]` →
   `rw [Turing.eq_pairEncode_of_pairDecode x u v hd]`, and deleted the
   private duplicate; the user approved by merging. Verify: the two lemmas
   are statement-identical (the public one is attached in context via the
   patch), the theorem's statement/signature/docstring are untouched, and
   the governance trail (escalation → flagged commit → human merge) is
   complete. This is the first exercise of the duplication policy's
   human-approval loop — report any gap in the trail as a major.
4. **Audit the three citations as strict simplifications**:
   (a) Loop's H4 — the forwarding lockstep now cites the public
   `Turing.emit_run` + `leftCfg_run` through a padded source (the glue is
   quoted in the RB1 report; `emLoopForwardCfg` the *definition* was
   retained because frame proofs consume it — verify that retention is
   right, not an oversight); (b) Hardness's `clFreshTM` — now literally
   `seamCompTM clWipeTM.tm 2 clReadTM.tm (.inl none)` with `clFresh_run`
   citing `seamCompTM_run_ofCfg`, the first §12 consumer outside `Build/`
   (verify the citation carries the displaced stream head through the
   general-configuration seam, and that the sanctioned `Build.Seam` import
   is the only import change in the epoch); (c) the Hardness swaps
   (`bufferedCompTM_computesInTime`, `bufferTape_append`,
   `clNative_fill true` — all 13 use sites are enumerated in the RB3
   report; verify the enumeration against the patch).
5. **The epoch duplication ledger** (failure mode 5, cumulative): all
   three deliveries declared "new copies: none", and the epoch's net
   effect on copied material is strictly negative (dead copies deleted;
   one cross-file duplicate pair collapsed by E1; the Loop↔Catalog and
   Primitives↔Catalog twin inventories untouched and still queued for
   12.2c). Verify no patch introduces a copy, and record the per-file
   totals: Loop 5,713 → 5,515, Primitives 7,636 → 6,374, Hardness
   8,904 → 8,725 (net **−1,639 lines, −85 privates** across the epoch).
6. **Verify the recorded errata**: the retrofit inventory's "two strict
   Encoding swaps" missed the public-body use that became E1 (now in the
   plan's decision log); the backlog's generated-kernel-artifact count
   corrects to 12, located in `Nondeterminism`/`EXP`/`SAT`, none in
   Hardness; Hardness's private count was 553, not ~538.
7. Report anything the epoch misstates, in the standard table and
   severity scale.

## Repository-side attestations (verify or challenge)

* Integration: `git am -3`, Codex authorship preserved on all seven agent
  commits; side-branch + PR discipline per the user's rule (PR #9 merged
  by the user with the flagged E1 commit; PR #10 merged by the user).
* Replays (per batch, on the side branches): RB1 — Loop + **Catalog** (the
  heavy importer) + the `TuringMachine` facade, exit 0 / 0 errors /
  0 sorries; RB2 — Primitives + facade likewise; RB3 — Hardness + the
  `CookLevin` facade likewise (logs
  `audits/logs/retrofit-rb{1,2,3}-integration-sweep.log`).
* Independent axiom prints: 8/8 (Loop — seven at the standard triple,
  `stateWord` axiom-free), 18/18 and 5/5 (standard triple), no `sorryAx`
  anywhere (`audits/logs/retrofit-rb{1,2,3}-axioms.log`).
* Style lint: 0 FAIL on every batch; the surviving size WARNs are the
  recorded retrofit/12.2c program.
* Delivery integrity: checksums verified on all three zips; bundles verify
  against the recorded base `5588628c`; RB2's and RB3's environment-shim C
  files **excluded** per the standing instruction (not compiled, not run,
  unreferenced by the patches; RB1's delivery carried none).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (failure mode 5 in force);
findings verbatim into `audits/retrofit-r1-findings.md`; the epoch gate
closes on zero blockers and majors, which completes the conservative
retrofit and arms the promoted 12.2c window (its precondition — the
shrunken `Build/` files — is now met).
