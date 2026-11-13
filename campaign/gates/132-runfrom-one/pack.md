# Gate 132 · `MultiTapeTM.runFrom_one` in Deterministic, cited at one-step sites (PR #296)

**Not yet clear to merge** · PR #296 is a draft. Seyoon dispatches and merges.
The Lean commit is `677970b0e7bba401a707e409b5c275a664924f0b`, against campaign Lean `7b6bd1685a1436313dfbc13ce191f40c7dd065d3` (the campaign after #242).
Dedup family RO-1; Seyoon ruled the home `Deterministic` on 2026-11-12
(`campaign/maintainer/HANDOFF.md` §0 and the RO-1 entry of `campaign/duplication-ledger.md`).

## What the PR does

- `Deterministic` gains one public theorem, `Turing.MultiTapeTM.runFrom_one`:
  `tm.runFrom c 1 = tm.step c`, proved by the upstream `runFrom_succ_eq_step` and
  `runFrom_zero`, with a header bullet recording the RO-1 ruling.
- 59 other owners cite it at one-step sites, replacing:
  - the two-lemma rewrite `runFrom_succ_eq_step(')`, `runFrom_zero`;
  - `change … step …` unfoldings of `runFrom … 1`;
  - `Function.iterate_one` reads.
- Five copies are deleted:
  - EmitIterEmbed's public, Bool-only `Turing.runFrom_one`, which the general lemma replaces
    (ruled 2026-11-06, second round; a public removal; its four `EmitIterBody` users re-point);
  - four private copies: `Turing.xr_runFrom_one` (ExhaustiveReplay),
    `Turing.recordStep_runFrom_one` (CfgRecord), `Turing.NTimeDiag.qy_run_one`
    (NTimeDiagonalizer), and `Complexity.satRed_one` (SAT; its instance at `satRedTM`).
- Mechanical re-points in colleague-owned files (`CircuitComplexity/`, Meyer) were allowed by
  the same ruling, with an FYI line in the PR.
- No other statement, name, import or attribute changes. The one changed definition is the private
  `Turing.zr_cellContract`, and only its proof fields `run` and `cut` change.
- `TOKEN-DELTA.json` totals the tokens per changed declaration:
  - **Added:** `MultiTapeTM.runFrom_one` and tactic glue (`rw`, `_`, `exact`, `trans`), six
    `Nat.zero_add` and three `runFrom_succ_eq_step'`.
  - **Removed:** 215 `runFrom_zero`, 212 `runFrom_succ_eq_step(')`, 11 raw `MultiTapeTM.runFrom`,
    7 `change`, 4 `Function.iterate_one`, five `show (1 : ℕ) = 0 + 1 from rfl` rewrites and the
    private copies.
  - No foreign definition token is added.

Where the lemma would close a goal only by unfolding `runFrom` natively, the PR keeps the
campaign text. These are the `0 + 1` induction bases (six `simp` sites in Primitives) and
`foldCfg_run` in Bidirectional. Bidirectional is therefore byte-identical to the campaign and
outside the PR. The base-against-head seal comparison found the Bidirectional case, which
`2a9f32da` restored. The last commit, `677970b0`, removes the `show (1 : ℕ) = 0 + 1 from rfl`
rewrites that stood before the two-lemma rewrite at five sites (NDNormalForm, SeamLayout ×3,
NDCodeSimulator); `runFrom_one` matches `1` directly. The maintainer found them while
dispositioning the copy screen. Every check below ran at `677970b0`.

## Brief for the auditor

1. Check `runFrom_one`: its statement, proof, docstring, home and header bullet, and that it
   is the only public addition. Check that each deleted copy states the lemma or its
   instance (Bool alphabet, or `satRedTM`), and that no user of a deleted copy remains.
2. Check that no changed proof gained a foreign read. The whole-proof seals make every
   ordinary foreign definition a changed proof reaches irreducible (211 definitions; private
   heads cannot be named in an attribute and are left unsealed, listed in the summary).
   26 of 60 owners pass in full. The rest fail on reads that already exist on
   the campaign, so the same seals were run on the campaign sources (`seals-cmp-base`) with
   the same heads. The comparison (`SEAL-COMPARISON.json`) finds:
   - **New failing roots at head:** none.
   - **Roots that newly pass:** `canonTag_step` (CodeSimulator), `sim_step` (CounterProg), `emitterP2_body_round` (Primitives), `fl_leaf_run` (StepBlockForward), `timed_clock_pass` (Universal), `timed_flush` (Universal).
   - **Shared failing roots:** at head, each fails at a subset of its base sites, except three
     cascades: `emCall_track_initial` (Loop), `oracleHost_initial` (OracleSim) and
     `seekTM_observe` (StepBlock). In each, the base fails at the `change` or `from first` that RO1
     replaces, which aborts the block. At head the replacement passes, and the proof reaches an
     unchanged later line that already reads `Action.apply`, `MultiTapeTM.step`/`Cfg.mapState` or
     `seekCfg` output.
   - **Other:** one unrooted kernel error in ObliviousSetup. `setupCfg_allocation` cites
     `setupCfg_start_center`, which fails its seal at both commits.

   Confirm these classifications against the logs and sources.
3. Check the 422 paired controls (run in 5 parts of at most 100 errors): each sealed
   head closes natively and fails sealed.
4. Check the copy screen on the 61 RO1 owners (the 60 changed files and Bidirectional): BASE
   `declarations screened: 4368; copy pairs (target reproduces >= half of source): 3808; reproduced text: 963,965 chars`; HEAD `declarations screened: 4366; copy pairs (target reproduces >= half of source): 3058; reproduced text: 898,829 chars`. Check the dispositions of every new and removed pair
   (`PAIR-DISPOSITIONS.json`). Report any exact reusable proof a changed declaration should cite
   instead, and any one-step site that should, but does not, cite `runFrom_one`.

## Evidence

- `evidence/SOURCE.json`: the 240 changed or added declarations per owner, the deletions
  and the definition change.
- `evidence/REPLAY.json`: the merged-tree replay of the 403-module downstream closure of
  the changed files on the complete campaign snapshot after #242 (876 objects;
  prospective tree `bf9e88502021f844646b9041c4441f5d9e4b5118`). 403 passed, 0 failed. The 65 inherited admissions
  are in downstream modules whose sources are byte-identical to earlier campaign replays (the
  four RecordTable admissions are the campaign's own and unchanged); the changed proofs have none.
- `evidence/CHECKED-SUMMARY.json`:
  - seals, the comparison and controls;
  - metadata (standard axioms only);
  - lint: no new finding;
  - the argument sweep: 684 candidates, all reads present on the campaign (listed with their roots in FOREIGN-ARGUMENTS.json).
- `evidence/DATA-CARRIER.json` and its recovery map hold 1856 logical files:
  - every replay receipt and log;
  - seal and control sources and logs on both sides;
  - metadata, lint and both screen outputs;
  - all 61 population files at both commits and the scorer;
  - the campaign versions of the owners;
  - the patch and the drivers.

  Decode each gzip+base64 blob and check its SHA-256 and byte count.
- The checks ran on the cloud machine with the approved wrappers. The 20 PFR-dependent
  NewmanTheorem modules are not built there; none is in or imported by the closure.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate132-runfrom-one-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in
your reply.
