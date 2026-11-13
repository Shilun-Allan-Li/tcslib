# Gate 132 round 2 resolutions for #296

Round 1 audited `677970b0e7bba401a707e409b5c275a664924f0b` and returned **HOLD** with three minors
and six notes (`findings.md`, SHA-256
`43fedbe4e78930732a62a806e8c6af4254cc87bb93e00018e42f0b956aed217e`). No soundness defect and no
new failing seal root was found. The current PR head is
`ce427bde6ee5464a4146dce2b3add69b7a05677d`, against the same campaign Lean
`7b6bd1685a1436313dfbc13ce191f40c7dd065d3`. Seyoon selected Codex for this follow-up.

| Finding | Resolution |
| --- | --- |
| G132-01 · thirteen uncited one-step sites in eleven declarations | **Repaired** in `525bf933`. Each site now cites `MultiTapeTM.runFrom_one`: `satScan_run`, `satMap_run` (SAT); `cont_pair_empty`, `a2Borrow_run` ×2 (Nondeterminism); `clA5Map_run` (Hardness); `loopReplay_run`, `loopHost_borrow_run` ×2, `loopHost_accept` (Loop); `exists_canonStripTM` (CodeSimulator); `oraclePrepare`, `oracleRestore_cut` (OracleSim). In `oracleRestore_cut` the one-step hypothesis is rewritten (`rw [MultiTapeTM.runFrom_one] at hq`) before `Option.some.inj`, as proposed. The `change` cases in `oraclePrepare` became `rw`. |
| G132-02 · five sites in three owners outside the PR | **Repaired** in `525bf933`, and the owners joined the PR: `pre_scan` ×2 and `pre_copy` (CodePrefix; `pre_copy`'s duration `[].length + 1` is normalized with `List.length_nil` and `Nat.zero_add`), `counter_body` (CounterLoop, both runs of its local `first`), `certGuard_run` (CertShell). The population, the source inventory and every check were regenerated. |
| G132-03 · the declaration counts | **Corrected** in `pack-r2.md`. Round 1's `SOURCE.json` had 229 changed or added declarations: 228 theorem or lemma bodies, including the new `runFrom_one`, and the private definition `zr_cellContract`. The 240 seal targets were those 228 bodies plus 12 unchanged probes, a fixed set of Simulation and Primitives declarations that the reused gate 121 seal tooling always selects (`focus` in `scripts/seals.py` and `scripts/metadata.py`). `zr_cellContract` is not a seal target; its two edited proof fields only cite `runFrom_one`. Round 2's counts are in `pack-r2.md` and `r2-evidence/CHECKED-SUMMARY-r2.json`, broken down the same way. |

## How the rest of the family was found

G132-01 and G132-02 showed that round 1's search, which looked for the two-lemma rewrite and
`change`, missed other forms. Round 2 swept **the whole library** (every `.lean` file under
`TCSlib/` that mentions `runFrom`) in two independent ways, against a replayed head snapshot.

1. **Mutation.** Each `runFrom_succ_eq_step(')` occurrence, one at a time, is replaced by
   `Turing.MultiTapeTM.runFrom_one`, with the unused-simp-argument linter on. A mutant that still
   elaborates marks a candidate one-step closing. Each candidate is re-run with `runFrom` locally
   irreducible. A genuine one-step closing still passes; a step-shift rewrite or a definitional
   closing fails.
2. **Irreducibility.** Each file is elaborated with `attribute [local irreducible]
   Turing.MultiTapeTM.runFrom` after its imports. A one-step run that a proof closes only by
   unfolding `runFrom` natively then becomes an error. The classifier
   (`sweep-classify/irr-classify.py`) parses the duration argument of every `runFrom` in each
   error's message and goals; context hypotheses are excluded, and OracleTM's oracle argument is
   skipped. An error is a one-step row when a duration is a closed term equal to 1: `1`, `0 + 1`,
   `Nat.zero + 1`, `[].length + 1`, a constant function applied, and so on.

The repairs came in three commits:

- **`525bf933`** repairs the sites the first pass found at `677970b0`: Codex's thirteen, four of
  G132-02's five, three more successor-rewrite sites in `WindowRun`, and 33 more native one-step
  unfoldings, some in the same declarations. These are the first pass's 40 one-step rows, less
  six G132-01 and G132-02 sites and RecordTable's two-step site. The first classifier recognised only a literal `1`,
  so `pre_copy` (`[].length + 1`) was repaired from Codex's report, not found by the sweep.
- **`43c5d693`** changes only the docstring of the private `Reductions.acceptCfg_step`. Citing
  `runFrom_one` there took its proof from 20 to 21 lines, and the style rule asks a proof that
  long for a **Proof sketch.** The docstring now has one. The statement and proof are unchanged
  (`SOURCE.json` lists it under `header_changed` because its header includes the docstring).
- **`ce427bde`** repairs eight more one-step runs that the classifier found once it evaluated
  closed durations. Their durations are written `0 + 1`, `Nat.zero + 1` or `(fun _ => 1) n`:
  - the `zero` cases of inductions in `inputLength_round` (InputLength), `loop_scan_left` and
    `emCall_clear_origin` (Loop), `arMoveCfg_run` and `arWriteCfg_run` (AlphabetReduction), and
    `clockStageCfg_run` (ObliviousCandidate, which also cites `runFrom_zero` for its zero-step
    source run);
  - the one-bit branch of `succFieldTM_trace` (StepBlock), a `change … step d`;
  - the one-step machine of the empty-output branch in SingleTape.

In all, round 2 changes 53 declarations in 29 files (`R2-CHANGED-DECLS.txt`, and
`patch/round1-to-head.patch` in the carrier). Nine owners are new to the PR: Reductions,
CodePrefix, CertShell, `Contract/Basic`, CounterLoop, WindowRun, AlphabetReduction, InputLength
and SingleTape. The PR now changes 69 files. Every repaired file elaborates natively, and under the
unused-argument linter no `runFrom_one` citation is unused.

## The final sweep at the head

The library-wide sweep ran again, with the evaluating classifier, on the snapshot replayed at
`ce427bde`. Its results are in `r2-evidence/SWEEP-FINAL.json`.

- **Mutation:** 728 site mutations in 96 files, 21 of them passing natively. Each passing mutant
  was re-run with `runFrom` irreducible, and none is a genuine one-step closing:
  - seven need `runFrom` unfolded natively, so their originals close a step shift or a
    definitional equation (including Bidirectional's `foldCfg_run`);
  - eight are shifts at a general duration (`runFrom (step c) u` against `runFrom c (u + 1)`) in
    declarations that already fail when `runFrom` is irreducible, for reasons the second pass
    classifies;
  - the six marked one-step are a docstring in StepBlock (1473), three OracleTM artifacts
    (mutating `Oracle.runFrom_succ_eq_step'` renames OracleTM's own theorem, so 378 resolves to it
    and 300 loses its reference; 368 is a docstring), and SingleTape 2088, whose mutant does fail.
- **Irreducibility:** 230 errors in 138 files. The one one-step row is RecordTable 2325, the
  disclosed two-step site below. Two more errors (Inclusions 225 and 2331) mention `runFrom … 1`
  only in a context hypothesis; their goals are zero-step `rfl`s.
- **Explicit reads:** the 781 explicit-read candidates of the argument sweep (386 distinct) all
  occur in the same declarations on the campaign base.
- **A parsing gap, disclosed.** Lean 4.25 writes some error headers as `error(<tag>): …`, and the
  sweep, confirmation and classifier scripts read only `error: …`. The only tagged errors in any
  sweep or confirmation log are four `lean.unknownIdentifier` errors, at SingleTape 2089 and Oracle
  301 in two mutation jobs and their confirmations; these are why SingleTape 2088 and Oracle 300
  were read as passes. No irreducibility log has a tagged error, so the one-step classification is
  unaffected. `SWEEP-FINAL.json` lists the four errors and a disposition for every row.

## Left as they are, disclosed

These sites unfold `runFrom` natively but are not one-step runs. They are outside RO-1, and the
PR does not change them.

- **Two-step and longer runs:**
  - `RecordTable` 2325 and 2336, `change … step (runFrom d 1)`, inside a two-step and a three-step run;
  - Primitives' six `show (2 : ℕ) = (0 + 1) + 1` sites (549, 661, 954, 1887, 1937, 8166);
  - `CodePrefix.pre_scan`'s two-step branch (166, 168), which the head seals show.
- **Zero-step bases:** `simp [MultiTapeTM.runFrom]` at EXP 2553, Nondeterminism 2459,
  Composition 128, Encoding 388 and MathlibBridge 881, all in `zero` cases of inductions.
- **General iteration:** StepBlock 1931 (`Function.iterate` for arbitrary `t`) and EmitIterEmbed
  279 (`iterate_succ_apply`). Deterministic's own `runFrom` lemmas are the API.
- **Bidirectional `foldCfg_run`:** its mutant passes natively but fails when `runFrom` is
  irreducible, so its base is a definitional closing, not a one-step citation site. It is
  byte-identical to the campaign and outside the PR, as in round 1.
- **OracleTM:** `Oracle`'s `unfold runFrom` (240) and its lemmas are about OracleTM's own `runFrom`.

**Limitations.**
- In the irreducibility pass an error ends its tactic block, so a one-step site later in the
  same block is reached only once the earlier error is fixed. The final sweep therefore ran on
  the repaired head.
- A duration that equals 1 only through a hypothesis, such as a variable `n` with `hn : n = 1`,
  is not a closed term, and the classifier does not count it.

## Notes N1 to N6

Each is accepted within its stated scope. This round's evidence replaces their source, replay,
seal, control, lint and screen inputs. N3's qualification stands: the seals establish a
comparative result (no new failing root), not universal rule-10 compliance.
