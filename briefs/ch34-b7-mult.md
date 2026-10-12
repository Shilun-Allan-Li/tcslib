# Ch3–4 fill campaign — Cluster B7, multiplication batch: target 12 (`MULT ∈ L`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor aa2373fe57b1b83407bec0ca70d0dbf0d2b9924c HEAD` succeeds. That
  commit contains:
  - the P4.4b statement layer and its closed gate (PR #24);
  - **all three earlier B7 deliveries**: targets 1–6 (PR #34), target 7 and three shared
    exports (PR #39), and target 8 with six more shared exports (the second continuation);
    their reports are `audits/b7-fill-agent-reports/fill-{1,2,3}-REPORT.md`;
  - this brief's order list `briefs/orders/ch34-b7-cont3.txt`.

  If the check fails, **stop**.
- **A parallel batch** works at the same time on targets 9–11 (`compQ`, `comp`, `trans`)
  (`briefs/ch34-b7-cont3.md`), owning `Logspace/QueryReshape.lean` and `Logspace/Reductions.lean`. Neither of you may edit the other's files or
  `InputAccess.lean`.
- Create your working branch off the campaign branch (suggested `fill/ch34-b7-mult`). Record the
  base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-b7-mult.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

**A batch split off from cluster B7** (user, 2026-10-11), so that multiplication runs in
parallel with B7's third continuation. Targets 1–8 of B7 are proved and on the campaign branch;
the parallel batch fills 9–11. Fill **target 12**, `Complexity.multLang_mem_LOGSPACE`:
[AB09, Example 4.7]'s `MULT = {⟨a, b, a·b⟩}` is in `L`.

The fill is an ARM over the physical-input access bank, like targets 7 and 8. **Read first:**
- the second continuation's report (`audits/b7-fill-agent-reports/fill-3-REPORT.md`), for the
  six shared exports and its target-12 frontier note;
- the first continuation's report (`audits/b7-fill-agent-reports/fill-2-REPORT.md`), whose
  "Completed construction" section describes the target-7 program and its fragments;
- the first continuation brief, `briefs/ch34-b7-cont.md` ("What this is"), for the received
  `LogProg` substrate and the P4.4b layer.

Read in full:
- `audits/ch4-p44-findings.md` (row T11; answer Q8);
- `audits/ch4-p44-resolutions.md` with `audits/ch4-p44-resolutions-addendum.md`, the binding
  route changes;
- `audits/b7-statements-findings.md` and `audits/b7-statements-resolutions.md`, whose gate
  guidance binds you (below), especially note 12;
- `policy.md`, `workflow.md` §4 and plan §4e.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/b7/B7StatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/b7-cont3-preship.log`). It gives 0 errors and no `sorry` of its own. Its
multiplication section elaborates route 12's layout and loop shape, but **assumes** Q8's
correctness invariant: you must prove it. Targets 1–8 print the standard triple, and target 12
rests only on itself (`audits/logs/b7-fill-3-axioms.log`).

## Owned file and target (modify this and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 12 | `Logspace/Mult.lean:71` | `Complexity.multLang_mem_LOGSPACE` | ARM over the access bank | 7 |

- **Owned file:** `Mult.lean`.
- **Not yours:** `InputAccess.lean` (frozen this round; ground rule 1), `PreimageHost.lean`,
  `QueryReshape.lean` and `Reductions.lean` (the parallel batch), and the facade.

### Proof route (binding; unchanged from the first continuation brief)

12. **`multLang_mem_LOGSPACE`.** ARM over `![inputBitLang, inputLenLang]` (pre-ship A2):
    validate `z = ⟨a', ⟨b', c'⟩⟩` (two aligned scans, three canonical fields); for
    `j < |a'| + |b'|` compute `column_j` by a double loop (`a'_p` at `2p`, `b'_q` at
    `2|a'| + 2 + 2q`), update the carry, compare with `c'_j` (zero past `|c'|`); reject a
    longer `c'` or a final carry. Registers `≤ 4(|z| + 1)`. Q8's invariant is a pure lemma
    over `bitsVal`; membership ↔ the product equation by `pairEncode_injective`,
    `bits_injective`.


### The frontier you inherit (three deliveries; all proved; cite them)

- **Public in `InputAccess`** (flagged exports, each with a `## Main results` bullet):
  - from the first continuation: `Complexity.pairEncode_getD` (the positional lookup law for
    doubled first fields, separator cells and suffixes), `Complexity.LogProg.inputLength_loop`
    (the physical host length), `Complexity.LogProg.alignedPair_loop` (aligned pair-shape
    validation at any positive stride, with no canonicality restriction on the fields);
  - **from the second continuation**, in `Complexity.LogProg`:
    - `register_update_le`: bound preservation after one register update;
    - `registerCopy_loop`: a bounded counting copy that preserves the source register;
    - `registerScale_loop`: a transfer into a destination at a fixed natural multiplier,
      including zero;
    - `canonicalTail_loop`: a strided tail scan that checks canonicality and width **before**
      numerical decoding, with the empty tail as zero. It consumes a numerical cap by halving,
      so it suits a **bounded** query index only;
    - `boundedDecode_loop`: the reverse binary decoder, given a bound on every suffix
      accumulator;
    - `indexedSeek_loop`: a bounded pointer and index walk within a strided segment, returning
      a hit or the segment's end.
- **File-local elsewhere:** `InputAccess`'s private helpers (the target-7 program's and the
  first delivery's `read*` helpers) and `QueryReshape`'s target-8 program (`dropARM` and its 43
  support declarations) cannot be cited from `Mult.lean`. Use `InputAccess`'s public exports.
  `dropARM` is a worked example of the ARM pattern to read, not to copy.

**What target 12 needs** (the second continuation's frontier):
- the complete multiplication ARM over `![inputBitLang, inputLenLang]`;
- a **proved** pure column and carry invariant over `bitsVal` (note 12: the probe only
  assumed it);
- validation of the three canonical fields (each empty, or ending in `true`), without decoding
  their values;
- rejection of an excessive result length, and comparison against zero-padded result bits;
- the final carry check;
- the full bounded all-input halting proof (registers `≤ 4(|z| + 1)`), and the
  `arm_decides_poly` assembly.

## Gate guidance (binding; `audits/b7-statements-resolutions.md`)

The P4.4b gate closed with every new statement true as stated. Its auditor's notes bind the
fill:

- **`readIn_run`** (note 4). Its head range does not depend on `i`. That is a head-motion
  bound only: constructing or storing an index still costs the index's bits.
- **N1** (note 5). Compare the query index with the counter while streaming, and never copy
  it into workspace. Reject a non-canonical index.
- **`OIS.run`** (note 7). The oracle laws are required only on genuine queries: length at
  `i ≤ |v|`, bit at `i < |v|`. Add no law for malformed or out-of-range queries.
- **`OIS.compile_decides`** (note 8). Keep the scalar radius `B`. It accommodates a
  non-monotone `sb`.
- **N3** (note 10). `dropIdx` decodes pair **shape** only. The discarded and retained payloads
  are arbitrary words: do not require them to be canonical indices.
- **N4** (note 11). Handle overflow with `compQ_length_le`.
- **Routes** (note 12). Keep the overflow, canonicality, carry and paired-layout
  obligations. The multiplication probe *assumes* Q8's correctness invariant, and route 12
  must **prove** it.

## Cited infrastructure (public and proved at the issue commit)

- `Machines/Compile` (`rrun`, `CallOK`, `compile_space`, `compileFinTM`, `tapeWord_bufferTape`),
  `Machines/Bank` (`bankTM`, `bankStart`, `bankK`, `bank_cleanRun`), `Machines/Clean`
  (`CleanRun.mono`); fragments `Machines/Lib` (`regCfg`, `rrun_add`, `rstep_noncall`,
  `inc_run`), `Machines/FragDec` (`dec_run`, `clr_run`, `Canon`, `canon_bits`),
  `Machines/Frag` (`half_run`, `eq_run`), `Machines/ParsePlain` (`xCfg`, `xAct`, `inSym`,
  `scanR`, `rewind_x`), `Machines/Parse` (`canon_eq_bits`, `cmpPlain_run`); `Machines/Bin`
  (`bitsVal_bits`, `bits_injective`, `length_bits_le_log`, `length_bits_mono`,
  `log_poly_bound`).
- ARM layer: `astep`, `AReach`/`AHalt` and combinators, `PreS`, `arm_decides_poly`,
  `indicator_eq_decide`; `Dbl.nilTM`; `ImplicitPoly.pairEncode_mem_indexLang` (its
  `ImplicitEnum.*`/`computesInSpace` are templates, not to be copied);
  `Turing.MultiTapeTM.abs_pos_lt_card_visited`, `visitedByTapeHead_mono`; `LOGSPACE_subset_NL`;
  `TuringMachine/Encoding` (`pairEncode_eq_dbl`, `pairDecode_pairEncode`,
  `eq_pairEncode_of_pairDecode`, `pairEncode_injective`, `length_pairEncode`).
- **Landed for you (proved):** `pairEncode_ne_nil`, `indicator_indexLang_pairEncode`,
  `LogProg.vword_whole₁`, `dropIdx_pairEncode`, `dropIdx_length_le`, `compQ_pairEncode`,
  `mem_indexLang_compQ_iff`, `compQ_length_le`, `inputBitLang_mem`/`inputLenLang_mem`;
  targets 1–8; the nine exports and the private frontier above.

Every declaration your targets may cite is sorry-free: the **"proved modulo" set is empty**,
and a complete delivery has no `sorryAx` (internal dependencies: the table's "Uses"). **Do not
cite** anything in `ConfigGraph`, `Path` or `ImmermanSzelepcsenyi`.

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/ch4-p44-findings.md`:

> | T11 | `multLang_mem_LOGSPACE` | Validate all three canonical number fields and compute product columns with the bounded carry invariant in question 8. Compare every relevant output bit, reject excessive result length, and check that no carry remains. Zero operands and empty binary words need no extra space or hypothesis. |

From **Q8** (route 12):

> Validate canonical words, reject a result field longer than the sum of the two operand bit-lengths, and compare through that many columns using zero for missing result bits. This handles products whose bit-length is smaller than the maximum column count, including zero; “simultaneous end” must not mean that these lengths are always equal.

The P4.4b gate's resolutions bind as amended there.

## Ground rules (binding)

1. **File ownership.** Only `Mult.lean`.
   - Change only target 12's body, and add new `private` helpers there.
   - `InputAccess.lean` is **not yours this round**, because a parallel batch shares it. If a
     lemma really belongs in a shared file, write it privately, flag it in `REPORT.md` as a
     promotion candidate, and the maintainer promotes it at integration (`workflow.md` §4,
     rule 1).
   - Every earlier delivery's helper is **cited and reused, never changed**.
   - List every new declaration with its role.
2. **Statement freeze** over all twelve targets, **every landed definition** and every landed
   helper.
   - Targets 1–8's bodies, and the nine exports' statements and bodies, are frozen too.
   - The landed definitions: `RdPh`, `readTr`, `OIS.*`, `inputBitLang`, `inputLenLang`,
     `dropIdx`, `compQ`.
   - No renames, re-signatures, restatements or attribution edits.
   - Docstrings stay; flagged sketch appendices are allowed.
3. **Status text.** Only target 12's "(… spec, fill pending …)" tags and the module-docstring
   "sorried" labels of your files may change, to "proved"; flag each. No new public
   declaration.
4. **Escalation** on anything unprovable as stated, including a landed table defect: stop on
   that item, record the obstruction, and continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports unchanged.** The landed edges are final.
   - A Mathlib import is allowed only if a needed lemma requires it; flag it.
   - No TCSlib import may be added.
7. **One proof per shared argument.**
   - The bit and length languages of 8 and 9 each come from **one** mode-parametrized program.
   - The aligned-scan facts are the landed `alignedPair_loop` and `pairEncode_getD`: cite
     them, never re-walk them.
8. **Size.** No size cap: report each owned file's line count in `REPORT.md`. Do not add
   files (that would change imports).
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states:
   - which targets are proved;
   - which `private` helpers remain `sorry` (partial delivery only, each with a "Proof
     sketch");
   - which proved targets are proved modulo them.

## Duplication governance (binding)

Run the text-level screen **before and after**. The base is the second continuation's
after-screen, `audits/logs/b7-fill-3-screen-after.txt`: **317 declarations, 72 pairs, 19,550
characters**, reproduced byte for byte at this brief's issue tree. Its in-file pairs are
justified in the earlier reports; the second continuation's five, at 51–89%, are target 8's
endpoint normalizations.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/SpaceComplexity/Logspace/{InputAccess,PreimageHost,QueryReshape,Reductions,Mult}.lean \
  TCSlib/Complexity/SpaceComplexity/{ImplicitPoly,UnaryLogspace,CounterProgSim,CounterProgSimRun,ConfigCount,SpaceClasses,Basic}.lean \
  TCSlib/Complexity/SpaceComplexity/Machines/{DblLang,ARMKit,ARMProof,Compile,Lib,FragDec,Frag,Bank,ParsePlain,Parse}.lean
```

- **No new cross-file pair** with an owned-file declaration on one side.
  - Watch targets 8, 9 and 12's ARMs against each other, and against the target-7 program's
    `access_*` normalizations.
  - The three ARMs share validation fragments: cite the landed ones.
- **Known hazards:**
  - every `arm_decides_poly` assembly against `UnaryLogspace::ltLang_mem`;
  - any new reachability relation against `ARMProof::AReach.trans` and `DblLang::Rch.trans`;
  - the multiplication invariant against `Machines/Bin`'s `bitsVal` lemmas: cite them;
  - re-walking `alignedPair_loop` or `inputLength_loop` inside a target.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- **The parallel batch is invisible to your screen.** A cross-file pair between your private
  helpers and the other batch's, found when both are integrated, is the maintainer's to
  factor. Avoid it where you can: build validation from the landed exports rather than new
  scanning loops.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-b7-cont3.txt`. It has **105 modules**: the
  upstream closure of the four B7 files and of every module downstream of them, at the issue
  tree. That is one more than the previous list: `CounterLoop` imports `SymbolLift` since
  R8.0b (PR #38).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-b7-cont3.txt )
  ```

  **Base sorry-warning set, 21** (`audits/logs/b7-cont3-base-sorries.txt`).
  - Yours: `Mult` 1.
  - `QueryReshape` 1 and `Reductions` 2 belong to the parallel batch: leave them.
  - Elsewhere: `Constructible` 2, `ConfigGraph` 3, `Savitch` 3, `Hierarchy` 4, `Path` 2,
    `ImmermanSzelepcsenyi` 3. (`CounterLoop` and `Inclusions` are now proved.)

  Record the base list by name first.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings.
  2. Every other module of the order list's final eight (`Logspace/InputAccess`,
     `Logspace/PreimageHost`, `Logspace/QueryReshape`, `Logspace/Reductions`, `Logspace/Path`,
     `Logspace/ImmermanSzelepcsenyi`, `Logspace/Mult`, the `SpaceComplexity` facade; root
     `TCSlib` excluded): zero errors, and sorry warnings exactly the base's minus yours. That
     is `QueryReshape` 1, `Reductions` 2, `Path` 2 and `ImmermanSzelepcsenyi` 3 (8 in these eight modules, **20** over the whole order list).
  3. Re-run the pre-ship probe: 0 errors, with your targets' prints now within
     `[propext, Classical.choice, Quot.sound]`.
- **Axiom prints** for all twelve targets: no `sorryAx`.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`,
  0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- **The parallel batch's targets:** `ImplicitlyLogspaceComputable.compQ`
  (`Logspace/QueryReshape.lean`); `ImplicitlyLogspaceComputable.comp`, `LogspaceReducible.trans`
  (`Logspace/Reductions.lean`).
- **Downstream (C2):** `PATH_mem_NL`, `PATH_NLComplete`; `compl_PATH_mem_NL`, `NL_eq_coNL`,
  `NSPACE_compl_eq`.
- **Upstream, in the order list:**
  - B3: `spaceConstructible_logSpace`, `spaceConstructible_linear`, `savitch`,
    `PSPACE_eq_NPSPACE`, `spaceConstructible_poly`;
  - S1b/B2: `NSPACE_subset_exp_dtime`, `NL_subset_P`, `polyTimeReducible_of_mem_NL`;
  - B6: `space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`,
    `SPACE_linear_ne_NP`.

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1 (target 12), or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role: the ARM (if any), the validation and decoding
      lemmas, and any pure invariant.
- [ ] Imports, requested shared lemmas, escalations, or "none"; appendices and status updates,
      each flagged.
- [ ] Duplication: both screens, in-file pairs justified, "new copies: none".
- [ ] File sizes; the final sweep tail; the re-run probe; the axiom prints of all twelve
      targets; the lint line. The diff touches only your owned files.

## Known pitfalls at this pin (hard-won)

- `ImplicitlyLogspaceComputable` is a `def` over `∧` (`.1`, `.2.1`, `.2.2`); `hf.compQ` is
  `Complexity.ImplicitlyLogspaceComputable.compQ`. Type preimages as
  `({x | f x ∈ C} : Language Bool)`, rewrite by `Set.ext`.
- Oracle answers are classical (`indicator_indexLang_pairEncode` uses `Classical.dec`): use
  `simp only [this, decide_eq_true_eq]`; `rw` fails inside `ite` (motive not type correct).
- An empty-register `whole` call presents `pairEncode u []` (`dbl u ++ [false, true]`); a call
  with **no** arguments presents `dbl u`. Nested pairs double positions at every level; `[]`
  is in no `indexLang`.
- In probes, a literal decider index needs its count: `callSegs (d := 2) ⟨0, …⟩`; and
  `Fin.lastCases` may need `(motive := …)` to elaborate.
- `Cfg.inputPos : Fin (|input| + 2)` starts at 1; 0 and `|input| + 1` are the clamped blanks
  (`moveInputPos`). `CallOK` needs argument registers as `bufferTape` words, heads at 0, and
  the host input head at 1 — the simulator never moves it.
- Fragment hypotheses are transition equations at named states with `P.call = none`; for
  `readIn_run` they are the two family hypotheses `htr`, `hc` (pre-ship R1 discharges them by
  `rfl`).
- `DecidesInSpace`'s `t` is a halting bound: `M` halts *by* `t`; simulate to its first halt.
- `arm_decides_poly` checks its register bound at every pre-halt step (temporaries included);
  `PreS` needs `Nodup` call arguments. Close oracle families by `fin_cases j`.
- No `nlinarith`/`linarith` in this closure: `ring` to expose products, then `omega` with
  products as atoms. `log_poly_bound A c B`: `Nat.log 2 (A (n+1)^c + B) + 1 ≤ K (Nat.log 2 n + 1)`;
  unfold `logSpace` before `omega`.
- `MultiTapeTM.indicator` is classical (start with `classical`); `omega` cannot see through sums
  or `Finset.card`. The linter needs a literal "Proof sketch" before every `sorry`.
