# Ch3–4 fill campaign — Cluster B7, continuation: targets 7–12 (N1, N3, N4, `comp`, `trans`, `MULT ∈ L`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor fdce1a557627b83872ce22b606e4eea17773914f HEAD` succeeds. That
  commit contains the P4.4b statement layer and its closed gate (PR #24), the order list,
  and **the first B7 delivery** (targets 1–6, integrated by PR; its report is
  `audits/b7-fill-agent-reports/fill-1-REPORT.md`). If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/ch34-b7`). Record the
  base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-b7-cont.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

**A continuation** (`workflow.md` §4, the continuation-brief precedent). The first B7 agent
proved targets 1–6 and stopped at its budget with no escalation and no admitted helper:
`OIS.run`, `OIS.compile_decides`, `mem_LOGSPACE_preimage` (N2), T3, T5 and `readIn_run`.
They are now on the campaign branch and are **frozen, proved material you cite**. Fill the
remaining **targets 7–12**: N1, N3, N4, `comp`, `trans` and `multLang_mem_LOGSPACE`. Read the
first delivery's report first: its "Continuation" section is written for you.

The original scope, for orientation: the **five audited-true P4.4 statements of cluster B7**
(plan §4e) and the **seven P4.4b contracts** they rest on. The received `LogProg` layer (Hydroxyi) gives the substrate:
`compile_space`, the decider bank, the counter/equality/rewind fragments, `arm_decides_poly`.
It does **not** give composition: a call's virtual input is read physically, and no ARM
instruction reads a non-unary input (`audits/ch34-p0-findings.md:184`). P4.4b closes both gaps:

| Layer | Contract | File |
|---|---|---|
| fragment (i) | `Complexity.LogProg.readIn_run`: read input bit `i` (binary index on a register) into the control state | `Logspace/InputAccess.lean` |
| class (N1) | `Complexity.implicitlyLogspaceComputable_id`: input random access in `L` | `Logspace/InputAccess.lean` |
| engine (ii) | `Complexity.LogProg.OIS.run`, `OIS.compile_decides`: the oracle-input simulator ([AB09, Fig. 4.3]) | `Logspace/PreimageHost.lean` |
| class (N2) | `Complexity.mem_LOGSPACE_preimage`: `{x \| f x ∈ C} ∈ L` | `Logspace/PreimageHost.lean` |
| class (N3, N4) | `Complexity.implicitlyLogspaceComputable_dropIdx`, `Complexity.ImplicitlyLogspaceComputable.compQ` | `Logspace/QueryReshape.lean` |

T3 is N2's corollary; `comp` comes from N2 and N4; neither is circular. Read in full:
`audits/ch4-p44-findings.md` (rows T1, T2, T5, T11, answers Q2 and Q8, note 3) and
`audits/ch4-p44-resolutions.md` with **`audits/ch4-p44-resolutions-addendum.md`** (the route
changes) — your **binding routes**; the P4.4b gate's `audits/b7-statements-findings.md` and
`audits/b7-statements-resolutions.md`, whose **gate guidance** is binding (section below);
`policy.md` (construction reuse, hand-built machines); `workflow.md` §4; plan §4e.

**Pre-ship check (maintainer, executed):** `audits/evidence/b7/B7StatementsProbe.lean.txt`
(output `.out`): 0 errors, no `sorry` of its own. It runs `readIn_run` on a concrete program
(hypotheses by `rfl`), `OIS` on a concrete decider (call nodes, the `nextPh` table, the lifted
step, both contracts), and derives T2, T3, T5 and `comp` from the contracts. Re-run after
the first delivery (`audits/logs/b7-fill-1-axioms.log`): 0 errors, and targets 1–6 now print
`[propext, Classical.choice, Quot.sound]`.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 7 | `Logspace/InputAccess.lean:532` | `Complexity.implicitlyLogspaceComputable_id` (N1) | program over 6 | 6 |
| 8 | `Logspace/QueryReshape.lean:160` | `Complexity.implicitlyLogspaceComputable_dropIdx` (N3) | ARM over the access bank | 7 |
| 9 | `Logspace/QueryReshape.lean:191` | `Complexity.ImplicitlyLogspaceComputable.compQ` (N4) | ARM over four oracles | 3, 7, 8 |
| 10 | `Logspace/Reductions.lean:95` | `Complexity.ImplicitlyLogspaceComputable.comp` | preimages along `compQ f` | 3, 9 |
| 11 | `Logspace/Reductions.lean:105` | `Complexity.LogspaceReducible.trans` | composition of witnesses | 10 |
| 12 | `Logspace/Mult.lean:71` | `Complexity.multLang_mem_LOGSPACE` | ARM over the access bank | 7 |

Targets 1–6 are proved (rows omitted): cite them, never edit them. **Owned files:**
`InputAccess.lean`, `QueryReshape.lean`, `Reductions.lean` and `Mult.lean`. `PreimageHost.lean`
is **not** yours: it is fully proved and frozen. Fill in the table's order. The facade is not
yours.

### Proof routes (binding; the contracts' sketches, amplified)

1. **`OIS.run`.** Encode `M`'s configuration `c` on `v`: work tapes/heads on `castSucc i`,
   `bits (p − 1)` on `q` (head `0`; `bits 0` at `p = 0`), host input head `1`, `c`'s output,
   state `(s, ask)` — `(s, work none true)` at `p = 0`. Induct on `n ≤` `M`'s first halt:
   ≤ 2 calls fix `inSym v p` (oracle laws); `work` applies `liftAct`, so the work registers
   move exactly as `M`'s tapes; `nextPh` realizes the clamped move (`inc_run` only when
   `p − 1 < |v|`; zero test + `dec_run` only when `p ≥ 2`; a phase change at the left blank).
   Intermediates are the received fragments' on `q`. Work heads: `|pos| < spaceUsed` by
   `abs_pos_lt_card_visited` + `visitedByTapeHead_mono` + `Finset.single_le_sum`. Template:
   `ImplicitEnum.{round, rounds, run}`. **The program is frozen**: a table defect is an
   escalation, never an edit.
2. **`OIS.compile_decides`.** Route 1 at the oracle `j, V ↦ [V ∈ As j]` (laws from `hA0`,
   `hA1`); `compile_space` with `OIS.lo`/`OIS.hi` (their sizes sum to `M.k (2S + 1) + W + 2`,
   `Fin.sum_univ_castSucc`); `CallOK` from route 1's call clause: virtual input
   `⟨x, bits i⟩` by `vword_whole₁` + `tapeWord_bufferTape`, clean run by `bank_cleanRun` then
   `CleanRun.mono` to `B`, `|bits i| ≤ W` by `length_bits_mono`.
3. **`mem_LOGSPACE_preimage`.** Per `x`, route 2 with `v := f x`, `M` = `C`'s decider at its
   time on `f x`, the bank `![length decider, bit decider]` (laws: `pairEncode_mem_indexLang`),
   `B := (c₀ + c₁) · logSpace (2|x| + 2 + |bits (|f x| + 1)|) + 1`; output
   `[indicator C (f x)] = [indicator {x | f x ∈ C} x]` (pre-ship N2'); bound
   `O(logSpace |x|)` by `log_poly_bound`, following `computesInSpace`'s arithmetic.
4. **T3.** `obtain ⟨f, hf, hB⟩ := h; rw [show B = ({x | f x ∈ C} : Language Bool) from
   Set.ext hB]; exact mem_LOGSPACE_preimage hf hC`. The docstring already gives this route
   (corrected at the gate, minor 3); no appendix.
5. **T5.** `Set.Subset.antisymm (fun B hB => mem_LOGSPACE_of_logspaceReducible (h.2 B hB) hC)
   LOGSPACE_subset_NL`. No nondeterministic construction.
6. **`readIn_run`.** Induction on the counter `k ≤ min i |x|`, input head on `k + 1`:
   `eq_run` (`r₁ := s`, so both heads stay within `|bits k|`); `k = i` → `yes` takes
   `inSym x (i + 1) = x[i]?`; else `no`: at the right blank (`k = |x| < i`) take `none`, on a
   letter step right and `inc_run` (`k + 1 ≤ |x|`); then `rewind_x` and `clr_run`. Close the
   final configuration with `Cfg.ext` (`hs` restores the counter, `hip` the input head).
7. **`implicitlyLogspaceComputable_id`.** Bound `⟨1, 1, _⟩`. **One** call-free program with a
   mode bit, compiled against `Dbl.nilTM` (`compile_space`, as `dblLang_mem`): validate
   `y = pairEncode z (bits r)` by aligned two-cell scans and a canonical tail, reading cells
   with route 6; walk a counter `k` over `dbl z`, comparing `bits k` with the tail in lockstep
   (the `cmpPlain_run` pattern) **while streaming, without copying the index into
   workspace**; answer cell `2k` (resp. `true`), or `false` at the separator. Reject a
   non-canonical index such as `[false]`. Each register holds at most `|bits (|y| + 1)|` bits;
   count each tape's origin and boundary cells (`[-1, W]` has `W + 2` cells) when applying
   `compile_space`, for an `O(logSpace |y|)` bound.
8. **`dropIdx`.** Bound: landed `dropIdx_length_le`. One ARM with a mode bit over
   `![inputBitLang, inputLenLang]` (`arm_decides_poly`; a `whole` call on `[r]` reads bit
   `v r`, pre-ship A1). On `h = ⟨z, bits q⟩`: validate `h`; **before accumulating `q`**,
   compare the tail length with `|bits |h||` (longer: `false`); decode `z = ⟨u, b'⟩`,
   `u = ⟨w, b⟩` (strides 2, 4; failure: `false`); answer by position arithmetic. Registers
   `≤ 4|h| + 4`.
9. **`compQ`.** Bound: landed `compQ_length_le`. One ARM with a mode bit over the four-oracle
   bank of pre-ship D4 (`{z | dropIdx (dropIdx z) ∈ ·}` of `f`'s languages, in `L` by route 3
   twice along route 8). On `h = ⟨w, bits p⟩`: (i) validate with the **overflow test before
   storing `p`**; (ii) `w = ⟨x, b⟩`, `b` canonical: **empty (the representation of `0`) or
   ending in `true`** (`canon_eq_bits`, `canon_bits`); (iii) `F := |f x|` by lifted length
   queries `j = 0, 1, …` while `j` is below the cap `C (|x|+1)^e`: `F` is the first failing
   query, or **the cap itself** when all succeed; a cap of `0` gives `F = 0` with no query. Handle
   overflow with `compQ_length_le`, not `dropIdx`'s shorter bound; (iv)
   `p < 2F`: lifted bit at `⌊p/2⌋` (`half`); `p ∈ {2F, 2F+1}`: separator; else `b`'s bit at
   `p − 2F − 2` from `h`; length: `p < 2F + 2 + |b|`.
10. **`comp`.** Pre-ship D2 verbatim: `comp_length_le` (private here) for the bound;
    `Set.ext (mem_indexLang_compQ_iff f p)` rewrites each language; `mem_LOGSPACE_preimage
    hf.compQ`. The docstring already gives this route (corrected at P4.4b); no appendix.
11. **`trans`.** `⟨g ∘ f, hf.comp hg, fun x => (hB x).trans (hC (f x))⟩`.
12. **`multLang_mem_LOGSPACE`.** ARM over `![inputBitLang, inputLenLang]` (pre-ship A2):
    validate `z = ⟨a', ⟨b', c'⟩⟩` (two aligned scans, three canonical fields); for
    `j < |a'| + |b'|` compute `column_j` by a double loop (`a'_p` at `2p`, `b'_q` at
    `2|a'| + 2 + 2q`), update the carry, compare with `c'_j` (zero past `|c'|`); reject a
    longer `c'` or a final carry. Registers `≤ 4(|z| + 1)`. Q8's invariant is a pure lemma
    over `bitsVal`; membership ↔ the product equation by `pairEncode_injective`,
    `bits_injective`.

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
  `mem_indexLang_compQ_iff`, `compQ_length_le`; `inputBitLang_mem`/`inputLenLang_mem`
  (modulo N1 until target 7).

Every module upstream of your files is sorry-free: the **"proved modulo" set is empty**, and a
complete delivery has no `sorryAx` (internal dependencies: the table's "Uses"). **Do not
cite** anything in `ConfigGraph`, `Path` or `ImmermanSzelepcsenyi`.

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/ch4-p44-findings.md`:

> | T1 | `ImplicitlyLogspaceComputable.comp` | The composite output bound is polynomial by the inequality in question 2. Simulating either query decider for `g` on the virtual paired input, and servicing virtual `f`-bits and boundaries with its two supplied deciders, uses logarithmic space. Malformed and oversized queries can be rejected within that bound; each simulation halts. |
> | T11 | `multLang_mem_LOGSPACE` | Validate all three canonical number fields and compute product columns with the bounded carry invariant in question 8. Compare every relevant output bit, reject excessive result length, and check that no carry remains. Zero operands and empty binary words need no extra space or hypothesis. |

From **Q2** (routes 8–10):

> On a query word `w`, parse the aligned pair and validate the canonical index. Before storing its numerical value, compare its bit-length and, if necessary, its bits against the displayed polynomial bound: values at or beyond the bound make both queries false.

From **Q8** (route 12):

> Validate canonical words, reject a result field longer than the sum of the two operand bit-lengths, and compare through that many columns using zero for missing result bits. This handles products whose bit-length is smaller than the maximum column count, including zero; “simultaneous end” must not mean that these lengths are always equal.

**Note 3's ledger** (malformed-query rejection, overflow handling, the paired layout, the
length boundary test) binds routes 8–9; **finding 2's** circularity rule holds by
construction (routes 1–3 cite nothing from `Reductions`). The P4.4b gate's resolutions bind
as amended there.

## Ground rules (binding)

1. **File ownership.** Only the four owned files; in each, only targets 7–12's bodies plus new
   `private` helpers. The first delivery's 14 private helpers in `InputAccess.lean` (`readModel`,
   `readAt`, `readFrame`, …) may be **cited and reused** but not changed. List every new
   declaration with its role.
2. **Statement freeze** over all twelve targets (1–6 now proved: their bodies are frozen too)
   **and every landed definition** (`RdPh`,
   `readTr`, `OIS.Ph`/`nextPh`/`liftAct`/`tr`/`call`/`prog`/`start`/`lo`/`hi`,
   `inputBitLang`, `inputLenLang`, `dropIdx`, `compQ`) and landed helper. No renames,
   re-signatures, restatements, attribution edits. Docstrings stay; flagged sketch
   appendices are allowed.
3. **Status text.** Only "(… spec, fill pending …)" tags and module-docstring "sorried" labels
   may change, to "proved"; flag each. New exports: none expected; any genuinely shared lemma
   (e.g. the aligned-scan facts of routes 8, 9, 12) goes public in `InputAccess` with one
   `## Main results` bullet, flagged.
4. **Escalation** on anything unprovable as stated (including a landed table defect): stop on
   that item, record the obstruction, continue with the rest.
5. **No touching other sorries.** Cite, never re-prove, proved material.
6. **Imports unchanged** (the landed edges are final). A Mathlib import only if a needed lemma
   requires it; flag it. No TCSlib import may be added.
7. **One proof per shared argument**: the bit and length languages of 7, 8 and 9 each come from
   **one** mode-parametrized program; the aligned-scan facts are one set of lemmas.
8. **Size.** No size cap: report each owned file's line count in `REPORT.md`. Do not add files
   (that would change imports).
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (partial delivery
   only, each with a "Proof sketch"), and which proved targets are proved modulo them.

## Duplication governance (binding)

Run the text-level screen **before and after** (base: the first delivery's after-screen,
`audits/logs/b7-fill-1-screen-after.txt`, **227 declarations, 58 pairs, 15,630 characters**;
its five in-file `InputAccess` pairs are justified in the first report):

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/SpaceComplexity/Logspace/{InputAccess,PreimageHost,QueryReshape,Reductions,Mult}.lean \
  TCSlib/Complexity/SpaceComplexity/{ImplicitPoly,UnaryLogspace,CounterProgSim,CounterProgSimRun,ConfigCount,SpaceClasses,Basic}.lean \
  TCSlib/Complexity/SpaceComplexity/Machines/{DblLang,ARMKit,ARMProof,Compile,Lib,FragDec,Frag,Bank,ParsePlain,Parse}.lean
```

- **No new cross-file pair** with an owned-file declaration on one side. Watch the three new
  files against each other and against `Mult` (aligned-scan loops).
- **Known hazards:** the engine's encoding lemma vs `ImplicitPoly::regCfg_cfg`/`DblLang::regCfg_K`;
  any new reachability relation vs `ARMProof::AReach.trans`/`DblLang::Rch.trans` (use
  `AReach` for ARMs; induct on `rrun` as `ImplicitEnum.rounds`); every `arm_decides_poly`
  assembly vs `UnaryLogspace::ltLang_mem`; route 3's bank set-up vs
  `ImplicitPoly::computesInSpace` (use `![…]` families and `indicator_indexLang_pairEncode`);
  route 6's sub-runs are citations of the four fragments, never re-walks.
- List every new in-file pair with a one-line justification; ≥ 90% is a copy: factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-b7.txt` (92 modules: the upstream closure of the
  five owned files and of every module downstream of them):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-b7.txt )
  ```

  Base sorry-warning set, **25**: yours `InputAccess` 1, `QueryReshape` 2, `Reductions` 2,
  `Mult` 1; elsewhere `Constructible` 2, `ConfigGraph` 3, `Inclusions` 2, `Savitch` 3,
  `Hierarchy` 4, `Path` 2, `ImmermanSzelepcsenyi` 3. `PreimageHost` has none.
- **Final checks:** (1) owned modules: zero errors, zero sorry warnings; (2) downstream
  (`Logspace/Path`, `Logspace/ImmermanSzelepcsenyi`, the `SpaceComplexity` facade): zero
  errors, sorry warnings exactly the base's (root `TCSlib` excluded); (3) re-run the pre-ship
  probe: 0 errors, and its axiom prints for the twelve targets now within
  `[propext, Classical.choice, Quot.sound]`.
- **Axiom prints** for all twelve targets: no `sorryAx`. **Lint:**
  `python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- **Downstream (C2):** `PATH_mem_NL`, `PATH_NLComplete`; `compl_PATH_mem_NL`, `NL_eq_coNL`,
  `NSPACE_compl_eq`.
- **Upstream, in the order list:** `spaceConstructible_logSpace`, `spaceConstructible_linear`,
  `savitch`, `PSPACE_eq_NPSPACE`, `spaceConstructible_poly` (B3); `NSPACE_subset_exp_dtime`,
  `NL_subset_P`, `polyTimeReducible_of_mem_NL` (S1b/B2); `NP_subset_PSPACE`,
  `SAT3_mem_PSPACE` (B2); `space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`,
  `SPACE_linear_ne_NP` (B6).

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 6/6 (targets 7–12), or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role (the mode-parametrized programs, the scan lemmas).
- [ ] Imports, requested shared lemmas, escalations, or "none"; appendices, status updates
      and any new-export bullet, each flagged.
- [ ] Duplication: both screens, in-file pairs justified, "new copies: none".
- [ ] File sizes; the final sweep tail; the re-run probe; twelve axiom prints; the lint line.
      The diff touches only the four owned files.

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
