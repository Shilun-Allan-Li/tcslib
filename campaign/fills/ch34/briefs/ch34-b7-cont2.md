# Ch3–4 fill campaign — Cluster B7, continuation 2: targets 8–12 (N3, N4, `comp`, `trans`, `MULT ∈ L`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 8e9a9b7eef75941a83ce036a195795c784758763 HEAD` succeeds. That
  commit contains the P4.4b statement layer and its closed gate (PR #24), **both earlier B7
  deliveries** (targets 1–6, PR #34; target 7 and its shared exports, PR #39; reports
  `audits/b7-fill-agent-reports/fill-{1,2}-REPORT.md`), and this brief's order list
  `briefs/orders/ch34-b7-cont2.txt`. If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/ch34-b7-cont2`). Record
  the base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-b7-cont2.zip`,
  containing `REPORT.md`, the full modified sources, a `git format-patch` series against your
  base, a git bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

**A second continuation** (`workflow.md` §4, the continuation-brief precedent). Targets 1–7
are proved and on the campaign branch:

- the first delivery: `OIS.run`, `OIS.compile_decides`, `mem_LOGSPACE_preimage` (N2), T3, T5
  and `readIn_run`;
- the first continuation: `implicitlyLogspaceComputable_id` (N1), with three shared exports
  and six `QueryReshape` support lemmas for target 8.

They are **frozen, proved material you cite**. Fill the remaining **targets 8–12**: N3, N4,
`comp`, `trans` and `multLang_mem_LOGSPACE`.

**Read the first continuation's report first** (`audits/b7-fill-agent-reports/fill-2-REPORT.md`).
Its "Continuation frontier" section is written for you, and its "Completed construction"
section describes the target-7 program, whose fragments you reuse. Its integration record is
`audits/b7-fill-integration-2.md`.

The scope, the received `LogProg` substrate and the P4.4b layer are as in the first
continuation brief, `briefs/ch34-b7-cont.md` ("What this is"). Read it for orientation. Read in
full:
- `audits/ch4-p44-findings.md` (rows T1, T11; answers Q2, Q8; note 3);
- `audits/ch4-p44-resolutions.md` with `audits/ch4-p44-resolutions-addendum.md`, the binding
  route changes;
- `audits/b7-statements-findings.md` and `audits/b7-statements-resolutions.md`, whose gate
  guidance binds you (below);
- `policy.md`, `workflow.md` §4 and plan §4e.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/b7/B7StatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/b7-cont2-preship.log`). It gives 0 errors and no `sorry` of its own. Targets
1–7 print `[propext, Classical.choice, Quot.sound]`, and **exactly targets 8–12** print
`sorryAx`. The maintainer's admission walk (`audits/logs/b7-fill-2-admissions.log`) shows
that each of targets 8–12 rests only on itself: no remaining target leans on another's
`sorry` or on a helper.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 8 | `Logspace/QueryReshape.lean:262` | `Complexity.implicitlyLogspaceComputable_dropIdx` (N3) | ARM over the access bank | 7 |
| 9 | `Logspace/QueryReshape.lean:293` | `Complexity.ImplicitlyLogspaceComputable.compQ` (N4) | ARM over four oracles | 3, 7, 8 |
| 10 | `Logspace/Reductions.lean:95` | `Complexity.ImplicitlyLogspaceComputable.comp` | preimages along `compQ f` | 3, 9 |
| 11 | `Logspace/Reductions.lean:105` | `Complexity.LogspaceReducible.trans` | composition of witnesses | 10 |
| 12 | `Logspace/Mult.lean:71` | `Complexity.multLang_mem_LOGSPACE` | ARM over the access bank | 7 |

Targets 1–7 are proved: cite them, never edit them.

- **Owned files:** `InputAccess.lean` (for new shared lemmas only; every landed declaration in
  it is frozen), `QueryReshape.lean`, `Reductions.lean` and `Mult.lean`.
- **Not yours:** `PreimageHost.lean` (proved and frozen) and the facade.
- Fill in the table's order. Targets 10 and 11 are short corollaries: do them **only after**
  9.

### Proof routes (binding; unchanged from the first continuation brief)

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

### The frontier you inherit (from the first continuation; all proved, cite them)

- **Public in `InputAccess`** (flagged exports, each with a `## Main results` bullet):
  - `Complexity.pairEncode_getD`: the positional lookup law for doubled first fields,
    separator cells and suffixes;
  - `Complexity.LogProg.inputLength_loop`: counts the physical host length with a
    length-query/increment loop, preserving the chosen register bound;
  - `Complexity.LogProg.alignedPair_loop`: validates an oracle-read word at an arbitrary
    positive stride. It uses distinct pointer/end registers and four bounded increment
    chains, and puts no canonicality restriction on the decoded fields. On success the pointer
    is just beyond the separator; on failure it reaches the caller's failure label. It assumes
    bit answers only at genuine in-range addresses.
- **Private in `QueryReshape`** (target 8's support):
  - `dropIdx_prefix_address`, `dropIdx_suffix_address`: the kept prefix and retained suffix
    lookups, for arbitrary discarded and retained payloads;
  - `query_index_bound`: a successful width check bounds the decoded index by twice the cap,
    including cap zero;
  - `query_suffix_value_le`;
  - `query_accumulator_bound`: bounds every reverse-scan partial accumulator after the width
    check;
  - `dropIdx_query_overflow`: both query answers are false when the canonical index is wider
    than the host-length bound.
- **Private in `InputAccess`:** the target-7 program's 43 helpers (`accessProg`, `accessPath`,
  the `access_*` step normalizations, …) and the first delivery's 14 `read*` helpers. You may
  **cite and reuse** them, but not change them.

**Resume at target 8**, as the report's frontier says.
- Instantiate the fragments in **one mode-parametrized ARM** over
  `![inputBitLang, inputLenLang]`.
- The missing work: the canonical outer-tail scan and the width test **before** accumulating
  the query value; a bounded decoder; the nested pair-shape scans (strides 2 and 4, through
  `alignedPair_loop`); the final position arithmetic; the full all-input run proof; and the
  `arm_decides_poly` assembly.
- Keep the register bound `4*|h|+4`, and keep both dropped and retained payloads arbitrary
  (note 10).

Then target 9:
- the four-oracle bank;
- the canonical inner tail;
- the polynomial output cap, including cap zero and the all-success cap case;
- `compQ_length_le` for overflow.

Targets 10 and 11 follow by their prescribed corollary routes. Target 12 needs its complete
multiplication ARM, with:
- a **proved** column/carry invariant (note 12: the probe only assumed it);
- canonical three-field validation;
- rejection of an excessive result length;
- the final carry check.

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
  `mem_indexLang_compQ_iff`, `compQ_length_le`, `inputBitLang_mem`/`inputLenLang_mem`
  (admission-free since target 7); targets 1–7; the three exports and the private frontier
  above.

Every declaration your targets may cite is sorry-free: the **"proved modulo" set is empty**,
and a complete delivery has no `sorryAx` (internal dependencies: the table's "Uses"). **Do not
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

1. **File ownership.** Only the four owned files. In each, change only targets 8–12's bodies,
   and add new `private` helpers, or flagged public shared lemmas in `InputAccess` (rule 3).
   - The earlier deliveries' private helpers are **cited and reused, never changed**: 14 + 43
     in `InputAccess`, 6 in `QueryReshape`.
   - List every new declaration with its role.
2. **Statement freeze** over all twelve targets, **every landed definition** and every landed
   helper.
   - Targets 1–7's bodies, and the three exports' statements and bodies, are frozen too.
   - The landed definitions: `RdPh`, `readTr`, `OIS.*`, `inputBitLang`, `inputLenLang`,
     `dropIdx`, `compQ`.
   - No renames, re-signatures, restatements or attribution edits.
   - Docstrings stay; flagged sketch appendices are allowed.
3. **Status text and exports.**
   - Only "(… spec, fill pending …)" tags and module-docstring "sorried" labels may change, to
     "proved"; flag each.
   - A genuinely shared lemma may go public in `InputAccess`, with one `## Main results`
     bullet, flagged. Examples: a canonical-tail scan used by 8, 9 and 12, or a bounded
     decoder.
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

Run the text-level screen **before and after**. The base is the first continuation's
after-screen, `audits/logs/b7-fill-2-screen-after.txt`: **273 declarations, 67 pairs, 17,169
characters**, reproduced byte for byte at this brief's issue tree. Its nine in-file pairs are
justified in the first continuation's report.

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
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-b7-cont2.txt`. It has **104 modules**: the
  upstream closure of the four owned files and of every module downstream of them.
  - It is 12 more than the first order list. Since then, `SpaceComplexity/Inclusions` (B2b)
    imports `CounterLoop`, `Seam`, `VirtualInput` and the Meyer tableau, and the facade
    reaches them.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-b7-cont2.txt )
  ```

  **Base sorry-warning set, 24** (`audits/logs/b7-cont2-base-sorries.txt`).
  - Yours: `QueryReshape` 2, `Reductions` 2, `Mult` 1. `InputAccess` and `PreimageHost` have
    none.
  - Elsewhere: `Constructible` 2, `ConfigGraph` 3, `CounterLoop` 1 (`expandTM_run_ofCfg`),
    `Inclusions` 1 (the private `b2b_host_contract`), `Savitch` 3, `Hierarchy` 4, `Path` 2,
    `ImmermanSzelepcsenyi` 3.

  Record the base list by name first.
- **Final checks:**
  1. The owned modules: zero errors, zero sorry warnings.
  2. Downstream (`Logspace/PreimageHost`, `Logspace/Path`, `Logspace/ImmermanSzelepcsenyi`,
     the `SpaceComplexity` facade; root `TCSlib` excluded): zero errors, sorry warnings
     exactly the base's.
  3. Re-run the pre-ship probe: 0 errors, with its twelve target prints now within
     `[propext, Classical.choice, Quot.sound]`.
- **Axiom prints** for all twelve targets: no `sorryAx`.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`,
  0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- **Downstream (C2):** `PATH_mem_NL`, `PATH_NLComplete`; `compl_PATH_mem_NL`, `NL_eq_coNL`,
  `NSPACE_compl_eq`.
- **Upstream, in the order list:**
  - B3: `spaceConstructible_logSpace`, `spaceConstructible_linear`, `savitch`,
    `PSPACE_eq_NPSPACE`, `spaceConstructible_poly`;
  - S1b/B2: `NSPACE_subset_exp_dtime`, `NL_subset_P`, `polyTimeReducible_of_mem_NL`;
  - B6: `space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`,
    `SPACE_linear_ne_NP`;
  - B2b's private `b2b_host_contract`, under `NP_subset_PSPACE`/`SAT3_mem_PSPACE`;
  - §12.8's `expandTM_run_ofCfg`.

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 5/5 (targets 8–12), or the partial frontier (rule 9); the base hash and the ancestor
      check.
- [ ] Every new declaration with its role: the mode-parametrized ARMs, the validation and
      decoding lemmas, and the multiplication invariant.
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
