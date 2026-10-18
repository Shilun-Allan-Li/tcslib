# Ch3–4 fill campaign — B4a: the TQBF configuration codec (`Complexity.exists_adjacency_codec_cnf`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 78116c5d5db075c9ce46ecec0b56735d1c600bef HEAD`
  succeeds. That commit contains:
  - the P4.3 statement layer and its closed gate (`audits/ch4-p43-*`, three rounds);
  - this brief's order list `briefs/orders/b4a-fill.txt` and pre-ship probe `audits/evidence/b4a/TQBFCodecProbe.lean.txt`.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/b4a-codec`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b4a-codec.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files; never edit another batch's file)

| Batch | Brief | Owns |
|---|---|---|
| R8.5c, the input length | `briefs/w1-fill-inputlength.md` | `TuringMachine/Build/InputLength.lean` |
| §12.8b record tables | `briefs/w1-fill-recordtable.md` | `TuringMachine/Build/RecordTable.lean` |
| §12.10 W2-S and W2-C | `briefs/w2-fill-oraclesim.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.10 W2-V | `briefs/w2-fill-certshell.md` | `TuringMachine/Build/CertShell.lean` |
| B5a, the code simulator | `briefs/b5a-fill.md` | `TuringMachine/CodeSimulator.lean`, `TuringMachine/Codes2Tape.lean`, `Diagonalization/EXPCOM.lean` |
| The ND code scheme | `briefs/ndcodes-fill.md` | `TuringMachine/NDCodes.lean` |
| B4a, the TQBF codec | `briefs/b4a-fill-codec.md` | `ClassPSPACE/TQBF.lean` (one target) |

Also in flight: §12.8 C continuation 3 (`Build/CfgRecord.lean`), B7 continuation 3
(`Logspace/QueryReshape.lean`, `Logspace/Reductions.lean`) and the B7 multiplication batch
(`Logspace/Mult.lean`); and a maintainer PR filling `POracle_eq_P_of_mem_P`
(`ClassOracle/Classes.lean`) and `baker_gill_solovay` (`Diagonalization/Relativization.lean`).
A parallel batch's work is invisible to your base and your screen.

## What this is

Fill **Claim 4.4(2) in its packaged quotient form** ([AB09, §4.2]; phase P4.3, audited true over
three rounds), the combinatorial half of cluster B4: for every machine a configuration
bit-codec of fixed length `C·(s + n + 1)` that factors through the input and the vertex quotient
`NDTM.coreSum`, and three CNFs for validity, adjacency and acceptance, with polynomial serialized
sizes. It is existence, not an algorithm: the uniform emitter is a private obligation of
`TQBF_PSPACEHard`, a later batch. **This is the only `TQBF` target in this batch.**

**Read first:** `ClassPSPACE/TQBF.lean`'s module docstring (the declared deviations) and the
target's sketch (binding, including its named fill obligations); `audits/ch4-p43-findings.md`,
`-r2-`, `-r3-` and `audits/ch4-p43-resolutions.md`; the Cook–Levin tableau
(`CookLevin/Hardness.lean`), `ConfigCount.coreCode_inj`, `ConfigGraph`'s `coreSum_stepWith` and
`outSummary`, and `Formulas/CNF*.lean`; `policy.md`; `workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/b4a/TQBFCodecProbe.lean.txt` (`audits/logs/w3-preship.log`): 0 errors; every
row the sketch names resolves from `TQBF`'s own import closure, so no import is needed.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `ClassPSPACE/TQBF.lean:160` | `Complexity.exists_adjacency_codec_cnf` | Cook–Levin marker discipline, carrying the input; three CNFs by per-gate universality | — |

- **Owned:** `ClassPSPACE/TQBF.lean`, for **this target's body only** and new `private` declarations. The file passes to the B4 summit batch afterwards.
- **Not yours:** `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete` (same file, not yours), every other file, and the facade.

### Proof route (binding; the docstring's sketch and its named fill obligations)

- **The codec** is the marker discipline of the Cook–Levin tableau row, now carrying the input:
  an input-content track of `n` bits, a one-hot input-position track of length `n + 2`, a one-hot
  state block (halt included), per work tape a window track of `2s + 1` cells (a three-valued
  symbol plus a head-marker bit), and a two-bit summary block; padded to exactly `C·(s + n + 1)`.
- **Injectivity** to `(x, coreSum)`: derive it from `ConfigCount.coreCode_inj` on the window tracks
  plus the content track. Factor the codec through `coreCode` where you can, and **cite**
  `coreCode_inj`; do not re-prove it. The output enters only through the summary block.
- **`φv`** conjoins per-track well-formedness (one-hot blocks, trit ranges, canonical padding);
  **`φacc`** reads the halt pattern and the summary block; **`φa`** conjoins content-track equality,
  locality of unmarked window cells, the marked-cell and neighbor updates by the transition table,
  the one-hot shifts by at most one, the state rewrite and the summary update (`outSummary`'s
  append table).
- **Sizes:** one-hot uniqueness by pairwise exclusion (quadratic); transition checks enumerated
  over the `(n + 2)·(2s + 1)^k` guarded cases, each a constant-size CNF by
  `Complexity.exists_cnf_boolFun` **per gate, never per row** (a whole-row truth table is
  exponential). The count is polynomial, not linear (round-2 finding 4); bound clause count,
  `numVars` and the serialized lengths through the chapter-2 serialization grammar (round-1
  finding 8), at base `s + n + 2` (round-2 finding 1).
- **Step-iff-adjacency** through `NDTM.coreSum_stepWith`; adjacency compares `coreSum (step c)`
  with `coreSum d`, so halted vertices are self-adjacent (round-2 finding 3).
- Named fill obligations: the codec with exact-length padding; the two injectivity lemmas; the
  validity characterization both ways; the per-position check enumeration; the three
  serialized-size ledgers; the step-iff-adjacency equivalence.

## Gate guidance (binding)

The P4.3 resolutions bind as amended over three rounds: the declared deviations (i)–(iii) of the
module docstring stand, and "the package is existence, not an algorithm". The uniform emitter
family is `TQBF_PSPACEHard`'s private obligation (round-3 note 1), not yours.

## Cited infrastructure (public and proved at the issue commit)

`ConfigCount.coreCode_inj`, `NDTM.coreSum`, `NDTM.coreSum_stepWith`, `outSummary`, `Cfg.InWindow`;
`Complexity.exists_cnf_boolFun`; `Std.Sat.CNF.serialize`, `serializeClause` and the chapter-2
serialization lemmas (`Formulas/CNFEncoding`); the Cook–Levin tableau's public lemmas
(`CookLevin/Hardness.lean`) where they apply. **Proved modulo: none.**

## Ground rules (binding)

1. **File ownership.** Only `ClassPSPACE/TQBF.lean`. Change only `exists_adjacency_codec_cnf`'s body, and add new `private` helpers
   there. List every new declaration with its role. A lemma that genuinely belongs in a shared
   file is written privately, flagged in `REPORT.md` as a promotion candidate, and promoted by
   the maintainer at integration (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged
   **"Fill appendix"** is expected wherever your proof refines or replaces a sketch's route.
3. **Status text.** Only your files' status text may change: the module's "Status" paragraph,
   its "Main results" tag, and your targets' "(statement)"/"(spec, fill pending …)" tags, each to
   "proved" (or to the new count, for a file you share with later targets); flag each. No new
   public declaration unless this brief names it.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
   it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout
   lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report each owned
   file's final line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and which proved targets are proved modulo them. A partial is expected and
   fine; an unreported gap is not.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/b4a-fill-screen-base.txt`:
**758 declarations, 358 pairs, 75,613 characters**.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/ClassPSPACE/TQBF.lean \
  TCSlib/Complexity/CookLevin/Hardness.lean \
  TCSlib/Complexity/CookLevin/Snapshot.lean \
  TCSlib/Complexity/Formulas/CNF.lean \
  TCSlib/Complexity/Formulas/CNFEncoding.lean \
  TCSlib/Complexity/Formulas/QBF.lean \
  TCSlib/Complexity/Formulas/QBFEncoding.lean \
  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean \
  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean \
  TCSlib/Complexity/ClassNP/SAT.lean \
  TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean \
  TCSlib/Complexity/CircuitComplexity/MeyerTab.lean
```

- **No new cross-file pair** with an owned-file declaration on one side, except a pair this
  brief pre-discloses (measure it and report it).
- **Known hazards:**
  - the Cook–Levin tableau (`CookLevin/Hardness.lean`) and the Meyer tableau: cite their public lemmas; never copy a tableau proof;
  - `coreCode_inj`: cite it, never re-prove it;
  - the CNF serialization lemmas: cite `Formulas/CNFEncoding`'s.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b4a-fill.txt` (**73 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b4a-fill.txt )
  ```

  **Base sorry-warning set, 10** (`audits/logs/b4a-fill-base-sorries.txt`, one entry per declaration).
  Yours: `ClassPSPACE/TQBF` 1 of its 4 (`exists_adjacency_codec_cnf`). Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**9** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/b4a/TQBFCodecProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/ClassPSPACE`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `SpaceComplexity/Constructible`: spaceConstructible_logSpace, spaceConstructible_linear
- `SpaceComplexity/ConfigGraph`: NSPACE_subset_exp_dtime, NL_subset_P, polyTimeReducible_of_mem_NL
- `TuringMachine/Build/CfgRecord`: exists_recordStepTM
- `ClassPSPACE/TQBF`: `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete` (B4's summit batch)

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.

## Known pitfalls at this pin (hard-won)

- `CNF` here is `Std.Sat.CNF` (`TQBF` opens `Std.Sat`): `Std.Sat.CNF.serialize`.
- `exists_cnf_boolFun` is per gate: a CNF for one fixed-arity Boolean function; compose gates,
  never tabulate a whole row.
- `omega` with products and powers as atoms (`ring` first); `decide` cannot evaluate `Nat.bits`.
