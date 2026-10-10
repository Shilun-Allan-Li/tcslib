# Ch3–4 fill campaign — Batch S1a: the configuration-graph lemmas (`SpaceComplexity/ConfigGraph.lean`, four targets)

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib`; branch **`complexity/arora-barak-ch3-4`**, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 447a6cc37f9bd79306d55a2768a1c920db091ae0 HEAD`
  succeeds. That commit lands the four shared declarations below and the order
  list. If the check fails, **stop**.
- Create your working branch off it (suggested name `fill/ch34-s1a`). Record
  the base commit hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR** (`workflow.md` §4): `fill-ch34-s1a.zip` with
  `REPORT.md`, the full modified source, a `git format-patch` series against your
  base, a git bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

Fill the **four audited-true graph lemmas** of phase P4.2 (plan §4e, the S1
split of 2026-10-10). Reachability is the choice-word run; a step's vertex
(core plus output summary) depends only on the vertex; [AB09, Claim 4.4(1)]
holds in acceptance form; and the packaged interface that Savitch, `NL ⊆ P`
and the exponential-time simulation consume. These are run inductions, a
splice and a pigeonhole count; no machine is built. The P4.2 gate passed in one
round (0 blockers, 0 majors). Read in full `audits/ch4-p42-findings.md` (its
§4 rows for these targets, finding 1 and Q1–Q4 are your **binding routes**),
`audits/ch4-p42-resolutions.md`, `policy.md`, `workflow.md` §4 and plan §4e.

The file's three summit statements are **S1b** (after the §12.8 library
extension), not yours; epoch C1 runs concurrently on disjoint files. **Four shared declarations were landed for you** at the issue commit, so that
the nondeterministic visited-set facts are instances, not copies:

- `Turing.NDTM.fixChoice` and `Turing.NDTM.stepWith_eq_fixChoice_step`
  (`TuringMachine/Nondeterministic.lean`). The slice is
  `tm.fixChoice b = ⟨tm.q₀, tm.tr b⟩ : MultiTapeTM`, and
  `tm.stepWith b cfg = (tm.fixChoice b).step cfg`.
- `Turing.MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps`
  (`SpaceComplexity/ConfigCount.lean`). For `p : ℕ → ℤ` with `p 0 = 0` and unit
  steps, every `z ∈ (range (t+1)).image p` has `|z| < ((range (t+1)).image p).card`.
- `Turing.MultiTapeTM.ConfigCount.mem_image_workTapePos_of_ne_none` (same
  file). For `cs : ℕ → Cfg …` from blank tapes, each step the identity or one
  `Action.apply`, a nonblank cell of `cs t` lies in
  `(range (t+1)).image (fun j => (cs j).workTapePos i)`.

**Pre-ship check (maintainer, executed):**
`audits/evidence/ch34-s1/S1aPreShip.lean.txt` (`.out`): 0 errors, 0 warnings;
both ND instances, route 2 end to end, the `Fin 3` cardinality identity,
truncation and padding, E1–E4, and the seven frozen statements.

## Owned file and targets (modify only what is listed)

Lines are at the issue commit (`ConfigGraph.lean` unchanged since `1852d20e`).

| # | Line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | 140 | `Turing.NDTM.reflTransGen_cfgStep_iff` | both inductions (Q2) | — |
| 2 | 156 | `Turing.NDTM.coreSum_stepWith` | slice + `core_step` + summary congruence (Q1) | — |
| 3 | 198 | `Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le` | window, splice, count, pad (Q3, finding 1) | 2 |
| 4 | 220 | `Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` | 3 forward; pad or truncate back (Q4) | 3 |

**Partial ownership.** You change only the four bodies, new `private` helpers
(inside `namespace Turing`, before their first use), the optional exports
E1–E4, and the status text (rule 2). Everything from `namespace Complexity`
(line 229) to the end stays **byte-identical** (the three summit statements,
docstrings and `sorry`s), and so do the five definitions.

### Sanctioned optional exports (audit §7 sanity lemmas; they ride the fill gate)

Add any that falls out of your proofs, with exactly these statements. Each
gets a docstring citing [AB09, §4.1.1] with a **Proof sketch**, and a *Main
results* bullet; flag each. Place E1 and E2 after `outSummary`, E3 after
target 2, E4 before target 3. A skipped one becomes a `private` helper.

```lean
/-- E1 -/ theorem outSummary_eq_accept_iff (u : List Bool) : outSummary u = .accept ↔ u = [true]
/-- E2 -/ theorem outSummary_append_congr {u v : List Bool} (h : outSummary u = outSummary v)
    (e : List Bool) : outSummary (u ++ e) = outSummary (v ++ e)
/-- E3 -/ theorem NDTM.coreSum_runWith (tm : NDTM k Bool S) (w : List Bool)
    {c d : Cfg k Bool S x} (h : coreSum c = coreSum d) :
    coreSum (tm.runWith w c) = coreSum (tm.runWith w d)
/-- E4 -/ theorem FinNDTM.not_acceptsWithin_zero (N : FinNDTM Bool) (x : List Bool) :
    ¬ N.AcceptsWithin x 0
```

### Proof routes (binding; the audit's derivations, amplified)

1. **`reflTransGen_cfgStep_iff`.** Forward: induct on the chain
   (`refl | tail`); `refl` is `[]`, and a `tail` edge `⟨b, rfl⟩` appends `[b]`
   via `runWith (w ++ [b]) c = stepWith b (runWith w c)` (`runWith_append`,
   `runWith_cons`, `runWith_nil`). Backward: induct on `w` generalizing `c`,
   with `runWith_cons` and `Relation.ReflTransGen.head ⟨b, rfl⟩`. No halting or
   finiteness is used (Q2).
2. **`coreSum_stepWith`.** Split `coreSum` with `Prod.mk.injEq`. Core:
   `rw [stepWith_eq_fixChoice_step]` twice, then **cite**
   `MultiTapeTM.ConfigCount.core_step`. Summary: `MultiTapeTM.step_output`
   twice, a private `outputSymbol` congruence from equal cores (the state,
   `Cfg.inputSymbol` and `Cfg.workTapeSymbols` are read off the core), and E2.
   The halted case needs no separate treatment.
3. **`acceptsWithin_of_spaceUsedWith_le`** (Q3 literally). Write
   `cfg j := N.tm.runWith (w.take j) (N.tm.initCfg x)`.
   - **Window.** Two private facts, both instances: `|z| < (visitedWith w init
     i).card` (`abs_lt_card_image_of_unitSteps`), and a nonblank cell of
     `runWith w init` lies in `visitedWith w init i`
     (`mem_image_workTapePos_of_ne_none`). Both rest on **one** prefix-step lemma:
     `w.take (j+1) = w.take j ++ (w[j]?).toList` (`List.take_succ`) and
     `runWith_append`. So each step is the identity or
     `(fixChoice b).step`, an `Action.apply` with unit head moves
     (`workTapePos_apply_le`). Bound the card by `Finset.single_le_sum` and
     `hs w hw`. Prefixes reach the cell bound through a private
     `visitedWith (w.take j) ⊆ visitedWith w`. Hence every `cfg j`, `j ≤ T`, has
     heads and nonblank cells in `[-s, s]`.
   - **Splice.** E3 on a common suffix. From equal vertices after `u` and
     `u ++ v`, the word `u ++ e` ends at the vertex of `u ++ v ++ e`, which is
     halted with summary `accept`, so it accepts by E1. Every new vertex is an
     old one, and windowedness reads only the core (Q3).
   - **Count.** Take the least `t` with an accepting length-`t` word whose
     prefix vertices are windowed (`Nat.find`). A repeat contradicts
     minimality. So
     `j ↦ (coreCode s (cfg j), sumCode (outSummary (cfg j).output))` is
     injective on `range (t+1)` (`coreCode_inj`), with
     `sumCode : OutSummary → Fin 3` a private injection. **`OutSummary` has no
     `Fintype` instance; add none.** Conclude `t + 1 ≤ N.configBound x.length s`
     by `Finset.card_le_card_of_injOn` and the probe's cardinality identity
     (the `of_spaceUsed_le` simp idiom, then `pow_mul`, `ring`). Make this
     **one** private lemma, "pairwise-distinct `coreSum`s of windowed
     configurations number at most `configBound`"; S1b reuses it.
   - **Pad.** `AcceptsWithin.mono` to the exact count. If `T` is already at most
     the count, pad the original word. Only the accepting branch stays halted
     (finding 1); **no sibling-halting argument**.
4. **`mem_iff_acceptsWithin_configBound`.** Forward: `h x` gives `T`, halting,
   the length-`T` space bound and the iff; apply target 3. Backward (Q4): if
   `V ≤ T`, pad; if `T < V`, `runWith w init = runWith (w.take T) init` by
   `List.take_append_drop`, `runWith_append` and `runWith_of_halt`
   (`HaltsWithin x T` at `w.take T`), then apply the iff. **Cite no C1a
   theorem** (`spaceUsedWith_append_of_halt` and `NSPACE.mono` are not needed).

## Cited infrastructure (public and proved at the issue commit)

- `TuringMachine/Nondeterministic.lean`: `NDTM.stepWith`, `runWith`,
  `runWith_nil`, `runWith_cons`, `runWith_append`, `stepWith_of_halt`,
  `runWith_of_halt`, `HaltsWithin`, **`fixChoice`**,
  **`stepWith_eq_fixChoice_step`**.
- `SpaceComplexity/ConfigCount.lean`: `MultiTapeTM.ConfigCount.core`,
  `core_step`, `coreCode`, `coreCode_inj`, `exists_eq_of_between`,
  **`abs_lt_card_image_of_unitSteps`**, **`mem_image_workTapePos_of_ne_none`**.
- Vendored (never edit): `Deterministic.lean` (`step`, `outputSymbol`,
  `step_output`), `Configuration.lean` (`Action.apply`, `Cfg.inputSymbol`,
  `Cfg.workTapeSymbols`, `workTapePos_apply_le`). And `ClassNP/NTIME.lean`:
  `FinNDTM.AcceptsWithin`, `AcceptsWithin.mono`.
- C1a's files, definitions only: `NDTM.visitedWith`, `spaceUsedWith`
  (`NondeterministicSpace`); `FinNDTM.DecidesInSpace` (`NSPACE`).
- Mathlib: `Relation.ReflTransGen.head`, `Nat.find`,
  `Finset.card_le_card_of_injOn`, `Finset.single_le_sum`, `List.take_succ`,
  `List.take_append_drop`, `List.length_take_of_le`.

No upstream `sorry` is cited, so the **"proved modulo" set is empty** and the
four targets carry no `sorryAx`. **Do not cite** the summit statements or
anything sorried.

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/ch4-p42-findings.md`, **§4** (lines are of snapshot `200f4693`):

> | `NDTM.reflTransGen_cfgStep_iff` (`ConfigGraph:140`) | A reflexive reachability derivation is realized by `[]`. Appending the witness bit for each additional edge extends the realizing word, by `runWith_append`. Conversely, induction on a choice word realizes each consumed bit as a `CfgStep` and composes the edges. Neither direction needs halting, finiteness, or a space bound. |
> | `NDTM.coreSum_stepWith` (`ConfigGraph:156`) | Equal cores give equal states and scanned symbols, hence the same action under the same choice. That action updates equal cores equally and appends the same optional emission to both outputs. The append table in question 1 preserves summary equality; the halted case is identity on both sides. |
> | `FinNDTM.acceptsWithin_of_spaceUsedWith_le` (`ConfigGraph:196`) | Apply the sibling-space hypothesis to an accepting witness word, obtaining a finite window for every prefix. Delete any segment between equal summary vertices; the remaining suffix has the same successive summary vertices and still accepts. A shortest such path has at most `configBound` vertices, hence fewer than that many steps, and the accepting word pads to the exact required length. Sibling halting is unnecessary. |
> | `FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` (`ConfigGraph:218`) | For membership, use the deciding budget and the preceding shortening lemma. Conversely, an accepting word at the configuration budget either pads to the deciding budget or has an already-halted deciding-length prefix with identical final output. In both cases the equivalence supplied by `DecidesInSpace` gives membership. |

**Finding 1:**

> The conclusion is nevertheless true: the accepting word alone can be padded.

**Q1** (target 2, E1, E2):

> For an arbitrary appended word `e`, an empty previous output gives `outSummary e`; an output `[true]` remains `accept` exactly when `e = []`; a dead output remains dead. Indeed, if `u ++ e = [true]`, then `u` must be a prefix of `[true]`, hence `u = []` or `u = [true]`. Thus no dead prefix can recover.

**Q3** (target 3):

> Every nonblank cell was previously visited, since initialization is blank and a transition writes only at a head. All prefix cores therefore satisfy the hypotheses of `coreCode_inj` in the wider window `[-s,s]`.
>
> Every vertex of the new path is a vertex of the old path: before the cut it is unchanged; afterwards it matches the corresponding suffix vertex. Window validity is consequently preserved.

**Q4** (target 4):

> If `V ≤ T`, acceptance at `V` implies acceptance at `T` by padding. If `T ≤ V`, write a length-`V` accepting word as `w.take T ++ w.drop T`; its prefix has length exactly `T`, so `HaltsWithin x T` applies.

**Q8, A13** (the reason for the window):

> | A13: remote nonblank cell | Two raw configurations differ only at a cell outside `[-s,s]`; their truncated codes can coincide. | `coreCode` is not globally injective. The actual-prefix window proof supplies precisely the missing side condition. |

## Ground rules (binding)

1. **File ownership.** Only what "Partial ownership" lists. List every new
   declaration with its role (the fill gate blind-restates them).
2. **Statement freeze.** No renames, re-signatures, restatements or attribution
   edits. Docstrings stay, with two flagged exceptions: sketch appendices, and
   **status text**: the four targets' "(spec, fill pending — phase P4.2)" tags,
   the module docstring's `**Status: statement skeleton (phase P4.2).**`
   sentence (line 29), and *Main results*' "(all sorried; phase-P4.2
   statements)" (line 65). The new status must still call the three class
   results sorried. *Main results* gains one bullet per delivered export.
   Nothing else changes.
3. **Escalation** on anything unprovable as stated: stop, record, continue.
4. **Leave every other sorry alone.**
5. **Cite, never re-prove**: the four shared declarations and `core_step`;
   `stepWith_eq_fixChoice_step` is the only `stepWith`/`step` comparison.
6. **Imports unchanged**; everything cited is reachable now. A Mathlib import
   is allowed only if a needed lemma requires it, flagged. No TCSlib import:
   escalate instead.
7. **One proof per shared argument**: one prefix-step lemma (both window
   facts), one counting lemma, one output-symbol congruence.
8. **Requested shared lemmas** (expected; each `private`): the window facts and
   the `visitedWith` prefix inclusion, for `NondeterministicSpace.lean` (C1a's).
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose
   `REPORT.md` states which targets and exports are proved, which `private`
   helpers remain `sorry` (allowed only then, each with a "Proof sketch"), and
   which proved targets are then proved modulo them (4 needs 3).

## Duplication governance (binding)

Run the text-level screen **before and after**:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean \
  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean \
  TCSlib/Complexity/TuringMachine/Nondeterministic.lean \
  TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean \
  TCSlib/Complexity/ClassNP/NTIME.lean \
  TCSlib/Complexity/TuringMachine/Deterministic.lean \
  TCSlib/Complexity/TuringMachine/Configuration.lean \
  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean \
  TCSlib/Complexity/TuringMachine/Oracle.lean
```

Pre-promotion (`29aa75be`): 96 declarations, 43 pairs, 3,980 characters,
none with `ConfigGraph`. Re-run at your base.

- **No new cross-file pair** with a `ConfigGraph` declaration on either side.
- **Known hazards.** `ConfigCount.visitedByTapeHead_mono` (about 114
  characters) already pairs at 54–57% with three ConfigCount proofs; your
  `visitedWith` prefix inclusion is that idiom, so report the pair (both
  declarations, the fraction) if it appears. Never transcribe
  `of_spaceUsed_le`'s injectivity block or `core_step`'s body (cite them), and
  do not reproduce `core_step`'s `hsym`/`hws` lines wholesale in the
  output-symbol congruence.
- **List every new in-file pair** with a one-line justification (90% or more is
  a copy: factor it). Quote both outputs; `REPORT.md` carries "new copies: none".

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**;
  `scripts/lean_check_tree.sh` for every check. **Bootstrap once** from
  `briefs/orders/ch34-s1a.txt` (upstream closure of `ConfigGraph` and of its
  downstream modules), `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < briefs/orders/ch34-s1a.txt )`,
  and record the base sorry-warning set.
- **Final checks:** (1) `SpaceComplexity/ConfigGraph`: zero errors and
  **exactly three** sorry warnings, at the summit statements (base lines 261,
  281, 301; report the shifted numbers). (2) Every downstream module, the
  `SpaceComplexity` and `ClassPSPACE` facades included (`TQBF`, `Savitch`,
  `Hierarchy`, `Logspace/Path`, `Logspace/ImmermanSzelepcsenyi`): zero errors,
  sorry warnings exactly the base's. The root `TCSlib` is excluded.
- **Axiom prints** (four targets, each export): at most `[propext,
  Classical.choice, Quot.sound]`, no `sorryAx`. **Lint:**
  `python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

In your file, the three summit statements (S1b). Upstream:
`NondeterministicSpace`, `NSPACE`, `SpaceClasses` (C1a) and `Constructible`
(B3). Downstream: `TQBF`, `Savitch`, `Hierarchy`, `Logspace/Path`,
`Logspace/ImmermanSzelepcsenyi`. **Never touch** C1a–C1d's files; a proof that
seems to *need* one is an escalation.

## REPORT.md checklist

- [ ] 4/4, or the partial frontier (rule 9); base hash and the ancestor check.
- [ ] Every new declaration with its role (the prefix-step lemma, the window
      facts, the counting lemma and `sumCode` identified); exports, or "none";
      status-text updates and bullets flagged; requested shared lemmas;
      imports, or "none"; escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none".
- [ ] Final sweep tail (ConfigGraph with exactly three warnings; downstream
      with the facades), the axiom prints, the lint line; the diff touches only
      `ConfigGraph.lean`, the summit section byte-identical.

## Known pitfalls at this pin (hard-won)

- **`coreCode` is not globally injective** (A13): every use carries the window
  hypothesis from the accepting word's *actual* prefixes. **Acceptance is
  halted plus `[true]`**, and a core-only splice is unsound (Q8 A5).
  `AcceptsWithin` demands exact length; `mono` pads with `false`s.
- `visitedWith` ranges over `range (w.length + 1)` of `w.take j`. The takes
  saturate past `|w|`, so the step is then the identity.
- `NDTM.initCfg` is a `@[simp] def` (prefer `simp only`);
  `coreSum c = (core c, outSummary c.output)` is `rfl`. `FinNDTM.configBound`
  is `3 * (…)`: after the `Fintype.card_*` simp, use `pow_mul`,
  `Nat.mul_comm (2*s+1) N.k` and `ring` (as in the probe).
- `List.length_take_of_le`, not `List.length_take` (`min`). Use the `notMem`
  spellings and `Function.update_of_ne`. Use `dsimp only` after `cases` on the
  state.
- The style linter requires a literal "Proof sketch" before **every** `sorry`.
