# Ch3–4 fill campaign — Epoch C1, Batch C1c: oracle locality, the oracle NDTM embedding, and `P ⊆ Pᴼ ⊆ NPᴼ`

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Before you start, confirm that
  `git merge-base --is-ancestor 44853c6f3177fed8f7f8d2288210593e9c094f7e HEAD`
  succeeds. That commit lands the order list and the maintainer's shared
  lemmas; the pre-ship check cited below is on the branch tip. If the check
  fails, **stop**.
- Create your working branch off the campaign branch (suggested name
  `fill/ch34-c1c`). Record the base commit hash in `REPORT.md`. Never
  rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch34-c1c.zip`. It contains `REPORT.md`, the three full modified
  sources, a `git format-patch` series against your recorded base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

Fill the **ten audited-true statements** epoch C1 assigns to this batch
(plan §4e): the locality layer of the relativization theorem ([AB09,
Thm 3.7]; [BGS75, §3]), the oracle NDTM embedding, and `P ⊆ Pᴼ ⊆ NPᴼ`. No
machine construction is needed. P3.1 passed in round 1, P3.2 in round 2 (the
locality layer survived round 1 unchanged). Read in full: your **binding
routes**, `audits/ch3-p32-findings.md` (verdicts 1–7, answer 5) and
`audits/ch3-p31-findings.md` (your other three targets' rows); both
resolutions files; `audits/ch3-p32-pack.md` item 6 (the promotions you now
carry out); `policy.md`, `workflow.md` §4, plan §4e. Batches C1a, C1b, C1d
and S1 run concurrently on disjoint files; C1d owns the downstream
`Diagonalization/Relativization.lean`.

The maintainer's pre-ship check, `audits/evidence/ch34-c1/C1cPreShip.lean.txt` (output `C1cPreShip.out`),
elaborates with 0 errors: every call shape, the route-1 step proof, E2–E3,
and every statement prescribed below, in their home contexts. Reuse its
patterns.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit. K and E1–E5 are defined below.

| # | File:line | Target | Uses |
|---|---|---|---|
| 1 | `TuringMachine/OracleNondeterministic.lean:278` | `Turing.OracleTM.toOracleNDTM_runWith` | — |
| 2 | `ClassOracle/Classes.lean:110` | `Complexity.P_subset_POracle` | — |
| 3 | `ClassOracle/Classes.lean:123` | `Complexity.POracle_subset_NPOracle` | 1 |
| 4 | `TuringMachine/OracleAgreement.lean:158` | `Turing.OracleTM.queriesWithin_length_le` | — |
| 5 | `TuringMachine/OracleAgreement.lean:240` | `Turing.OracleNDTM.length_le_of_mem_queriesAlong` | E5 |
| 6 | `TuringMachine/OracleAgreement.lean:199` | `Turing.OracleNDTM.runWith_eq_of_agree_length_lt` | K, E5 |
| 7 | `TuringMachine/OracleAgreement.lean:217` | `Turing.OracleNDTM.runWith_eq_of_agree_queriesAlong` | K |
| 8 | `TuringMachine/OracleAgreement.lean:109` | `Turing.OracleTM.runFrom_eq_of_agree_length_lt` | K, 1 |
| 9 | `TuringMachine/OracleAgreement.lean:132` | `Turing.OracleTM.runFrom_eq_of_agree_queriesWithin` | K, 1 |
| 10 | `TuringMachine/OracleAgreement.lean:146` | `Turing.OracleTM.length_le_of_mem_queriesWithin` | — |

**Fill order:** `OracleNondeterministic.lean` (target 1, then E1–E5),
`Classes.lean`, `OracleAgreement.lean`. **`Classes.lean` is shared:** you own
it for the epoch but change only targets 2 and 3 (plus at most one `private`
helper above them); its four B1 statements stay byte-identical.

### Sanctioned public exports in `OracleNondeterministic.lean` (they ride the C1 fill gate)

These are pack item 6's natural-home promotions. Insert them immediately
after target 1, with exactly these names and statements. Give each a
statement-prose docstring and a **Proof sketch**, and flag each in
`REPORT.md`. The gate blind-restates them.

```lean
/-- E1 -/ def OracleNDTM.fixChoice (N : OracleNDTM k Symbol State) (b : Bool) :
    OracleTM k Symbol State := ⟨N.q₀, N.qQuery, N.qYes, N.qNo, N.tr b⟩
/-- E2 -/ theorem OracleNDTM.stepWith_eq_fixChoice_step (N : OracleNDTM k Symbol State)
    (O : Language Symbol) (b : Bool) (cfg : Cfg (k + 1) Symbol State input) :
    N.stepWith O b cfg = (N.fixChoice b).step O cfg
/-- E3 -/ theorem OracleNDTM.stepWith_eq_of_ne_qQuery {N : OracleNDTM k Symbol State}
    (O₁ O₂ : Language Symbol) {b : Bool} {cfg : Cfg (k + 1) Symbol State input}
    (h : cfg.state ≠ some N.qQuery) : N.stepWith O₁ b cfg = N.stepWith O₂ b cfg
/-- E4 -/ theorem OracleNDTM.runWith_workTapes_invariant (N : OracleNDTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) (w : List Bool) :
    (∀ i, |(N.runWith O w (N.initCfg x)).workTapePos i| ≤ (w.length : ℤ)) ∧
      ∀ i (z : ℤ), (w.length : ℤ) ≤ |z| → (N.runWith O w (N.initCfg x)).workTapes i z = none
/-- E5 -/ theorem OracleNDTM.queryString_runWith_length_le (N : OracleNDTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) (w : List Bool) :
    (OracleTM.queryString (N.runWith O w (N.initCfg x))).length ≤ w.length
```

### Proof routes (binding; the audits' derivations, amplified)

1. **Target 1.** A private step lemma after `toOracleNDTM_wellFormed`,
   `M.toOracleNDTM.stepWith O b cfg = M.step O cfg`, by
   `unfold OracleNDTM.stepWith OracleTM.step` and `cases hs : cfg.state`
   (halted, query and ordinary cases agree since `toOracleNDTM.tr b = M.tr`).
   Then induct on `w` generalizing `cfg`: `show` the definitional cons forms,
   rewrite with the step lemma, apply `ih`. This is **the batch's only
   `stepWith`-against-`step` comparison**.
2. **E1–E5: ND from the deterministic machine, per choice bit.** **E2** is the
   step lemma at `N.fixChoice b` (both sides are `OracleNDTM.stepWith` at
   definitionally equal fields). **E3** is `rw [E2, E2]` and
   `OracleTM.step_eq_of_ne_qQuery`. **E4** comes from a private
   generalization: heads within `n` and blank cells at `|z| ≥ n` in `cfg`
   persist to `runWith O w cfg` at `n + w.length`, by induction on `w`
   generalizing `cfg` and `n`, each step being E2 followed by the public
   `OracleTM.workTapePos_step_le` and `workTapes_step_eq_of_ne`. **Never
   re-prove a per-step fact by unfolding `stepWith`.** **E5** is E4 plus a
   private blank-cell bound (a blank query cell `n` gives
   `(queryString cfg).length ≤ n`, via `Nat.find_le`). The deterministic twins
   are `Oracle.lean`'s private `runFrom_workTapes_invariant` and the tail of
   `queryString_length_le`: **write yours directly, never transcribe**, and
   never edit `Oracle.lean`.
3. **Targets 2 and 3.** From `L ∈ DTIME (n^e+1)` via `c` and `M`, the witness
   is `M.toFinOracleTM` at the **same** `c` and `e`, per input
   `(FinTM.toFinOracleTM_computesInTime M O _ _ _).mpr`. For target 3 it is
   `M.toFinOracleNDTM`, same `c` and `e`. A per-input private helper may
   mirror the shape of `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff`
   (`ClassNP/NTIME.lean`; not importable here, do not import it): by target 1
   every length-`t` branch is `M.tm.runFrom O · t`, so halting follows,
   `List.replicate t false` accepts a member, and a non-member outputs
   `[false] ≠ [true]` on every branch.
4. **The private core of `OracleAgreement.lean`**, inserted between
   `queriesWithin` (ends at line 91) and target 8's docstring (Lean has no
   forward references and targets 8–10 precede `queriesAlong`):
   - **(i) step agreement:** if `cfg.state = some M.qQuery` makes `O`, `O'`
     agree on `queryString cfg`, then `M.step O cfg = M.step O' cfg`
     (`step_eq_of_ne_qQuery` off the query state, one unfolding at it);
   - **(ii) K, the one induction:** with
     `c O s := N.runWith O (w.take s) (N.initCfg x)`, if the oracles agree on
     `queryString (c O s)` whenever `s < w.length` and
     `(c O s).state = some N.qQuery`, then `c O s = c O' s` for all
     `s ≤ w.length`. Induct on `s`:
     `w.take (s+1) = w.take s ++ [w[s]]`, `runWith_append`, the hypothesis,
     E2 and (i);
   - **(iii) constant-word bridge:** for `s ≤ t`,
     `M.toOracleNDTM.runWith O ((List.replicate t false).take s) (M.toOracleNDTM.initCfg x) = M.runFrom O (M.initCfg x) s`
     (`List.take_replicate`, `Nat.min_eq_left`, target 1).
5. **The locality targets.** 6: K at `s = w.length`, hypothesis from E5 and
   `List.length_take_le`. 7: K, hypothesis by membership introduction into
   `queriesAlong`. 5: the member's index `s < w.length`, then E5. 8 and 9: K
   for `M.toOracleNDTM` along `List.replicate t false`, transported by (iii);
   hypotheses from `queryString_length_le` (8) and membership in
   `queriesWithin` (9). 10: as its sketch, via `queryString_length_le`. 4: one
   line. **Sanctioned appendix:** one flagged sentence on 8 and 9: their
   induction is the shared branchwise one, run along the constant word
   through target 1.

## Cited infrastructure (public and proved at the issue commit)

| File | Declarations |
|---|---|
| `TuringMachine/Oracle.lean` | `OracleTM.step`, `runFrom`, `queryString`, `step_eq_of_ne_qQuery`, `workTapePos_step_le`, `workTapes_step_eq_of_ne`, `queryString_length_le` |
| `TuringMachine/OracleNondeterministic.lean` | `OracleNDTM.stepWith`, `runWith`, `runWith_cons`, `runWith_append`, `runWith_of_halt`, `HaltsWithin`, `FinOracleNDTM.AcceptsWithin`, `OracleTM.toOracleNDTM`, `FinOracleTM.toFinOracleNDTM` |
| `TuringMachine/OracleFinite.lean` | `FinTM.toFinOracleTM`, `FinTM.toFinOracleTM_computesInTime` |
| `ClassP/{P,DTIME}.lean`, `TuringMachine/Deterministic.lean` | `Complexity.P`, `DTIME`, `FinTM.DecidesInTime`, `MultiTapeTM.indicator` |

Everything upstream of your files is sorry-free, so the **"proved modulo"
set is empty**. A complete delivery has no `sorryAx`. `EXPCOM`'s class
identities cite target 3, but they are themselves sorried, so there is
nothing for you to do there.

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/ch3-p32-findings.md`, **statement verdicts 1–7**:

> | 1 | `OracleTM.runFrom_eq_of_agree_length_lt` | **True.** Induct on the elapsed steps up to $t$. At step $s<t$, an initialized query has length at most $s<t$; agreement therefore fixes the answer. Other steps are oracle-independent. |
> | 2 | `OracleTM.runFrom_eq_of_agree_queriesWithin` | **True.** The same induction uses membership of the actual query at index $s$ in the first oracle's list. Equality of prefix configurations makes the asymmetry sufficient. |
> | 3 | `OracleTM.length_le_of_mem_queriesWithin` | **True.** A listed word comes from an index $s<t$, with length at most $s$. In fact the stronger conclusion $\vert z\vert <t$ holds. |
> | 4 | `OracleTM.queriesWithin_length_le` | **True.** `filterMap` retains at most one item per element of `List.range t`. |
> | 5 | `OracleNDTM.runWith_eq_of_agree_length_lt` | **True.** Induct over prefixes of the fixed word. The same tape invariant holds because actions write at the old head and move by at most one, while query/halting transitions do not write. |
> | 6 | `OracleNDTM.runWith_eq_of_agree_queriesAlong` | **True.** Prefix equality plus agreement on the first branch's submitted queries gives equality of the next transition under the common next bit. |
> | 7 | `OracleNDTM.length_le_of_mem_queriesAlong` | **True.** A listed query occurs after $s<\vert w\vert $ transitions and has length at most $s$; again the strict bound is available. |

From its **answer 5** (indexing):

> The transition from time $s$ to time $s+1$ consults the oracle exactly when the time-$s$ state is `qQuery`; these are precisely the indices $s<t$. At $t=0$, the query list is empty. At $t=1$, an initial query state submits the empty word and is correctly included.

> For nondeterminism, `runWith` consumes the next bit before recursively processing the suffix, including when `stepWith` ignores it at a query state. Prefix length therefore equals elapsed transitions.

From `audits/ch3-p31-findings.md`, the **sorried-declaration table**:

> | `OracleTM.toOracleNDTM_runWith` | **True.** One embedded nondeterministic step equals the deterministic oracle step for either bit, separately in the halted, query, and ordinary cases. Induction on the choice word therefore gives equality with `runFrom` at its length, for every starting configuration. Well-formedness is unnecessary for this identity because both sides use the same special states even when they collide. |
> | `P_subset_POracle` | **True.** Take the plain P witness and apply `FinTM.toFinOracleTM`. Its proved computation iff transfers the indicator output at every input with the same multiplicative constant and polynomial exponent. |
> | `POracle_subset_NPOracle` | **True.** Duplicate the deterministic transition function. Every word of the chosen budget has the deterministic final configuration, hence all branches halt; a word of that length always exists, and it accepts exactly when the deterministic output is `[true]`. |

## Ground rules (binding)

1. **File ownership.** Only the three owned files: the ten bodies, E1–E5, and
   new `private` helpers. List every new declaration with its role (the
   epoch audit blind-restates them).
2. **Statement freeze.** No renames, re-signatures, restatements or
   attribution edits; existing definitions byte-identical. In docstrings,
   only **status text** ("(spec, fill pending …)" tags, "sorried" labels:
   yours are `OracleAgreement.lean:49`, `OracleNondeterministic.lean:63`,
   `Classes.lean:52`, where four statements stay sorried) and **flagged
   sketch appendices** may change, plus **one module-docstring *Main results*
   bullet per new export E1–E5**. Nothing else. Flag every update.
3. **Escalation** on anything unprovable as stated: stop on it, record the
   obstruction, continue. **Touch no other sorry.**
4. **Cite, never re-prove**: `Oracle.lean`'s per-step lemmas (through E2),
   and target 1 once filled.
5. **Imports unchanged**; everything cited is reachable now. A Mathlib import
   only if a needed lemma requires it, flagged; no TCSlib import (escalate).
6. **One proof per shared argument.** K serves all four agreement targets;
   the deterministic ones are its constant-word instance, never sibling
   inductions. Route 1's step lemma is the only unfolding of `stepWith`
   against `step`.
7. **Requested shared lemmas:** the blank-cell bound (home `Oracle.lean`,
   making `queryString_length_le` its corollary) and optionally (i); both
   `private` here.
8. **Continuation budget.** A partial zip's `REPORT.md` states the proved
   targets and exports, every `private` helper still `sorry` (each with a
   "Proof sketch"), and what is then proved modulo them.

## Duplication governance (binding)

Run the text-level screen **before and after**:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/OracleAgreement.lean \
  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean \
  TCSlib/Complexity/ClassOracle/Classes.lean \
  TCSlib/Complexity/TuringMachine/Oracle.lean \
  TCSlib/Complexity/TuringMachine/OracleFinite.lean \
  TCSlib/Complexity/TuringMachine/Nondeterministic.lean \
  TCSlib/Complexity/ClassNP/NTIME.lean
```

The base has 22 pairs, all pre-existing P3.1 skeleton mirrors; none involves
a target.

- **New cross-file pairs: only these three, each disclosed** with both
  declarations and the shared fraction (the gate rules; never silently):
  (a) target 3 or its helper against `NTIME.lean`'s
  `toFinNDTM_haltsWithin_and_accepts_iff` or `DTIME_subset_NTIME`;
  (b) target 1 or its step lemma against `Nondeterministic.lean`'s
  `MultiTapeTM.toNDTM_runWith`; (c) E4/E5's invariant or the blank-cell
  bound against `Oracle.lean`'s `runFrom_workTapes_invariant` or
  `queryString_length_le`, as a **disclosed adaptation**. No other
  cross-file pair, between your own files included.
- Write each proof from its route; never reword one to evade the screen.
- List every new in-file pair with a justification; at 90% or more it is a
  copy, so factor it (5 and 10 can share one membership lemma in the core).
- Quote both outputs; `REPORT.md` carries **"new copies: none"** apart from
  (a)–(c).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**. Use `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-c1c.txt`, which lists in
  dependency order the upstream closure of your files **and** of every
  downstream module. Record the base sorry-warning set before editing:

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-c1c.txt )
  ```

- Iterate per edit on the changed file, then the later modules in order.
- **Final checks:** (1) owned modules: zero errors; no sorry warnings in
  `OracleNondeterministic` or `OracleAgreement`, exactly four in `Classes`
  (B1). (2) Downstream — `ClassOracle/SATOracle`, `Diagonalization/EXPCOM`,
  `Diagonalization/Relativization`, and the `ClassOracle` and
  `Diagonalization` facades: zero errors, sorry warnings exactly the base's
  (the root `TCSlib` is excluded).
- **Axiom prints** for the ten targets, E1–E5,
  `Turing.OracleTM.queriesWithin` and `Turing.OracleNDTM.queriesAlong`: each
  at most `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`.
- **Lint:** `python3 scripts/campaign_style_lint.py` on
  `TCSlib/Complexity/TuringMachine` and on `TCSlib/Complexity/ClassOracle`,
  0 FAIL each.

## Out-of-scope sorries you will see (leave every one untouched)

- **Yours:** `Classes.lean`'s four B1 statements. **Downstream:** `SATOracle`
  (3), `EXPCOM` (6), `Relativization` (4, incl. C1d's enumeration).
  **Bootstrap only:** `NotTimeConstructible`, `NDCodes`, `NTimeHierarchy`.
- **Concurrent:** C1a `NondeterministicSpace`, `NSPACE`, `SpaceClasses`,
  `Inclusions`; C1b `ZeroSpace`, `Examples`, `CounterProgRun`; C1d `QBF`,
  `QBFEncoding`, `Games`, `TQBF`, `Logspace/Reductions`, `Relativization`;
  S1 `ConfigGraph`.

If a proof seems to *need* one of these, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 10/10 and E1–E5, or the partial frontier (rule 8); base hash and
      ancestor check.
- [ ] Every new declaration with its role (the step lemma, K, (i), (iii), the
      invariant generalization, the blank-cell bound named by role); E1–E5
      flagged as new public surface, with its module-docstring bullet.
- [ ] Imports, or "none"; requested shared lemmas; status-text updates and
      sketch appendices, flagged; escalations, or "none".
- [ ] Duplication: the screen before and after; any (a)–(c) with fractions;
      in-file pairs justified; "new copies: none".
- [ ] Final sweep tail, the seventeen axiom prints, both lint lines; diff
      only in the three owned files, B1 statements byte-identical.

## Known pitfalls at this pin (hard-won)

- **Separately defined functions are not `rfl`-equal** (distinct matchers;
  the §13d G1 probe): hence route 1's `unfold` + `cases`. E2 is fine, both
  sides being `OracleNDTM.stepWith`.
- `OracleTM.step_eq_of_ne_qQuery` takes `M` implicitly: write
  `(M := N.fixChoice b)`. `runWith_cons`/`runWith_append` take `N`
  implicitly, `O` explicitly. `OracleTM` has no `runFrom_succ*` lemmas:
  `M.runFrom O cfg (t+1) = M.runFrom O (M.step O cfg) t` is `rfl`
  (`Function.iterate_succ_apply`).
- Defeq, not syntactic: `M.toOracleNDTM.initCfg x` vs `M.initCfg x`;
  `M.toFinOracleNDTM.tm` vs `M.tm.toOracleNDTM`; `(N.fixChoice b).qQuery` vs
  `N.qQuery`. `rw` will not see through them; use `exact`, `show`, or
  `have …; exact` (the pre-ship check's bridge).
- `queriesWithin`, `queriesAlong`, `step`, `stepWith`, `queryString` and
  `indicator` are `open Classical` definitions: `if_pos`/`if_neg`/`split_ifs`,
  never `decide`; `classical` before `Nat.find` reasoning.
- `List.mem_filterMap.mpr ⟨s, List.mem_range.mpr hs, ?_⟩` leaves a
  beta-redex: close it with `simp only [if_pos hq]`, not `rw`.
  `List.take_succ` gives `l[i]?.toList`: finish with
  `List.getElem?_eq_getElem hs` and `Option.toList_some`; the one-bit append
  is `(runWith_append O u [b] c).trans rfl`.
- `omega` cannot see `|·|` (`rw [abs_le]` first); keep casts as
  `((m : ℕ) : ℤ)` and settle `ℕ` arithmetic before casting;
  `Function.update_of_ne`.
- Class budgets arrive as `(fun n => c * (fun n => n ^ e + 1) n) x.length`:
  `dsimp only`/`show` before a matching `rw`. `P`, `POracle`, `NPOracle` are
  `def`s: unpack with `Set.mem_iUnion`.
- The linter wants a literal "Proof sketch" before every `sorry` (partial
  delivery) and a docstring on every public declaration (E1–E5).
