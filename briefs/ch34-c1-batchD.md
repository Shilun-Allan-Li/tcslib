# Ch3–4 fill campaign — Epoch C1, Batch C1d: QBF, games, the `PSPACE` collapse, `≤ₗ ⊆ ≤ₚ`, and the BGS enumeration

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Before you start, confirm that
  `git merge-base --is-ancestor 44853c6f3177fed8f7f8d2288210593e9c094f7e HEAD`
  succeeds. That commit lands the order list this brief uses. If the check
  fails, **stop**.
- Create your working branch off the campaign branch (suggested name
  `fill/ch34-c1d`). Record the base commit hash in `REPORT.md`. Never
  rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch34-c1d.zip` with `REPORT.md`, the full modified sources, a
  `git format-patch` series against your base, a git bundle, the sweep,
  axiom, screen and lint logs, and `SHA256SUMS`.

## What this is

Fill the **six audited-true statements** that epoch C1 assigns to this
batch (plan §4e): the QBF round trip and `SAT` embedding, Zermelo
determinacy ([AB09, Exercise 4.10]), the `PSPACE`-complete collapse,
`≤ₗ ⊆ ≤ₚ`, and the [BGS75] oracle-machine enumeration. Five are short. The
sixth is pure but **substantial**, and carries the budget risk (rule 9).

Read the audit passages quoted below (your **binding routes**), the P4.3,
P4.4 and P3.2 `-resolutions.md` files, `policy.md`, `workflow.md` §4 and
plan §4e. C1a, C1b, C1c and S1 run concurrently on disjoint files. You
read C1a's `Inclusions.lean` through one import, and never edit it.

**Pre-ship check (maintainer, executed):**
`audits/evidence/ch34-c1/C1dPreShip.lean.txt`, with output `C1dPreShip.out`.
It elaborates with 0 errors: route 4 against the frozen statements (with the
`Inclusions` import), R2's table codomain as a `Fintype` (only with the
search-size option in R2), R3's default as well-formed, and the two
definitional transports R1 relies on. The cited lemmas print within the
standard triple, apart from `P_subset_PSPACE`'s sanctioned `sorryAx`.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route |
|---|---|---|---|
| 1 | `Formulas/QBFEncoding.lean:88` | `Complexity.QBF.decode_encode` | pair and CNF round trips |
| 2 | `Formulas/QBF.lean:119` | `Complexity.QBF.truth_exPrefix_iff_satisfiable` | two prefix inductions |
| 3 | `ClassPSPACE/Games.lean:97` | `Complexity.Game.determined` | backward induction, **fixed player-one perspective** |
| 4 | `ClassPSPACE/TQBF.lean:121` | `Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P` | `P_subset_PSPACE` (**modulo C1a**) and downward closure |
| 5 | `SpaceComplexity/Logspace/Reductions.lean:130` | `Complexity.LogspaceReducible.polyTimeReducible` | received `polyTimeComputable` |
| 6 | `Diagonalization/Relativization.lean:153` | `Complexity.exists_finOracleTM_enumeration` | relabel, rank, repetition coordinate |

**Fill order:** 1–5 first (independent, each short), then 6 in the order
R1–R6.

**Three files are shared.** `TQBF.lean`, `Logspace/Reductions.lean` and
`Relativization.lean` also hold group-B targets: B4's four, B7's four and
B1/B5's three. You own each whole for the epoch. Change only your target's
body and the new `private` helpers above it, plus the one import in
`TQBF.lean`. Everything else stays byte-identical, status text aside
(rule 2).

### Proof routes (binding; the audits' derivations, amplified)

1. **`decode_encode`** (S2). Prove a `private`
   `quantOfBit (quantBit q) = q` by `cases q <;> rfl`. Then `cases Q`, run
   `simp only [encode, decode, pairDecode_pairEncode, List.map_map, CNF.decode_serialize]`,
   and close with `List.map_id''`.
2. **`truth_exPrefix_iff_satisfiable`** (S1). Three `private` lemmas:
   - **(Q1)**, forward, no coverage hypothesis, induction on `j`:
     `truthAux m (List.replicate j .ex) σ i → m.Satisfiable`.
   - **(Q2)**, the update-prefix agreement lemma:
     `(∀ v < i, σ v = τ v) → ∀ v < i + 1, Function.update σ i (τ i) v = τ v`.
   - **(Q3)**, backward, given `m.eval τ = true`:
     `(∀ v < i, σ v = τ v) → m.numVars ≤ i + j → truthAux m (List.replicate j .ex) σ i`.
     The step uses `τ i` and (Q2); the base case is
     `eval_congr_of_lt_numVars`.

   Assemble at `σ := fun _ => false`, `i := 0`, `j := n`.
3. **`determined`** (finding 9; round-2 "Games").
   - **(G1)** A `private` value: `val 0 h = W h`, and `val (r+1) h` is
     `val r (h ++ [true]) || val r (h ++ [false])` at even `h.length`, `&&`
     at odd. Never use a mover-relative value.
   - **(G2)** `ply s₁ s₂ h := h ++ [if h.length % 2 = 0 then s₁ h else s₂ h]`;
     prove `playOut s₁ s₂ n = (ply s₁ s₂)^[n] []` (`iterate_succ_apply'`).
   - **(G3)** Greedy: `s₁⋆ h := val (n - (h.length + 1)) (h ++ [true])`, and
     `s₂⋆` is its negation.
   - **(G4)** One induction along play, generic in the target bit `b`. If
     `h.length + r = n`, `val r h = b`, `b = true → s₁ = s₁⋆` and
     `b = false → s₂ = s₂⋆`, then `W ((ply s₁ s₂)^[r] h) = b`. Peel with
     `iterate_succ_apply`. In each (even/odd) × `b` case, the constrained
     mover keeps the value greedily. For the other mover, a `false` OR or a
     `true` AND fixes both children. Horizon zero is the base case.
   - **(G5)** Case on `val n []`. Mutual exclusion is not claimed.
4. **`PSPACE_eq_P_of_pspaceComplete_mem_P`** (S3). The proof is
   `Set.Subset.antisymm (fun L hL => mem_P_of_polyTimeReducible (h.2 L hL) hP) P_subset_PSPACE`.
   It needs **the one sanctioned import**,
   `import TCSlib.Complexity.SpaceComplexity.Inclusions` in `TQBF.lean`.
   That import adds `ClassNP/SAT` and `Inclusions` upstream, with no cycle
   and no name clash. TQBF's out-of-scope sorries shift down one line.
5. **`LogspaceReducible.polyTimeReducible`** (T4).
   `obtain ⟨f, hf, hB⟩ := h; exact ⟨f, hf.polyTimeComputable, hB⟩`.
6. **`exists_finOracleTM_enumeration`.** Name a partial frontier by these
   labels.
   - **R1. Oracle state relabelling** (`private`, generic in `Symbol`).
     - **Definition.** `relabel (tm : OracleTM k Symbol S) (e : S ≃ S')`
       maps `q₀`, `qQuery`, `qYes` and `qNo` by `e`, and sets
       `tr q i w := (tm.tr (e.symm q) i w).mapState e`, the
       `MultiTapeTM.relabelState` shape. Well-formedness follows by
       `e.injective.ne`.
     - **Step.**
       `(relabel tm e).step O (cfg.mapState e) = (tm.step O cfg).mapState e`.
       Halted configurations are fixed. At `q = tm.qQuery`
       (`e.injective.eq_iff`), `queryString` is definitionally unchanged and
       `apply_ite` plus `Cfg.ext` close. Otherwise use
       `Equiv.symm_apply_apply`, then `Cfg.mapState_apply`.
     - **Runs.** Apply `Function.Semiconj.iterate_right` to the step lemma,
       since `OracleTM.runFrom := (M.step O)^[t]`. Do not re-induct.
     - **Transfer.**
       `(relabel tm e).ComputesInTime O x out t ↔ tm.ComputesInTime O x out t`.
       `Cfg.init` transports definitionally, and haltedness follows by
       `Option.map_eq_none_iff`. This is `exists_codeTM`'s pattern; do not
       copy it.
   - **R2. Finite canonical tables.**
     `CanonTab k n := {tm : OracleTM k Bool (Fin n) // tm.WellFormed}` gets
     **one** named `private` `Fintype` structure, by `Fintype.ofInjective`
     along the field-tuple map (after `Subtype.val`) into
     `Fin n × Fin n × Fin n × Fin n × (Fin n → Option Bool → (Fin (k + 1) → Option Bool) → SignType × (Fin (k + 1) → Option (Option Bool) × SignType) × Option Bool × Option (Fin n))`.
     Injectivity: `cases`, `OracleTM.mk.injEq`, `Action.mk.injEq`, `funext`.
     **Instance synthesis for that codomain needs a larger search size**
     (maintainer probe, below): at default limits it fails; with
     `set_option synthInstance.maxSize 1024 in` it succeeds. Raising
     `synthInstance.maxHeartbeats` alone does not help. Scope the option to
     the one declaration, or assemble the instance with `letI` in stages.
   - **R3. The default.** `k := 0`, `State := Fin 3`, `qQuery := 0`,
     `qYes := 1`, `qNo := 2`, `q₀ := 1`, every row
     `⟨0, fun _ => (none, 0), none, none⟩` (it halts on its first ordinary
     transition), well-formed by `⟨by decide, by decide, by decide⟩`.
     `FinTM.toFinOracleTM` of a one-state machine also works.
   - **R4. The decoder `E j`.** Take `k := (Nat.unpair j).1`,
     `n := (Nat.unpair (Nat.unpair j).2).1` and
     `r := (Nat.unpair (Nat.unpair j).2).2`.
     - If `h : r < Fintype.card (CanonTab k n)`, return
       `⟨k, Fin n, x.1, x.2⟩` with `x := (Fintype.equivFin _).symm ⟨r, h⟩`;
       otherwise the default (rank overflow, empty sets at `n < 3`).
     - Prove the `private` completeness lemma
       `E (Nat.pair k (Nat.pair n (Fintype.equivFin _ x))) = ⟨k, Fin n, x.1, x.2⟩`.
   - **R5. The family.** `N i := E (Nat.unpair i).1`. The repetition
     coordinate `(Nat.unpair i).2` gives `N(pair(j, r)) = E(j)`.
   - **R6. Assembly.** `rcases M with @⟨k, Q, hQ, dQ, tm, wf⟩` and `letI`
     the instances. Put `e := Fintype.equivFin Q`, `x := ⟨relabel tm e, _⟩`
     and
     `i := Nat.pair (Nat.pair k (Nat.pair (Fintype.card Q) (Fintype.equivFin _ x))) i₀`.
     - `Nat.right_le_pair` gives `i₀ ≤ i` (round 2's counting step).
     - `Nat.unpair_pair` and R4 give `N i = ⟨k, Fin (Fintype.card Q), relabel tm e, _⟩`.
     - R1's transfer gives the iff.

     Estimate: 120–200 lines.

## Cited infrastructure (public and proved at the issue commit)

| Target | Cited | Home |
|---|---|---|
| 1, 2, 5 | `Turing.pairDecode_pairEncode`; `Std.Sat.CNF.decode_serialize` (`CNF.…` under `open Std.Sat (CNF)`); `Complexity.eval_congr_of_lt_numVars`; `Complexity.ImplicitlyLogspaceComputable.polyTimeComputable` (sorry-free upstream) | `TuringMachine/Encoding`; `Formulas/CNFEncoding`; `Formulas/CNF`; `SpaceComplexity/ImplicitPoly` |
| 4 | `Complexity.mem_P_of_polyTimeReducible`; `Complexity.P_subset_PSPACE` (**sorried, C1a**) | `ClassNP/Reductions`; `SpaceComplexity/Inclusions` |
| 6 | `Turing.Cfg.mapState`, `Action.mapState`, `Cfg.mapState_apply`; the `OracleTM` layer; `Turing.FinOracleTM`. Models only (`MultiTapeTM`-only): `relabelState`, `relabelState_step`, `Turing.exists_codeTM` | `StateRenaming`, `Oracle`, `OracleFinite`, `Encoding` |

Every Mathlib and core lemma the routes name is reachable now. The
repository has no oracle relabelling and no finiteness instance for
`OracleTM` or `Action`, and `Configuration.lean` is vendored, so R1 and R2
are yours, `private`.

**"Proved modulo" set: target 4, modulo `P_subset_PSPACE`.** Rely on its
frozen statement, and never prove `P ⊆ PSPACE` yourself. The expected print
is:

```text
'Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Two diagnostics locate the `sorryAx`: `Complexity.P_subset_PSPACE` shows
it, and `Complexity.mem_P_of_polyTimeReducible` stays within the standard
triple. No other target may show `sorryAx`.

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/ch4-p43-findings.md`, "All 12 sorried statements":

> | S1 | `QBF.truth_exPrefix_iff_satisfiable` | **True.** Existential witnesses give a total final assignment satisfying the matrix, so the forward implication needs no coverage hypothesis. Conversely choose the satisfying assignment's bit at each index below `n`; `m.numVars ≤ n` ensures agreement on every mentioned variable. |
> | S2 | `QBF.decode_encode` | **True.** Apply `pairDecode_pairEncode`, cancel `quantOfBit ∘ quantBit` pointwise, and use `CNF.decode_serialize`. Equality of the two fields gives equality of QBF structures. |
> | S3 | `PSPACE_eq_P_of_pspaceComplete_mem_P` | **True.** Hardness and downward closure of `P` under polynomial-time reductions give `PSPACE ⊆ P`. The reverse inclusion follows from the polynomial-space simulation of polynomial-time deciders; the positive polynomial bounds absorb fixed tape-count overhead. |

From the same file, finding 9, proposed fix:

> Define the value as “player one can force `W = true`,” use OR at even histories and AND at odd histories, and explicitly construct player two's strategy where the value is false. The theorem itself is true.

From `audits/ch4-p43-r2-findings.md`, "The six revised non-codec sketches":

> **Games.** At terminal histories use `W`. At an even nonterminal history take OR of the child values; at an odd history take AND. If the root value is true, player one chooses a true child at every even winning node, while every odd successor remains true. If false, player two chooses a false child at every odd losing node, while every even successor remains false. Induction along play proves the respective strategy wins, including horizon zero. Playing two alleged winning strategies against one another proves mutual exclusion, although the declaration asks only for the disjunction. The unchanged statement needs no repair.

From `audits/ch4-p44-findings.md`:

> | T4 | `LogspaceReducible.polyTimeReducible` | Apply the received `ImplicitlyLogspaceComputable.polyTimeComputable` to the same witness. `PolyTimeReducible` requires exactly that resulting computability property and the unchanged membership equivalence. |

From the same file, its answer to question 1:

> State relabeling is strong enough: a bijection on states preserves the initial state, all three distinguished states, transition outputs, and halting. Its configuration transport commutes with each step, including query resolution. Well-formedness ensures at least three states; all such machines occur among the canonical `Fin (m+1)` tables. Empty well-formed table sets at smaller state counts cause no completeness problem.
>
> For explicit recurrence, first let $E(j)$ enumerate canonical tables with a valid default. Set
>
> \[ N(\mathrm{pair}(j,r))=E(j). \]
>
> For each fixed $j$, injectivity of the pairing makes these indices infinite, hence unbounded. This proves the required recurrence without asserting literal equality of bundled state types.

From `audits/ch3-p32-r2-findings.md`:

> For the last row, fix the tape count, state count, and table rank of a representative. Distinct fourth-coordinate values give distinct natural indices. Among `i₀+1` such indices, at least one is at least `i₀`, proving the exact recurrence quantifier. A direct default uses three distinct query/yes/no states, starts in the yes state, and halts on its first ordinary transition; it is well-formed under every oracle.

## Ground rules (binding)

1. **File ownership.** Only the six owned files, as "Three files are
   shared" allows. List every new declaration with its role (the epoch
   audit blind-restates them). No new public declarations.
2. **Statement freeze.** No renames, re-signatures, restatements or
   attribution edits. Status text may be updated to reflect the fill: the
   "(spec, fill pending …)" tags in your targets' docstrings, and the
   "sorried" labels in module docstrings. In shared files these must stay
   accurate for the remaining sorries. Otherwise only flagged sketch
   appendices are allowed. Flag each update.
3. **Escalation** on anything unprovable as stated: stop on that item,
   record the obstruction, and continue.
4. **No touching other sorries**, including the 11 in your own files.
5. **Cite, never re-prove** the infrastructure above.
6. **Imports.** Exactly one TCSlib import, `SpaceComplexity.Inclusions`
   into `ClassPSPACE/TQBF.lean`. Flag any Mathlib import; none is expected.
7. **One proof per shared argument:** G4 and R1's step lemma.
8. **Requested shared lemmas:** the R1 relabelling family and the R2
   finiteness structure, with `TuringMachine/Oracle.lean` as the proposed
   home. They stay `private` here; promotion waits for a second consumer.
9. **Continuation budget.** Deliver targets 1–5 complete before starting 6.
   If your budget runs out, deliver a partial zip. Its `REPORT.md` states
   which targets are proved, which `private` helpers remain `sorry`, and
   the R1–R6 frontier. Sorried helpers are allowed only in a partial
   delivery, each with a "Proof sketch". A target proved over a sorried
   helper counts as not proved. The maintainer issues a continuation brief.

## Duplication governance (binding)

Run the text-level screen **before and after**:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/Formulas/{QBF,QBFEncoding,CNF,CNFEncoding}.lean \
  TCSlib/Complexity/ClassPSPACE/{Games,TQBF}.lean \
  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean \
  TCSlib/Complexity/Diagonalization/Relativization.lean \
  TCSlib/Complexity/TuringMachine/{StateRenaming,Oracle,OracleFinite,Encoding,Deterministic}.lean \
  TCSlib/Complexity/ClassNP/Reductions.lean \
  TCSlib/Complexity/SpaceComplexity/{Inclusions,ImplicitPoly}.lean
```

- **No new cross-file pair** except three pre-named justified pairings:
  R1 step with `Turing.MultiTapeTM.relabelState_step`, R1 transfer with
  `Turing.exists_codeTM`, and target 4 with
  `Complexity.P_eq_NP_of_NPHard_mem_P`. If the screen pairs one, report both
  declarations and the shared fraction. R1's run lemma comes from
  `Semiconj.iterate_right` and should not pair with `runFrom_comm_of_step`;
  if it does, report it.
- List every new in-file pair with a one-line justification. A pair at 90%
  or more is a copy; factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"**,
  with each proof's citations named.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**. Use `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-c1d.txt`. It lists, in
  dependency order, the upstream closure of your files and of every module
  downstream of them, with TQBF's new import accounted for:

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-c1d.txt )
  ```

  Record the base sorry-warning set before editing. Then iterate per edit
  on the changed module.
- **Final checks:**
  1. **Owned modules:** zero errors; sorry warnings exactly at the 11
     out-of-scope declarations below.
  2. **Every downstream module**, root `TCSlib` excluded: zero errors, and
     sorry warnings exactly the base's minus your six. That includes the
     `Formulas`, `ClassPSPACE`, `Diagonalization` and `SpaceComplexity`
     facades, and `Logspace/{Path,ImmermanSzelepcsenyi}`.
- **Axiom prints** for the six targets and the two diagnostics: each target
  is at most `[propext, Classical.choice, Quot.sound]`. `sorryAx` may
  appear only in target 4, through `P_subset_PSPACE`.
- **Lint:** 0 FAIL on each owned subtree, one per run:
  `for d in Formulas ClassPSPACE SpaceComplexity/Logspace Diagonalization; do python3 scripts/campaign_style_lint.py "TCSlib/Complexity/$d"; done`.

## Out-of-scope sorries you will see (leave every one untouched)

- **In your files (11).** `TQBF.lean`: `exists_adjacency_codec_cnf`,
  `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`.
  `Logspace/Reductions.lean`: `ImplicitlyLogspaceComputable.comp`,
  `LogspaceReducible.trans`, `mem_LOGSPACE_of_logspaceReducible`,
  `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE`. `Relativization.lean`:
  `unaryWitnessLang_mem_NPOracle`, `exists_oracle_ne`, `baker_gill_solovay`.
- **Concurrent batches:** C1a (`NondeterministicSpace`, `NSPACE`,
  `SpaceClasses`, `Inclusions`), C1b, C1c (`OracleAgreement`,
  `OracleNondeterministic`, `Classes`), S1 (`ConfigGraph`). Also every
  other chapter-3/4 statement surface.

If a proof seems to *need* one of these, escalate. The one exception is
`P_subset_PSPACE`.

## REPORT.md checklist

- [ ] 6/6, or the R1–R6 frontier; the base hash and the ancestor check.
- [ ] Every new declaration with its role. Identify (Q1)–(Q3), (G1), (G2),
      (G4) and R1–R4.
- [ ] The import added, plus any Mathlib import; the requested shared
      lemmas; status-text updates and appendices, each flagged.
- [ ] Escalations or "none"; the modulo set and its two diagnostic prints.
- [ ] Both screens, pairings with fractions, in-file pairs justified, and
      "new copies: none".
- [ ] Final sweep tail (owned, then downstream), the axiom prints, and the
      four lint lines.
- [ ] Diff touches only the six owned files, as rule 1 allows.

## Known pitfalls at this pin (hard-won)

- Use `Function.update_self`/`update_of_ne`. `List.replicate_succ` is
  `rfl`. `decode` matches on `pairDecode x`, so use `simp only`, not `rw`.
  `QBF` has no `@[ext]`.
- `playOut s₁ s₂ (n+1) = ply s₁ s₂ (playOut s₁ s₂ n)` is `rfl`; state it
  once. Give `omega` the invariant `h.length + r + 1 = n`.
- `OracleTM.step` is under `open Classical in`. Use `if_pos`/`if_neg`, never
  `decide`.
- **Instance diamonds (R2/R4).** `Fintype.equivFin` depends on the
  instance. Pass the one named structure explicitly
  (`@Fintype.card _ inst`, `@Fintype.equivFin _ inst`). Never
  `open Classical` at section level: `Subtype.fintype` would compete, and
  `symm_apply_apply` would then fail.
- **Never evaluate a table cardinality.** Never `decide` or `simp` a table
  type's `Fintype.card`; it is astronomically large. Use `Fin.isLt` with
  `dif_pos`.
- `Nat.unpair`: use `.1`/`.2`, never `let (a, b) := …`. Rewrite
  `Nat.unpair_pair` with `simp only`; `rw` meets "motive is not type
  correct" through the `dite` proof. The precedent is
  `CircuitComplexity/UHalt.lean`.
- `⟨k, Fin n, tm, wf⟩ : FinOracleTM Bool` synthesizes both instance fields.
- The linter needs a literal "Proof sketch" in the nearest docstring above
  every `sorry`. Never put a helper between an out-of-scope theorem's
  docstring and its body.
