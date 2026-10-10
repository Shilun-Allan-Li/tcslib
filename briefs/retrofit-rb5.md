# Chapter-1/2 retrofit — Batch RB5: finish the relocation family (`Simulation.lean` + `Build/Loop.lean` + `Build/Primitives.lean` + `CookLevin/Hardness.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- **RB5 builds on RB4.** RB4 was integrated on the side branch
  `retrofit/rb4` and is merged into the campaign branch by PR #13. Before
  you start, confirm that `git merge-base --is-ancestor 4b5c2179 HEAD`
  succeeds. If it fails, **stop**: RB4 is not merged yet.
- Create your working branch off the campaign branch (suggested name
  `fill/retrofit-rb5`). Record the base commit hash in `REPORT.md`; the
  brief was issued at `841122fc6d39657f764e5b46e9756121e98e879e`. Never rebase.
- **Delivery is by zip, not PR or push**: `retrofit-rb5.zip` with the
  standard contents. Integration note, no action for you: the maintainer
  integrates retrofit deliveries on a side branch and opens a PR for the
  user's manual merge.

## What this is

A retrofit batch finishing the **human-acknowledged three-file relocation
family** debt (`audits/duplication-ledger.md`, acknowledgment table; owner RB4,
user 2026-10-09). **Zero `sorry` and zero `error:` before and after every
commit.**

RB4 (`audits/retrofit-r2-agent-reports/rb4-REPORT.md`; read it in full)
completed the work in Loop:

- it collapsed the H3 copies;
- it replaced Loop's four `emCall*` relocation originals by the R1
  embedding, an injective state transport and same-carrier Z5.

It deferred **Primitives' four copies** (`emitterP2Action`, `emitterP2Cfg`,
`emitterP2_apply`, `emitterP2_relocate_run`) and **Hardness's four**
(`clSlotAction`, `clSlotCfg`, `clSlot_apply`, `clSlot_run`) on a legitimate
escalation, which binds you:

> The old generic relocation family is stronger than literal R1 embedding at
> its abstract interface. Its assumption `select (index i) = some i` forces
> `index` to be injective but permits **extra aliased host slots** [...]. The
> old state map is `S → H`, without injectivity. [...] These are obstructions
> to a **literal generic replacement**, not a claim that the concrete
> injective call sites are mathematically blocked. Loop's concrete sites
> demonstrate the public route. A continuation should promote the shared
> state lemma, then remove/specialize the generic private consumers while
> preserving every surviving statement, prove exact selector/range
> correspondence for each concrete layout, and retrofit Primitives before
> Hardness.

**What this brief sanctions.** The generic relocation declarations and their
generic private consumers are **private**. You may **specialize or delete
them**, including `emitterP2_segment`, `emitterP2_call_segment`, `clSlot_run`
and `clMap_run`, replacing each use with the concrete layout's own R1 + state
transport + Z5 argument. This is allowed provided that:

- every **public** statement of all four files stays byte-identical;
- every consumer is re-proved.

You must never *weaken* a surviving generic statement. Either delete it, or
keep it exactly.

**What RB4 left behind in Loop (maintainer analysis after the merge).** RB4
met its binding target of 13 fewer privates, but a text-level screen shows
that part of the copied material was *inlined* into consumers rather than
eliminated. The text in Loop's forwarding host that reproduces the original
loop host fell only from 16,858 to 11,476 characters, while that host's total
proof text grew from 61,642 to 70,002. The inlined or retained copies:

| Consumer | Reproduces |
|---|---|
| `emLoopHost_round` | 100% of `loopHost_reject`; 71% of `loopHost_borrow_rewind`; 63% of `loopHost_borrow` |
| `emLoopHost_prepare` | 99% of `loopHost_prepare`; 100% of `loopHost_input_rewind` |
| `emLoopHost_anchor_return` | 95% of `loopHost_anchor_return` |
| `emLoopHost_start` | 92% of `loopHost_start` |

RB4's frame proofs also made the relocation consumers more alike in pairs.
`emCall_bank_final` now reproduces 94% of `emCall_bank_initial` (83% before),
and `emCall_finish_final` 79% of `emCall_finish_initial` (33% before).
**Task 2 below finishes this work.**

## Tasks

**Task 1 — promote the shared state-transport lemma (`Simulation.lean`).**
Add the public `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`. This is the
one RB4 implemented locally as Loop's private `emCall_state_run`, with its
proof. The contract below is from RB4's report; the name is negotiable, but
the contract is not:

```lean
{k : ℕ} {S H : Type} {x : List Bool}
(src : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
(emb : S ↪ H) (good : S → Prop)
(hagree : ∀ q, good q → ∀ inp work,
  host.tr (emb q) inp work = (src.tr q inp work).mapState emb)
(c : Cfg k Bool S x) (t : ℕ)
(hguard : ∀ u < t, ∀ q, (src.runFrom c u).state = some q → good q) :
host.runFrom (c.mapState emb) t = (src.runFrom c t).mapState emb
```

Move the proof; **delete Loop's local copy**; Loop cites the public lemma.
The proof uses no `Build/Embed` declaration, so `Simulation.lean` gains no
import. This is the batch's **one sanctioned public addition**: a docstring
with a proof sketch, flagged in `REPORT.md`. It rides the next retrofit
epoch's audit.

**Task 2 — finish Loop (RB4's leftovers).** For each consumer in the table
above, replace the inlined copy with a **citation** of the original
`loopHost_*` lemma, transferred by Z5 through the existing `emLoopHost_agree`.
Each transfer needs its strict-prefix guard: that the forwarding host stays
outside body states along the original phase. **Prove that guard reasoning
once**, as one private lemma quantified over the phase, rather than
restating it in each consumer; restating it is what grew RB4's consumers.
Then:

- factor the shared frame argument of `emCall_bank_initial`/`_final` into one
  lemma;
- do the same for `emCall_finish_initial`/`_final`;
- delete `emLoopHost_prepare`, `emLoopHost_anchor_return` and
  `emLoopHost_start` if their uses reduce to citations, or keep them as
  one-line corollaries.

**Task 3 — Primitives.** For each concrete layout that uses the
`emitterP2*` relocation family:

- establish exact selector/range correspondence with an injective R1 tape
  embedding;
- establish injectivity of the concrete state map;
- run the Loop-style route: `embedEmitCfg`/`embedEmitTM`, then the promoted
  lemma, then `runFrom_eq_of_agreeOn`, then the selected-tape and frame
  exports.

Delete the four `emitterP2*` relocation declarations, and specialize or
delete `emitterP2_segment`/`emitterP2_call_segment`. RB4 notes these
explicitly mention the old Action/Cfg interface, including the mandatory
first action when entry equals exit; your re-proof must cover that case.

**Task 4 — Hardness (last).** The same for the four `clSlot*` declarations
and the arbitrary-map `clMap_run`. There are **13 direct `clSlot_run`
sites** plus the `clMap_run` consumers. Prove each site's concrete selector
and state map injective, or route it through a concrete specialization.

**Priority on exhaustion:** Tasks 1, 2, 3 and 4, in that order. A partial
delivery means fewer files finished, never an admission.

## Ground rules (binding)

1. **Ownership**: exactly the four named files.
2. **Public-surface freeze**: every public declaration of Loop, Primitives
   and Hardness byte-identical, including signature, statement, docstring
   and proof body. `Simulation.lean` gains only the Task-1 lemma.
3. **Duplication governance: measured on text, not on declaration
   counts.** RB4 showed that a declaration count can be met by inlining a
   copy into its consumer. The **binding** measure is
   `python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root>
   <the four owned files>`, run before and after. It lists every like-kind
   pair in which one declaration reproduces at least half of another's
   extracted body, within a file and across the four files, together with
   the total reproduced text. Before your change, Loop alone has 110 such
   pairs (56,666 characters); many are the original loop host's own
   internal repetition and are out of scope. The rules:
   - **No pair may appear after that was absent before.** Inlining a deleted
     copy into a consumer is such a pair, and it counts as keeping the copy.
   - **Every RB4 leftover pair in the table above must disappear.**
   - **The total reproduced text must decrease.**

   Quote both outputs in `REPORT.md`. **Zero new copies**, and no local copy
   of anything, because Task 1 makes the shared lemma public.
   - **Net private count must not increase in any file.** The targets are
     Loop −1 or more (`emCall_state_run`, plus any Task-2 leftovers that
     reduce to citations), Primitives −4 or more, and Hardness −4 or more.
     The copy-text screen over all four files takes several minutes.
   - Run `python3 -I audits/evidence/retrofit/r1-public-proof-screen.py
     <repo-root>` (about three minutes) before and after, and quote pass 4's
     file totals: Loop 98, Primitives 173 at base. Report Hardness's four
     relocation members directly, since Hardness is outside the script's
     files.
4. **Escalation** on any site where the concrete route genuinely cannot
   reproduce a needed fact: restore it, record it, and continue. Never
   weaken a surviving statement.
5. **Imports**: none, except `Build.Embed` into `Hardness.lean` if it is
   not already reachable. Flag it.

## Proved infrastructure to cite (never copy)

- **Z5**: `Turing.MultiTapeTM.AgreeOn`, `step_eq_of_agreeOn` and
  `runFrom_eq_of_agreeOn` (`Simulation.lean`), which are same-carrier only.
- **R1**: `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_runFrom` and
  `embedEmitTM_frame`, plus the selected-tape exports
  `embedEmitCfg_selected_tape` and `embedEmitCfg_selected_pos`
  (`Build/Embed.lean`).
- **RB4's Loop sites as the worked template**: `emCallEmbeddedCfg`,
  `emCallPairEmbedding`, `emCallTripleEmbedding`, and the three rewritten
  `emCall_*` consumers.

## Environment and verification

The standard setup: the bootstrap order list plus the Build files; **never
`lake build`**. Iterate per edit. The final checks, in order:

1. `Simulation`;
2. `Build/Loop`;
3. `Build/Primitives`;
4. `Build/Catalog`;
5. `CookLevin/Hardness`;
6. the `TuringMachine` facade;
7. the `CookLevin` facade.

All seven must have **zero errors**. All must have zero sorry warnings
except `Build/Catalog`. Catalog's five §12.6 framed statements are being
filled by a concurrent batch, outside your ownership, so they may appear as
admissions; report what you observe, and cite none of them.

**Axiom prints** for every public declaration of the four files (Loop 8,
Primitives 18, Hardness 5, plus the new Simulation lemma). The pre-existing
ones must be byte-identical to baseline. None may carry `sorryAx`.

Lint `TCSlib/Complexity/TuringMachine`, `TCSlib/Complexity/TuringMachine/Build`
and `TCSlib/Complexity/CookLevin`: 0 FAIL each.

## REPORT.md checklist

- [ ] The four tasks' status, per file; the net line and private deltas
      per file; census before/after; **the copy-text screen before/after**
      (pair list and total), showing every RB4 leftover pair gone and no
      new pair.
- [ ] Every new or deleted declaration listed, including **every private
      whose statement changed**. RB4's report missed three such changes.
- [ ] Every specialized or deleted generic consumer, with the concrete
      layout that replaces it.
- [ ] The final sweep tail (seven checks), the axiom prints, and the lint
      lines.
- [ ] Diff touches only the four owned files.

## Known pitfalls at this pin (hard-won)

- **Z5 is same-carrier: transport first, then agree.** Never feed
  `runFrom_eq_of_agreeOn` two machines of different tape counts or state
  types. This is the binding composition plan quoted in the RB4 brief.
- **Aliased host slots**: R1 preserves the ambient frame at host tapes
  outside the index range. A concrete layout's correspondence must show its
  selector has **no** aliasing, never assume it.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; deleting a
  declaration takes its docstring with it.
- Hardness's publics live in namespace `Complexity`, and Loop's and
  Primitives' in `Turing.FinTM`; print axioms with the names as declared.
