# Chapter-1/2 retrofit — Batch RB5 (revision 2): finish the relocation family (`Build/Embed.lean` + `Build/Loop.lean` + `Build/Primitives.lean` + `CookLevin/Hardness.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Before you start, confirm that
  `git merge-base --is-ancestor 0aea21088db1f8c44d4c1bb5ba57f28eceb3c354 HEAD`
  succeeds. That commit integrates the §12.6 fill, so `Build/Catalog.lean` is
  sorry-free; it already contains RB4 (PR #13). If the check fails, **stop**.
- Create a **fresh** working branch off the campaign branch (suggested name
  `fill/retrofit-rb5-v2`). Record the base commit hash in `REPORT.md`. Never
  rebase.
- **Delivery is by zip, not PR or push**: `retrofit-rb5.zip` with the
  standard contents (`REPORT.md`, the full modified sources, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom log, and `SHA256SUMS`). Integration note, no
  action for you: the maintainer integrates retrofit deliveries on a side
  branch and opens a PR for the user's manual merge.

## What changed since the first issue (read this first)

The first dispatch stopped on two conflicts in the brief. Both were brief
defects, and both are resolved here.

1. **The Task-1 lemma moves to `Build/Embed.lean`.** Its statement needs
   `Cfg.mapState`/`Action.mapState` (`StateRenaming.lean`), and its proof
   needs Z5 (`Simulation.lean`). Neither file imports the other, and the
   first issue forbade new imports. `Build/Embed.lean` already imports both,
   and every consumer already reaches it, Hardness included. So the lemma
   lands there, with **no import change anywhere**. `Simulation.lean` is no
   longer an owned file.
   - **Pre-ship check (executed by the maintainer).** The contract below,
     with Loop's proof moved verbatim, elaborates in `Build/Embed.lean`'s
     import context. Its axioms are `[propext, Classical.choice, Quot.sound]`
     (`audits/evidence/retrofit/rb5-preship-task1.lean.txt`).
2. **The old Task 2 (Loop's RB4 leftovers) is withdrawn.** Your counterexample
   confirms the defect. The anchor-return phase runs in **body control from
   `t = 0`**, which is exactly where the capturing and forwarding hosts differ
   by design, so no non-body guard can hold. The structural fix belongs to the
   maintainer's 12.2c refactor. **Include your kernel-checked counterexample in
   the delivery** as `evidence/anchor-return-guard-counterexample.lean.txt`,
   not in any source file. It becomes the 12.2c item's evidence. Leave
   `emLoopHost_*`, `emCall_bank_*` and `emCall_finish_*` exactly as they are.

If you have work from the first dispatch, re-apply only what conforms to this
revision onto the fresh branch; cherry-picking is fine. The patch series must
be against your new recorded base.

## What this is

A retrofit batch finishing the **human-acknowledged three-file relocation
family** debt (`audits/duplication-ledger.md`, acknowledgment table; owner
RB4, user 2026-10-09). **Zero `sorry` and zero `error:` before and after
every commit.**

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

## Tasks

**Task 1 — promote the shared state-transport lemma (`Build/Embed.lean`).**
Add the public `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, inside
Embed's `namespace Turing`, in a short new section before its closing
`end Turing`. This is the lemma RB4 implemented as Loop's private
`emCall_state_run`. The contract (from RB4's report) is not negotiable:

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

- Move the proof. **Delete Loop's local copy**, and make its four call sites
  cite the public lemma.
- Give it a docstring with a proof sketch, and add one bullet for it to
  Embed's module docstring (*Main results*).
- This is the batch's **one sanctioned public addition**. Flag it in
  `REPORT.md`; it rides the next retrofit epoch's audit.
- **Also in Primitives:** `splitEmbed_run` is the unguarded special case,
  over all states with no guard. Its two uses map states along the constructor
  `SplitBodyState.emit`, which is injective. Re-prove both by citing the
  public lemma with `good := fun _ => True`, then delete `splitEmbed_run`. If
  this genuinely fails, keep it unchanged and report why.

**Task 2 — Primitives.** For each concrete layout that uses the
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

**Task 3 — Hardness (last).** The same for the four `clSlot*` declarations
and the arbitrary-map `clMap_run`. There are **13 direct `clSlot_run`
sites** plus the `clMap_run` consumers. Prove each site's concrete selector
and state map injective, or route it through a concrete specialization.

**Priority on exhaustion:** Tasks 1, 2 and 3, in that order. A partial
delivery means fewer files finished, never an admission.

## Ground rules (binding)

1. **Ownership**: exactly the four named files.
2. **Public-surface freeze**: every public declaration of Embed, Loop,
   Primitives and Hardness byte-identical, including signature, statement,
   docstring and proof body. Embed gains only the Task-1 lemma and its
   module-docstring bullet.
3. **Duplication governance: measured on text, not on declaration
   counts.** RB4 showed that a declaration count can be met by inlining a
   copy into its consumer. The **binding** measure is

   ```sh
   python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
     TCSlib/Complexity/TuringMachine/Build/Embed.lean \
     TCSlib/Complexity/TuringMachine/Build/Loop.lean \
     TCSlib/Complexity/TuringMachine/Build/Primitives.lean \
     TCSlib/Complexity/CookLevin/Hardness.lean
   ```

   Run it before and after; it takes about four minutes. It lists every
   like-kind pair in which one declaration reproduces at least half of
   another's extracted body, together with the total reproduced text. **At
   the base: 873 declarations, 739 pairs, 180,218 characters.** Most pairs
   are pre-existing internal repetition and are out of scope. The rules:
   - **No pair may appear after that was absent before.** Inlining a deleted
     copy into a consumer is such a pair, and it counts as keeping the copy.
     The one sanctioned carry-over: a pair of `emCall_state_run` may
     reappear under the promoted lemma's name. If `splitEmbed_run` is
     deleted, its pair disappears instead.
   - **For each finished file, every pair with one of its relocation
     declarations on either side must disappear.** At the base, these pairs
     are:

     | Pair | Share |
     |---|---|
     | `emitterP2Cfg` ↔ `clSlotCfg` | 100% both ways |
     | `emitterP2Action` ↔ `clSlotAction` | 100% both ways |
     | `emitterP2_relocate_run` ↔ `clSlot_run` | 93% / 90% |
     | `emitterP2_apply` ↔ `clSlot_apply` | 65% / 61% |
     | `emitterP2_call_segment` → `emitterP2_segment`, `→ emitterP2_relocate_run` | 60%, 52% |
     | `emitterP2_relocate_run` and `clSlot_run` → `emLoop_run_prefix`, `clCount_idle_run`, `clBank_run`, `emCall_right_run` | 84%, 78%, 78%, 69% each |

   - **RB4's Loop leftovers are out of scope**: the `emLoopHost_*` pairs and
     the `emCall_bank_*`/`emCall_finish_*` pairs must stay exactly as they
     are.
   - **The total reproduced text must decrease.**

   Quote both outputs in `REPORT.md`. **Zero new copies**, and no local copy
   of anything, because Task 1 makes the shared lemma public.
   - **Net private count must not increase in any file.** At the base:
     Embed 23 public / 16 private, Loop 8 / 191, Primitives 18 / 254, and
     Hardness 5 / 544. The targets are:
     - Embed: +1 public, 0 private;
     - Loop: −1 private or more (`emCall_state_run`);
     - Primitives: −4 or more (−5 with `splitEmbed_run`);
     - Hardness: −4 or more.
   - Run `python3 -I audits/evidence/retrofit/r1-public-proof-screen.py
     <repo-root>` (about three minutes) before and after, and quote pass 4's
     file totals: Loop 98 and Primitives 173 at the base, and **neither may
     increase**. Report Hardness's four relocation members directly, since
     Hardness is outside the script's files.
4. **Escalation** on any site where the concrete route genuinely cannot
   reproduce a needed fact: restore it, record it, and continue. Never
   weaken a surviving statement.
5. **Imports: none.** Every owned file already reaches `Build/Embed.lean`.

## Proved infrastructure to cite (never copy)

- **Z5**: `Turing.MultiTapeTM.AgreeOn`, `step_eq_of_agreeOn` and
  `runFrom_eq_of_agreeOn` (`Simulation.lean`), which are same-carrier only.
- **R1**: `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_runFrom` and
  `embedEmitTM_frame`, plus the selected-tape exports
  `embedEmitCfg_selected_tape` and `embedEmitCfg_selected_pos`
  (`Build/Embed.lean`).
- **The Task-1 lemma**, once added.
- **RB4's Loop sites as the worked template**: `emCallEmbeddedCfg`,
  `emCallPairEmbedding`, `emCallTripleEmbedding`, and the three rewritten
  `emCall_*` consumers.

## Environment and verification

The standard setup: the bootstrap order list plus the Build files; **never
`lake build`**. Iterate per edit. The final checks, in dependency order:

1. `Build/Embed`;
2. `Build/Loop`;
3. `Build/Primitives`;
4. `Build/Catalog`;
5. `CookLevin/Hardness`;
6. the `TuringMachine` facade;
7. the `CookLevin` facade.

All seven must have **zero errors and zero sorry warnings**. The maintainer's
integration replays Embed's full downstream: 83 modules.

**Axiom prints** for every public declaration of the four files (Embed 24
including the new lemma, Loop 8, Primitives 18, Hardness 5). The pre-existing
ones must be byte-identical to baseline. None may carry `sorryAx`.

Lint `TCSlib/Complexity/TuringMachine/Build` and `TCSlib/Complexity/CookLevin`:
0 FAIL each.

## REPORT.md checklist

- [ ] The base hash and the ancestor check.
- [ ] The three tasks' status, per file; the net line and private deltas per
      file; census before/after; **the copy-text screen before/after** (pair
      list and total), showing every relocation pair of each finished file
      gone and no new pair.
- [ ] Every new or deleted declaration listed, including **every private
      whose statement changed**. RB4's report missed three such changes.
- [ ] Every specialized or deleted generic consumer, with the concrete
      layout that replaces it; `splitEmbed_run`'s disposition.
- [ ] The anchor-return counterexample, as evidence.
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
- **Body-control phases do not transfer by a non-body guard** (the first
  dispatch's counterexample). The promoted lemma's `good` set is the source's
  own states. Supply a guard that actually holds along the source run from
  `t = 0`.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; deleting a
  declaration takes its docstring with it.
- `⇑emb` for an embedding built from a constructor is definitionally the
  constructor, but `rw` matches syntactically. Prefer `exact`/`change`, or
  state the embedding once as a local definition.
- Hardness's publics live in namespace `Complexity`, and Loop's and
  Primitives' in `Turing.FinTM`. Embed's new lemma is
  `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`. Print axioms with the
  names as declared.
