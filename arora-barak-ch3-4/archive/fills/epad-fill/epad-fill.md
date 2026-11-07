# Ch3–4 fill campaign: E-PAD, padding transfers space bounds down (`Padding.lean`)

Target: `Complexity.mem_SPACE_padLang` in `TCSlib/Complexity/SpaceComplexity/Padding.lean`.

> **Issued** (maintainer, 2026-11-06). The statement passed its statement gate, **gate 110**
> (`campaign/gates/110-epad-statements/`: PASS 0/0/1; the auditor confirmed it is true as stated,
> boundary cases included). It merged as #219. **Rulings (the user, 2026-11-06):** a general lemma
> in a new `SpaceComplexity/Padding` module, for later reuse; `Hierarchy` will import it; the
> maintainer then closes `SPACE_linear_ne_NP` in a small PR. Dispatched by pasted prompt; the
> agent is the user's choice.
> **Pre-ship** on the campaign snapshot after #214 and #223: the import probe
> (`campaign/fills/epad/inputs/EPadImportProbe.lean.txt`) elaborates with exit 0, and every host
> named below prints its type. The target's only admission is its own `sorry`
> (`campaign/fills/epad/logs/epad-preship-importprobe.out`).

> **A single fill**, under addendum v2.6 Parts 1 and 2. Deliver a checkpoint zip after each
> checkpoint, because the session may end at any time.

## Repository and branch: read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out branch
  **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor 72fcfbef3c1deb331aedc95d4a158a9ed4c56524 HEAD`
  succeeds. If it fails, **stop**. That commit contains your target as a gated statement, every
  host named below (proved), the addendum `campaign/standards/fill-environment-addendum.md`
  (v2.6), and the copy-text screen `scripts/copy-text-screen-v3.py`.
- **Run Part 1 of the addendum first**: the preflight, with its stop rule. Fetch the cache for your
  roots only, and never run the unfiltered `lake exe cache get`. If Lean cannot start, follow Part
  2. **If Lean never runs, do not draft proofs blind**: deliver the environment report only.
- **Branch at exactly that commit:**

  ```sh
  git checkout -b fill/epad 72fcfbef3c1deb331aedc95d4a158a9ed4c56524
  git rev-parse HEAD:TCSlib/Complexity/SpaceComplexity/Padding.lean
  # must print 39a59037fb3b7582ef154cd8819640ac05c1b6ea
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4). Attach `fill-epad.zip` in your reply.
  It contains:
  - `REPORT.md`;
  - the full modified source;
  - a `git format-patch` series against your base;
  - a git bundle whose only prerequisite is your base;
  - the environment logs;
  - the final elaboration log with each module's time and maximum memory;
  - the axiom log;
  - the seal test's source, its controls and both outputs;
  - both screen outputs;
  - `SHA256SUMS`.

  After each checkpoint, write `fill-epad-cp<N>.zip` with the same contents as of that commit,
  and deliver the latest if the session ends early.

## The target (frozen)

```lean
theorem mem_SPACE_padLang {L : Language Bool} {S T : ℕ → ℕ} (C d : ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + C * (n + 1) ^ d)) (hT : ∀ m, m + 1 ≤ T m) :
    padLang L (fun n => C * (n + 1) ^ d) ∈ SPACE T
```

`padLang L pad = {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)}`, read only
through `mem_padLang_iff`. The statement, `padLang`, `mem_padLang_iff`, the module docstring's
headings and the target's docstring are frozen. You may extend the target's docstring with an
**Implementation** paragraph and refine its proof sketch to match your proof.

**The mathematics.** Gate 110's auditor gives this sketch (its note 4). Let `M` decide `L` within
`c · S n` work cells. On input `y` of length `m`:
1. check that `y` is `pairEncode x w` with `w = 1^{C (|x| + 1)^d}`, rejecting otherwise, in
   `O(m + 1)` cells, including on malformed inputs, without writing the pad;
2. for a valid `y`, run `M` on `x` (copied to a work tape, or read in place through a bounded
   input device) within `c · S |x|` cells, and answer as `M` does.

For a valid word, `m = 2|x| + 2 + C (|x| + 1)^d` (`Turing.length_pairEncode`), so `hST` and `hT`
give `O(T m)`. Invalid words are rejected within `O(m + 1) ≤ O(T m)`. No monotonicity of `S` or
`T` is used, and neither is ever computed.

Account explicitly for initialization and for the simulated input (gate 110, note 4). Note the
library's space convention: `SPACE` counts work cells (`SpaceComplexity/Basic`;
`ZeroSpace.SPACE_id_eq_SPACE_zero`).

## Owned region and imports

- **Only `Padding.lean`:** the target's proof, plus new private declarations under the `epad_`
  prefix (`EPad`/`epad` for types and definitions; the prefix is unused in the tree at the base).
  List every new declaration with its role.
- **No new public declaration.** If the route needs one, escalate it (ground rule 4).
- **Imports:** you may add imports of TCSlib modules and Mathlib modules, provided that:
  - none of them imports `SpaceComplexity/Padding` or `SpaceComplexity/Hierarchy`;
  - they create no cycle.

  List every added import and why. The import probe `campaign/fills/epad/inputs/EPadImportProbe.lean.txt`
  covers the hosts below. If you cite anything else outside your file, extend a copy of the probe
  and run it.

## Hosts and routes (the host-first rule, `policy.md` §1, `workflow.md` §2)

**Read before you build.** Two routes are known. Choose one at checkpoint 1, in a short design note
in `REPORT.md`, with a route probe in which only your own leaves are `sorry`.

- **(A) The preimage route, recommended for the run phase.** `Complexity.LogProg.OIS.compile_decides`
  (`Logspace/PreimageHost`) runs an arbitrary decider `M` on a *virtual* input `v` that is never
  written out. It is answered by a bank of two deciders, for `v`'s length and for its bits. It
  computes `M`'s output on `v` within `M.k (2S + 1) + |bits (|v|+1)| + 2 + bank`, where `S` is the
  space `M` uses on `v`. `Complexity.mem_LOGSPACE_preimage` is its worked consumer and the model
  to follow.

  Take `v :=` the first component of `y` when `y` is valid. The length and bit deciders of `v`,
  and the validity check, then need `O(m + 1)` space. Their logspace forms may already be
  available through `ImplicitlyLogspaceComputable` (`Logspace/QueryReshape`,
  `SpaceComplexity/ImplicitPoly`); search for them. The verdict must be the conjunction of
  validity and `M`'s answer, so you need a wrapper or a case split for invalid inputs.
- **(B) The machine route.** A pad validator, then `M` run on the first component through the
  published input devices: `Turing.exists_rulerHostTM` (`Build/InputDevice`, a bounded-prefix
  ruler), `Turing.vhostEmitTM` (`Build/VirtualInput`), or a copy through
  `Turing.FinTM.exists_inputCallTM` (`Build/InputCall`, time-based). Seams, branches and contracts
  come from `Build/Seam`, `Build/Contract/*`. The validator must be space-bounded; a time bound
  alone is not enough here.

Gate 109's review of B6's H has a note on this escalation
(`campaign/fills/b6/review/hierarchy-REVIEW.md`, note 6 and its assessment). Read it.

## Ground rules (binding)

1. **File ownership:** `Padding.lean` only, as above.
2. **Statement freeze** over the target, `padLang` and `mem_padLang_iff`.
3. **No new public declaration.**
4. **Escalation:** if the target is unprovable from the published hosts without a new public
   lemma in another file, stop, record the exact missing statement, and deliver what you have,
   with checkpoints. Do not add declarations to other files.
5. **No touching other `sorry`s.** Cite proved material; never re-prove it.
6. **One proof per shared argument.** Never write a second copier, counter, seam, branch,
   validator-of-pairs, input device or oracle simulator if a published one does the job. Never
   re-walk another file's privates.
7. **The pinned base, and no unfolding** (the user, 2026-10-16):
   - Cite only declarations public at your base, and your own file's privates.
   - **Never unfold a definition of another file**, and do not rely on definitional closure
     either. Read `SPACE` through `mem_SPACE_iff`, `FinTM.DecidesInSpace`/`ComputesInSpace`
     through `decidesInSpace_iff`/`computesInSpace_iff`, `padLang` through `mem_padLang_iff`, and
     machines, configurations and transports through their published equations.
   - Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step, but are never
     passed to `simp`, `rw` or `unfold`.
   - If a fact you need has no published lemma, escalate it, naming the lemma.
   - **Self-check by a seal test with controls:**
     - make a scratch copy of your module with `attribute [local irreducible]` on every
       other-file TCSlib definition your proofs mention;
     - add `attribute [-simp]` on the `@[simp]` TCSlib definitions `Action.apply`, `Cfg.init`,
       `MultiTapeTM.initCfg` and `NDTM.initCfg` if you reach them;
     - for each sealed definition, add a control that closes by `rfl` unsealed and fails sealed;
     - also produce an inspection table of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
       argument in your diff.

     Ship the raw outputs.
8. **No `sorry`, no `admit`, no new axiom.** The target must print
   `[propext, Classical.choice, Quot.sound]`, or fewer.
9. **Size:** no cap. Report the line count and the declaration counts (base: 77 lines, 3 public,
   0 private).

### Checkpoints

1. **The design note and route probe:** the chosen route, its hosts by exact name, and the
   space-ledger arithmetic, with only your leaves `sorry`.
2. **The validator:** decides "is `y` a valid padded word" (or its virtual-input form) in
   `O(m + 1)` space, malformed inputs included.
3. **The run phase:** `M` on the first component within `c · S |x|` plus overhead.
4. **Assembly and the space ledger:** `mem_SPACE_padLang` proved.

Each may land alone. **Add no new admission.** One checkpoint, one commit, one zip, delivered at
once.

## Duplication governance (binding)

- **Before and after:** run `scripts/copy-text-screen-v3.py` on a frozen `git worktree` of each
  commit, one run at a time, under `nice -n 10`. The population is your file plus every TCSlib
  file you cite.
- **For every private lemma you add:** search for a published statement or generalization in the
  tree, by name and by statement (`git grep`), and with an `exact?`/`apply?` probe. `REPORT.md`
  lists the search and its result per private.

## Environment and verification

Follow addendum v2.6 (Parts 1 and 2; Part 3's one-Lean rule and no-stop rule apply). Elaborate
with the project's tools as the addendum prescribes. Never build the whole library. The final
check covers:
- your module;
- the `SpaceComplexity` facade;
- the axiom print of the target;
- the seal with its controls;
- both screens.

## REPORT.md checklist

- the base hash and the branch;
- the route and the design note;
- every new declaration and its role;
- every added import and why;
- every cited declaration outside the file;
- the seal and its inspection table;
- the axiom print;
- the semantic-duplication search per private;
- both screens;
- per-module time and memory;
- the checkpoints reached;
- any escalation, stated as an exact Lean statement.
