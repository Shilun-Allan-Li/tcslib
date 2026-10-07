# Machine-library fill campaign — Batch W

**Complete: 4/4 targets, 14/14 points.** The final fresh sweep passes all 57
modules with zero `error:` lines. All four targets have exactly the allowed
axiom triple and no `sorryAx`. No statement escalation was needed.

## Revision and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required base branch: `complexity/arora-barak-ch1`.
- Base commit: `e346139ccc9e3141908f7414bf27f74d8759c9be`.
- Working branch: `fill/lib-W`, created directly from that base as instructed
  by `briefs/lib-fill-batchW.md`.
- Delivery commit: `f34cfd2686c9b426fcf71f61378c77973cad011a`.
- The only repository file changed is
  `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean`.
- No push, pull request, or change to another existing branch was made.
- Final source: 687 lines, 7 existing public declarations, 20 new private
  declarations, no admissions. The file remains below the brief's 1000-line
  threshold; no size escalation is required.

## Targets, in fill order

| Target | Implemented proof route |
|---|---|
| `Turing.capture_run` | Induction on elapsed steps. `capture_apply` splits source and capture tapes, using `bufferTape_append` for an emission. The liveness guard permits the final halting transition, whose emission is captured before returning. Arbitrary prefixes and physical output are preserved. |
| `Turing.FinTM.redirectTM_computes` | Lockstep with the register equal to the optional last source emission. The register updates before the halt test. The correspondence includes absorbing source halts, so it applies directly at the supplied budget and gives empty output. |
| `Turing.FinTM.redirectTM_live` | The same correspondence includes the stationary live loop after a mismatching source halt. Any alleged redirected halt forces a genuine source halt with matching last bit; output uniqueness contradicts the supplied mismatching completed output. This includes empty output. |
| `Turing.FinTM.computesFunInTime_cond` | Pad the decider with blank branch tapes and instantiate `capture_run` with the actual controller as host. Two transitions read its captured singleton. A quantitative refinement of `rewind_from_any` rewinds the original input. `branchTM` then runs from its genuine initial configuration. The construction supplies multiplier **5**, without a monotonicity hypothesis. |

The redirect engine strengthens the first-halt invariant to an all-time
correspondence by handling both absorbing halt and stationary live-loop steps.
Consequently the halting clause does not need a separate final call to
`ComputesInTime.mono`; the absorption is inside the invariant. The conditional
clause uses `ComputesInTime.mono` for the branch maximum and final budget.

The conditional prefix is at most `2 * T₀ n + 5`; the selected branch takes at
most `max (T₁ n) (T₂ n)` further steps. Lean proves that their sum is at most
`5 * (T₀ n + max (T₁ n) (T₂ n) + 1)`.

Harvest sources acknowledged: the controller/capture engine in
`TuringMachine/Composition.lean`; the `acceptCfg`/`acceptTM` invariant family in
`ClassNP/Reductions.lean`; the `enumCapture_step`/`enumCapture_run` templates in
`ClassNP/EXP.lean`; and the `universalCaptureTM` layer in
`TuringMachine/UniversalStartup.lean`. The code adapts these routes locally and
does not reference any other file's private declarations. Public tape-block,
branch, buffer, and scan lemmas come from `TuringMachine/Simulation.lean`.

## New private declarations

The first declaration is in namespace `Turing`; all others are in
`Turing.FinTM`.

| Declaration | Meaning |
|---|---|
| `capture_apply` | Applying the transformed action equals capturing the source action's resulting configuration. |
| `redirectState` | Map source state and optional last bit to simulation, halt, or the live loop. |
| `redirectAction` | Suppress output and update the register before redirecting control. |
| `redirectCfg` | Preserve source input/work fields, store its last bit, and clear physical output. |
| `redirect_loop` | A configuration in the stationary live state is fixed for every run length. |
| `redirect_apply` | Redirection commutes with action application. |
| `redirect_step` | Redirection commutes with every step, including steps after source halt. |
| `redirect_run` | The initialized redirected run equals the correspondence applied to the source run. |
| `timedPadTM` | Simulate the decider with an additional idle tape bank. |
| `timedCondTM` | The finite capture/read/rewind/branch controller. |
| `timedBranchCfg` | Embed a branch configuration while retaining decider tapes and the captured bit. |
| `timedControlCfg` | Capture the padded decider with both branch banks blank. |
| `timed_capture` | Instantiate the public capture theorem through the first decider halt. |
| `timed_control_init` | Identify the host's actual initial configuration with the captured padded source initial configuration. |
| `timed_input_bound` | A run's input position is at most its initial position plus elapsed steps. |
| `timed_rewind` | Rewind from any input position in at most that position plus two steps, preserving work and output. |
| `timed_branch_run` | Branch lockstep retains the inactive decider and capture tapes. |
| `timedReadyCfg` | Branch work is initialized, the verdict is in control, and only input rewind remains. |
| `timed_read` | A halted singleton-output capture reaches the ready configuration in exactly two transitions. |
| `timed_start` | A completed decider run reaches the selected branch's initial configuration within twice its budget plus five. |

## Freeze, documentation, and requested shared lemmas

`verification/check-freeze.py` and `logs/freeze.log` verify:

- All seven existing declaration signatures and their public order are
  unchanged; all three existing definition bodies are unchanged.
- Every existing declaration docstring remains byte-identical.
- Imports and option headers are unchanged; all new declarations are private.
- No `sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by` occurs in the
  comment-stripped edited source.
- The repository diff against the pinned base touches only the owned file.

The sole edit to existing prose is an **append-only module implementation
note**, disclosing that the four contracts are now proved and recording the
conditional controller's bound. Original spec-phase descriptions and every
target docstring are retained.

**Requested shared lemmas:** consider serial promotion of `timed_input_bound`
to the run calculus and `timed_rewind` to `Simulation.lean`. They are generic
in tape count and state type, and independent of the conditional controller.
They remain private copies here under the ownership rule. No shared edit is
needed to integrate this batch. **Escalations: none.**

## Verification

- Lean: **4.25.0**, release commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: **`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**, from the unchanged
  committed manifest. Cache setup required interrupted retries, finally using
  an isolated cache for the 57-module order's imported dependencies. The
  successful fetch unpacked 916 cache files. No `lake build` was run.
- Checks use the committed `scripts/lean_check_tree.sh`. After proof
  development and bootstrap, the final downstream sweep checks positions
  **10–57: 48 PASS, exit 0, zero errors**.
- The final sweep uses a separate initially empty olean tree:
  **57/57 PASS, exit 0, zero errors**. It reports **47 out-of-scope admission
  warnings**, none in `Build/Wrappers.lean`; their files are unchanged.
- Axiom prints use this same final fresh olean tree; all four are:

```text
'Turing.capture_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_computes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_cond' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Style lint on `Build/`: **0 FAIL, 0 WARN**. The broader campaign invocations
  report **0 FAIL, 6 WARN** on `TuringMachine/` and **0 FAIL, 1 WARN** on
  `ClassNP/`; all seven warnings concern unchanged pre-existing files over
  1000 lines. A supplemental whole-`Complexity/` invocation reports 14
  pre-existing failures, all in unchanged legacy `NPReductions/` files,
  outside this campaign. All invocation logs are included with their scope.
- `git diff --check`: pass. The post-commit working tree is clean.

Final sweep tail:

```text
CHECK 54 TCSlib/Complexity/Uncomputability
PASS 54 TCSlib/Complexity/Uncomputability
CHECK 55 TCSlib/Complexity/Formulas
PASS 55 TCSlib/Complexity/Formulas
CHECK 56 TCSlib/Complexity/CookLevin
PASS 56 TCSlib/Complexity/CookLevin
CHECK 57 TCSlib/Complexity/ClassNP
PASS 57 TCSlib/Complexity/ClassNP
```

## Archive and integration

The archive contains this report, the full modified source at its repository
path, one `git format-patch` patch, `fill-lib-W.bundle`, verification programs,
the final/downstream/style/freeze/axiom logs, and `SHA256SUMS` over every other
archive member. Verify with `sha256sum -c SHA256SUMS` from the extracted root.

The bundle is **incremental**, advertising `refs/heads/fill/lib-W` and requiring
the pinned base commit above. `git bundle verify` succeeds in the base
repository. This avoids including unrelated repository history. The patch is
the normal integration route (`git am -3`), preserving this batch's author.
