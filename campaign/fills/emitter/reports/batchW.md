# Emitter fill batch W — REPORT

## Outcome and provenance

Completed **3/3 points**: `Turing.emit_run` is proved, and
`Wrappers.lean` is admission-free, including its private and generated
kernel declarations. No concurrent Loop/Primitives contract is cited.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Working branch: `fill/emitter-W`.
- Required and actual base: `d7b5b6f94d28df8095165dd4dfe82fd09ba0d414`.
  The object resolved as a commit before work started.
- Delivery commit: `e6925cc6322d04a2e476ff4b6ff2a856e864aaf4`.
- The requested source branch was cloned and checked out first. Its
  observed tip was `dd22fb9e33a17b81ce7f334c248c59893af17e48`, carrying the
  brief. The working branch was then created at the brief's exact pinned
  base. The source-branch and remote-tracking refs remain at that observed
  tip. No other branch was modified; no push or PR was made.
- Binding records read: `briefs/emitter-fill-batchW.md` at the observed
  source tip; `audits/emitter-infra-resolutions.md`, especially “Binding
  on the fill batches”; round-1 finding 7; round-2 finding 7; `policy.md`,
  `workflow.md`, `AGENTS.md`; the prior wrapper brief and inherited
  toolchain/pitfall instructions. The round-2 finding is available under
  its exact attachment header inside the committed
  `audits/emitter-infra-r3-bundle.md`; no standalone round-2 findings file
  exists at the base.

## Proof obligations discharged

| Obligation | Discharging proof |
| --- | --- |
| Forwarded action/configuration identity | New private `Turing.emit_apply`: `Cfg.ext` makes state, input head, work tapes, and work heads reflexive; `List.append_assoc` proves the output equality. |
| One step from a live source | Local `hstep` inside `Turing.emit_run`: the source-state case split rules out `none`; `hagree` selects the forwarded action, and `emit_apply` gives the complete configuration equality. |
| Guarded run equality | `Turing.emit_run`: induction on time, exactly following `capture_run`; the successor uses the restricted guard for the induction hypothesis and `hlive` for the last source step. |

**Halting emission:** `emit_apply` holds for every action, including one
whose successor state is `none` and whose output is `some b`. That same
action appends the bit to physical output and changes host control to
`some ret`. The run guard permits a halt at the endpoint; it forbids only
an earlier halt. The zero-time case is `rfl`, including for an already
halted initial source configuration. No injectivity or state-disjointness
hypothesis is added. Unlike capture, forwarding adds no tape.

The structural template is the existing `capture_apply`/`capture_run`
pair in the owned file; the final proof cites its own private action
identity and proved model infrastructure only.

## Scope, freeze, and declarations

- The sole changed repository path is
  `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean`.
- One new private declaration: **`Turing.emit_apply`**.
  The local `hstep`, `hstate`, `hinput`, and `hwork` are proof-local facts.
- No existing declaration is renamed, removed, or re-stated. No public
  declaration is added. All existing definitions and all other proof
  bodies are unchanged. Imports and options are unchanged.
- Original docstrings are retained. The only addition to an existing
  docstring is the appended emitter implementation note in the module
  header. The new private lemma has its own statement and proof sketch.
- `VerifyFreeze.py` reverses exactly the new helper, appended note, and
  target proof replacement, recovering the base source **byte-for-byte**.
  This checks more than comment-stripped signature equality.
- Final file: **739 lines, 39,085 bytes**, below the 1,000-line ceiling.
  Diff: **35 insertions, 1 deletion** (the target's `sorry`).
- Source SHA-256:
  `027a1fb63939cfcf44a803b6b34a31d08e2e0ca9230ab94d57a6472245949bea`.

## Verification

| Check | Result |
| --- | --- |
| Bootstrap, committed 57-module order | 57/57 PASS, exit 0, zero `error:` lines |
| Final independent fresh 57-module sweep | 57/57 PASS, exit 0, zero `error:` lines |
| Final admission warnings | 19: six sibling emitter contracts + 13 campaign admissions |
| `emit_run` kernel dependency roots | Empty; axioms `[propext, Quot.sound]` |
| Entire Wrappers module | All 77 kernel declarations checked; empty roots; at most the standard triple |
| Statement/source freeze | PASS; exact restoration to base source |
| Build style lint | 0 FAIL, 2 inherited WARNs |
| Patch replay / git bundle verification | PASS / PASS |

The sweeps follow the committed `scripts/ab_ch1_module_order.txt` and
invoke `scripts/lean_check_tree.sh` once per module in dependency order.
Each check removes its old output and requires a fresh nonempty olean,
exit 0, and no `error:` diagnostic. The final sweep uses a separate,
initially empty output directory; no stale repository oleans satisfy it.

The 19 remaining admission warnings are the **six sibling emitter
contracts plus 13 campaign admissions**. They are untouched and are not
dependencies of this batch's target. Style lint has 0 FAIL and two
inherited file-size WARNs, for `Loop.lean` and `Primitives.lean`.

`EmitterAxioms.lean` adapts the committed closure checker: it walks
**checked kernel declarations**, traversing types, values with
`allowOpaque := true`, and inductive constructors. It checks the target
closure and every declaration originating in the Wrappers module,
including unused private helpers and generated declarations. Both have
empty admission-root sets; all encountered axioms belong to the allowed
standard triple.

Final axiom output:

```text
'Turing.emit_run' depends on axioms: [propext, Quot.sound]
'Turing.capture_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_computes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_cond' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Turing.emit_run: []
AXIOMS Turing.emit_run: [Quot.sound, propext]
ROOTS Wrappers whole module: []
AXIOMS Wrappers whole module: [Classical.choice, Quot.sound, propext]
WHOLE WRAPPERS PASS: 77 checked declarations, including private and generated declarations; empty admission roots and at most the standard axiom triple.
```

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
CHECK 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1271:8: warning: declaration uses 'sorry'
CHECK 52/57 TCSlib/Complexity/TuringMachine
CHECK 53/57 TCSlib/Complexity/ClassP
CHECK 54/57 TCSlib/Complexity/Uncomputability
CHECK 55/57 TCSlib/Complexity/Formulas
CHECK 56/57 TCSlib/Complexity/CookLevin
CHECK 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS 57/57 modules; END 2026-10-05T20:54:29.562302+00:00
```

Environment details and exact dependency pins are recorded in
`environment.log`. Lean is the unmodified official 4.25.0 release at
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib is
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The required
`lake exe cache get` was invoked once. After an archive-ownership setup
failure, the compiled cache helper resumed with `--no-same-owner`; its
download was narrowed to the 28 direct Mathlib imports of the campaign
order, successfully unpacking their 916-file closure. No repository
`lake build` was run. This runtime also requires the included
`lean-self-exe.c` compatibility shim: it maps only the executable's own
numeric `/proc` path to the permitted equivalent `/proc/self/exe`.
Compiler, kernel, dependency sources, and pinned manifests were not
changed. These setup issues were resolved before successful verification.

## Delivery and reproduction

`fill-emitter-W.zip` is flat: every member is at its root, including
`SHA256SUMS`. It contains this report, the full modified `Wrappers.lean`,
the one-commit `git format-patch` series, the git bundle, both sweep
logs, the final axiom log and checker, freeze checker/log, style log,
environment evidence, and bundle-verification output.

The root `Wrappers.lean` maps to the sole repository path named above.
The bundle is incremental and requires the recorded base commit;
`git bundle verify` passes. The patch preserves Codex's authorship.
Replaying it from the base in a temporary git index exactly reproduces
the delivery commit's tree, without changing any branch or working tree.
Check the extracted archive with `sha256sum -c SHA256SUMS`; replay the
patch with `git am -3` on an integration branch containing the base.
Re-run the campaign's committed full-sweep loop, then run
`EmitterAxioms.lean` with `LEAN_PATH` pointing first to that fresh olean
tree and then to the dependency cache paths. `VerifyFreeze.py <repo>`
reproduces the source-preservation check.

## Shared requests and escalations

**None.** No statement change, new shared lemma, or further fill work is
requested for batch W.
