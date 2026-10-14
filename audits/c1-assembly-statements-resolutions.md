# C1-A assembly statement gate: resolutions (round 1)

**Gate:** the guess-then-run assembly in `Build/NDHost.lean` (`audits/c1-assembly-statements-pack.md`;
bundle SHA-256 `fc27aee38181d7eab8f3989d9c41acb9a5a94afa3153003a2e49519476eb968d`, 53 sections, dispatch
folder 19).

**Round 1** (`audits/c1-assembly-statements-findings.md`, verbatim): **OPEN, 0 blockers, 1 major, 3
minors.** No assembly theorem is false, and no hypothesis is missing or spurious. The auditor checked
all eight theorems, the core interface and both consumer derivations (UN's statement matches the
frozen theorem character for character after whitespace removal), and ran the 13 adversarial cases
of brief point 11 with an independent transition model. The major is policy only. The statements
need no relaxation.

## Findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| M1 | major (policy) | `guessRunCfg_clean`'s proof repeats `SpaceComplexity/Inclusions.lean`'s private `b2b_capture_shape` calculation, and re-derives `embedSlot_unselected` by exposing its body; the copy is not human-acknowledged | **Repaired by the export, round 2.** Add the auditor's public `Turing.embedSilentCfg_cap` to `Build/Embed.lean` (capture tape and head, general frame, prefix, output and source), and replace the local `hslot` and both capture-field `change` blocks with it. The export is a new public statement, so round 2 gates it. Its earlier consumer, `Inclusions.lean`'s private `b2b_capture_shape` (3 uses), retires onto it in the same landing if the instances match; otherwise it is recorded as debt. Both files are campaign files. No human acknowledgment of a copy is needed, because none remains |
| m1 | minor | `guessRunTM_accepts_iff`'s docstring: a first verdict `rej` gives no accepting branch, which is wrong when `acc = rej` | **Fixed in round 2:** "a first verdict equal to `rej` and different from `acc`", or the tested predicate `state = some acc`. The theorem is unchanged |
| m2 | minor | `neg4` is not a false statement (at length 15 the handoff gives liveness; its error was a type mismatch), and `neg1` moves the stream one bit early, not two | **Fixed in round 2:** a positive handoff-time liveness corollary; `neg4` replaced by a concrete false post-halt liveness assertion (the accepting two-cell branch at length 19, by `decide`), its failure inspected; `neg1` relabelled; the auditor's early-setup-exit example added. The round-1 log is kept as committed and its description is corrected here |
| m3 | minor | The name screen ignores pending-file clashes in its exit status, and the isolation builder neither fails closed nor deletes stale targets; the short-name summary omits the `GuessRunPhase.State` overlap | **Fixed in round 2:** pending clashes count in the exit condition (or a reviewed allowlist); each generated target is deleted first, the builder's status is checked, and Lean runs only after a fresh generation; pipeline failures propagate; a control for each failure path; the summary corrected. Until then, round 1's blanket "fails closed" attestation is read as covering the checks the auditor did not break |

## Rulings on the open questions (adopted)

1. The rewind stays inside the assembly, with the new `Build.Catalog` import. The cut and affected
   closure are re-run at the landing tip.
2. UN's setup is a fill obligation. UN's brief carries the consumer probe's `hsetup` verbatim
   (quantifier order, first exit, complete cleanup, no input-length term in the bound), and the
   H1 harvest prerequisite stays separate.
3. The `embedSilentCfg_cap` export is added with this landing (M1).
4. The verdict leaf stays inline.

## Next

Round 2: the export, its use, the m1–m3 repairs and regenerated evidence, rebuilt at the current tip
(after #92 and #93), as a new dispatch.

## Round 2 (gate CLOSED)

**Round 2** (`audits/c1-assembly-statements-r2-findings.md`, verbatim; bundle SHA-256
`e2cd68c2f0762a80603c072106f293f2a94795cbfee00b812d5614e3914708c0`, 65 sections, dispatch folder
23): **CLOSED, 0 blockers, 0 majors, 1 minor.**
- **M1 closed:** the public `Turing.embedSilentCfg_cap` (`Build/Embed`), with the auditor's
  signature and proof. `guessRunCfg_clean` and `Inclusions`' `b2b_capture_shape` cite its two
  projections. Keeping `b2b_capture_shape` private is justified: it is a whole-configuration
  identity.
- **m1 and m2 closed.**
- **m3 still open,** only as R2-m3.
- **Freeze:** no existing statement changed.
- **The shim:** adequate for the gate. The landing compiles the real export.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| R2-m3 | minor | `names_asm.py`'s allowlist uses a string-prefix test, so a sibling directory such as `…/assembly-other/` is exempted | **Fixed in the landing's checks:** path-component containment, via `os.path.commonpath`. A sibling-directory collision control must exit 1, and the legitimate round-1 evidence still returns 0 |

**Landing obligations** (the auditor's):
- compile the real export and its whole dependent closure at landing. `Embed` has about 150
  downstream modules, so the replay is large;
- carry UN's setup hypothesis verbatim into UN's fill brief;
- keep H1's prerequisite separate. It has landed, in #94.

**Next:** one landing PR for `Build/Embed`, `Build/NDHost` and `SpaceComplexity/Inclusions`, at the
tip after #94 (snapshot `oleans-lh1`), with the R2-m3 repair.
