# ARM-extensions fill gate: resolutions (round 2)

**Round 2** (`audits/arm-extensions-fill-r2-findings.md`, verbatim; bundle SHA-256
`59c8f436cdbf16f1a155d4f9d0c648e8bbd43e8292f4168d7c5e3e23c494b490`, 170 sections, dispatch folder
21): **OPEN, 0 blockers, 2 majors, 6 minors.**
- **Reproduced:** the pair inventory (512 directed, 353 unordered), the screen, the classification
  scripts and every published total.
- **No false Lean interface.**
- **Round-1 findings closed:** 6, 7, 10, 12 (by disposition), 13 and 14.
- **Still open:**
  - findings 1–4, held by one joint scope condition (R2-1);
  - finding 5 (R2-2);
  - findings 8, 9 and 11, as minors (R2-6, R2-7, R2-8).

## Findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| R2-1 | major | Two exclusions were genuine copies. `arm_reach` (`Machines/ARMReach.lean:197–231`, pair L066) inlines `DblLang.Rch.trans`'s guarded run composition; counted, it puts `ARMReach.lean` at 21.52% by whole-declaration code lines. `halvCount_loop` (`Codec/Engine.lean:348–402`, L049) re-proves `InputAccess`'s private `access_width_half` | **The user (2026-10-14): remove the copies before closure, not acknowledge them.** A refactor PR, cleared with Hydroxyi like #93:<br>• `halvCount_loop` cites `InputAccess.access_width_half`, promoted to public;<br>• `arm_reach` and `DblLang.Rch.trans` both use one generic guarded-segment composition lemma over an iterated step function, in a low-level home. It is the seed of ARM-2's reachability kit (K18), which `MReach`/`AReach` join later under ARM-2.<br>Round 3 presents the refactor's diff, re-measures with the copies removed, and keeps both pairs visible as "removed" |
| R2-2 | major | H7–H13 are drafted but not installed in `machine-library-design.md` §14; H1 and H4 still name the superseded routes (MIG-22, MIG-19) | **The maintainer installs the rows in §14**, with contracts, consumers, resource clauses, the accepted first-use exception and the gate-before-further-consumer rule. H1, H3, H4, H6 and the pure-kit paragraph are reconciled. The auditor's precision repairs are applied:<br>• "direct importers and named transitive users";<br>• `vword_whole₁` at line 93;<br>• H3's #92 status set to merged;<br>• H13's "one consumer each" qualified;<br>• H8's bound per input, H9's count per run.<br>MIG-19 and MIG-22 retire as overtaken for their named targets |
| R2-3 | minor | Below-floor members of acknowledged families: `sbI`/`hvI` (K1), `MReach.single`/`mono` (K18), and the S072–S074 preimage-oracle pairs (K2) | Added in round 3 as manual rows and as K2/G with a parameterized preimage-answer lemma; the totals are rerun. These are inside the acknowledged families, so they need no new acknowledgement (the auditor's ruling) |
| R2-4 | minor | Overrides I082 and I083 are false positives: both prove length-oracle facts, not `orc_bit` | Changed to N/X in round 3; K2's counts are corrected |
| R2-5 | minor | "Cite" is impossible as written for I032 and I040, because each source imports the consumer. I064's two oracle relations differ | Round 3's factorings name the lower homes: the window lemma moves to `Bridge` or below, the bit-length bound to `Parse` or below. I064 is factored over a slot-aware query |
| R2-6 | minor | Record corrections are still proposals: plan B2/fills-6, backlog MIG-19/MIG-22, design §12.8/§16b, historical-probe and Bonnet annotations | Applied by the maintainer with R2-2, preserving historical decisions and probe files, with dated annotations |
| R2-7 | minor | The full-path screen key and the review of older screens are deferred. 421,911 counts only screen-eligible body characters (17,116 more lie below the floor) | Round 3 labels 421,911 "screen-eligible body characters" and also reports the all-body denominator 439,027. The full-path-key repair and the older-screen review are the queued screen-fix task, carried explicitly |
| R2-8 | minor | #93 changed 32 added files and the existing facade, not "33 of the 73"; finding 11's two `SpaceComplexity` facade lines are deferred, not fixed | Round 3's pack corrects the wording. The two facade lines are carried to the payback PR (ARM-1), as are the three missing sketches and the `predB_iff` entry |

## Next

1. **The refactor PR:**
   - the promotion and the generic composition lemma;
   - `halvCount_loop`, `arm_reach` and `Rch.trans` re-pointed.

   Lean, in Hydroxyi's files and ours. It is cleared with Hydroxyi and merged after round 3.
2. **The maintainer's records commit:** R2-2 and R2-6.
3. **Round 3's pack:**
   - the regenerated ledger;
   - the refactor's diff;
   - excerpts of the 25 absent N-pair counterparts, so the exclusions are source-backed;
   - the corrected texts.
