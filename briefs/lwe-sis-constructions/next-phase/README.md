# Next construction phase: readiness record

This is internal planning, dated 2026-11-08. It introduces no Lean declaration,
external gate, worker dispatch or security theorem. The detailed contracts and
proof obligations are in [phase1-contracts.md](phase1-contracts.md).

Current continuation (2026-11-07 Pacific): these records have been brought into
`cryptography/lwe-sis-phase1-statements`; the separate planning worktree is retired
from active use. The central integration/PR target is now
`cryptography/lwe-sis-constructions`, as selected by the user. The table below
preserves the original planning checkpoint. The implemented statement skeletons
and their verification live under `../gates/02-construction-core/`; no nontrivial
proof has been filled before that statement gate.

| Item | Identity |
|---|---|
| Records worktree | `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-next-phase-plan` |
| Records branch | `cryptography/lwe-sis-next-phase-plan` |
| Full branch baseline, read with `git rev-parse` | `2c37f3f486822a52f4a9e337c6b742e995ebb118` |
| Campaign PR target | `cryptography/pass-shelat-ch2-4` |
| Reviewed foundation statements | `4364d0e0fe9accd649b6acb4751e8684aa93ad1e` |
| Reviewed representation proofs | `893e921bf2afeca293be9da9d495613bb1486796` |
| Published code review | Draft [PR #236](https://github.com/Shilun-Allan-Li/tcslib/pull/236) |
| Representation-proof input | Exchange `ebe777ba3bf904f6a6909aaf8b931fcb0c53f358` |
| Representation-proof intake records, separate code worktree | `0769cba3e44c56700349f954190fc99d9e622270` |
| Lean / Mathlib pins | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

The old topic snapshot is this records branch's ancestor so that planning does not
change the published proof-review branch. It contains the historical admitted
representation statements; use the reviewed proof pin above for a future code
branch. Do not build this planning checkout or present its ancestry as the filled
source. No packages or build objects are installed here. Its older root plan and
campaign README remain historical snapshots; this directory records the current
planning checkpoint.

Both foundation gates now pass with zero blockers, majors and minors. Their three
continuing notes remain: primary-source archival/ingestion, scoped native and
integration evidence, and the consumer obligations described here. The proof
audit returned during planning; its original report is preserved on the separate
proof PR branch. No repair was required.

## Findings that change the implementation order

1. The existing `PrivateKeyScheme` accepts arbitrary bit-string keys. Direct Regev
   encryption fits by encrypting the entire parameter-length message as a batch
   under the full uniform LWE secret; no key reindexing is needed.
2. Its `MultiMessageSecure` predicate covers every polynomial message count.
   `DLWEAssumption` currently covers one stored sample schedule. Add an LWE-owned
   schedule substitution and make the extra outer hardness quantifier explicit.
   Preserve the existing assumption's name and meaning.
3. The current base provides nonadaptive message-vector security. An adaptive
   private-key CPA owner is absent, and `Games.exists_handlerMachine` remains
   admitted. Plan the batch result now; coordinate the generic CPA bridge before
   editing a shared owner.
4. The SIS collision reduction is direct and independent of LWE. A concrete
   dyadic profile supplies compression, solution existence and exclusion of the
   trivial modulus-multiple solutions. It supplies no hardness proof.
5. The prospective CRH owner in frozen PR #232 pads/truncates a collision finder's
   output. A reduction must reproduce that behavior. Its API is not merged into
   this checkout and must not be copied into a competing definition.

## Ordered work

| Step | Deliverable | Required boundary |
|---|---|---|
| 1 | Primary-source acquisition and applicable ingestion/source matching | Complete N01; propose any shared registry diff separately |
| 2 | Schedule substitution, modular parsers and bit-decoding contracts | New owned modules; public definitions get non-simp readers; statement PR/gate before proof fill |
| 3 | Direct Regev algorithms, perfect correctness and batch/multi-message security | Exact noise sampler, sample counts, uniform implementations and explicit hardness quantification |
| 4 | SIS binary matrix hash, collision-to-solution theorem and concrete profile | Independent `SISAssumption`; no lattice or LWE bridge |
| 5 | Machine and existing-primitive bridges | Reuse proved public hosts; coordinate adaptive CPA and consume the CRH owner's approved landing |

Steps 3 and 4 have disjoint primitive ownership and can be developed separately.
The initial shared parsing and arithmetic adapters should have one owner. Facade
and root export edits belong in a separate small commit. No exact shared-owner
diff is proposed or authorized by these records, and none was implemented.

Two authorized internal agents supplied read-only interface and source inventories.
Root checked the key/message quantifiers, sample count, prospective CRH parser and
named reuse points against pinned source. No agent edited or built in a checkout.
Source browsing checked the primary construction anchors; it does not archive PDF
bytes or replace the source-ingestion workflow. No native run was needed for these
records.

**Ready to run — the next statement design is concrete. New Lean work still needs
its own PR, source-policy work and statement gate; shared CPA/CRH bridges wait for
owner coordination.**
