# External audit pack — Chapter 2, epoch-3/4 fill gate, round 2

Round-2 review of the repairs to the two majors and one minor from
`audits/ch2-epoch34-findings.md` (attached verbatim). The round-1 pack
and bundle are immutable and unchanged; this supplement is additive.
Scope of this round: findings 1–3 and any challenge to the new
evidence; the round-1 notes confirmed the mathematics and need no
re-review. Gate closes on zero blockers/majors across both rounds'
open items. Record findings in `audits/ch2-epoch34-r2-findings.md`.

Summary of repairs (full detail in the attached resolutions):

1. **Finding 1 (major)** — `audits/programs/ch2-epoch34-R2Axioms.lean`
   (attached, with its run log and the fresh 65/65 sweep log): all 21
   targets explicit with roots and permitted axioms; a memoized
   transitive axiom-closure walk over every checked declaration of the
   six owned modules AND the whole TCSlib import closure (11,510
   declarations) — the probe class (`private axiom … : False`) now
   fails the run; missing checked declarations panic; per-module kernel
   surface against source-derived public lists (cross-validated by
   lint); all 65 order modules asserted imported. Two self-caught
   disclosures are recorded in the resolutions: the prior programs'
   three-umbrella import gap, and 11 itemized generated kernel
   artifacts in the owned modules (eight imported-definition equation
   lemmas + the derived instance trio of a private structure).
2. **Finding 2 (major)** — the merge evidence supplement:
   `merge2-owned-diffs.md` (both owned-file first-parent diffs with
   blob identities, plus merge #1's Tautology diff closing note 12's
   caveat); the cited `colleague-merge2-sweep.log`; the substituted
   shared sources `PolyTimePairing.lean` and `Composition.lean` in
   full; and `final-source-manifest.md` — repository commit, source
   SHA-256 and fresh-olean SHA-256 for all 65 modules of the round-2
   run.
3. **Finding 3 (minor)** — `ch2-epoch34-r2-lint.log`: the scoped lint
   over all six owned files, 0 FAIL, the five exceptions named,
   TMSAT's standing epoch-2 exception identified.
4. **Notes 4 and 13** — the mechanical 22+76 deletion itemization
   (resolutions §4) and `duplicate-run-record.md`: archive and patch
   SHA-256s for both runs and the mechanically re-verified binding of
   β's patch to the integrated tree.

Severity scheme as always; this round-2 pack is immutable once sent.

## Bundle manifest — 12 attachments after this pack

The resolutions; the round-1 findings (verbatim); the R2 program; its
run log; the fresh sweep log; the scoped lint log; the merge diffs; the
source/olean manifest; the duplicate-run record; the merge sweep log;
`PolyTimePairing.lean`; `Composition.lean`.
