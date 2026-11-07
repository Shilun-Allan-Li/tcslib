# Independent PR-description review

Reviewed draft SHA-256
`096bed25c8e9f93468a4009edeac2b5251fff77ea0cbfe44f9102d3025206450`
against the final-source freeze, compiled comparison, repair reports and the
three proposal records. No proof, source, Git, Lean, screen or cache action was
performed. This review does not clear a gate or merge.

The comparison base is consistent: the +3/−6 source delta and 140 changed roots
are relative to the API prerequisite (#230 / supplied API1160), not the current
campaign branch before that prerequisite. The private header exceptions and two
embedding proof-field changes are disclosed correctly. The 11-module native
chain, 140 roots plus 228 descendants, three RAM exceptions, producer-log limits,
partial status and outstanding first-entry/zero-space/home decisions agree with
the records.

Two wording changes are needed to prevent overclaims:

1. Replace **“Scoped owner seals and paired controls pass, with the generated
   rewind-matcher limitation recorded explicitly.”** with:

   > Executed seals and paired controls pass for the completed repair scopes.
   > The two Catalog constant-space rows and the redirect-space header remain
   > excluded HOLDs pending the decisions below. The generated rewind matcher
   > has no effective discriminating negative control and is disclosed for
   > gate118's assessment; no global legacy rule-10 seal is claimed.

   The current sentence can be read as covering the three known failing Catalog
   scopes. The matcher limitation is validation evidence for the external gate,
   not a passed opacity control.

2. Replace the two sentences beginning **“Two pre-existing, reserved Convention
   equation names…”** with:

   > The compiler census has 132 non-private additions and 179 removals,
   > including generated proof and instance artifacts; these are distinct from
   > the +3/−6 source-export delta. Two additions are Convention's pre-existing
   > reserved split-search equations, materialized lazily by Primitives. They
   > were not materialized in the baseline. Convention-only opacity probes
   > check their availability and use; gate118 must still assess this exact
   > published-equation use under rule10. No general generated-reader exemption
   > is assumed.

   The current phrase “the two compiler-visible additions” risks suggesting that
   only two non-private compiler constants were added. `generated-equation-review`
   supports reserved-name availability, not pre-existing materialization or gate
   approval.

Three small precision edits are recommended:

- Replace **“removes356 private Catalog copies”** with **“retires 356 private
  Catalog declarations”**. The number includes implementations, configurations,
  types and proofs, not 356 separately duplicated theorem statements.
- Begin the preservation sentence **“Relative to #230's API tree, surviving…”**
  to keep all freeze claims attached to their actual base. The draft correctly
  says the PR itself includes #230 until that prerequisite merges; retain that
  prerequisite warning and the campaign target branch.
- Replace **“Those proposals are tested but not applied.”** with **“The bounded
  proposals have isolated owner/consumer tests and remain unapproved and
  unapplied; they do not constitute integrated landing repairs.”** The first-entry
  and zero-space consumer checks are explicitly hypothetical. Keep external
  gate118, the full current downstream replay and expanded screens pending.

Before publishing after the in-flight comment cleanup, refresh the exact source
pins and reconcile them with the recorded archived preflight inputs. The existing
140+228 inventory was checked before that cleanup. Describe it as the recorded
preflight/inventory until the final source identity check is attached; comment
changes should not silently replace the evidence's input hashes. Refresh the
description again if any pending API/home decision is later implemented.

No other missing human-dependent HOLD was identified in this bounded wording
review. T4/T7 dispositions are being reviewed separately, so this note does not
assert complete assigned-factoring closure or accept retained debt.
