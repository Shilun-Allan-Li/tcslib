# RAM work branch: records

This folder holds the records of the RAM work on `complexity/ram-simulation`: proving stage 2's
14 admitted declarations in `TCSlib/Complexity/RAMSimulation/` (Seyoon, 2026-11-17). Like the
chapters 3–4 campaign's `campaign/`, it stays off `main` when the branch is integrated.

**Shape (Seyoon, 2026-11-17).**
- The branch was cut from `main` at `5cb25d52` (after the chapters 3–4 integration, #364), with
  `seyoon-devtools` merged in for the wrappers and the gate kit (`devtools/seyoon/gatekit/`).
- **Lean changes reach this branch by gated PRs**, and the branch reaches `main` later through
  one integration PR, as chapters 3–4 did.
- **Records go directly to this branch**, after a fetch and rebase.
- **Fills are Codex's, as delegated fills.** The maintainer writes a brief per tier, stages it on
  the exchange for Seyoon to dispatch, then lands each delivery as a gated PR. Seyoon dispatches
  the audits and merges.

**Rules.** `policy.md` and `workflow.md` at the root, then `campaign/maintainer/WORKFLOW.md`
(inherited from chapters 3–4), `campaign/standards/TEMPLATE.md` and
`campaign/standards/fill-environment-addendum.md`. In particular:
- elaborate only through the `devtools/seyoon` wrappers, never `lake build`, within the pool of
  `leanpool.sh`;
- ask before new public APIs, statement changes, renames, frozen-file imports, home decisions or
  debt acceptance;
- no campaign labels in Lean docstrings (gate 159's G159-01);
- no model identifiers in repository artifacts.

**State:** `maintainer/HANDOFF.md`. **Plan:** `items/ram-tm/PLAN.md`.
