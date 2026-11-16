# Final helper-seal manifest review

This is a read-only metadata/source review by final_manifest_review, written in its own
sc-yao-b worktree. No Lean, Lake, tree check, proof edit, commit or delivery was run.
The authoritative root sources were read cross-path. All272 prepared probes reconstruct
current67helper children plus the hub byte for byte after exactly42 injected lines.
Every source has A/B × strict/coe, and all probe paths/module stems are unique.
All68source files are genuinely absent at the issue base, independently checked by git
ls-tree. The three shard manifests equal manifest[0::3], [1::3], [2::3], with91/91/90 rows,
so their union is complete and disjoint. Maximum source width is100.

The injection follows all original imports and adds import Lean plus the sealing command;
all other source bytes are preserved. It iterates the complete environment, selects every
TCSlib-origin definition by its module (not namespace), seals generated matchers even when
reducible, skips only authorized reducible abbreviations and the requested polynomial/
projection-coercion notation, checks installed irreducibility, and logs every exclusion.
A excludes PolyExpr.eval as notation; B seals it. Coe variants exempt only projection-bodied
Coe/CoeFun. Foreign core/Mathlib explicit-definition discipline is a separate root audit.

The runner imports one own bootstrap TCSlib tree plus own package paths. The optional
.lake/build/lib/lean fallback does not currently exist. Independent --output-root paths are
used only for fresh outputs, not appended to LEAN_PATH. There is no dependency-tree copy,
foreign-session artifact reuse or joining of TCSlib trees. Each shard is sequential; every
Lean command passes through the unmodified shared wrapper, with tag sc-yao and maxErrors0.
Both diagnostic forms and fresh output files are recorded. LEAN_SLOT_DIR and LEAN_SLOTS
are unset in the inspected environment; no custom slot override is installed by the tools.

Two prelaunch robustness improvements were sent to root. The initial parent-only EX lock
could be released if the parent died while a child survived. Parent and child shared import
locks, with ordinary writers retaining exclusive locks, preserve the barrier through such
an interruption. The initial final aggregator did not compare result hashes to initial
probe hashes. Root agreed to add both guards before launch. The implementation and runtime
verification of those fixes remain root-owned; this report does not claim pending checks
passed. probe-inventory.json supplies independent exact hashes for all272 source/probe pairs.
Reviewed tool versions and hashes are retained here, even if root subsequently strengthens
them. Before/after TCSlib artifact hashes, full final results and package manifests remain
required final evidence.
