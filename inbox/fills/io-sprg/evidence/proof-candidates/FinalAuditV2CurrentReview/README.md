# Final-audit V2 integration review — AST-only, UNRUN

All candidate adapter and gate scripts remain unexecuted. No source, Lean, cache, Git or child-agent action was performed. This review compares their text with the current runners and actual archived evidence schemas. Root's independently executed freeze_global.py is separate from these adapter candidates.

Three minimal candidate fixes are staged under candidates/ with exact before/after hashes in candidate-fix-bindings.json:

1. checkpoint_report.py: actual completed-theorem-names-v2.json is a JSON string array. The old whitespace split would retain quotes, commas and brackets and fail exact census lookups. The replacement accepts either a strict JSON string array or the documented whitespace list, rejecting empty/duplicate/nonstring/whitespace-containing names. Existing name, theorem-kind and standard-axiom checks remain.
2. io-sprg-rule10/prepare_static.py: remove only the unused collector-order.txt write hardcoded to the old io_sprg_m0 collector. orchestrate.py already emits its own run-specific orders/collector.txt. No owner/closure/runtime guard is reduced.
3. checkpoint_inventory.py: strengthen the root-export Counter guard by also preserving the original command sequence after removal of exactly the single approved import insertion. This prevents accidental import reorder while retaining the existing exact-content guard.

Current compatibility findings:

- Dynamic inventory must be regenerated from pinned base to the committed final HEAD. The filesystem currently has 34 observed area source owners (including new Sections); no fixed 22/26/33/34 count is valid as a final discovery mechanism. Every newly added owner must remain in the exact owner-by-four Rule10 coverage, seals and control set.
- bootstrap_runner source-build records provide module (slash path), rc, errors, error_forms, source/head/log/object bindings. runner_full probe records instead provide rc, errors, error_substr, sorry, warnings and source/log bindings, with object_sha256 null. V2's explicit scan now uses the actual probe fields plus independent diagnostics scanning; no remaining required-error_forms mismatch was found.
- Actual seals manifest brief fields are label/module/source/source_sha256/probe_sha256/probe_module/requested/term_names/term_in_closure/stored_constants/term_excluded. Detailed records add rev/closure_modules/term_readers/rows. Current V2 consumers match these names.
- Actual control plans contain label/module/owner/kind/sealed/requested/controls/expected_errors/source_sha256; control rows contain control/target/reader/negative/start_line/end_line. Coverage rows contain target/reader/letter/status/owner/requested/term_used. V2 consumers match these schemas and retain exact expected-set checks before totals.
- Historical M0 rev=HEAD is not a resolved current-head binding and must be regenerated, never relabeled. Existing M3 selected-axiom summaries lack inventory/environment/owners/full-graph bindings and are not valid inputs to the full V2 census reporter. Regenerate the full canonical graph/print pipeline; do not add a schema bypass.
- CensusGraph.lean has the expected owners list and GRAPH/ROOTMETA/STMT markers. Full owner builds must precede collectors/seals. Any owned olean change invalidates the captured environment and requires fresh bound gates. Final tagged slot snapshot must follow the last Lean/cache action and retain the historic known overlap; it cannot claim whole-history serialization.

No additional definite runner/result schema failure was identified. The three candidate scripts parse as Python AST, but runtime, environment, gate and package validation remain pending root execution. A source change during this review can stale the captured hashes; use the recorded bindings rather than blind overwrite.
