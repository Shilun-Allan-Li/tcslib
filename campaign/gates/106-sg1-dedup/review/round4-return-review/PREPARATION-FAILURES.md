# Preparation outcomes retained honestly

The four upstream failures in round4-compiled-and-seals/attempts remain failures: missing namespace on appended census commands (three actual diagnostics although the old generic counter said one), reserved local identifiers, projection-query namespace/type misuse, and an offline Python SyntaxError before any Lean run. Their complete sources, receipts and compressed outputs are in the published/frozen inputs and were hash checked; none is an owner-source failure or a successful probe.

This return review also retains its own data-only preparation failures, without changing any input or source:

1. A displayed source slice requested through line369 of the365-line PolyTimePrefix capture, producing an IndexError after the relevant source had printed. It was a read-only display failure, not Lean/native/source validation.
2. checks-attempt1 assumed every section included a final separator newline; the first Markdown section showed that separator belongs between indexed sections.
3. checks-attempt2 corrected the first section but did not yet skip the inter-section separator.
4. checks-attempt3 handled separators but had not yet accounted for plain code fences around .lean/.py inputs.
5. checks-attempt4 passed publication/source/compiler/archive/control/screen checks, then incorrectly compared occurrences of -j4 to launch count. The actual MSG8 trace has329 launch lines, each with two redundant -j4 tokens.
6. checks-attempt5 passed the preceding checks but used an invented dictionary key sg1_new_head; the recorded key is sg1_after_f6.

Each failed checker version and stdout/stderr remains in this folder. Corrected checks-attempt6 exited0. retention-attempt1 exited0. None of these reviewer preparations executed a delivered script or a Lean/screen/replay job, changed source/Git/snapshots/cache/canonical records, or alters the independent audit result.
