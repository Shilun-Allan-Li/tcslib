# Required API axiom diagnostic — NOT RUN

RequiredAPIAxioms.lean contains24 fully qualified #print axioms commands for the
exact external APIs used by the prepared proof routes. It imports only the current
cached area facade TCSlib.Cryptography.Obfuscation. SupplementalAPIAxioms.lean
optionally covers10 additional direct readers and semantic glue APIs.

Both files contain no declarations, tactic blocks, execution commands, automation,
or implementation changes. No script, Lean/Lake/cache, git command, or agent spawn
was run for this task. Only source searches and temporary diagnostic text were used.
Each full namespace/name was checked against the declaration and enclosing namespace
in the current source; APIs.tsv records the positions and intended role.

Root may copy the primary text into an evidence/probes module and invoke the
existing serial pinned-slot probe/check route after M0 controls, with the existing
job olean tree and no olean output. No cache/build/import change is needed. Retain
the complete stdout/stderr and both error forms. Each command should print its
named constant and its complete transitive axiom set; an unknown-name/import error
is a diagnostic failure, not an empty axiom set.

Inspect each printed set for sorryAx or any axiom outside propext, Classical.choice,
and Quot.sound. Report any offending API by its exact name and source; do not infer
that it is an io-sprg hole merely because the area facade imports146 M0 holes.
#print axioms follows the selected constant's dependency graph, so unrelated
imported M0 holes do not automatically contaminate these external API prints.
Conversely, a pre-existing sorryAx dependency of a MUST-REUSE API would be inherited
by downstream proofs that consume it and must be addressed explicitly by root.

This is an early dependency diagnostic. It neither fills a theorem nor replaces
the final axiom census/trace of every stored new constant. No output, pass, absence
of sorryAx, or proof validation is claimed before the lead runs the probe.
