# Sparse actual-Name catalog review

Source-only independent review. No Lean/Lake execution and no active source/evidence changes. This reviews the proposed early wanted-spelling filter against `evidence/tools/prepare_seals_final_r2.py:201–239`; it does not certify an uninspected generated candidate or any performance result.

## Equivalence argument

Let `N` be the ordered actual `(Name, ConstantInfo)` entries traversed by the existing `env.constants.map₁.toList` loop. Let `s(n) = n.toString`, and let `H(n)` mean that the unchanged `getModuleIdxFor?` succeeds and the actual indexed module name has the existing actual-Name `TCSlib` prefix. For every spelling `a`, the old catalog value is the ordered array

`C[a] = [ n in N | H(n) and s(n) = a ]`.

Let `W` be the set of exactly the spelling fields of the original strictly parsed request rows. The proposed loop changes this to

`Cw[a] = [ n in N | s(n) in W and H(n) and s(n) = a ]`.

For every requested row `(a, home)`, `a` belongs to `W`, so `Cw[a] = C[a]`, with the same names, multiplicities and order. Therefore the original request lookup, `ns.size == 1`, selection of the actual stored `Name`, exact module-home check, definition check, irreducibility installation/verification and count checks have the same successful input and successful result. No assertion about catalog keys outside `W` should be retained: this is a sparse index for the worklist, not a complete inventory catalog.

The membership test must happen before module lookup, but the actual module lookup and original home filter must still happen before pushing a surviving name into the array. Scanning every actual name remains necessary. A declared or guessed name prefix cannot replace that actual-name scan or module-home check.

## Collisions and unusual names

The argument uses equality of `n.toString` values, not injectivity or parseability of that rendering. If multiple actual names share a requested spelling, each passes the early test and is pushed by the unchanged original home filter. The original `ns.size == 1` then rejects exactly the same ambiguous spelling. Keep the `HashMap String (Array Name)` and append each matching actual `Name`; do not replace the array by one last stored name.

This includes private names and names with numeric components. Pinned Lean's `Init/Data/ToString/Name.lean:85–100,112–122` explicitly warns that number-component, anonymous and `»`-containing names may not round-trip, and handles macro-scoped/inaccessible names specially. That warning causes no gap in the filter argument: the request spelling came from the original actual-name census using the same `toString`, and all equal rendered spellings survive. No `String.toName`, parser reconstruction, escaping normalization, `_private` prefix reconstruction, or `Name` constructor guess should appear.

A collision between a requested TCSlib name and a non-TCSlib name remains harmless only because the original actual module-home filter still precedes catalog insertion. A collision between two qualifying TCSlib actual names remains an ambiguity and must still reject. A new local declaration with the same spelling and no imported module index is excluded by the same original `getModuleIdxFor?` branch. EOF must rebuild using its own current environment exactly as before; do not reuse the installation catalog or skip the final checks.

## Request parsing and multiplicity

1. Keep the serialized line count assertion. Parse each row by the same exact `splitOn "\t"` followed by an exact two-element list match before inserting its first field into `W`. Reject malformed rows; do not silently take the first two pieces of a longer row or drop blank lines.
2. Do not trim, case-fold or normalize either field. Byte-for-byte String equality must match the existing census/request convention.
3. The wanted HashSet is only an acceleration index. Preserve the original request line array/list, order, length and duplicates for the later validation/install/EOF loop. Deduplicating HashSet keys is safe; deduplicating the verified request rows changes multiplicity and final-count semantics and is not this equivalence-preserving optimization.
4. If the existing request rows contain duplicates, both versions see those duplicates. The original per-name already-irreducible skip must remain so a duplicate name or pre-existing irreducible attribute does not introduce a second invalid local status transition. Independently, the generated request-manifest uniqueness checks should remain in force.
5. Empty spelling or home fields still satisfy the old two-field syntax match but fail the existing absence/home checks as appropriate. Tightening those checks can be done deliberately, but is not needed for this optimization and should not be silently claimed as byte-for-byte error behavior.
6. Earlier strict parsing changes the timing of malformed-row failure: it rejects before the expensive environment scan. It does not turn an old invalid payload into a valid one. Successful payload behavior is the equivalence claim.

## Performance limits

Pinned `Lean/Environment.lean:1160–1162` implements `getModuleIdxFor?` as an environment-base constant-to-module-index map lookup. The proposed filter avoids that lookup for names outside `W`, but must render and hash every actual environment name. The old loop rendered names only after the actual TCSlib-home filter. String rendering/hashing may be expensive, so a speedup is a hypothesis until measured; the source review does not identify the observed 47.7-second bottleneck conclusively. `env.constants.map₁.toList` still materializes/traverses all entries, and the optimization does not remove any required name validation or reducibility update.

The full native census/inventory must remain unchanged and independent. Sparse lookup is appropriate only inside the install and EOF worklist resolver. Preserve fresh versioned candidate source, exact request rows, complete per-name install/EOF logs, and native collision/absence/home/status control evidence before adopting the candidate.
