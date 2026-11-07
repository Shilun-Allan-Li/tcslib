# Stronger public pair-bound comparator — passed hypothetical adapter

**Not yet clear to merge: #215.** A mechanical opaque adapter exists for the exact current private header, using the already published `Complexity.length_pair_components_le` (`ClassNP/PolyTimeBlockLoop.lean:207`). The new BlockLoop import remains **unapproved and unapplied** by this task. No new public API is required by the observed route.

The target remains exactly:

```lean
private lemma clA5Pair_sizes (w : List Bool) :
    (clHeaderField 0 w).length ≤ w.length ∧ (clHeaderTail 1 w).length ≤ w.length
```

The two same-home header definitions and complete target header/docstring were copied literally from current Hardness, hash `a6edf9fe11e89d71a028143d1cedf9be896124bbcbc5a86d779e6c6278b5c597`. The hypothetical fragment imports the six actual Hardness imports, in order, plus BlockLoop. It does not import/refer to inaccessible private definitions from another file.

The public bound is stronger: `2*(pairFstD w).length + (pairSndD w).length ≤ w.length`. A total projection equation on malformed inputs is unnecessary for this adapter:

1. Reduce only the same-home `clHeaderField 0` / `clHeaderTail 1` definitions and split the opaque value `pairDecode w`.
2. On `none`, both local fields are empty, so both required bounds are zero bounds. No value of foreign `pairFstD`/`pairSndD` is read.
3. On `some (a,b)`, the existing public inverse identifies `w = pairEncode a b`. The public `pairFstD_pairEncode` / `pairSndD_pairEncode` equations adapt `length_pair_components_le w` to `2*a.length+b.length ≤ w.length`; arithmetic gives both desired inequalities.

`Inventory-v1` confirms all four named reader/bound theorems already exist as nonprivate compiled theorems, with their actual owners, complete raw types and standard axioms, before candidate use. No `.eq_def` or `.eq_1` was queried, materialized or used.

## Executed checks

- Exact-header native fragment: **PASS4.43s**.
- Strong sealed fragment: **PASS1.73s**, with pairEncode, pairDecode, pairFstD and pairSndD irreducible **before the helper definitions and target doc/header**. All four are actual ordinary definitions. Their default simp/unfold flags are false, so no default-definition simp attribute needed removal. Native/sealed metadata is byte-identical.
- One root plus two generated proof auxiliaries: axioms exactly `[propext, Quot.sound]`; no sorry or nonstandard axiom. The complete direct ordinary-definition inventory is exactly the four guarded definitions; direct TCSlib theorem homes are Encoding, PolyTimePairing and PolyTimeBlockLoop. Same-home header helpers remain local.
- Fresh point and abstract controls for every guarded definition: all **eight pass unsealed and fail sealed**, with exactly eight diagnostic identities/multiplicities. The checker rejects four deliberately malformed evidence cases. No unsafe reducibility setting or private imported alias is used.
- Explicit argument review: `change` reduces only the two same-home header functions; foreign `pairDecode` remains symbolic. `simp only` uses Option/List theorems, the inverse equality and the published projection equations. No foreign ordinary definition is passed to `simp`, `rw` or `unfold`.

All five invocations were sequential managed plain `leanelab.sh` elaborations against the complete read-only MSG5 tree, local budget3/machine5. Raw commands, complete outputs, input hashes, all probe sources and controls are retained. The negative control exit1 is expected; there were no unexpected failed attempts.

## Concrete proposal and limits

`proposed-body.txt`, `body-only.patch`, `hypothetical-Hardness.patch` and inert `Hardness-proposed.lean.txt` make the possible source change reviewable. Reversing exactly one import and one proof-body replacement recovers the current full source byte-for-byte. The full proposed module was **not** elaborated; only the small exact-header fragment was pre-shipped. Production source/imports remain unchanged.

The source-header import closure would grow **51→54 TCSlib modules**, adding PolyTimeBlockLoop, EmitIterBody and EmitIterEmbed. The full Core/package source closure grows2738→2741 by those same three modules; all compiled inputs are already present, and the hypothetical TCSlib graph is acyclic. Exact source/olean pins and counts are in `hypothetical-import-delta.json`. The current Encoding-based proof is mathematically valid; this result establishes that the stronger public comparator can also be consumed through its published interface.

Applying this proposal needs Seyoon's import ruling and fresh production-source checks/replay appropriate to the changed tree. It does not inherit a full-module pass from this fragment or extend the frozen d0c4 current-comparison evidence. The upstream theorem's existing proof was not sealed or rewritten here. No debt acknowledgment, new API approval, dispatch or gate closure is claimed.
