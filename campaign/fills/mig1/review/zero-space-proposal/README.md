# Four zero-space readers: unapproved proposal

2026-11-07. **Not yet clear to merge.** This is bounded evidence for asking Seyoon about
exactly four new public operational facts. The scope has not been approved. No source,
API, Git, cache, compiled snapshot, or screen change was made.

Current-source searches and the compiled `Availability` probe found no published tape-count
or exact space reader for `idTM`, `constTM`, `prependTM`, or `pairValidTM`. Their time specs
do not state space. The compiled environment contains generated constructor `.eq_1`
equations for `idTM`, `prependTM`, and `pairValidTM`; this review does not treat those as
an approved machine run/contract interface. The existing public
`MultiTapeTM.spaceUsed_zero_tapes_eq_zero` requires a tape-count equality, which Catalog's
foreign `rfl` currently obtains by reading each owner's machine definition.

## Concrete minimal scope

Propose these four names in namespace `Turing.FinTM`, with no `simp` attributes or import
changes and no machine-definition changes:

```lean
-- Composition.lean, beside their machines:
theorem idTM_spaceUsed (x : List Bool) (t : ℕ) :
    idTM.tm.spaceUsed (idTM.tm.initCfg x) t = 0

theorem constTM_spaceUsed (w x : List Bool) (t : ℕ) :
    (constTM w).tm.spaceUsed ((constTM w).tm.initCfg x) t = 0

-- Build/Primitives.lean, beside their machines:
theorem prependTM_spaceUsed (w x : List Bool) (t : ℕ) :
    (prependTM w).tm.spaceUsed ((prependTM w).tm.initCfg x) t = 0

theorem pairValidTM_spaceUsed (x : List Bool) (t : ℕ) :
    pairValidTM.tm.spaceUsed (pairValidTM.tm.initCfg x) t = 0
```

Each means zero work-tape space at every finite horizon, on every input, including
pre-halting and post-halting times. Its owner-local proof is exactly:

```lean
  exact MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl
```

Here `rfl` reads only the same-home machine's zero tape count. The generic space and
initial-configuration definitions remain sealed. No time-spec proof is used, so the
probe does not inherit any admitted time specification from the current skeleton.
These operational facts avoid exposing four additional `*_k` readers.

## Actual validation

Complete snapshot: `oleans-mac2`, adopted at
`3555163f40d9c101a2ef4e81407c1bda58fe5ca4`; Lean `v4.25.0`. `context.json` records full
source/object pins and compiled module hashes; current Composition, Primitives, and
Deterministic sources match that base byte for byte. The existing adoption receipt is
`campaign/status/2026-11-07-natbits-merge/receipt.json`.

| Probe | Exit / errors | Result |
| --- | --- | --- |
| `Availability` | 0 / 0 | Compiled reader inventory and generic zero-tape theorem signature retained. |
| `Composition-home` | 0 / 0 | First two proposals prove using only Composition's existing import context. |
| `Proposed-and-consumer` | 0 / 0 | All four proposals and four sealed consumers prove in Primitives' import context. |
| `Controls-unsealed` | 0 / 0 | All 12 direct-definition controls pass. |
| `Controls-sealed` | 1 / 12 | All 12 paired controls fail, exactly two per effective consumer seal. |

The consumer seals all four canonical machines, `MultiTapeTM.spaceUsed`, and
`MultiTapeTM.initCfg` **before its theorem headers**. It removes `initCfg`'s definition-level
`simp` attribute. Each consumer proves space at most an arbitrary natural bound by
rewriting with the proposed operational fact and applying `Nat.zero_le`. It neither
extracts a tape count nor reads the machine body. This establishes the space-side repair
needed by cp07 Catalog's four canonical constant-space rows (lines 1934, 1949, 1968, 2128).
It does not validate their time conjuncts or the rest of Catalog.

All four proposal theorems and all four consumer theorems print only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom occurs.
No development elaboration failed; the negative controls are the intentional failures.

## Receipts, seal scope, and limits

Each source is archived as `.lean.txt`, read before running, and copied to a unique
`/private/tmp/tcslib-zero-space-*/*.lean`. `run_probe.py` invokes only the managed
`devtools/seyoon/leanelab.sh`, against the full snapshot, one Lean process at a time with
the shared slot locks and local budget three. Every actual run has a raw `.out` and
`-run.json` with command, timing, exit, diagnostic count, and input/output SHA-256.
`results.json` verifies those hashes and outcomes; `SHA256SUMS` covers this evidence folder.

The six effective consumer seals each have direct `rfl` controls: a projection delta and
complete constructor equation for each canonical machine, pointwise and abstracted
defining equations for `spaceUsed`, and a state delta plus defining equation for
`initCfg`. Their intentional negative diagnostics occur at source lines 13, 18, 21, 24,
27, 35, 38, 46, 51, 54, 58, and 60 of `Controls-sealed.lean.txt`.

The production-shaped probes pass no definition to `simp`, `rw`, or `unfold`: home proofs
use the existing zero-tape theorem, and consumers rewrite only the proposed theorem names.
No reducible TCSlib abbreviation is reached. The generic theorem's existing internal
proof is not re-audited as a new definition read. `runFrom`, visited-set, and per-tape-space
definitions are not directly read here; this is not a global Catalog seal.

Only these four facts are proposed. No `polyBits`, `pairExtract`, `pairDiag`, or `incFixed`
API is added or requested by this review. Full Catalog consumer integration, its complete
foreign-definition inventory, and the ordinary gate/replay requirements remain outside
this bounded proposal. The new public facts must be approved before implementation.
