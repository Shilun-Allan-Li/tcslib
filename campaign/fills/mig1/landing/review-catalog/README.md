# Catalog migration: independent source and guard review

**Not yet clear to merge: MIG-1 landing — three Catalog rule-10 HOLDs remain.**
This is an internal maintainer review, not an external gate, fill, dispatch,
merged-tree replay, or acknowledgment of debt.

The current Catalog has **24 changed/new proof regions passing** a guard of **45
ordinary foreign definitions**, with **90 calibrated controls**. The two pending
constant-space rows and the redirection row are excluded from that passed claim.
The independently discovered CodeSimulator configuration-read gap was repaired
by the root maintainer; its exact repaired source now passes the full **22-name
guard**, with **44 controls**. All original failures and narrower passes remain.

## Exact source and context

- Catalog: `eb55b3b7688f3949667df21151b8dc3036b99bd80ed467b20bf466bcedee213d`,
  209,176 bytes, 4,123 lines; archived as `Catalog-current.lean.txt`.
- Initially supplied CodeSimulator:
  `78837a1492da3245b0a5b54573d850294ae5b3f1dacde2e470d111b171be8b70`,
  archived as `CodeSimulator-current.lean.txt`.
- Root's one-line CodeSimulator repair:
  `57e7dc52dedf3d146499ad5694270d1c6fee7255cad74338d4174c5cce3e1a73`,
  archived as `CodeSimulator-repaired.lean.txt` and checked unchanged on disk.

The supplied worktree is `wt-epad`, source commit `af3273…` plus uncommitted
repairs. Frozen comparison data came from `wt-natbits`, supplied API head
`1160c18f03fd318f0dec25738790935fa61379d4`; this review ran no Git command to
independently attest those supplied commit identifiers. Both full comparison
sources are preserved.

All **21 actual elaborations** used the managed `leanelab.sh` wrapper, authorized
scratch locking, local budget three under the machine limit five, no outer lock,
and plain elaboration with no compiled output. Their own wrapper intervals do
not overlap. Inputs, copied `/private/tmp` sources, requests, raw logs, exit codes
and input/output hashes are independently checked in `verification.json`.

The complete read-only import tree was `oleans-mig1-preflight-current1`, whose
eleven compiled modules match the parent's archived preflight receipts. Its
Primitives source is exactly **milestone2** (`2e3fab6f…`), not the concurrently
edited later private T2 proof. Its compiled CodeSimulator is the initial
`78837…`; the repaired `57e7…` is checked by a fresh **whole-source** plain
elaboration against unchanged imports. Controls depend only on unchanged
definitions. No new current snapshot or full downstream replay is certified.

## Confirmed HOLDs

| Row | Exact current source location | Confirmed strict failure / disposition |
| --- | --- | --- |
| `computesFunInTime_pairDup_spaceUsed` | `Catalog-current.lean.txt:2223`; old `rfl` at 2231 | Its constant space bound still uses zero tape count by reducing opaque `pairDiagTM`. The separately proposed zero-space reader remains unapproved. No weakened bound or substitute API was used. |
| `computesFunInTime_incFixed_spaceUsed` | `Catalog-current.lean.txt:2324`; old `rfl` at 2331 | Same issue for opaque `incFixedTM`; its separate zero-space reader remains unapproved. |
| `redirectTM_spaceUsedByTape` | `Catalog-current.lean.txt:2412`, header tape index at 2415 | With `redirectTM` sealed **before the docstring/header**, `i : Fin M.k` is rejected where `Fin (redirectTM M haltOn).k` is expected. Its subsequent proof goal also fails. This is a frozen-header/home issue, not merely an omitted rewrite in the body. Root has a separate bounded home/statement proposal; no decision is made here. |

`Catalog-pending-strict-v1` records the first two failures (exit1/errors2).
`Catalog-strict-v1` guards the other 25 candidates and records the redirection
failure (exit1/errors2). `Catalog-eligible-strict-v2` then guards exactly the
remaining **24**, without weakening any guard: exit0/errors0, all 24 axiom prints
exactly `[propext, Classical.choice, Quot.sound]`. The three HOLD rows remain
unsealed outside that successful scope. Their native compiled axioms being
standard does not establish rule-10 compliance.

The successful full Catalog copy retains the same 28 linter warnings as the
parent's unguarded native compile; none was suppressed. Root's new increment
helper accounts for one unnecessary sequence-focus warning. The repaired Code
copy has no warning.

## CodeSimulator gap and validated repair

Root's 21-name guard passed initially, and all 21 associated pairs already exist
in the final CertShell 41/82 controls, including `stateWord` as C41. Direct source
review found another reached ordinary definition, `embedEmitCfg`. Extending the
guard to 22 exposed the implicit field reading in `canonPreserveInstall`:

```lean
-- old source line 1312, after rw [lift]
exact cut₁ u hu
-- root's exact repair at the same line
simpa only [embedEmitCfg_state] using cut₁ u hu
```

The original exact source with 21 guards passes (`CodeSimulator-strict-current-v1`),
but the same source with 22 fails once (`v2`); the failed axiom print contains
`sorryAx` and is not a success claim. The exact root-repaired source with 22
guards passes (`v3`, exit0/errors0) and its target has standard3 axioms. Guard
removal restores each respective source byte-for-byte. This is a mechanical use
of an existing public reader; no API, statement, import, definition or table
changed. `Code-controls-*-v2` adds only the missing `embedEmitCfg` pair, for 44
examples total.

## Freeze and assigned factoring

`freeze.json` uses a balanced **depth-zero proof delimiter**, so named arguments
such as `(input := x)` inside a header cannot truncate the comparison. It confirms:

- Catalog public declarations **113→107**: exactly the six approved canonical-row
  retirements, with no public addition.
- Private declarations **392→39**: 356 private retirements and precisely three
  new proof helpers: `catalog_buffer_clip`, `catalog_increment_framed`, and
  `pairExtract_space_row`.
- Every retained public/private header, visibility and relative order is literal
  equal; every retained definition, type and transition-table body is literal
  equal. The sole Catalog import addition is the explicitly authorized
  `Build.Primitives` edge (megafill brief lines94–97).
- There are **27** actual proof changes/additions. Four further changed
  declaration chunks have doc-only differences and byte-identical proofs:
  transfer, copy, clear and compare framed rows. These unchanged proofs and other
  legacy helpers remain outside the local guards.
- CodeSimulator retains all **208** declaration names, headers, visibility,
  order, imports, definitions and tables. Its only changed declaration versus
  frozen1160 is the private `canonPreserveInstall` proof, including root's final
  field-reader repair (`code-freeze-repaired.json`).

T5's proved material now shares the private clipping fact between canonical copy
and transfer endpoints and the framed increment fact between success and overflow.
T6's three extraction space rows share `pairExtract_space_row` and cite the
published time/space-from-time interface. These are proof helpers, not new machine
hosts. Their signatures and uses were read in full and included in the passing
guarded regions.

The executable `copyMapTM` and `transferMapTM` tables are retained **byte-for-byte**;
their rewind actions have different semantics. Combining their literal table
data into a parameterized implementation would change frozen public definition
bodies. This review distinguishes that retained data from the proved material
factored above. It does not approve a table exception, acknowledge new debt, or
claim that all possible legacy duplication has been screened. No new large
copy-text screen was run or cited.

## Guard coverage, controls and arguments

Catalog's final inventory extends model14/Simulation5 with the directly reached
configuration/pure/witness constructors. `loopHostTM` is an allowed reducible
abbreviation; its underlying **ordinary private `loopHostM` is also sealed**.
The standard `open private … from …` command exposes it only in scratch guard and
control instrumentation, using a normal validated irreducibility attribute. No
unsafe reducibility option, production private reference, or new API is involved.
Unchanged legacy theorem helpers remain opaque and outside the guard.

Every guard precedes its declaration's docstring and header. Existing default
simp attributes on `Action.apply`, `Cfg.init`, and `MultiTapeTM.initCfg` are removed
within each instrumented region and restored before the following legacy code.
Removing all instrumentation restores the exact archived full source.

| Final controls | Unsealed | Sealed |
| --- | --- | --- |
| Catalog: 45 definitions / 90 examples | exit0, errors0 | exit1, exactly90 expected `rfl` failures |
| CodeSimulator: 22 definitions / 44 examples | exit0, errors0 | exit1, exactly44 expected `rfl` failures |

Each pair is checked with **only that definition sealed in its own section**;
there is exactly one expected error per example and no other error kind.
`*-controls-checked-map.json` gives exact IDs, definitions and source/error lines.
The offline checker rejects missing, duplicated-in-place, exit0 and wrong-kind
synthetic diagnostics. Thus a neighboring opaque definition cannot be the reason
a particular control pair fails.

All 81 recorded `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`change` sites in the changed
regions and repaired Code proof were inspected separately. No foreign ordinary
definition is passed as an unfolding argument. Two raw symbol mentions are term
parameters to `Nat.add_mul` and same-home `canonEmbedWords`, not unfolding commands.
Same-home `catalogTrace`, `catalogIncF/R`, `catalogTape` and local proof lets are
legitimate named arguments. Core/Mathlib uses name equations/lemmas; no Core or
Mathlib definition is explicitly unfolded. This is a bounded source review,
not an exhaustive library sweep (`tactic-arguments.json`).

## Axioms, failed attempts and limits

`Compiled-axioms-v1` imports the exact preflight modules and prints all **27
changed Catalog roots plus the initial Code root**: all 28 are standard3. This
resolves the earlier focused mra2 identity-row `sorryAx` context limit, because
the combined Composition proof is now compiled. The repaired Code root is
separately standard3 in its fresh strict22 source run. Global census/compiled
metadata and final replay remain the root maintainer's separate work.

All failed Lean attempts are retained: the original Catalog25 seal, two-row
negative, two signature-inventory mistakes (wrong namespace, then numeric private
name syntax), a private-control qualification mistake (v2, rejected), and the old
Code22 field-read failure. Catalog control **v3** and Code control **v2** are the
authoritative successful pairs. The two preparation failures occurred before
Lean and are described separately; their original scripts are preserved. None
is silently counted as a pass. All eleven compiled context hashes remain
unchanged at final verification; no source, Git, snapshot, cache, or compiled
output mutation was performed by this reviewer.
