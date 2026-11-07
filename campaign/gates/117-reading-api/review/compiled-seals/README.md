# Gate 117: compiled census, axioms, seals and consumers

Executed evidence for frozen PR head `1160c18f03fd318f0dec25738790935fa61379d4`, against
base `e3adffac67377a8b6e23bed74bfdbb44a123dd86`. The checks below pass in their stated
scopes. **Not yet clear to merge:** the external gate and the maintainer's replay/merge
decision are separate. This folder does not claim a global seal of legacy code or a
repair of the complete `condTM` consumer.

## Compiled population and axioms

`Census-base` and `Census-head` enumerate every constant owned by the five changed
modules, including internal/generated/private constants, with its full name, module,
kind and privacy flags. They filter only by owner module. The raw outputs and parsed
`census-{base,head}.json` are retained.

| Module suffix | Base | Head | Added |
| --- | ---: | ---: | ---: |
| `Encoding` | 175 | 176 | 1 |
| `Simulation` | 162 | 175 | 13 |
| `Composition` | 86 | 88 | 2 |
| `Build.Wrappers` | 80 | 85 | 5 |
| `Build.Primitives` | 1279 | 1281 | 2 |
| Total | 1782 | 1805 | 23 |

There are exactly **23 new public theorems**: eight explicit source declarations and
15 generated field readers. No constant is removed or changes its owner/kind/privacy
classification. The private population remains 1293. There is no additional new
internal/private/compiler auxiliary; the separate target-prefix auxiliary scan also
finds none. This conclusion comes from the unfiltered delta, not a target-name filter.

`Metadata-head-v2` walks axioms for all 23 actual new names, checks their simp membership,
prints their complete types, inventories referenced TCSlib definitions and their owners,
and dynamically inventories the imported default simp definitions/equations.

- Eight explicit theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- Ten Simulation field readers use only `propext`, `Quot.sound`.
- Five capture-field readers are axiom-free.
- All 23 are public, non-internal, and absent from both the simp-lemma and unfold sets.

No new theorem depends on `sorryAx` or a custom axiom. The five generated names in each
of the `leftCfg`, `rightCfg`, and `captureCfg` families are exactly `_state`, `_inputPos`,
`_workTapes`, `_workTapePos`, and `_output`. Their actual compiled types, including all
index/cell binders and capture universes, are in the metadata log.

## Owner-scoped strong seals

The direct foreign ordinary-definition inventory is:

| New theorem home | Foreign ordinary definitions in its new compiled types/proofs |
| --- | --- |
| Encoding | none |
| Simulation | `MultiTapeTM.runFrom` |
| Composition | `MultiTapeTM.initCfg`, `MultiTapeTM.spaceUsed` |
| Primitives | `MultiTapeTM.initCfg`, `MultiTapeTM.spaceUsed` |
| Wrappers | `FinTM.bufferTape` |

The actual default simp-definition inventory adds `Action.apply`, `Cfg.init`, and
`MultiTapeTM.initCfg`. No additional definition is exposed through an active `eq_*`
simp equation in this import closure.

All five `Owner-*-sealed` probes pass, exit 0 with zero errors. They are complete copies
of the exact frozen owner sources with guards around **only the nine new source
insertions**. Each guard seals the six-definition union above, except that Simulation's
same-home `bufferTape` is excluded there. It removes the three model definition-level
simp attributes while the new section elaborates, then restores those original attributes
before legacy code continues. `analyze.py` checks that removing only these guards recovers
the frozen source byte for byte. Source and guarded-copy hashes are recorded in
`owner-full-source-map.json` and `context.json`.

Same-home definitions may reduce in their own reader proofs. Legacy sections remain
unsealed, and their existing sorry/linter warnings are retained in the raw logs. Those
warnings are not a claim about the new APIs: the independent compiled axiom walks above
cover all 23 additions. Nothing here certifies the old implementations globally.

The remaining nine foreign definition references are reducible structure projections:
the five `Cfg` fields, `FinTM.k`, `FinTM.State`, `FinTM.tm`, and `MultiTapeTM.tr`. The metadata
classifies them as abbreviation hints. `Abbreviations-unsealable` actually attempts each
standard irreducibility attribute: exit 1, exactly nine rejections because they are
reducible. They fall under the policy/TEMPLATE abbreviation exception. No unsafe
reducibility or relaxed transparency option is used.

## Actual published consumers and controls

`Published-consumers-sealed-v2` passes using the actual head APIs, with all 16 relevant
ordinary definitions sealed **before** its headers and with the three model simp
attributes removed. It consumes every new API name:

- The actual `CodeTM.toFinTM_eq` transports the bundled space expression to the raw one.
- Three complete field-collection theorems consume all 15 actual generated readers.
- Four arbitrary-natural-bound space proofs use the actual zero-space equations.
- The actual branch shape/run equations support the explicit transported view and a
  conditional right-bank consumer. Its host-table-agreement premise remains explicit;
  no full legacy `condTM` repair is claimed.

All ten consumer theorem axiom walks are within the same standard sets; the capture
consumer is axiom-free. These probes do not replace the APIs with hypotheses.

The 16 consumer seals are listed in `control-definitions.txt`: the six model/default
definitions, the bundled/configuration/branch/four canonical-machine definitions, and
`rightAction`. The paired controls instantiate their actual compiled defining values.
For structure-valued results the point control projects a data field, so it differs
from the abstract whole-function equation even for nullary machines. Each positive
direct `Eq.refl` proof is installed as a theorem through the kernel's `addDecl`; a
failed proof is never admitted.

- Unsealed controls: exit 0, zero errors, exactly 32 distinct kernel-checked successes.
- Sealed controls: exit 1, exactly 32 labeled failures, one pointwise and one abstracted
  equation for each of the 16 definitions.

`check_controls.py` verifies exact identifier and diagnostic multiplicities, not merely
the total error count. Its own negative cases reject duplicate diagnostic identity
while preserving count, missing identity, an unexpected pass, and a zero negative exit.
See `control-check.json`. Every actual failed control goal is printed in the raw negative
log with its definition/mode identifier.

## Retained attempts and receipts

Three development attempts are retained and superseded:

1. `Metadata-head`: one printing error because `ReducibilityHints` has no `Repr`; v2
   prints its constructor classification explicitly.
2. `Owner-sections-sealed`: three errors because `simps` cannot modify imported
   declarations. The successful exact owner-source copies replace this attempted method.
3. `Published-consumers-sealed`: four header errors from partially applied
   `Fin.addCases` without an expected motive. v2 supplies the explicit motives. Failed
   attempt error-recovery axiom prints are not evidence about the published APIs.

All raw sources, outputs and per-run receipts are retained. `results.json` reconciles
all 15 runs, actual exits/errors, input/output hashes, full source recovery, 23-name
coverage and axiom/simp results. `analyze.py` and `check_controls.py` reproduce these
checks; `SHA256SUMS` covers this folder.

Every elaboration used only `devtools/seyoon/leanelab.sh`, one Lean process at a time,
shared slot locks/local budget three, against complete `oleans-mac3` or
`oleans-reading-preflight2` trees and the corresponding managed worktree. Copies named
`.lean` lived only in unique `/private/tmp/tcslib-gate117-seals-*` directories. No Git
operation mutated state; no actual source, snapshot, cache, screen, or reference was
changed by this review. The 394-module replay is separate maintainer evidence.
