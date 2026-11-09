# Incremental cleanup acceptance

[PR #248](https://github.com/Shilun-Allan-Li/tcslib/pull/248) targets
`cryptography/pass-shelat-ch2-4` at candidate `7750947a65d262b8a4e4e557b6dae2a48865807a`.
The Lean comparison base is `b9f39f118efa40f4d76e0ebe8d7db59555b11735`.
The checked live campaign tip `811373578e079b8a4b86f20ed8406a768de15032` has the
same Lean, checker, and dependency inputs. This implements the
[approved incremental target](../../../CLEANUP-PLAN.md).

The delivery's 13 attributed commits remain in the branch. Reconciliation
resolved 21 conflict hunks across 13 files and retained the #232 probability
projection fixes. The last commit changes two proof bodies.
`Ensemble.copies_X` and `YaoMachine.ans_layout` had acquired conversions
through the relocated block definitions. The focused checks exposed those
conversions even with their earlier blockers transparent. The repaired
proofs use the existing copy, product, and block equations. Their
statements and the representation bodies are unchanged by the repairs.

## Verification

| Check | Exact result |
|---|---|
| Ordinary Lean | 1,075 local modules pass, including `TCSlib` and campaign Checks. 82 ran fresh on the repaired head and 993 retained objects were verified against their source and prerequisites. |
| Whole-file seals | 168 valid harnesses across 122 edited owners and 46 unchanged sources with changed import closures. 80 ran fresh on the repaired head and 88 had identical source, masks, and transitive import objects. |
| Sensitivity | All 13 control outcomes and both repaired block-helper probes match their expectations. |
| Explicit tactic reads | 344 retained entries, each paired with its baseline occurrence, including the selected-open review. |
| Generated-equation reads | 4 retained actual pairs, 57 removed, with zero additions. |
| Kernel census | 11,201 actual stored declarations across the scoped modules. Retained handwritten types and 59 admitted-dependent identities are unchanged. The 94 changed types belong to generated auxiliaries. All five standard-axiom shifts and 13 changed definition values are accounted for. |
| Style | The repair adds no new lint failure. Four fill-owned files crossed 1,000 lines in the increment. GGMReduction, HardCoreLemmas, GraphIsomorphism, and ThreeColoring/Machines stay intact under the fill-size rule for the planned layout stage. |

The full baseline produced 657 raw seal diagnostics.
The final source produced 465, including two
interactions with pre-existing local irreducibility attributes.
The ledger pairs the retained failures with the original source, provider,
and native evidence, including focused baseline runs for failures that
only become visible after an earlier read is repaired. Several diagnostics can come from
a single declaration. The baseline
has 47 source show/change hits on failing lines and the candidate
has 42.

## Carry-forward and provenance

The archived ledger keeps all 509 original keys and 764 observations.
The prior delivery reported 173 open keys. Its independent intake
identified 34 historical failed-attempt logs absent from that payload.
The new baseline and candidate comparisons have their own raw logs and
dispositions. The three separate ClassNP/PolyTime provider proposals
remain deferred with the rest of the inherited-read cleanup.

The first candidate replay exposed stale Closeness reader names. The
first isolated Ensemble repair needed the Mathlib inverse-pair reader.
Both attempts are preserved. The initial repaired-head equation and
kind outputs had predecessor labels. The labelled probes were rerun
on the same exact repaired object tree and both outputs are archived.

After the user merges #248, the [PKE pilot map](PKE-PILOT.md) gives the
first facade and import moves. The inherited ledger remains the input
to the final seal stage on the reorganized source.

## Evidence

The numbered archives contain the source and object receipts, exact
native censuses, whole-file probes and masks, control logs, historical
intake joins, and current read dispositions. SHA256SUMS records
the file digests. Every archive has its own file digest inventory.

**Clear to merge — the repaired head meets the approved incremental target, with witnessed inherited reads recorded for the final stage.**
