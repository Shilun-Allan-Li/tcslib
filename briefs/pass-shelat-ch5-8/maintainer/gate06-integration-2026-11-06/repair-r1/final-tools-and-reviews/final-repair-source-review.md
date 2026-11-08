# Final repair source review

**Static verdict: 0 blockers / 0 majors / 0 minors in the reviewed repair delta.**
No Lean/cache/native check was run by this reviewer. This is not a Gate06 closure verdict.

## Snapshot

Compared only new repair code against `e9d64158461bfe24ddc88ab885bc4017899b4c16`; the original statement-prong
comparison is outside this review. The stable capture at `2026-11-07T12:19:37.813631+00:00` has
HEAD `d370905303223ba2b31d26bc218d90ae2ee8a6ac` and 33 changed modules. It includes the Garbling
`values_eq` owner/consumer repair and the GI attemptAt patch, already applied as data in the
snapshot. The latter's six owner readers are in the correct global Encoding/GraphIsomorphism
homes, separate from GI.Proofs' shadow namespace.

Root later added only `all_goals rfl` after the existing reader simp in Simulator's `hπ`
subproof. That exact overlay is recorded at source SHA
`0ad712e26071f91a0bcce913d287e9c3c26b66bf8be7650a15b22d63813d5ed4`; every other captured source matches the stable
snapshot. Its conditional reflexivity closes residual goals without adding a hypothesis,
changing a function or bypassing an obligation. Root reported ordinary r3 passing; R4 was
still running when this review was prepared. No native result is independently certified here.

The reconciled **1,108-file** list includes the root `TCSlib.lean` facade (unchanged from base):
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/final-repair-source-review.current.sha256`.
SHA-256: `4210415be64f6d1723ff3e04e00d1ed6225d0faa8229bcf940518a5ab3640cf8`.
Root should reconcile this list with the final frozen source; later advances are not covered.

## Statement and data preservation

The existing-public-header comparison identifies exactly the five approved equivalences:
`runAt_hsGen`, `runAt_hsSign`, `runAt_padEnc`, `yaoHybrid_callA`, `yaoHybrid_callB`.
These reparameterize full Fin/coin domains through public equalities/equivalences, preserve
`List.ofFn` words/index values, and retain all inputs including parameter0. Their callers
were checked in the earlier transport review and remain updated. Every other existing
public statement matches the base in this review's comparison; no security premise or game
was weakened. There is no new RSA/Rabin/PKE implication or security-notion bridge.

The six changed structure-valued definitions (`hashAndSign`, `prfMAC`, `ccaScheme`,
`prfFixedScheme`, `ofPadded`, `specialScheme`) retain byte-identical headers and data/uniformity
prefixes; their changes are correctness/length proof fields. All raw string functions,
samplers, graph-decoder data, protocol moves and bounds remain unchanged.

The sole ordinary algorithm-body replacement is the approved `decodeMsgs` delegation to
`BinArith.decWords`. The base already proves equality for arbitrary words using fuel
sufficiency and strict second-projection length, so malformed/default and empty-word
semantics are preserved. Public decoder interfaces stay the same. Exactly the private fuel
definition and its two private helper theorems are retired, with no remaining Yao references.
All 33 changed modules retain their code-level `sorry`/`admit` counts; no substantive security
admission or axiom has been added, removed or filled by the repairs.

Twenty-two new public declarations are owner-local reading equations/bridge readers. They
add no helper definition, host, algorithm or global simp attribute. Typed OT and dependent
graph-index readers state the existing total behavior rather than requiring valid encodings
or positive lengths. The Compose, HBC and GI term chains use the correct equality/iff
directions and keep the original round, efficiency and simulator clauses. The known Garbling
foreign-values gap is explicitly opened through the new public `DAGCircuit.values_eq`.

## Policy and prose

Added explicit `simp`/`rw` entries were inspected as definitions/lemmas, not accepted by name
prefix. Imported entries are published theorem equations; remaining definition entries are
homed in the consuming file, such as Lamport's `lamportGen` and OT's protocol/strategies.
Core/Mathlib entries including `Function.comp_apply`, `Nat.min_self`, `List.length_zipWith`
and `eq_self_iff_true` are actual lemmas. No new foreign ordinary definition is named in an
explicit unfold/rewrite list. Core Fin/constructor reductions in `rfl` remain permitted by
policy; source inspection alone is not an implicit-read certificate.

The GI attemptAt proof now reads the exact total graph decoder, sampler/identity fallback,
efficiency/uniform-advice clauses and view/history encodings through public equations.
Its success condition, guessed bit/graph, coin-block cuts, view contents and runtime functions
are unchanged. Its expanded sketch describes these routes. The new readers have adjacent
formula docstrings; nontrivial term replacements retain or add human-readable sketches.
The NonMalleable/SequentialZK prose corrections distinguish their actual formal conventions
without changing a formal statement. Global GraphIsomorphism remains at 999 physical lines,
1000 under the style counter's final-empty-line convention, within its existing cap.

Final dynamic scope is **54**, including all three repair owners beyond the initial51:
`Complexity/Randomized/PolyTimeModel.lean`, `Cryptography/Asymptotic/MultiMessage.lean`, and
`Cryptography/ZeroKnowledge/Encoding.lean`. Root acknowledged that complete scope. Fresh final
collection/sealing and source/HEAD reconciliation remain necessary; old diagnostic rows are
not final coverage.

## Recorded review inputs

* GI attemptAt proposal SHA-256: `4bbb6c2c335ab64d700fb121b740b946703cbd879e9c1833ced18c8aea74328e`.
* Snapshot with exact per-file diffs/SHA: `final-repair-source-review.snapshot.json` — `a0d74444adc41c60137458abae7dcae6a5a7bdfa3d9114abf0d79353f964557a`.
* Header/admission/data checks and one-line overlay: `final-repair-source-review.validation.json` — `3b86c48037204f3024a34cbedf69780477e0c6a04a8df63fec9a6703e763f068`.
* Reconciled current SHA list: `final-repair-source-review.current.sha256` — `4210415be64f6d1723ff3e04e00d1ed6225d0faa8229bcf940518a5ab3640cf8`.

Only ignored review artifacts were written. No library, Git or campaign-evidence mutation,
runner execution, received-program execution, computer app or build/check command occurred.
