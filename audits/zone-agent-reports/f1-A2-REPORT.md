# ZF-A2 — partial delivery and shared-interface escalation

**0/2 machine rows completed. The file remains at 18/20 original targets proved. This is not a zero-sorry delivery and does not close the fill gate.** The inward row was investigated first. Both target proofs remain byte-identical admissions; no statement, existing proof, or attribution was weakened or edited.

This delivery adds the three sanctioned imports and seven proved/private staging declarations (one definition and six lemmas). It stops at the continuation brief's explicit shared-lemma escalation: the public catalog transfer contract does not cover a delimited word at displaced heads inside a larger tape. The exact requested shared contract and a kernel-checked regression are supplied below and in the accompanying Lean evidence files. This is an interface/ownership escalation, **not a counterexample to either existential zone-shift theorem**, and not a claim that the new shared lemma alone would finish a row.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Received branch: `complexity/arora-barak-ch3-4`.
- Working branch: `fill/zone-f1-A2`.
- Recorded base: `42627f368fef1fbdc5f0c8af777498d26be124bd`.
- Brief's issued base: `f171767f32e573c345f3fa9b6e9fb87e14b84ddf`.
- The received `Zone.lean` is byte-identical at these two bases. The intervening changes issue the continuation briefs and their plan/evidence records.
- No rebase, push, or PR was performed. Final commit: `18c85b42d750b433bf5b00d5408bd8414c211269` (metadata in `commits.log`).

Read: `AGENTS.md`, `policy.md`, `workflow.md`, the complete A2 and A briefs, `audits/zone-agent-reports/f1-A-REPORT.md`, all three zone statement-gate findings files, their resolutions, and the relevant §12 registry and source contracts.

## Changes and freeze

**Sanctioned imports added, explicitly flagged:**

```lean
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Catalog
```

No other import changes. There are no public docstring/sketch appendices and no optional public exports.

| New private declaration | Role |
|---|---|
| `zoneStageWord` | Encode a zone word in physical order away from home: presence/data on the right, data/presence on the left. |
| `zoneStageWord_length` | The staging word has exactly twice the virtual word's length. |
| `zoneStageWord_getElem` | Identify each staging bit by quotient/remainder of its physical offset. |
| `zoneStageSlot` | Specialize `zoneIndex_eq_iff` to an offset inside a named zone and read its virtual word. |
| `zoneStage_rightWindow` | Relate the right physical window to the staging word, including its blank suffix inside capacity. |
| `zoneStage_leftWindow` | The corresponding negative-coordinate window equation, with the correct reversed bit roles. |
| `zoneStage_window_bounds` | Both oriented windows, including adjacent delimiter cells, fit the target's allowed data interval. |

All seven are complete; no new private admission. The left-window equation is an address/readout fact, not a claimed reflected-machine simulation. An ascending physical transfer on the left would read the reversed staging word and still needs its controller proof.

`freeze.log` establishes a stronger check than signature comparison: remove exactly the three new import lines and the contiguous new private block, and the **entire file equals the recorded base byte-for-byte**. Thus all eighteen proved targets, all nine old private lemmas, both unfinished rows, every public statement, and all old documentation remain unchanged. The only changed tracked path is `TCSlib/Complexity/TuringMachine/Build/Zone.lean`.

## Why canonical transfer is insufficient

The missing premise is not solved by the newly authorized imports:

1. `transferTM_run`, `copyTM_run`, and `clearTM_run` start from `Cfg.ofWords`: heads at zero, native input position 1, and globally canonical `bufferTape` contents on every tape. The transfer/copy rows additionally assume a blank destination word.
2. `embedEmitCfg` and `embedSilentCfg` transplant an entire selected tape unchanged. Their frame clauses protect **unselected tapes**, not the outer cells of a selected tape. At two tapes, the suppressing embedding also has no third capture tape available when both source tapes are selected.
3. `seamCompTM_run_ofCfg` correctly composes arbitrary configurations, but its `h₁` and `h₂` hypotheses already require the constituent framed runs. It does not provide those runs from the canonical catalog theorem.
4. `runFrom_eq_of_agreeOn` compares transition tables on the **same initial configuration**. It supplies neither a change of tape origin nor an initial tape frame.

This is a missing public specialization, not a theorem that no generic simulation argument could ever derive. Building another private catalog trace here would violate the brief's ban on copying/re-deriving that layer. The requested shared theorem should be proved in its shared home by generalizing the existing transfer invariants, once.

The boundary conditions matter even with an enabled inward guard. `BoundaryRegression.lean` constructs a valid three-level carrier with right lengths `(0,4,1)` and a nonempty left level zero. At inward level 1:

- The donor starts at physical cell 6 and occupies eight bits.
- Physical cell 14 belongs to the next outer zone and contains `some true`; it is not a terminating blank.
- Starting bare `transferTM 2 0 1` at data head 6 and a blank scratch head 0 consumes **ten** bits, reaches `done` at time **22**, and erases cell 14.
- The required `zoneShiftIn true 1` preserves cell 14 as `some true`.
- The original data tape cannot equal any `bufferTape w`, because its cell -2 is occupied.

The regression uses exact kernel reduction, not `native_decide`, and does not claim to refute the zone row. It shows why boundary preparation and a framed run proof are necessary. The proposed route saves the boundary symbols in finite control, installs blank delimiters, calls the shared transfer, and restores the symbols. The new window lemmas establish the physical interior and allowable delimiter locations; no preparation controller is claimed complete.

## Requested shared lemmas

**Exactly one request:** add and prove `Turing.transferTM_run_ofCfg` in `Build/Catalog.lean`.

`RequestedSharedLemma.lean` contains the complete proposed type as `requested_transferTM_run_ofCfg : Prop`. It is a **typechecked specification only**, not a theorem or a proof; it contains no `sorry` and adds no axiom. The public theorem should inhabit that proposition (the proposed helper definition need not itself be exported).

Inputs and obligations:

- Distinct source/destination tapes; arbitrary native input, input position, output prefix, inactive tapes, and displaced heads.
- Initial control `some SweepPhase.sweep`.
- A source word agreeing with `bufferTape w` at the source head's relative coordinates from **-1 through `w.length`, inclusive**. Thus both boundary cells really are blank. The destination's old contents are unrestricted because the controller never tests that read component.
- At exactly `2*w.length+2`, control is `some SweepPhase.done`, both touched heads return to their initial coordinates, native position and output are unchanged, the source word interval is erased, the destination word interval is overwritten by `w`, and every cell outside those intervals is unchanged.
- No earlier visit to `done`.
- Through that time each touched head lies in its translated interval `[-1,w.length]`; every other head stays fixed.

The exact final configuration and the two trajectory clauses are included in the supplied type. The translated interval bound yields the per-tape `w.length+2` space bound by the existing interval-cardinality export. The original canonical contract is a specialization with zero heads and globally buffered words; the destination-blank restriction can be reinstated at that specialization.

Mathematical proof route for the shared owner: generalize the existing forward/rewind transfer invariants over the fixed outer frame and starting head coordinates. The forward pass copies the prefix without changing the source; the source's right delimiter turns the heads; the rewind erases only the source interior; the left delimiter supplies the final return step. There are `w.length` forward steps, one turn, `w.length` erase steps, and one entry step. These are proof obligations for the shared owner, not a claimed new Lean proof in this delivery.

## Remaining inward frontier

The requested shared lemma removes the **first staging-interface gap**. It does not supply the rest of the witness:

1. A single finite controller must preserve the unary level while constructing and using the anchored binary navigation counter, with the audited geometric carry/borrow sum. No level may be compiled into control.
2. Locate the windows, evaluate the inward guard, save/blank/restore boundary symbols, stage and rewrite the prefix/suffix, and prove the identity branch including arbitrary outer contents.
3. Compose the proved phase runs by `seamCompTM_run_ofCfg`, transport their cuts and visited sets, restore scratch to the exact unary buffer, and return both heads.
4. End with an explicitly halting phase, derive the first-halt cut, and choose one coefficient for time and scratch space.

Two source-level cautions for that continuation:

- `incrementTM_run_succ` exposes the loose `2*width+2` bound. Its docstring describes the sharper carry-sensitive cost, but the public theorem does not state it. Repeating the loose bound alone would give a width factor and does not prove the audited geometric navigation ledger. No additional shared theorem is requested in this delivery; that cost proof remains an explicit obligation.
- The continuation table's phrase “release to genuine halt” is not what `seamReleaseTM` does. It executes the original anchor action from a fresh entry state and subsequently runs the original machine. `seamReleaseTM_firstReturn` returns to a **live** anchor. A terminal halt must be supplied explicitly; the table was guidance, so no statement was altered to match it.

The outward row was not started, respecting the inward-first priority.

## Duplication ledger and citations

new copies: none

There is no local catalog controller, trace, transfer proof, embedding proof, seam proof, loop host, or primitive copy. The additions are zone-specific codec/address facts. Public declaration count remains 38; private count rises from 9 to 16. No completed machine phase is claimed to consume §12 contracts.

| Intended phase | Exact shared citations and present status |
|---|---|
| Delimited staging | `transferTM_run` / `transferTM_spaceUsedByTape`: inspected, canonical forms insufficient; first request is `transferTM_run_ofCfg`. |
| Additional copy/cleanup if selected | `copyTM_run`, `copyTM_spaceUsedByTape`, `clearTM_run`, `clearTM_spaceUsedByTape`: inspected; their framed applicability must likewise be established, not presumed. The current request does not claim to resolve all such future choices. |
| Host tape selection | `embedEmitTM_runFrom`, `embedEmitTM_frame`, `embedEmitTM_visitedByTapeHead`; returning variant `embedEmitRetTM_run` / `embedEmitRetTM_visitedByTapeHead` only for genuinely halting source phases. No spatial-frame conclusion is attributed to them. |
| General sequencing | `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamCompTM_visitedByTapeHead_ofCfg`: applicable after phase contracts exist. |
| Fresh-entry positive-return control | `seamReleaseTM_firstReturn`, `seamReleaseTM_visitedByTapeHead`: available for their actual live-return purpose, not as an implicit halting adapter. |

## Verification and archive

Verification results are finalized in `verification-summary.txt`. All Lean checks use the unmodified `scripts/lean_check_tree.sh`; no `lake build` was run. `lake exe cache get` succeeded with the manifest-pinned dependencies. A fresh, dependency-ordered sweep covers the standard order list and the five prescribed Build modules; additional actual import prerequisites are included rather than assumed present.

The twenty target axiom prints are in `axioms.log`. The eighteen integrated targets remain within `[propext, Classical.choice, Quot.sound]`; the two unfilled rows deliberately still carry `sorryAx`. All seven new staging declarations and all five boundary regression facts are checked separately and use only the standard triple. No proof of the requested shared specification is included or claimed.

Style: `style_lint: 0 FAIL, 4 WARN over 11 files`. The `Zone.lean` size warning (now 1,191 lines) is covered by the plan decision-log entry “A-S2 fill epoch: ZF-A and ZF-C partials INTEGRATED; ZF-B received and HELD”: this single owned audited surface remains together until the 12.2c split window. The other three size warnings are received files.

The archive contains the full `Zone.lean`, report, patch series against the recorded base, incremental git bundle, final sweep and axiom logs, freeze and integration evidence, the two Lean escalation evidence files, and `SHA256SUMS`. Only `Zone.lean` is changed by the patch; evidence files are not repository contributions. No compatibility shim, toolchain executable, dependency cache, or build output is delivered.

Notation: `w` is the proposed transfer's finite Boolean word; `d` its arbitrary starting configuration; `p` a relative integer cell offset; `T = 2*w.length+2` its proposed exact phase time. Other names are existing source identifiers or listed private additions.
