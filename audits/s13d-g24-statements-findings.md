# External audit findings — §13d G2–G4 statement gate

**Verdict: PASS.** Zero blockers, zero majors, five minors. The scoped statements are credible, nonvacuous specifications at the required geometric cost; the G4 contracts supply the information needed by G5. The requested table and contract-constructor restructures are present, without a public-statement or admitted-axiom regression in the existing Catalog surface. This is a statement-gate verdict, not certification that the five remaining landed admissions have been filled or that the final Hennie–Stearns simulator has been proved.

## Scope and evidence

Audited the first pack, the standards, the G24 unit and design note, all seven parts, the six landed forms, the sanity and fit probes, the scripts and logs, the cited library sources, and the relevant earlier gate and MIG-1 records. `Build/…` below abbreviates `TCSlib/Complexity/TuringMachine/Build/…`; declaration locations refer to the supplied proposed landing unless explicitly marked “unit” or “probe.”

The attachment has exactly 106 section headers and SHA-256 `3154dc39b1c5493e9c0b4d97ba272d5bbdc1d4375afaa71e4343276a0e2dca1f`, matching the request. Removing bundle wrappers and terminal separator padding reproduces the unit hash printed in the elaboration log: `f7cc421e534d2b9ca13946b1f93c89e89b5185e25893fb07b6b41e751774ac25`. The request identifies campaign commit `fd63239a`; the embedded build records identify `f2d48ad5`, with Lean content `1b6b972c`. I audited the attached texts; I did not independently verify those Git identities against a remote repository.

For code-first readings, I removed comments and recorded the new definitions' meanings before consulting their declaration docstrings. I independently reran source comparisons, landing generation, the axiom-log comparison and its public-name inventory, and the copy-text screens. I also executed a separate transcription of the pure operations, carrier and sweep tables. These checks support the analysis below; neither a Python transcription nor an elaboration log is a Lean proof. The bundle does not include a complete matching dependency/olean snapshot, and I did not perform a fresh Lean elaboration or the whole downstream replay.

For the source comparison I consulted the indexed text of the published [Arora–Barak (2009), §1.7](https://kubokovac.eu/zlozitost/arora.pdf); direct PDF retrieval was unavailable. It specifies capacity `2 · 2^i`, half occupancy `2^i`, paired occupancies summing to capacity, a least nonempty feeding zone, and initialization of newly encountered zones with stored blanks. The code preserves those quantities and the represented tape. Separators and inner packing change physical locations, not the virtual order; the additional distance through level `i` is linear in `i`, absorbed by `O(2^i)`. The explicit short/extend interface implements the finite-layout boundary. No fidelity defect was found in these declared deviations.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `audits/evidence/s13d/g24/G24-design.md` §5(e); fit probe · `run_cost_le` | The displayed rebalance budget cannot absorb the controller's fixed per-step cost uniformly at `k = 0`. | The lemma is true as a conditional statement about rebalance cost. But at `k = 0`, `T = 1`, and `cost 0 = 1`, its proposed `hstep` becomes `1 ≤ 0`. Thus it cannot also account for a nonzero transition/input/output cost in that case. | State that this lemma covers the rebalance phase only. In G5, either handle/pad zero-work-tape machines separately, or carry a fixed overhead: replace the step bound by `B + A * Σ_t (2^idx + 1) + k`, and add `B*T` to the conclusion. Do not absorb that term into a factor of `k` without `0 < k`. |
| 2 | minor | `audits/evidence/s13d/g24/probes/G24FitProbe.lean.txt` · `trackStep_fit` | The fit theorem's exported conclusion hides facts required to reuse it directly as a finite simulator component. | It quantifies over `S : Type` with `DecidableEq S`, but not `Fintype S`. Its final `zoneRowPre` clause also omits preservation of `inputPos`, `output`, and the original scratch-head position. The sum-state construction and the G4 endpoint equalities retain these facts, so this is a probe-interface weakness, not a missing G4 hypothesis. | Add `Fintype S` to the existential conclusion and endpoint equalities for those fields under the stated precondition. Alternatively, explicitly restrict the probe's advertised role to chaining the zoned representation and bounding its time; G5 must then construct and expose the stronger interface from G4. |
| 3 | minor | `Build/Catalog.lean` · `copyMapTM`, `transferMapTM`; `Build/Contract/Catalog.lean` · `sweepPost` docstrings | Some prose describes distinct-tape behavior without its side condition, and one generic contract description says “both heads.” | The definitions permit `src = dst`. With `k = 1`, Boolean symbols, both indices `0`, identity extraction, and merge that negates the extracted bit, mapped copy writes the source cell immediately. Thus “the source is never written” is false for the definition's whole domain. The framed theorems and contracts correctly require `src ≠ dst`. `sweepPost` preserves all `k` work heads. | Qualify the copy/transfer behavioral descriptions by `src ≠ dst`; make clear that their advertised cross-tape guarantees use that hypothesis. Change “both heads” to “all work heads” in `sweepPost`. No theorem or table change is needed. |
| 4 | minor | `Build/ZoneRebalance.lean` · `exists_zoneRebalanceTM`, `exists_zoneExtendTM` docstrings | The two proof-sketch labels do not use the literal required form. | Both have `**Proof sketch** (fill plan…)`, whereas the pack explicitly requires `**Proof sketch.**`, consistent with `policy.md` §3. Substantial sketches are present; they are not missing. | Change both labels to `**Proof sketch.**` and retain the fill-plan text after the label. |
| 5 | minor | `audits/s13d-g24-statements-pack.md` · duplication accounting | Two quantitative descriptions are inaccurate, although the totals and the removal of the chosen families are correct. | The screen-extracted body of `zonedTape_left_word` has 724 whitespace-free characters, not fewer than 530; its overlap with the 522-character right-word body is 285. The old table overlaps are 369/369/475 characters by unordered pair; the new overlaps are 369/344/478, not literally unchanged amounts. | Correct the size claim to distinguish body size from reproduced text, and describe the table pairs as the same sibling family with slightly changed counts. Retain the exact totals and dispositions below. This does not introduce another debt family or require reversing the user's decision. |

The minors should be repaired or explicitly waived with reasons in the findings disposition, as the template requires. They do not change the G2–G4 statement-gate verdict.

## Definition restatements and comparison

These are the code-first readings of all 34 definitions/abbreviations in the unit. Comparison with the docstrings and intended source role found no semantic discrepancy except finding 3. The classical empty/half/full condition is deliberately absent from the carrier type; it belongs to the G5 simulation invariant.

| Definition | Mathematical meaning read from the body |
|---|---|
| `ZoneContents.words` | Select the right list family for `true`, the left family for `false`. |
| `ZoneContents.swap` | Exchange the two list families and their capacity proofs, retaining home. |
| `zoneCascadeLeft` | Mirror the contents, run the existing right cascade at the chosen level, then mirror back. |
| `zoneCascade` | Choose the right or left cascade from the direction Boolean. |
| `zoneShiftIndex` | Find the first nonempty list on the feeding side, in increasing level order; return `ℓ` if there is none. |
| `zoneRebalance` | Run the chosen cascade at that index when it is less than `ℓ`; otherwise return the original contents. |
| `ZoneContents.extend` | Preserve home and all existing levels; append a level with `2^ℓ` stored virtual blanks on each side. |
| `zoneTrackTape` | Read home at zero, the concatenated right lists at positive positions, and the concatenated left lists at negative positions in outward order. Stored blanks and positions beyond either finite word both decode as virtual blank. |
| `copyMapTM` | Scan the source rightwards. At each present source symbol, extract a value and merge it into the current destination cell. On the right delimiter turn left; on the left delimiter step right into `done`. The source is intact when the indices are distinct. |
| `transferMapTM` | Use that forward pass, then replace each source symbol by its residue while returning left. With distinct indices, each residue is computed from the original source symbol. |
| `sweepPost` | Change state to `done` and overwrite one tape's half-open word interval, starting at its original head, using the supplied replacement function on the original configuration. Preserve everything else. |
| `sweepContract` | Turn a supplied first-exit run theorem into a contract: delimited-source precondition, exact time `2*length+2`, supplied endpoint, bounded touched heads, and fixed untouched heads. |
| `sweepMapWrite` | At a displacement inside the source word, extract that source symbol and merge it with the destination's original cell; return blank outside the word. |
| `copyMapTM_contract` | Apply the shared constructor to mapped copy, touching the source and destination heads and overwriting the destination interval. |
| `transferMapTM_contract` | Apply it to mapped transfer, with a destination overwrite followed by a source-residue overwrite. |
| `ZoneCell` | A function assigning each track an optional occupied slot; an occupied slot contains an optional Boolean virtual symbol. |
| `ZoneSym` | The disjoint union of Boolean scratch symbols and multi-track cells. |
| `zoneSlotOf` | Read a track's slot from a cell symbol; report unused on a Boolean scratch symbol. |
| `zoneCellOfCell` | Extract a present multi-track cell; otherwise return the cell with every slot unused. |
| `zoneSlotSet` | Produce a cell symbol with one slot replaced. Preserve all other slots if the input was already a cell symbol; otherwise start them unused. |
| `zoneStart` | Place level `i` at `zoneBase i + i + 2 = 2^(i+1)+i`, accounting for separators. |
| `zoneOwner` | Return the level whose half-open capacity interval contains a nonnegative coordinate, or none in a gap or beyond the layout. |
| `zoneCells` | Encode a whole capacity-length zone word. For each track, list entries occupy its inner prefix and the remaining slots are unused. |
| `zoneCellAt` | Encode the owning side/level cell at a coordinate; give physical blank if no zone owns it. |
| `zonedTape` | Encode the home tuple at zero and the two sides at opposite coordinates. Every laid-out zone cell is physically present, even when every slot is unused. |
| `ZoneData` | A level count together with one bounded `ZoneContents` value per track over that count. |
| `zoneRowPre` | Tape 0 is exactly the indexed zoned encoding with head zero; tape 1 is blank everywhere. The scratch head, input position, and output are unrestricted. |
| `zoneRebalanceIndex` | Compute the selected track's feeding index. |
| `zoneRebalanceData` | Rebalance that track, preserving all other tracks and the level count. |
| `zoneExtendData` | Increase the shared level count and extend every track. |
| `zoneRebalancePost` | Replace tape 0 by the rebalanced encoding; select `done` iff a feeding level existed, otherwise `short`; retain all other configuration fields. |
| `zoneExtendPost` | Replace tape 0 by the extended encoding and enter `done`; retain all other configuration fields. |
| `zoneRowLo` | Bound the zoned head below by `-zoneStart(r+1)` and the scratch head below by its original position minus `C*(2^r+1)`. |
| `zoneRowHi` | Give the corresponding upper bounds. |

The three restructured existing definitions have these meanings: `copyTM` is mapped copy with identity extraction and destination replacement; `transferTM` is its transfer analogue with blank residue; `clearTM_contract` applies the shared constructor to the existing clear run theorem and a blank overwrite. These are definitional restatements, not replacement specifications.

For the fit probe, `stopContract` has precondition `True`, time zero, identity endpoint, and singleton head intervals at an already-exiting state. `zoneTrackStepData` rebalances directly when the index is in range, otherwise extends and then rebalances. The sanity fixtures are concrete bounded contents: `zA` has one occupied cell on each side; `D0` has no levels and blank home; `zB` has an empty lower right zone and a full lower left zone with a level-1 donor; `zC` has full `L₀` and nonempty `R₀`. Their roles agree with their comments.

The retained pure layer supplies capacities and capacity bounds only. Inward transfer takes a prefix of size `2^(i-1)` from the upper list when the lower list is empty; outward transfer retains the lower first half and prepends its second half to the upper list when the guard permits. This explains why non-classical inputs, including short donors and blocked receivers, are meaningful inputs rather than ill-typed objects.

## The six sorried statements

### 1. `zoneCascadeRight_frame` — true; already proved at landing

The central move touches level zero, and the pair at level `i` touches only `i-1` and `i`; induction on the cascade therefore leaves every level above its index unchanged. This is nonvacuous whenever such a higher level exists, with arbitrary contents there. The landed declaration is the existing private theorem promoted with the same proof, rather than a new admission. It supplies exactly the higher-level frame subsequently used for rebalance footprints.

### 2. `zoneCascadeRight_home` — true under the stated hypotheses

The descending pass preserves the concatenated right word and brings a nonempty prefix down to level zero, even if the initial donor is shorter than the requested half. The left-side fullness and top-room assumptions make room for the central move, which takes the first symbol of that right word as the new home; the ascending pairs preserve home. At `j = 0`, natural subtraction gives `2^(j-1)=1`, so the room condition is exactly sufficient for the one-cell push. The hypotheses have concrete instances, and this is the missing home equality needed with the existing side-word theorem to obtain the virtual shift at every integer position.

### 3. `copyMapTM_run_ofCfg` — true

For a word of length `n`, there are `n` forward writes, one turn step, `n` return steps, and one final step, giving exactly `2n+2`. Each destination cell is read once before its write, while the distinct source tape remains unchanged, so the merge uses precisely the original destination cell asserted in the endpoint. The two delimiters determine the first `done` time and the interval `[start-1,start+n]`; all other heads and all fields omitted by the endpoint update are preserved. The assumptions are realizable for every source word on two distinct tapes with arbitrary destination data, and the result contains the run, cut, and envelope clauses needed by the shared constructor.

### 4. `transferMapTM_run_ofCfg` — true

Its forward pass is the same copy pass, and the return pass reads each original source symbol before replacing that cell by its residue. A blank residue cannot terminate the rewind early: the machine leaves the rewritten cell and next reads the still-unmodified cell to its left, eventually reaching the unchanged left delimiter. Thus the same exact time, first-exit cut, head bounds and destination merge apply, with the additional source overwrite. This includes arbitrary blanking residues and the empty word, and supplies the transfer contract without assuming an injective map or a finite intermediate type `Δ`.

### 5. `exists_zoneRebalanceTM` — true as an existence specification

For fixed `k`, direction and track, a finite controller can find the first occupied feeding slot by scanning the full nonblank physical zone words and their separators, detecting exhaustion at two consecutive physical blanks in `O(2^i+1)` time. It can implement each guarded pair by a bounded number of linear passes over its two zones, using the second tape for copied slots, repacking and unary rulers; summing the descending and ascending costs gives a geometric bound, not an additional logarithmic factor. Temporary markers can remember the initially arbitrary scratch-head origin, and the construction can erase scratch, restore both heads, ignore input/output, and stay within the stated zoned envelope; taking the maximum over the finitely many track/direction choices gives the uniform constant. The pinned pre/post fields require real behavior on every bounded contents, including the short identity branch, so the contract cannot be discharged by an empty precondition or an arbitrary endpoint. This is enough for the G5 branch/extend/retry composition, subject to G5's separate classical invariant for semantic head motion.

### 6. `exists_zoneExtendTM` — true as an existence specification

The physical layout is observable independently of track occupancy, so a finite controller can locate its end and construct the next zones using a doubled unary ruler in `O(2^ℓ+1)` time. At `ℓ = 0` it writes cells `±2` and `±3`; in general it writes the new full-capacity physical zones with inner halves occupied by stored virtual blanks and outer halves unused. It can preserve all old cells, restore its heads and clear scratch within the stated envelopes, including when `k = 0`, where the layout still changes. The exact endpoint and universal precondition make this nontrivial, and the extension/index lemmas ensure that the subsequent retry has an in-range feeding level while preserving every represented virtual tape.

These are mathematical plausibility arguments for a statement gate. In particular, the last two are not claims that their executable witnesses have already been constructed.

## Contract adequacy and nonvacuity

The common constructor asks for an actual run theorem with the claimed endpoint, first-exit cut and head bounds; it does not manufacture those facts. An arbitrary `touched` predicate or endpoint is harmless because the same choices appear in the supplied premises. It also does not claim a frame for an arbitrary endpoint: the instance frames follow from `sweepPost` and `sweep_ite_keep`.

The transfer endpoint is the source overwrite around the destination overwrite. Because the indices are distinct and head positions do not change, the outer source write cannot alter the destination interval, and its residue expression does not depend on the already-updated destination. The inner destination write uses the original configuration. Clear is the same endpoint shape with an everywhere-blank replacement.

For the G4 rows, fix any `D` and construct an entry configuration with its exact zoned tape, zero zoned head, blank scratch, and any allowed scratch head/input position/output. It satisfies the prescribed precondition. The machine and its finite state type are chosen before the input word and data, and the constant is chosen before the unbounded level count; neither a data-dependent oracle machine nor a data-dependent overhead constant is permitted.

The absence of an explicit `entry ∉ exits` premise is benign. The contract cut includes time zero: an entry that is already an exit would force a zero-time run. For a genuine track, `entry = done` contradicts the short output on empty feeding contents, while `entry = short` contradicts the done output on a nonempty feeding instance. For extension, its changed layout rules out a zero-time endpoint even at `k = 0`. At `k = 0` the rebalance family has no track to select, so that part is intentionally vacuous; the carrier and extension theorem are not.

The G4 equalities preserve the input position, output, scratch contents and scratch-head position at the endpoint. They do not assert that every such field is unchanged throughout the interior run; the supplied frames are endpoint frames, and the envelopes concern head positions throughout the run. That is sufficient for the intended sequential consumer. Finding 2 concerns how much of this information the fit theorem re-exports.

## Adversarial instances

| Instance | Result and implication |
|---|---|
| `k = 0` | `ZoneCell 0` has one value and `ZoneSym 0` has three. The physical home/zones remain present, so different level counts remain distinguishable and extension still has work to do. No rebalance track exists. The separate controller-cost issue is finding 1. |
| `k = 1` | Six symbols, with physical blank outside that alphabet. The `zA` encoding has home at zero, separators at `±1`, occupied slots at `±2`, and unused but physically present cells at `±3`. |
| `ℓ = 0` | Only home is present. Every feeding index is zero and is short; extension writes `±2, ±3`, leaving separators `±1, ±4` blank. The retry index is zero below the new level count one. |
| All lists empty | The index is `ℓ`; rebalance is identity. With blank home, the represented tape is everywhere blank even though a positive-level physical layout is present. |
| `L₀` full, `R₀` nonempty (`zC`) | The scanned index is zero and the exit is `done`, but the central move is blocked and contents are unchanged. This refutes an unconditional “done means a virtual move” interpretation, which the actual represented-tape theorems correctly avoid. |
| Donor shorter than half | Take `j = 2`, `ℓ = 3`, lower right lists empty, lower left lists full, `R₂ = [some true]`, `L₂ = []`. The donor length one is below `2^(2-1)=2`, but the descending prefixes remain nonempty and the new home is `some true`; no stronger donor hypothesis is needed. |
| One side full, the other empty | The cascade length laws give the intended redistribution on a classical instance, including the `zB` index-one case. Extending an exhausted classical side supplies a half-full donor and leaves lower pair sums intact. |
| Full top receiver | An outward guard may fail on non-classical data; the total row is required to realize that guarded result, not an unguarded book shift. The home/represented-move theorems exclude the obstructed case by their room hypotheses. |
| Stored virtual blank versus unused slot | An occupied blank is `some none` in a track slot; an unused slot is `none`. Both lie inside a physically present `.inr` cell. The former counts toward the donor's list length, so a zone full of stored blanks is full and not a separator. |
| Leftward move | Swapping `zB`, applying the left rebalance, and swapping back gives the right result. The represented coordinate shift is `p-1`, rather than `p+1`. |
| Empty sweep word | Both mapped machines take two steps, move left and then right, write nothing, and reach `done` for the first time at the advertised time. |
| Blanking transfer residue | Even an all-blank residue preserves the rewind schedule, because erasure occurs only as a cell is left. Mixed blank/nonblank residues behave the same way. |
| Arbitrary heads and exterior data | Sweep tests used source/destination origins `-7` and `19`, an untouched third head at `101`, and nonblank exterior cells. The asserted endpoint, exact time, envelopes, and exterior frame held. For G4, a scratch origin can likewise be marked temporarily and restored; no precondition fixes it to zero. |
| Two tracks | Updating slot 1 in a cell retains slot 0. A copy to blank scratch yields a present cell containing the selected slot and unused other slots; writing back by `zoneSlotSet` preserves the other track. |
| Identity specializations and clear constructor | The old and proposed plain-table bodies reduce to the mapped identity instances. The clear constructor's data fields reduce to the old ones, and proof irrelevance accounts for its proof fields. |
| Aliased sweep indices | The negating-copy example in finding 3 changes the source. This is outside the framed theorem's `src ≠ dst` hypothesis and exposes only the unqualified definition prose. |

The independent executable transcription passed 1,014 one-level rebalance cases; 12,660 instances of the cascade-home hypotheses over indices 0–5; 36,450 three-level occupancy/mirror cases; 879 carrier/extension cell checks; all 4,096 left/right histories of length 12 from empty initialization; and 49,536 mapped-sweep runs over words of length 0–2, all Boolean merge tables, and all Boolean-to-optional-Boolean residue maps. These bounded checks supplement, rather than replace, the arguments above. No executable G4 witness was available to test.

The carrier boundary is tight: for `ℓ > 0`, coordinate `zoneStart ℓ - 2` is still a present cell; the outer separator at `zoneStart ℓ - 1` is blank. For `ℓ = 0`, home zero is present and all coordinates of absolute value at least one are blank. The left-word lemma correctly reverses the encoded zone when a sweep travels from the outer negative coordinate toward home.

Useful additional sanity statements are: equality of physical encodings implies equality of level counts, including at `k = 0`; combining that fact with `zonedTape_injective` gives injectivity for `ZoneData`. Also useful are explicit entry/exit-distinctness consequences of the G4 contracts and a small `j = 2` short-donor example. These would expose properties already supported by the current definitions, not repair missing hypotheses. The proposed fit strengthening is the substantive interface improvement among these checks.

## Restructure, freeze and admitted dependencies

The source comparison reproduces the freeze:

| File | Old declarations | Identical | Signature changes | Body-only changes | Removed | Added |
|---|---:|---:|---:|---:|---:|---:|
| `Build/Catalog.lean` | 480 | 475 | 0 | 5 | 0 | 6 |
| `Build/Contract/Catalog.lean` | 3 | 0 | 0 | 3 | 0 | 10 |
| `Build/Zone.lean` | 53 | 36 | 1 intentional private-to-public promotion | 0 | 16 | 36 |

Catalog's five changed bodies are exactly `copyTM`, `transferTM`, `catalog_copy_forward`, `catalog_copy_trace`, and `catalog_transfer_trace`. The proof repairs add the mapped definition to existing simplifier sets at nine sites: one in the copy-forward proof, four in the copy trace, and four in the transfer trace. They do not replace a proved trace with a call to either admitted mapped run theorem.

Contract/Catalog's three old bodies are exactly the clear contract and its frame/trajectory proofs. The shared constructor contains no new admission and receives the existing proved `clearTM_run_ofCfg`. Its data fields agree definitionally with the old clear contract; the proof fields agree by proof irrelevance. Plain copy/transfer are definitionally the mapped identity instances against both the old tables and the proposed restatements, as the `rfl` probes assert.

I independently enumerated the 92 public declarations in the two base Catalog sources and matched them against the before/after axiom-print entries: none missing or unexpected, 92 unchanged axiom sets, zero gained `sorryAx`. This tests completeness of the supplied comparison rather than merely accepting its summary. Source dependency inspection corroborates the result: the old proved rows retain their old proved traces, and the changed definitions/constructor introduce no admitted premise. The new mapped contracts correctly inherit the admitted mapped run theorems; the unit's frame admission disappears in the actual promoted landing.

Regenerating Catalog, Contract/Catalog, Zone and the facade with the supplied writers reproduced the corresponding attached landed texts after removing bundle terminal padding. The standalone/chain-check scripts assemble the new bodies without silently importing the old versions of those same home modules. Their recorded elaboration results remain supplied evidence, not an independently repeated kernel check.

The downstream name search is a useful heuristic, not a proof that no syntax-sensitive consumer exists: a line-based keyword check can miss multiline simplifier lists or differently named equation lemmas. Definitional equality preserves typing and `change`, but it need not preserve every unfolding tactic's behavior. The already-required downstream replay must therefore remain a landing obligation. No public-statement or admitted-axiom regression was found in the supplied sources.

## Duplication: the chosen families are removed

I reran the two screens sequentially under `nice -n 10`. Every reported pair line matches the corresponding supplied log, not just its headline count.

| Measurement | Before | After |
|---|---:|---:|
| Screened declarations | 455 | 506 |
| Directed pairs | 302 | 319 |
| Reproduced characters | 106,512 | 108,813 |

There are 24 new directed pairs and 7 removed pairs. New pairs contribute 4,968 characters, removed pairs 2,692; retained pairs change by a net 25 characters from the minimal proof repairs. Thus `4,968 - 2,692 + 25 = 2,301`, exactly the total increase. These are the screen's overlap counts, which double-count bidirectional/overlapping material; they are not unique copied-source totals.

The new counts split as follows: mapped table siblings 2,382 characters; the two constructor applications 240; Zone's five directed pairs 906; ZoneTape's eleven 1,440; ZoneRebalance zero. No new pair crosses a source-file boundary. The screen's basename labels conflate the two Catalog filenames, so I checked the actual homes of their declarations.

No pair now involves `copyTM` or `transferTM`: their table bodies are gone and each is one specialization. No pair involves `clearTM_contract` or its frame/trajectory proofs, and the new contract instances contain constructor applications rather than replicated contract-field proofs. The seventh removed pair is the retired staging-window sibling. This implements question 10's decision; it is not a request to acknowledge the rejected debt.

All 24 new directed pairs are listed below, grouping reverse directions where both were reported. An arrow means “the left declaration reproduces the right declaration” in the screen's terminology. Fractions use the right declaration's extracted body size.

| Pair or grouped pair | Reported overlap | Disposition |
|---|---|---|
| `clearTM` → `copyMapTM`; reverse | 369/498; 369/409 | Accept the pre-existing clear/copy sibling shape, now represented only by the generic copy table. |
| `clearTM` → `transferMapTM`; reverse | 344/533; 344/409 | Accept the pre-existing clear/transfer sibling shape. |
| `copyMapTM` → `transferMapTM`; reverse | 478/533; 478/498 | Accept the two operation tables; consolidate their trace family at G2 fill, as Q7 requires. |
| `copyMapTM_contract` → `transferMapTM_contract`; reverse | 120/233; 120/139 | Accept two short applications of the shared constructor with related endpoints; no copied field proofs remain. |
| `zoneShiftIndex_extend` → `zoneShiftIndex_extend_of_lt` | 179/334 | Accept short sibling index arguments. |
| `zoneShiftIndex_nonempty` → `zoneShiftIndex_empty` | 115/185 | Accept short complementary index arguments. |
| `zoneShiftIndex_nonempty` → `zoneShiftIndex_le` | 80/111 | Accept the shared list-index reduction. |
| `zoneSide_rebalance_right` → `zoneTrackTape_rebalance_right`; reverse | 266/275; 266/269 | Accept small bridges supplying the same scan hypotheses to different established conclusions. An optional helper is reasonable during fill. |
| `zoneOwner_beyond` → `zoneOwner_sep`; reverse | 105/199; 105/111 | Accept short owner-exclusion arguments. |
| `zonedTape_left` → `zonedTape_left_sep` | 92/162 | Accept coordinate-case overlap. |
| `zonedTape_left` → `zonedTape_right`; reverse | 171/183; 171/191 | Accept short mirror cell calculations. |
| `zonedTape_left` → `zonedTape_right_sep` | 79/158 | Accept coordinate-case overlap. |
| `zonedTape_left_sep` → `zonedTape_right_sep`; reverse | 124/158; 124/162 | Accept short mirror separator calculations. |
| `zonedTape_left_word` → `zonedTape_right_word` | 285/522 | Accept the common buffer-word calculation; the left version additionally handles reversal. Correct the body-size accounting in finding 5. |
| `zonedTape_right` → `zonedTape_right_sep`; reverse | 92/158; 92/183 | Accept coordinate-case overlap. |

These small local sibling arguments are not a new wholesale copied implementation or a second private machinery family. I do not require a debt acknowledgment for them. The existing Catalog trace/host debt remains governed by its existing records and planned resolutions; the nine unfolding repairs do not create another such family. In particular, approval here does not authorize retaining two trace families after the G2 fill.

## Fit with G5 and the book-strength bound

The G4 rows provide a finite alphabet and finite state witnesses before data/input are chosen. The fit builds a sum-state branch: rebalance; stop on `done`; otherwise extend and rebalance again, using the landed `Contract.branch` and `Contract.seq`. The short branch preserves the data before extension, extension preserves represented tapes, and `zoneRebalanceIndex_extend_of_short` makes the retry index the old `ℓ`, now below the new count. The cost is bounded by `(2*C + C' + 2)*(2^i+1)`, including the seams. Thus the rows are adequate; finding 2 identifies information the probe's conclusion should retain if G5 will consume that theorem opaquely.

The G5-internal obligations listed in design §5 are correctly separated from G4's total row contracts:

1. **Classical invariant.** With zero levels it is vacuous. Extension adds half/half pairs. Under a classical pre-state, the cascade length laws reset lower pairs to half/half and transfer `2^j` at the top, preserving the allowed occupancies and pair sums.
2. **Virtual motion.** Minimality gives empty lower feeding zones. The paired invariant makes their opposite zones full and gives room at the donor's opposite zone; the represented-tape theorem therefore applies. A stay step only updates home. The `zC` counterexample shows why this invariant cannot be replaced by the exit tag.
3. **Count bound.** After a shift with index greater than `i`, levels zero through `i` are half full on both sides. Their total occupied length on either side is `2^(i+1)-1`. Until the next such shift, a move changes this side total by only one; reaching an empty feeding side therefore requires at least that many intervening moves. This implies the weaker stated bound `#{s < T : idx s > i} ≤ T / 2^i + 1`, allowing a first event before any reset. Extending for another track does not disturb existing lower levels.
4. **Level bound.** At level count `ℓ`, each side's total stored length for a track is `2^ℓ-1` plus or minus its net displacement from the initialized head. A short event requires a side to be empty, hence displacement magnitude `2^ℓ-1`; after at most `T` simulated steps this gives the advertised logarithmic level bound, with the stated additive slack. Treat initialization and `T = 0` separately when expressing the final total-time estimate.
5. **Controller cost.** Sequential row costs, seam dispatches and constant transition/home work have the intended bound for a fixed positive track count. For all natural `k`, account for the fixed term as in finding 1.

The amortization is the correct geometric calculation. For every natural `j`,

`2^j = 1 + Σ_{i<j} 2^i`.

Summing over the `T` indices and using the count hypothesis gives

`Σ_{s<T} 2^(idx s) ≤ T + Σ_{i<L} (T + 2^i) ≤ (L+1)*T + 2^L`.

With `L ≤ log₂ T + 2`, both terms are `O(T log T)` for positive large `T`. The additive ones in the local contracts handle index zero. A total bound valid at small `T` and all `k` can use `(k+1)*(T+1)*log₂(T+2)` up to a machine-dependent constant. Nothing in these G2–G4 statements forces an extra logarithmic factor; the final simulation and time-hierarchy assembly remain G5 and later gates' obligations.

## Retirements, homes, policy and sequencing

The landed Zone deletes exactly the intended sixteen declarations in five blocks, 281 source lines: the three paired-cell codec declarations (`zoneCellBits`, `zoneCellOf`, `zoneCellOf_bits`); the four old binary-tape declarations (`zoneTape` and its empty/bound/home-write lemmas); the seven private staging declarations (`zoneStageWord`, its length/get-element lemmas, `zoneStageSlot`, and the right-window/left-window/bounds lemmas); and `FinTM.exists_zoneShiftInTM`, `FinTM.exists_zoneShiftOutTM`. Their pure cascade dependencies remain. The new carrier and G4 row contracts replace their roles without preserving the retired binary representation or its weaker row budget.

No other existing Zone body changes, and `zoneCascadeRight_frame` retains its proved body. The three documented prose repairs are appropriate: describe the unused slot without the retired pairing codec, describe the pure cascade cost without claiming a retired row budget, and restore the sketch label on `zoneSide_adjacent`. The supplied external-consumer search reports none; I found none in the attached consumer sources. The bundle is not the entire tree, so full-tree absence and downstream elaboration remain matters for the existing landing replay. Historical design/audit mentions should remain.

`zoneSlot`, `zoneIndex`, and `zoneIndex_eq_iff` may remain until the planned split. “Consumer-free” here should mean no remaining external consumers of the family; internal references among its members still exist.

The layering is coherent: pure Zone imports the two Mathlib modules; ZoneTape imports the pure layer and Simulation; ZoneRebalance imports ZoneTape and the core Contract module. The mapped tables belong below their contract instances. During fill, importing Catalog/Contract composition into ZoneRebalance need not create a cycle. The facade adds the two new imports and their entries while retaining the supplied #92 additions. The new/edited material introduces no line over 100 characters; Catalog's 100 over-width lines are inherited. The reported facade-lint failure is already in the base; the large Catalog/Zone sizes are not new mathematical defects.

The G4 fill must use a public host appropriate to the actual two-tape layout. Existing phase/round interfaces are candidates; a generic counter-loop construction that adds a tape cannot simply be substituted for a two-tape witness. Before the fill brief, identify the host and its scratch/ruler layout, or gate a missing reusable host under the existing hosts-first policy. This is an implementation obligation already implied by that policy, not a reason to weaken the contracts or insert a private host.

MIG-1 stage S adds `Cfg.ofWords_copy_endpoint` and `Cfg.ofWords_transfer_endpoint` beside the framed rows and moves the two rewind-head lemmas to Simulation. This gate inserts mapped tables near the original definitions, makes the nine private unfolding repairs, and appends the mapped framed rows. The supplied staged sources support the claimed semantic independence and disjoint edit regions; no S proof needs a table unfolding. MIG-1's later F-D work is distinct from S and must continue to use the frozen framed interface.

**Order:** land S first, then rebase this gate's landing PR on S. Regenerate the landed files and rerun the landed-Catalog check, Catalog chain, freeze, and complete public axiom inventory at that actual tip; the inventory must include S's new public declarations rather than be fixed at 92. Preserve the planned user-merged PR and downstream replay. Fill G2 only after S, then fill the cascade-home lemma and G4 witnesses, run the fill gate, and proceed to G5's own statement gate.

## Rulings on open questions 1–9

| Question | Ruling | Reason / condition |
|---|---|---|
| 1. G2 home | **`Build/Catalog.lean`.** | The plain rows now depend on the mapped tables. A new module importing Catalog and also supplying those definitions back to Catalog would create a cycle; a broader foundational split is unnecessary for this gate. Rebase after MIG-1 S. |
| 2. Exhausted feeding side | **Keep `short`, identity, and separate extension/retry.** | It realizes the total pure operation without pretending level `ℓ` is laid out. Extension supplies the donor and preserves represented tape contents. |
| 3. Pure Zone imports | **Use exactly the two proposed Mathlib imports.** | The retired machine realization is gone; the remaining definitions and lemmas are pure. The supplied standalone/chain evidence supports this cut. |
| 4. Packing | **Keep inner packing.** | The innermost occupied-slot test finds a nonempty track zone, and full-capacity physical words support mapped sweeps. Leftward physical traversal is handled explicitly by reversal. |
| 5. Existential G4 rows | **Accept now; name witnesses at fill.** | The finite state/alphabet data, fixed machine, exact endpoint, first-exit cut, and bounds are sufficient and nonvacuous. Preserve these facts when exposing the named machines. |
| 6. Residual slot/index family | **Keep until the planned Zone split.** | It is a small pure family, not a conflicting second physical carrier. Removing it is unnecessary to make this gate coherent. |
| 7. Shared trace at G2 fill | **Yes.** | Prove the generalized trace family once using the public trace facility, then derive the plain framed rows from the proved mapped rows. Do not retarget existing proved plain theorems to admitted mapped results during the intervening statement phase. |
| 8. Scratch envelope | **Keep the time-implied bound.** | Each transition moves a head at most one cell; the uniform time bound yields the stated interval around any initial scratch position. Endpoint restoration remains essential and is present. |
| 9. Three Zone doc fixes | **Include all three.** | They remove obsolete representation/row references and restore the required sketch label without changing the mathematics. |

Question 10 was decided by the user. Its removal requirements are satisfied; the small remaining sibling-pair rulings above do not reopen it.

## Final disposition

**PASS — 0 blockers, 0 majors, 5 minors.** Address or explicitly waive the five listed minors, retain the existing rebase/replay obligations, and proceed with the statement landing in the ruled homes and order. No scoped theorem needs a stronger hypothesis or a weaker conclusion on the evidence examined.

## Notation

`k` is the number of simulated tracks; `ℓ` is the number of laid-out levels; `i`/`j` are level or shift indices; `L_i` and `R_i` are the per-track left/right lists; `D` is `ZoneData`; `T` is the simulated run length; `L` is an upper bound on indices. A **virtual blank** is a stored `none` value inside an occupied slot, an **unused slot** has no list entry, and a **physical blank** is the outer `none` on the machine tape. These three notions must not be conflated.
