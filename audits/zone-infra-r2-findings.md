**§13 tranche A-S2, round-2 statement-gate audit**

**FAIL — 1 blocker, 0 majors, 1 minor. The gate remains open.**

Audited the eight attachments in `zone-infra-r2-bundle.md`, attributed by its pack to commit `fb721402`, branch `complexity/arora-barak-ch3-4`. Audit date: 2026-10-09 (America/New_York). Bundle SHA-256: `e78257a8a4b7fe2917470d1eeb2784098e09d71c4ba13396a655160b3bff3cc8`.

The old inward-shift domain defect is repaired, and the old Z4 witness is explicitly replaced in the binding sketches. However, **both new cascade contracts are false as stated**: the hypotheses omit room in the top left zone. This is one shared blocker affecting two declarations, not a failure of the guarded definitions' capacity fields.

Line references below refer to the extracted attachment, not the enclosing bundle. `Zone.lean` abbreviates `TCSlib/Complexity/TuringMachine/Build/Zone.lean`; `SingleTape.lean` abbreviates its `Robustness/SingleTape.lean` sibling.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| A-S2-R2-1 | **blocker** | `Zone.lean:443–475` · `zoneSide_cascadeRight`, `zoneCascadeRight_lengths` | The supplied hypotheses ensure one right move and restoration of all lower zones to half-full. | Set `ℓ=1`, `j=0`, left word `[none, none]`, right word `[some true]`. Both theorems' hypotheses hold, but the guarded head move is identity because `2+1≤2` is false. The word conclusion implies `2=3`; the length conclusion explicitly requires the left word to have length 3. Positive-level counterexamples below show the same defect and distinguish room for one pass from room for both. | Add top-left receiving room. The length theorem needs `length(L_j)+2^j≤zoneCapacity j`. The word theorem is valid with `length(L_j)+2^(j-1)≤zoneCapacity j` (natural subtraction), or with the stronger common `+2^j` condition. Alternatively supply a classical invariant that implies the relevant condition. Amend the docstrings/sketches and add regressions at `j=0`, a full top receiver, and a receiver with room for only one pass. |
| A-S2-R2-2 | minor | Round-2 pack · disposition A-S2-3, brief item 2, elaboration inventory | The repair's declaration/definition/capacity counts are consistent. | `Zone.lean` has **20 definitions/structures, 18 sorried declarations, 22 literal `sorry` terms, and 8 capacity holes in 4 definitions**. The pack still says six capacity fields; its explanation of the 22 warnings mixes the old whole-tranche declaration count with the new Zone count. Five definitions are introduced, two already included among the six new sorried declarations. | Use the inventory below. Distinguish 3 additional sorry-free definitions from 5 newly named definitions, declarations from `sorry` terms, and Zone counts from tranche counts. The literal count 22 is correct; the reported compiler warning count is not independently certified here. |
| A-S2-R2-3 | note — no findings | `Zone.lean:253–339,512–571` · raw shifts, wrappers, machine rows; disposition A-S2-1 | A full donor is admitted inward; failed outward guards produce identity. | The inward wrapper and row have no room binder. The outward room inequality is a conjunct inside the raw guard. The former `zoneShift` declaration is absent. The old `ℓ=2` dead end, full-chain family, and four-move cycle are served locally; see the traces below. | The operational repair is accepted. Closure still requires repairing A-S2-R2-1. |
| A-S2-R2-4 | note — no findings | `Zone.lean:307–430` · full-donor regression, total wrappers, `zoneMove`, fold definitions | These new declarations implement their stated data operations. | Body-first readings are recorded below. All eight capacity fields are provable; `zoneMove` needs pushed-side room but deliberately does not require a nonempty popped side. The fold order is exactly descending, one move, ascending. | No repair to these definitions is needed. |
| A-S2-R2-5 | note — no findings | `Zone.lean:484–486` · `zoneCascade_cost_le` | The reindexed sum is a geometric charge for four shift calls per level. | Reindexing by `i+1` gives precisely the sum over levels 1 through `j`; the independent calculation below proves the stronger bound `16*(2^j-1)`. It also covers `j=0`. | Retain the statement. Correct cascade preconditions before using half-full restoration in event separation. |
| A-S2-R2-6 | note — no findings | `SingleTape.lean:994–1043` · both Z4 sketches; disposition A-S2-2 | The binding route now uses a demand-grown witness and handles all enlarged-alphabet inputs. | The old stationary-head counterexample is explicitly binding. The replacement route names demand-only growth, the interleaving factor, partial-sweep containment, the same-length retraction, empty alphabet, zero tapes, and the composite coefficient `c₂*(c₁+1)`. The current theorem shapes agree with the round-1 report. | This closes the old proof-route major at statement-gate level. Construct and verify the new witness at fill time; the received `sweepTM` remains unsuitable. Historical byte equality is subject to A-S2-R2-10. |
| A-S2-R2-7 | note — no findings | `Zone.lean:70–99,492–547` · exports/row docstrings; disposition A-S2-4 | Export names and identity-branch semantics have been corrected. | The listed raw operations and wrappers exist; the interval export includes `MultiTapeTM`; both machine docstrings expressly include identity behavior. | The requested correction is accepted. |
| A-S2-R2-8 | note — no findings | `machine-library-design.md:1174–1180` · §13c; disposition A-S2-5 | Ex 4.1 is a design assessment with an outstanding implementation ledger. | The text explicitly requires a space-accounted native/suffix input interface or buffer, records a materialized copy's linear cost, and requires a parser space ledger. A uniform bounded-acceptance scheme alone is not a space guarantee; the new text still requires that separate ledger. | Preserve this boundary in the stage-1 brief. |
| A-S2-R2-9 | note — no findings | Repair delta · debt screen; disposition A-S2-10 | No new copies of proved machinery are introduced. | The new cascade composes this layer's shifts and move via two folds. There is no new private controller/proof family in `Zone.lean`. The existing sweep family is received material, and the replacement sketch expressly requires reuse/refactoring without copying. | No new debt acknowledgment is required for the supplied repair. Screen the actual replacement witness during filling. |
| A-S2-R2-10 | note | Pack · evidence boundaries; dispositions A-S2-6–A-S2-11 | Execution and historical freeze claims are independently verified. | The packet supplies current sources and the old report, but no old source blobs, repair diff, compiler/lint logs, `AlphabetReduction.lean`, or the ND/scheme mirror files. Neither `lean` nor `lake` is available on this audit's PATH. Current counts and source shapes were checked; historical byte identity, compiler results, and an independent repeat of omitted mirror comparisons cannot be certified from this packet. | Carry the round-1 evidence boundary explicitly. Attach old blobs/diff and execution evidence if independent freeze/elaboration certification is required. This does not affect the source-level counterexample. |

I extracted the Lean source and removed comments before reading the new declaration bodies. I then compared these readings with their docstrings and the inherited brief:

| New declaration | Body/statement-derived reading | Assessment |
|---|---|---|
| `zoneShiftIn` | Preserve home and the opposite family; apply `zoneShiftInW` on the selected family (`true` selects right). No domain hypothesis. | Faithful; both capacity fields are provable. |
| `zoneShiftOut` | The analogous total lift of `zoneShiftOutW`; fullness and room are decided inside the raw operation. | Faithful; both capacity fields are provable. |
| `zoneMove` | On a nonempty level set, push/pop in the selected direction if the pushed level-zero word has room; otherwise return the original contents. Popping an empty word yields `none`. | Faithful. It is not an unconditional virtual move on every carrier value. |
| `zoneStepPair` | First shift the right family inward at level `i`, then shift the left family outward at that same level. | Faithful; the two operations affect disjoint families and preserve home. |
| `zoneCascadeRight` | Apply stages `j,j-1,…,1`, then the total right move, then stages `1,2,…,j`. At `j=0`, both lists are empty, so this is just `zoneMove true`. | Faithful as a total definition; successful restoration needs additional hypotheses. |
| `zoneShiftInW_full_donor` | For a valid level with empty lower word, the two updated words are exactly the upper word's prefix and suffix at `2^(i-1)`. No donor length bound is assumed. | True. It covers full donors and is stronger than a full-donor-only regression. |
| `zoneSide_cascadeRight` | Below `j`, assume right words empty and left words full; assume only a nonempty right donor at `j`. Conclude that left concatenation gains home and right concatenation loses its head. | False: neither top-left room nor a balance invariant is assumed. |
| `zoneCascadeRight_lengths` | Under the same lower-zone conditions and a donor of at least `2^j` cells, assert half-full lower words and a transfer of exactly `2^j` cells between the two top occupancies. | False: the asserted left-top growth need not fit its capacity. |
| `zoneCascade_cost_le` | Bound the sum of four level budgets for levels 1 through `j`, independently of data or guards. | True; it is a numerical budget lemma, not a complete simulator-time theorem. |

The two amended raw operations also agree with their bodies: inward is identity unless the level is valid and the lower word is empty; outward is identity unless the level is valid, the lower word is full, **and** the upper word has enough room. Neither false conjunct can create an ill-typed contents value.

For a completely explicit counterexample to both cascade statements, take

\[
\ell=1,\quad j=0,\quad z.home=\mathrm{none},\quad
z.left(0)=[\mathrm{none},\mathrm{none}],\quad
z.right(0)=[\mathrm{some\ true}].
\]

Both words fit `zoneCapacity 0 = 2`. The lower-zone hypotheses quantify over `k<0`, so are vacuous. The donor hypotheses hold because the right word is nonempty and

\[
2^0=1\le |z.right(0)|=1.
\]

Now unfold the actual definitions, in order:

\[
\begin{aligned}
\mathrm{List.range}\ 0&=[],\\
\mathrm{zoneCascadeRight}\ 0\ z&=\mathrm{zoneMove}\ \mathrm{true}\ z,\\
|z.left(0)|+1\le\mathrm{zoneCapacity}\ 0
&\iff 3\le2\iff\mathrm{False},\\
\mathrm{zoneMove}\ \mathrm{true}\ z&=z.
\end{aligned}
\]

Consequently the first theorem's left-word equality implies

\[
2=|\mathrm{zoneSide}(z.left)|
=|z.home::\mathrm{zoneSide}(z.left)|=3,
\]

and the second theorem's last equality requires the same impossible `2=2+1`. Its right-top equality additionally requires `1=1-1=0`. The counterexample uses no questionable capacity proof or inaccessible machine configuration.

The defect is not confined to `j=0`. Write `L_i=z.left(i)` and `R_i=z.right(i)` for the following occupancy traces. Each displayed pair lists left lengths first, then right lengths. At `ℓ=2`, `j=1`, take `(|L₀|,|L₁|)=(2,4)` and `(|R₀|,|R₁|)=(0,2)`. Both contracts' hypotheses hold.

| Stage | Left lengths | Right lengths | Guard behavior |
|---|---|---|---|
| Initial | `(2,4)` | `(0,2)` | Both families fit. |
| Descending pair | `(2,4)` | `(1,1)` | Inward-right succeeds; outward-left fails `4+1≤4`. |
| Head move | `(2,4)` | `(1,1)` | Fails `2+1≤2`. |
| Ascending pair | `(2,4)` | `(1,1)` | Inward-right fails emptiness; outward-left again fails room. |

The left concatenation never gains home. The length theorem demands left lengths `(1,6)`, although the top capacity is 4.

Even admitting the first outward transfer is insufficient for the length theorem. With initial left lengths `(2,3)` and right lengths `(0,2)`, the trace is

\[
((2,3),(0,2))
\longrightarrow((1,4),(1,1))
\longrightarrow((2,4),(0,1))
\longrightarrow((2,4),(1,0)).
\]

Here the word theorem's conclusion holds, but the second outward transfer is blocked and the length theorem incorrectly demands left lengths `(1,5)`.

The missing classical condition can be supplied without putting fullness into the carrier. The textbook's stable invariant couples the two occupancies at each level and permits only empty, half-full, or full zones. Thus at a nonempty classical donor,

\[
|L_j|+|R_j|=2\cdot2^j,\qquad |R_j|\ge2^j
\quad\Longrightarrow\quad
|L_j|+2^j\le2\cdot2^j.
\]

This coupling is absent from `ZoneContents` and from both new contracts. The implication is a direct calculation; it is not available from the shipped hypotheses. Source comparison used the indexed [Arora–Barak §1.7 chapter excerpt](https://people.tamu.edu/~rojas/arorabarakbackground.pdf); direct PDF opening was unavailable. The counterexamples above depend only on the attached Lean definitions.

A sufficient shared repair is the additional hypothesis

```lean
(hroom : (z.left ⟨j, hj⟩).length + 2 ^ j ≤ zoneCapacity j)
```

For the length theorem this is necessary, since its conclusion and the result's `left_le` field imply precisely this inequality. It does not exclude any classical pre-state. For the word theorem alone, the weaker `+ 2 ^ (j - 1)` suffices and preserves more of the present nonclassical domain; at `j=0`, natural subtraction makes this `+1`.

Here is the independent schedule argument with the shared repair. At `j=0`, donor nonemptiness and room make the head move legal; the length theorem's donor bound is exactly `1≤|R₀|`. For `j≥1`, under the length theorem's donor bound, the descending pass ends with

\[
\begin{aligned}
(|R_0|,|L_0|)&=(1,1),\\
(|R_k|,|L_k|)&=(2^{k-1},3\cdot2^{k-1}) &&(1\le k<j),\\
|R_j|&=|z.right(j)|-2^{j-1},\\
|L_j|&=|z.left(j)|+2^{j-1}.
\end{aligned}
\]

The top outward guard is legal by `hroom`; subsequent descending receivers were just drained and have room. The head move changes the level-zero pair to `(0,2)`. Immediately before ascending stage `i`, the lower pair is `(0,2^i)`. For `i<j`, the upper right has `2^(i-1)` cells and the upper left has `3*2^(i-1)` cells, so both transfers fit and leave the lower pair `(2^(i-1),2^(i-1))`. At `i=j`, the donor has at least another `2^(j-1)` cells and the second outward transfer is legal exactly because

\[
|z.left(j)|+2^{j-1}+2^{j-1}
=|z.left(j)|+2^j\le\mathrm{zoneCapacity}\ j.
\]

This proves the advertised final lengths by induction through the two passes. For the word theorem with only a nonempty donor, each descending prefix is nonempty, hence `R₀` is nonempty at the central move; the left descending pass makes room. Every surrounding shift preserves concatenation whether its guard succeeds or fails. The single legal push/pop therefore gives exactly the two word equalities. That proof does **not** need to claim half-full restoration from a merely nonempty donor.

The requested old counterexamples now behave correctly:

| Round-1 instance | Round-2 replay |
|---|---|
| Dead end: `ℓ=2`, left `(2,0)`, right `(0,4)` | The descending pair gives left `(1,1)`, right `(1,3)`; the move gives `(2,1)` and `(0,3)`; the ascending pair gives `(1,2)` on each side. All outward guards have room, and the full donor is legal inward. |
| Full chain: `R₀` empty, levels 1 through `m` full, level `m+1` half-full; left complementary | Level-1 inward now succeeds immediately. The entire right cascade uses only levels 0 and 1. No operation at level `m+1` is needed. |
| Four moves: right, left, left, right | Right lengths at levels 0 and 1 follow `(0,4)→(1,2)→(2,2)→(1,4)→(0,4)`, with cascade indices `1,0,1,0`. The left moves are the side-swapped application of the same raw API. Higher words remain unchanged. |
| Full outward lower zone with receiver exactly at capacity minus `2^(i-1)` | The guard succeeds and the new receiver exactly fills. Increasing its old length by one makes the guard false and the operation identity. |
| Nonfull outward lower zone; nonempty inward lower zone; invalid level | Each corresponding operation returns its original family. The total wrappers retain valid capacity fields. |

All eight capacity obligations have direct proofs. Inward lower length is at most `2^(i-1)≤zoneCapacity(i-1)`, and the donor's suffix cannot be longer than the original. For an enabled outward shift, fullness makes the moved suffix's length exactly `2^(i-1)`, and the room conjunct bounds the new upper length; a disabled guard changes nothing. For the head moves, the pushed word's extra cell is covered by the explicit room hypothesis and a tail never increases length. The opposite side and all untouched levels retain their bounds. Thus the new blocker is entirely in the two universal cascade claims.

The inherited concatenation theorems also remain true after the guard repair: enabled inward replaces the adjacent segment `[] ++ w` by `take q w ++ drop q w`; enabled outward reassociates the same prefix/suffix decomposition; every disabled guard is identity. The full-donor theorem follows by unfolding the two enabled inward branches, using `i-1≠i` when `1≤i`.

The geometric ledger is unchanged. Reindex the literal `Finset.range` sum:

\[
\begin{aligned}
\sum_{r=0}^{j-1}4(2^{r+1}+(r+1)+1)
&=4\sum_{i=1}^{j}(2^i+i+1)\\
&\le8\sum_{i=1}^{j}2^i
&&\text{because }i+1\le2^i\text{ for }i\ge1\\
&=16(2^j-1)\\
&\le16\cdot2^j.
\end{aligned}
\]

At `j=0`, the sum is empty and equals zero. The inequality `i+1≤2^i` follows inductively from equality at `i=1` and `i+2≤2(i+1)≤2^(i+1)`. Taking the maximum of the four fixed row coefficients supplies one common multiplier. Unary-level maintenance and level discovery are separate controller costs; as in round 1, `O(j²+2^j)=O(2^j)` suffices.

With **correct** half-full restoration, the total right occupancy below level `i` after an event reaching that level is `2^i-1`. An intervening move not reaching that level changes the total by one. Reaching empty or full and then triggering the next such event needs at least `2^i` moves, including the triggering move. From all-half initialization, at most `⌊T/2^i⌋` events reach level `i`; four level-`i` calls per such event therefore cost `O(T)`. The repaired API permits the classical logarithmic-overhead schedule. The false length contract cannot be used to justify this schedule on arbitrary carrier values.

The two amended machine existence statements remain mathematically credible as literally quantified: for each fixed side, one finite machine and coefficient precede all choices of level, level count, data, and native input. Testing the new outward room guard scans only its bounded two-zone window. Constantly many staged scans can perform the prefix/suffix transformation, preserve all outer contents, clean scratch back to the unary level word, return both heads, and leave native input and output unchanged. The affected data cells lie within

\[
[-2\,\mathrm{zoneBase}(i+1),\;2\,\mathrm{zoneBase}(i+1)+1],
\]

inside the promised interval with endpoints `±(2*zoneBase(i+1)+2)`. Scratch is separately bounded by the same geometric scale. These are statement-gate construction arguments, not a supplied transition-table proof.

For Z4, re-running the inherited scanner still refutes the old witness: with one stationary source work head, source space is always 1, while `sweep_run_to_halt` places the simulator head at `-(n+2)` after `n+1` simulated steps on a length-`n` input. Its visited space is at least `n+3`, contradicting any all-`n` bound `n+3≤2c`. The repaired prose correctly keeps this counterexample and changes the witness route.

For a demand-grown witness, source visited intervals all contain the origin, so their union's size is at most the sum of their sizes. Interleaving adds a fixed tape-count factor and boundary allowance. Applying the bound through the current source transition also covers partial sweeps; after halting the configuration is fixed. A finite-control retraction of enlarged-alphabet inputs preserves their lengths, so the all-input/all-horizon hypothesis applies without monotonicity. Empty source alphabet and zero source tapes are explicitly handled. The composite estimates are exactly

\[
\begin{aligned}
c_2\bigl(c_1(S(n)+1)+1\bigr)
&\le c_2(c_1+1)(S(n)+1),\\
c_2\bigl(c_1(T(n)+1)^2+1\bigr)
&\le c_2(c_1+1)(T(n)+1)^2.
\end{aligned}
\]

Both inequalities use only the corresponding final factor being at least one. Thus the old major is repaired at the proof-sketch level, with no new statement-shape objection.

The current inventory is:

| Surface | Definitions/structures | Sorried declarations | Literal `sorry` terms | Skeleton-time proved theorems |
|---|---:|---:|---:|---:|
| Attached `Zone.lean` | 20 | 18 | 22 | 2 |
| Attached `Codes2Tape.lean` | 6 | 2 | 2 | 1 |
| Attached Z4 appendix in `SingleTape.lean` | 0 | 2 | 2 | 0 |
| **Attached A-S2 surface** | **26** | **22** | **26** | **3** |
| Unattached `alphabet_reduction_spaceUsed`, carried as unchanged | 0 | 1 | 1 | 0 |
| **Whole A-S2 tranche, conditional on that unchanged row** | **26** | **23** | **27** | **3** |

The Zone repair removes one sorried definition, introduces five definitions (two with two `sorry` fields each), and introduces four sorried theorems. Therefore its sorried-declaration count is `13-1+6=18`, and its literal-term count is `16-2+8=22`. Its definition count is `16-1+5=20`. There are 36 explicit Zone declarations, 47 explicit declarations in the attached A-S2 surface, and 48 in the whole tranche under the unchanged-alphabet-row attestation. The eight capacity holes belong to `zoneShiftIn`, `zoneShiftOut`, `zoneMoveRight`, and `zoneMoveLeft`.

The unchanged Zone layout and framing claims have no new source-level objection: bases telescope by capacities, the positive log argument gives the even/odd slot sandwich, and the paired-cell map has the stated signed extent. Z3's visible enumeration still has 27 records per state and reuses `actionBits₂`/`workPair`; the old record-width result of 13 gives the carried table bound `351*(numStates+1)` and complete minimum length 354. The exact ND record/structure comparison and the unattached alphabet-reduction row are inherited evidence, not newly repeated byte comparisons. This qualifies the pack's carried A-S2-6–A-S2-9 dispositions without reopening them on the supplied delta.

Independent finite-model corroboration completed **62,550 checks**: 29,032 guarded-shift order/capacity checks through four levels; 22,098 checks of the word theorem's exact top-room condition for `j=0,…,6`; 11,310 length-condition checks over the same range with sufficiently large donors; nine full-chain four-move cycles; and 101 geometric-sum checks. The model used the actual three virtual-cell values and also reproduced the displayed counterexamples. These finite checks corroborate the general arguments; they are not Lean kernel certification.

No Lean build, proof filling, repository mutation, or historical checkout was performed. `Zone.lean` has 588 lines and `SingleTape.lean` 1,045 lines in this packet. Elaboration, warning emission, lint, unchanged historical prefixes, and the claimed exact changed-file set remain maintainer attestations. A repair of A-S2-R2-1, followed by re-audit of its hypotheses and traces, is required before this statement gate can close.

Notation introduced in this report: `L_i` and `R_i` denote the left and right level-`i` words; `|w|` is list length; `q=2^(i-1)` is the shift cutoff in the concatenation identities; `r` is the zero-based summation index; `c₁,c₂` are the two conversion coefficients. Other variables and identifiers are those already used in the attached sources and briefs.
