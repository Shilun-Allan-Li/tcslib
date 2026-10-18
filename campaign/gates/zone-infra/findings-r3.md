**§13 tranche A-S2, round-3 statement-gate audit**

**PASS — 0 blockers, 0 majors, 1 minor. The statement gate closes under the pack’s stated evidence boundary.**

The missing-room blocker A-S2-R2-1 is repaired. Both amended cascade contracts and both new regressions are true as literally stated. The inventory correction A-S2-R2-2 remains inaccurate: the current `Zone.lean` contains **20 sorried declarations and 24 literal `sorry` terms**, not 22 sorried declarations.

Audited the seven attachments in `zone-infra-r3-bundle.md`, including the complete 647-line `Zone.lean`. Branch attribution: `complexity/arora-barak-ch3-4`; the round-3 pack supplies no exact commit hash. Audit date: 2026-10-09 (America/New_York). Bundle SHA-256: `081535e127c51bb2872ed146c3d7801c212f91b9c6e511764f14076f7c1966d3`. Extracted `Zone.lean` SHA-256: `fd7ce4c0705d4ea6fc1f5067b90b783b81a5697c16d04ef6a2ee0706b36cce17`.

Line references below refer to the extracted `TCSlib/Complexity/TuringMachine/Build/Zone.lean`, not the enclosing bundle. This is a mathematical statement audit; no Lean proof filling or kernel verification is claimed.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| A-S2-R3-1 | note — no findings | `Zone.lean:458–503` · `zoneSide_cascadeRight`, `zoneCascadeRight_lengths`; disposition A-S2-R2-1 | The added top-left room hypotheses repair the two false contracts. | The exact additions are `length(L_j) + 2^(j-1) ≤ zoneCapacity j` for words and `length(L_j) + 2^j ≤ zoneCapacity j` for lengths. The former makes the central move legal; the latter also makes the second top transfer legal. The old counterexamples and the complete two-pass induction are replayed below. | **Close A-S2-R2-1.** Retain the distinct hypotheses and the separate word proof; nonempty donors alone do not imply half-full restoration. |
| A-S2-R3-2 | **minor** | Round-3 pack · disposition A-S2-R2-2 | Four sorried theorems were added, giving 22 sorried declarations. | Only `zoneCascadeRight_zero` and `zoneCascadeRight_blocked` are new. The two main contracts are amended existing declarations. Current counts are 20 definitions/structures, 16 sorried theorems, 4 sorried definitions containing 8 capacity holes, and 2 proved theorems: **20 sorried declarations, 24 `sorry` terms, 38 explicit declarations**. | Record a pack erratum and use the corrected inventory below for the fill brief. The prior minor is not closed by the supplied count. |
| A-S2-R3-3 | note — no findings | `Zone.lean:511–516` · `zoneCascadeRight_zero` | The zero-level regression has exactly the relevant specialized hypotheses. | `range 0 = []`; `2^(0-1)=2^0=1` in natural-number arithmetic; the lower-level premises are vacuous. Nonempty right word is equivalent to length at least one. Thus these are the main contracts’ zero-level hypotheses, and the asserted word equalities follow from the enabled head move. | No change required. The regression asserts word equalities; the zero-level length conclusions also follow directly. |
| A-S2-R3-4 | note — no findings | `Zone.lean:527–534` · `zoneCascadeRight_blocked` | Fullness on the left through level `j` blocks every outward-left call and the central move, preserving both represented words. | At every scheduled level `1 ≤ i ≤ j`, the receiving word is still full, so `zoneCapacity i + 2^(i-1) ≤ zoneCapacity i` is false. Inductively all left words remain unchanged; full level zero blocks the move. Right shifts preserve concatenation for arbitrary right words. No right-side premise is missing. | No change required. Do not strengthen the conclusion to equality of all zone contents: right words can be redistributed. |
| A-S2-R3-5 | note — no findings | `Zone.lean:259–436,543–630` · inherited operations, cost, machine rows, exports; dispositions A-S2-R2-3/4/5/7 | The accepted operational repair and geometric budget remain available. | Current source still has no inward room binder, puts outward room inside its guard, uses total wrappers and the descending/move/ascending fold, and explicitly includes identity behavior in both machine rows. The cost statement retains the reindexed geometric sum. These shapes agree with the prior report; the restored length contract now supports its schedule argument. | Carry those source-level acceptances. Exact historical byte identity has the limitation in A-S2-R3-7. |
| A-S2-R3-6 | note — no findings | `Zone.lean` · repair debt screen; disposition A-S2-R2-9 | The repair adds no copied proved machinery. | The two additions are sorried regression statements over existing operations. There is no private controller/proof family in the current file, and no new definition is required by the repair. | No new debt acknowledgment is required for the supplied repair. Retain the fill-time screen for the eventual Z4 witness. |
| A-S2-R3-7 | note — evidence boundary | Round-3 pack · carried dispositions A-S2-R2-6/8/10 and exact-delta claim | Historical confinement, unchanged external files, and execution can be independently certified from this packet. | The packet contains current `Zone.lean`, the plan, template, prior packs, and prior findings. It does **not** contain the old Zone source, a repair diff, compiler/lint logs, `Codes2Tape.lean`, the Robustness files, or `machine-library-design.md`. Neither `lean` nor `lake` is on PATH. Consequently the exact changed-file/byte claims and execution results remain attestations; Z4 and §13c acceptances are inherited from round 2. | Preserve this explicit boundary. Supply old blobs/diff and logs only if independent historical or execution certification is required. No source-level objection in this repair reopens the inherited acceptances. |

I read the current declarations with comments removed before reading their declaration docstrings. The statement-derived restatements are:

| Declaration | Restatement from the literal statement | Comparison with documentation |
|---|---|---|
| `zoneSide_cascadeRight` | For a valid index, all lower right words are empty, all lower left words are full, the top right word is nonempty, and the top left has room for `2^(j-1)` cells. The cascade prepends the old home to the concatenated left words and removes the first cell of the concatenated right words. | Matches. It asserts neither half-full restoration nor an equality for the new home. No balance invariant is silently assumed. |
| `zoneCascadeRight_lengths` | Under the same lower-zone conditions, a top right donor of at least `2^j` cells, and top left room for `2^j` cells, every lower word ends with length `2^k`; the top right loses `2^j` cells and the top left gains that amount. | Matches. The stronger donor and room premises are both used by the second pass. |
| `zoneCascadeRight_zero` | On a nonempty level set, with nonempty right level zero and room for one cell on left level zero, the zero-level cascade has exactly the two represented-word effects above. | Matches. No condition is imposed on higher words. |
| `zoneCascadeRight_blocked` | If every left word at or below a valid `j` is full, both concatenated words are preserved by the cascade, regardless of home and of every right word. | Matches. Its conclusion permits redistribution of the right words. |

The following arguments use `L_i = z.left(i)` and `R_i = z.right(i)` for the **initial** words, and `|·|` for list length. Capacity is the source’s `zoneCapacity i = 2·2^i`. Every referenced index is valid because `j < ℓ` and the folds call only levels `1,…,j`.

First, the shifts preserve concatenation directly. An enabled inward call replaces the adjacent segment

\[
[]\mathbin{++}R_i
=\operatorname{take}(2^{i-1},R_i)
 \mathbin{++}\operatorname{drop}(2^{i-1},R_i).
\]

An enabled outward call replaces

\[
L_{i-1}\mathbin{++}L_i
=\operatorname{take}(2^{i-1},L_{i-1})\mathbin{++}
 \bigl(\operatorname{drop}(2^{i-1},L_{i-1})\mathbin{++}L_i\bigr).
\]

These are the prefix/suffix identity and associativity; all other words are untouched. Disabled calls are identities. Both contents-level wrappers also preserve home and the opposite side. Thus every finite fold of shift pairs preserves both concatenations and home.

For `zoneSide_cascadeRight`, split on `j`.

1. **`j=0`.** Both folds are empty. Natural subtraction gives `0-1=0`, so the room premise is exactly `|L_0|+1≤2`. The guarded move therefore fires. Since `R_0≠[]`, taking its tail removes the first cell of the whole right concatenation, even when higher words are nonempty; the push prepends `z.home` to the left concatenation.
2. **`j≥1`, left descent.** At stage `j`, the lower left word is full and the new room premise is exactly the outward guard. After this stage the lower word has length `2^(j-1)`. Before each subsequent stage `i<j`, the previous stage `i+1` has left the receiving word at level `i` with length `2^i`, whereas level `i-1` is still full. Its guard holds because

   \[
   2^i+2^{i-1}=3\cdot2^{i-1}
   \le4\cdot2^{i-1}=\operatorname{zoneCapacity}(i).
   \]

   Induction down to `i=1` leaves left level zero with length one.
3. **Right descent.** Before stage `j`, the lower right word is empty. At each following stage the next lower right word is still its initial empty word. An inward call takes a positive-length prefix of a nonempty donor because `2^(i-1)≥1`. More explicitly, the word delivered to level `i-1` has length

   \[
   \min(|R_j|,2^{i-1})\ge1,
   \]

   by descending induction and `min(min(a,b),c)=min(a,c)` when `c≤b`. Right level zero consequently has length one.
4. **Move and ascent.** Left level zero has room (`1+1=2`), right level zero is nonempty, and home is still `z.home`. The single central move has the two required word effects. Every ascending shift preserves them by the identities above, independently of which ascending guards fire. This proves the word theorem without asserting any restoration property.

For `zoneCascadeRight_lengths`, the case `j=0` is the same enabled move: its right length becomes `|R_0|-1` and left length becomes `|L_0|+1`; the lower-level conclusion is vacuous. Suppose now `j≥1`.

The stronger room premise implies the one-pass room premise. The donor bound ensures that the first top inward call transfers exactly `2^(j-1)` cells. Each later descending call at level `i<j` receives a donor of length `2^i` from the preceding stage, and transfers exactly `2^(i-1)` cells. The left guard calculation is the one above. Induction through these calls gives the following **current** lengths after the descending pass; pairs in this table are ordered **(right, left)**:

| Level | Current lengths after descent |
|---|---|
| `0` | `(1,1)` |
| `1≤k<j` | `(2^(k-1), 3·2^(k-1))` |
| `j` | `(|R_j|−2^(j-1), |L_j|+2^(j-1))` |

The central move changes the level-zero pair to `(0,2)`. The ascending induction is:

\[
\begin{aligned}
\text{before stage }i:\quad
&\text{level }i-1=(0,2^i),\\
i<j:\quad
&\text{level }i=(2^{i-1},3\cdot2^{i-1}),\\
&3\cdot2^{i-1}+2^{i-1}
=2^{i+1}=\operatorname{zoneCapacity}(i),\\
\text{after stage }i:\quad
&\text{level }i-1=(2^{i-1},2^{i-1}),\\
&\text{level }i=(0,2^{i+1})\quad(i<j).
\end{aligned}
\]

The right lower word is empty and the left lower word is full, so both guards fire. The last line is precisely the induction hypothesis for stage `i+1`; smaller restored levels are untouched. At the final stage `i=j`, the remaining donor and receiving room satisfy

\[
\begin{aligned}
|R_j|-2^{j-1}&\ge2^{j-1},\\
|L_j|+2^{j-1}+2^{j-1}
&=|L_j|+2^j\le\operatorname{zoneCapacity}(j).
\end{aligned}
\]

Thus both final transfers have length `2^(j-1)`. The top lengths become `|R_j|−2^j` and `|L_j|+2^j`; the donor bound justifies the natural-subtraction calculation. Every lower level has the asserted half-full lengths. This proves the length theorem.

The stronger room condition is also necessary for this conclusion: the conclusion and the result’s `left_le` field give

\[
|L_j|+2^j
=|(\mathrm{zoneCascadeRight}\ j\ z).left(j)|
\le\operatorname{zoneCapacity}(j).
\]

Under the inherited classical stable invariant, `|L_j|+|R_j|=zoneCapacity j`, and a nonempty donor has length `2^j` or `2·2^j`. Consequently

\[
|L_j|+2^j\le |L_j|+|R_j|
=\operatorname{zoneCapacity}(j).
\]

The repair therefore excludes no pre-state satisfying that invariant. The extra room is not inferred from `ZoneContents` alone.

For `zoneCascadeRight_zero`, specializing the main hypotheses gives

\[
\begin{gathered}
j<\ell\ \Longleftrightarrow\ 0<\ell,\qquad
\forall k<0,\ (\cdots)\quad\text{vacuously},\\
2^{0-1}=2^0=1,\qquad
R_0\ne[]\ \Longleftrightarrow\ 1\le|R_0|.
\end{gathered}
\]

These are exactly the regression’s hypotheses, with logical equivalence for the donor bound. Unfolding the empty folds and the enabled move proves its stated word conclusion; no new assumption or hidden nonempty outer zone is needed.

For `zoneCascadeRight_blocked`, the hypotheses imply that every left zone with index at most `j` is full. Induct over the descending stages: an inward-right call leaves all left words unchanged, while the outward-left receiving inequality would be

\[
\operatorname{zoneCapacity}(i)+2^{i-1}
\le\operatorname{zoneCapacity}(i),\qquad 1\le i\le j,
\]

which is false because `2^(i-1)≥1`. Therefore every such outward call is identity. At the central move, left level zero is still full—by `hfull` when `j=0`, and by `hl` otherwise—and its guard is the false inequality `2+1≤2`. The move is identity. The identical induction applies to the ascending stages. All left words and home are unchanged, and all right shifts preserve their concatenation. This proves the regression for arbitrary right data, including an empty right side.

The required counterexamples replay as follows. In the traces, each state is shown as **left lengths; right lengths**.

| Instance | Guarded execution | Effect of amended hypotheses |
|---|---|---|
| `ℓ=1, j=0`, `L_0=[none,none]`, `R_0=[some true]` | The move remains identity: `3≤2` is false. Both old conclusions still fail. | Both new room premises are `3≤2`, so both contracts now exclude this input. The blocked regression covers it. |
| `ℓ=2, j=1`, `(2,4);(0,2)` | `(2,4);(0,2) → (2,4);(1,1) → (2,4);(1,1) → (2,4);(1,1)` | Word room fails (`4+1≤4`); length room fails (`4+2≤4`). Both concatenations are unchanged, exactly as the blocked regression says. |
| `ℓ=2, j=1`, `(2,3);(0,2)` | `(2,3);(0,2) → (1,4);(1,1) → (2,4);(0,1) → (2,4);(1,0)` | Word room holds (`3+1=4`), length room fails (`3+2>4`). Word equalities hold; the second outward call is blocked and half-full restoration fails. This is the intended separation. |
| Exact two-pass boundary: `(2,2);(0,2)` | `(2,2);(0,2) → (1,3);(1,1) → (2,3);(0,1) → (1,4);(1,0)` | Both hypotheses and both conclusions hold, including equality in the stronger room bound. |
| Short nonclassical donor: `j=3`, `(2,4,8,12);(0,0,0,1)` | The move fires; final lengths are `(1,2,8,16);(0,0,0,0)`. | Weak room holds (`12+4=16`); word equalities hold. Neither the stronger donor nor stronger room premise holds. The word proof correctly requires no half-full restoration. |

As an additional inherited-domain check, the former dead end `(2,0);(0,4)` executes

\[
((2,0);(0,4))\to((1,1);(1,3))
\to((2,1);(0,3))\to((1,2);(1,2)).
\]

Both new room conditions hold, so the repair has not reintroduced the prohibition on full inward donors. Levels above `j` remain untouched by every scheduled operation. When `ℓ=0`, all four contracts’ valid-index/positive-level hypotheses are impossible, as intended.

The geometric charge remains

\[
\begin{aligned}
\sum_{r=0}^{j-1}4(2^{r+1}+(r+1)+1)
&=4\sum_{i=1}^{j}(2^i+i+1)\\
&\le8\sum_{i=1}^{j}2^i
&& (i+1\le2^i\text{ for }i\ge1)\\
&=16(2^j-1)\le16\cdot2^j.
\end{aligned}
\]

For the auxiliary inequality, the base `i=1` is equality and `i+2≤2(i+1)≤2^(i+1)` gives the induction step. The empty sum at `j=0` is zero. Thus the hypothesis repair changes neither the scheduled calls nor their geometric charge, and the classical pre-states still satisfy the repaired restoration contract. This closes the cascade obstruction to the inherited amortization argument; it is not a claim that the consumer simulator has already been built or proved.

The authoritative current-source inventory and the conditional carried totals are:

| Surface | Definitions/structures | Sorried declarations | Literal `sorry` terms | Skeleton-time proved theorems | Evidence |
|---|---:|---:|---:|---:|---|
| Current `Zone.lean` | 20 | 20 | 24 | 2 | Recounted from attached source |
| `Codes2Tape.lean` | 6 | 2 | 2 | 1 | Round-2 inventory; unchanged-file attestation |
| Z4 appendix in `SingleTape.lean` | 0 | 2 | 2 | 0 | Round-2 inventory; unchanged-file attestation |
| `alphabet_reduction_spaceUsed` | 0 | 1 | 1 | 0 | Inherited inventory and unchanged-row attestation |
| **Whole A-S2 tranche, conditional on those unchanged rows** | **26** | **25** | **29** | **3** | Current Zone plus carried rows |

Definitions with sorried proof fields count in both the definitions and sorried-declarations columns. The eight capacity holes are still the two fields in each of `zoneShiftIn`, `zoneShiftOut`, `zoneMoveRight`, and `zoneMoveLeft`. The calculations are

\[
\begin{aligned}
\text{Zone sorried declarations}&=16+4=20=18+2,\\
\text{Zone literal holes}&=16+8=24=22+2,\\
\text{Zone explicit declarations}&=20+16+2=38,\\
\text{whole-tranche sorried declarations}&=20+2+2+1=25,\\
\text{whole-tranche literal holes}&=24+2+2+1=29.
\end{aligned}
\]

There are 50 explicit declarations in the conditional whole-tranche inventory. The two new theorems explain the increase from round 2; adding hypotheses to two existing theorems does not add two more declarations. Literal holes are source counts, not an independently observed compiler-warning count.

Independent finite-model corroboration passed **74,562 applicable contract/regression instances**: 49,908 word instances and 17,166 length instances covering every pair of top lengths and all three home values through `j=6`; 7,344 blocked instances covering every vector of right lengths through `j=3`; and 144 zero-level instances covering every eligible level-zero word over `none`, `some false`, and `some true`. The larger cases used patterned words over those same three values, with an additional nonempty outer level to check framing. All checked intermediate states met their capacity bounds; all blocked outward/move guards were false. The model also reproduced the six displayed traces. These finite checks corroborate the general list and induction arguments above; they do not replace them or certify Lean elaboration.

No repository checkout, mutation, Lean build, proof filling, or historical byte comparison was performed. The current source supports the repaired statements and the accepted operational shapes. Confinement of the historical delta to the advertised hypotheses/docstrings, regressions, and header cannot be proved from descriptions alone; the pack explicitly carries that limitation. Z4’s demand-grown witness route and §13c’s outstanding input-interface/parser ledger remain the prior round’s accepted obligations, not newly inspected source in this packet.

Notation: `L_i` and `R_i` are the initial left and right level-`i` words; `|·|` denotes list length; `++` denotes list concatenation; `take(n,·)` and `drop(n,·)` denote the length-`n` prefix and remaining suffix. Length pairs in the induction table are ordered (right, left); trace states list left lengths before right lengths. `i`, `j`, `k`, and `ℓ` are the source’s level indices and level count; `r` is the zero-based summation index; `a,b,c` in the minimum identity are natural numbers.
