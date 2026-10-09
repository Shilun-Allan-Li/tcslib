# §13 A-S2 statement-gate audit

**FAIL — 1 blocker, 1 major, 2 minors. The gate must remain open.**

Audited: the 13 attachments in `zone-infra-bundle.md`, attributed by the pack to `c43f3a53` (spec commit `ca2bb11b`). Audit date: 2026-10-09. Bundle SHA-256: `58e86447461c2f68c02fb616b90059ba845f5623add84adac7c14a519385c2d0`.

The blocker concerns the delivered inward-shift interface and the claimed Hennie–Stearns amortization. The major concerns a false claim about the existing one-tape witness. **Neither finding is a counterexample to an embedded capacity obligation; those obligations are provable.** The existential theorem statements admit the mathematical constructions described below, but the advertised consumer interface and binding proof route need repair before filling.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| A-S2-1 | **blocker** | `Build/Zone.lean` · `zoneShift`, `FinTM.exists_zoneShiftInTM`; module design | The delivered shifts can reproduce the classical rebalance with its geometric amortized cost. | Inward shifting requires upper-word length plus `2^(i-1)` to fit, although it removes cells from that word. A full donor therefore cannot be read inward. Already at `ℓ=2`, right lengths `(0,4)` and left lengths `(2,0)` satisfy the classical fullness/complement invariant but admit no legal shift that changes `R₁`. With more levels, the full-chain example below forces a level-`m+1` transfer during an index-1 classical shift; a four-step cycle repeats this cost, giving quadratic rather than logarithmic-overhead behavior for exact classical rebalancing. | Remove the room premise from the inward row. Split the wrappers, or make `zoneShift`'s room obligation conditional on `inward = false`. Retain the outward premise. Add a full-donor regression and the two-pass cascade/charge lemma below before closing this gate. |
| A-S2-2 | **major** | `Robustness/SingleTape.lean` · `one_work_tape_spaceUsed`, proof sketch; dependent composite | The received `sweepTM` sweeps only source-visited intervals and therefore supplies the new space bound. | Its `.growLeft` and `.growRight` phases unconditionally extend the window every source step. For a one-work-tape machine that scans its native input while keeping its work head at zero, source space is always 1, but the received simulator reaches `-(n+2)` on length-`n` input. No constant bounds this by `c*(1+1)`. See the explicit ledger below. | Replace the sketch with a space-preserving, demand-grown sweep construction, reusing/refactoring existing infrastructure without copying it. Account for the factor from interleaving and for **all target-alphabet inputs**, as the statement requires. The existential statement can remain unchanged; a new witness/proof route is necessary. |
| A-S2-3 | minor | Audit pack · inventory | There are 25 new definitions/structures. | The supplied surface has **22**: 16 in `Zone.lean`, 6 in `Codes2Tape.lean`, none in the Z4 appendices. The 18 sorried declarations, 21 `sorry` terms, and 3 skeleton-time proofs do agree with the source inventory. | Acknowledge a pack erratum; retain the shipped bundle verbatim. Use the inventory below for fill ownership. |
| A-S2-4 | minor | `Build/Zone.lean` · machine-row docstrings and main-results list | The rows “must not be invoked” outside the pure guards; listed exports name the actual API. | Neither row assumes lower-zone emptiness/fullness. Its equality instead requires the machine to implement the **identity** when that guard fails. The main-results list also names absent `zoneShiftIn`/`zoneShiftOut` and `zoneSide_shiftIn`/`zoneSide_shiftOut`, and omits `MultiTapeTM` from the interval-cardinality export. | State that the machine realizes the total guarded operation, including its identity branch. Correct the export names to the `W` operations, `zoneShift`, and `MultiTapeTM.spaceUsedByTape_le_card_Icc`. |
| A-S2-5 | note | Pack · Ex 4.1 design assessment; design §13 Z1/Z4 | The primary route is plausible, but the assessment does not establish its proposed space ledger. | Z1 hosts a **buffered virtual input** on an extra work tape. Materializing or fully traversing a copy of `x` costs `Ω(length(x))` visited work cells, which is absent from `O(S + length(α) + log t)`. The selected-payload-tape bound does not pay for that buffer. Also, an arbitrary effective scheme has no code-length space bound on its canonizer. | Keep this as a completed design assessment, not a discharged implementation proof. The stage-1 review must specify native/suffix input access or another space-accounted input interface, and a concrete parser with its own space ledger. If an input copy is intended, its length must appear or be justified by a hypothesis. |
| A-S2-6 | note — no findings | `Build/Zone.lean` · layout, carrier, pure list identities, six capacity fields | Layout and local data operations are consistent as literally stated. | Independent telescope, logarithm sandwich, signed-cell calculation, and capacity proofs are below. Fullness is not needed for any of these local facts. | No repair beyond A-S2-1/A-S2-4. Add the suggested sanity lemmas. |
| A-S2-7 | note — no findings | `Build/Zone.lean` · both machine existence statements, considered literally | A uniform two-work-tape implementation with unary level and the stated local budgets is possible on the stated domain. | The level is an input to one fixed machine, not a finite-control parameter. Constantly many bounded scans and staged transfers suffice; the data interval contains both affected zones, and scratch has its separate space clause. False pure guards must take the identity branch. | Preserve the uniform quantifier order and geometric budget when repairing the inward domain. |
| A-S2-8 | note — no findings | `Codes2Tape.lean` · all six definitions and both existence statements | Deterministic serialization and scheme laws faithfully mirror the attached references. | Enumeration matches `CodeNDTM.serialize` after deleting only the outer choice enumeration and its transition argument. The shared record has minimum length 13, hence the table guard is `351*(numStates+1)`, versus 702 for ND. The uniform record matches `UniformMachineCode` field-for-field after type/name substitution. | Add the exact serialization-length and parser-guard lemmas. Only the **table term**, not the header-inclusive length, halves. |
| A-S2-9 | note — no findings | Z4 · alphabet reduction, statement shapes, composition | All-time coefficient-constant bounds need no monotonicity assumption on `S`. | Every simulation horizon is compared with a source horizon on an input of the **same length**, and `hS` covers every such horizon. Fixed block width, finite tape count, and additive boundary allowances are absorbed into a single coefficient. The binary composite has the promised fallback shape. | Retain the shapes; resolve A-S2-2 before claiming the composite has a proved route using the received sweep. |
| A-S2-10 | note — no findings | Tranche · debt screen | No new copied proved machinery is present in the supplied increment. | `Zone.lean` contains no copied `SweepCell`/sweep-controller family. Z3 directly reuses `actionBits₂` and `workPair`; its type-specific scheme mirrors are the commissioned surface, not duplicated proof infrastructure. The Z4 appendices contain statements, not private copies. | No human debt acknowledgment is required for this supplied increment. Apply the same screen to the replacement Z4 witness at fill time. |
| A-S2-11 | note | Pack · execution, freeze, and additivity attestations | Source checks are distinguishable from maintainer execution claims. | I verified attachment/declaration counts, the locations of the Z4 appendices, absence of earlier `sorry` terms in the two attached Robustness files, and the recorded size exception. The packet contains no pre-change blobs/diff or sweep logs, and this environment has no `lean`/`lake`. | Elaboration, fresh `.olean`s, lint, facade reachability, and byte-identical historical prefixes remain maintainer attestations. Attach the two pre-Z4 blobs or their diff if independent byte-level freeze verification is required. |

## Blind restatements and inventory

I extracted the attachments, removed Lean comments with a nested-comment/string-aware pass, and recorded these readings **before** reading declaration docstrings. The subsequent docstring comparison found the discrepancies identified above.

| Definition/structure | Body-derived meaning and comparison |
|---|---|
| `zoneCellBits` | An optional bit becomes its presence bit and its data bit, with false data for absence. Faithful. |
| `zoneCellOf` | False presence decodes to absence; true presence decodes to the supplied bit. Faithful; it need not invert all four bit pairs. |
| `zoneCapacity` | Level `i` has capacity `2*2^i` virtual cells on each side. Faithful to the resolved layout. |
| `zoneBase` | Level `i` begins at virtual slot `2*(2^i-1)`, with natural subtraction. This is the sum of preceding capacities. |
| `zoneIndex` | The owning level is `⌊log₂(⌊s/2⌋+1)⌋`. The floor operations are essential and correct. |
| `ZoneContents` | One optional home bit and two `Fin ℓ`-indexed word families, each bounded above by its level's capacity. No fullness, cross-side balance, lower-zone nonemptiness, implicit blank padding, or simulation invariant is stored. This exclusion is explicit and locally sound. |
| `zoneSlot` | An in-range level lookup followed by a word lookup at the slot's offset from that level's base. Outer `none` means an unoccupied slot; `some none` means an occupied virtual blank. |
| `zoneTape` | Home presence/data are at 0/1. Right slot `s` has presence/data at `2s+2`/`2s+3`; left slot `s` has presence/data at `-2s-2`/`-2s-1`. Occupied slots always occupy both physical cells, including virtual blanks. Faithful, including the reversed offset parity on the left. |
| `ZoneContents.empty` | Blank home and empty words on both sides at every existing level. Its physical tape still has two nonblank false bits at home. |
| `zoneSide` | Concatenate the zone words in increasing level order; no padding or reversal is inserted. Faithful. |
| `zoneShiftInW` | Identity unless `1≤i<ℓ` and the lower word is empty. Otherwise put the upper word's first `2^(i-1)` cells, or all available cells if fewer, in the lower zone and retain its suffix upstairs. |
| `zoneShiftOutW` | Identity unless `1≤i<ℓ` and the lower word is full. Otherwise retain its first `2^(i-1)` cells and prepend its remaining half to the upper word. The raw family operation itself does not enforce target capacity. |
| `zoneShift` | Keep home and the opposite side; apply the chosen raw operation to the selected side (`true` means right). Require selected upper length plus `2^(i-1)` to fit **even for inward or inactive operations**. The fields are inhabitable, but this excess domain restriction causes A-S2-1. |
| `zoneHomeWrite` | Change only home. The frame theorem says that only the two home cells can change, not that either must change. |
| `zoneMoveRight` | Push old home onto `L₀`; pop `R₀` into home and remove its head. On empty `R₀`, `headI` is `none`, the default for `Option Bool`. Require room on the pushed side. This is a genuine virtual move only under the consumer's refill/blank-extension condition. |
| `zoneMoveLeft` | The same operation with sides exchanged and the corresponding room hypothesis. |
| `Code2TM` | A deterministic Boolean machine with exactly two work tapes and state type `Fin (numStates+1)`. Thus `numStates=0` still supplies one state. |
| `Code2TM.toFinTM` | Bundle that same transition system with tape count 2 and the same state type. |
| `Code2TM.serialize` | Pair-frame binary `numStates` with unary initial state followed by transitions ordered by state, input read, work-0 read, work-1 read. Each read uses `[none, some false, some true]`; each record uses the existing `actionBits₂`. |
| `MachineCode2` | Total encoder and decoder, with exact machine recovery after any finite all-true padding of an encoded machine. Padding lengths are distinct, so each machine has infinitely many codes; the zero-padding case also forces encoding injectivity. |
| `EffectiveMachineCode2` | Add a finite deterministic canonizer and an arbitrary length-only running-time bound for producing the fixed serialization of `decode α`. No polynomial canonization bound is present. |
| `UniformMachineCode2` | Add one finite deterministic bounded-acceptance decider, with a single coefficient/degree bounding time jointly in code length, input length, and numeric deadline. Its complementary branches decide exact halting output `[true]` by that deadline versus its negation. It is not a space-universal or linear-time-universal contract. |

| File group | Definitions/structures | Sorried declarations | Literal `sorry` terms | Skeleton-time proofs |
|---|---:|---:|---:|---:|
| `Zone.lean` | 16 | 13 | 16 | 2 |
| `Codes2Tape.lean` | 6 | 2 | 2 | 1 |
| Z4 appendices | 0 | 3 | 3 | 0 |
| **Total** | **22** | **18** | **21** | **3** |

The three sorried definitions are included in both the definitions and sorried-declarations columns. There are 40 distinct new declarations: 22 definitions/structures, 15 sorried theorems, and 3 proved theorems.

## Independent layout and capacity arithmetic

The geometric sum is

\[
\sum_{j<i}\operatorname{zoneCapacity}(j)
=2\sum_{j<i}2^j
=2(2^i-1)
=\operatorname{zoneBase}(i).
\]

Since `2^i≥1`, the natural subtraction loses nothing. Consequently

\[
\operatorname{zoneBase}(i+1)-\operatorname{zoneBase}(i)
=2(2^{i+1}-2^i)=2^{i+1}
=\operatorname{zoneCapacity}(i).
\]

For the index lemma, write `s=2r+ε` with `ε∈{0,1}`. Both base endpoints are even, so

\[
\begin{aligned}
2(2^i-1)\le 2r+\varepsilon<2(2^{i+1}-1)
&\iff 2^i-1\le r<2^{i+1}-1\\
&\iff 2^i\le r+1<2^{i+1}\\
&\iff \lfloor\log_2(r+1)\rfloor=i.
\end{aligned}
\]

Here `r+1≥1`, so there is no logarithm-at-zero case. In particular:

| Slots `s` | 0–1 | 2–5 | 6–13 | 14–29 | 30–61 |
|---|---:|---:|---:|---:|---:|
| `zoneIndex s` | 0 | 1 | 2 | 3 | 4 |

At `zoneBase i` the answer is `i`; for `i>0`, at `zoneBase i-1` the answer is `i-1`. At the upper boundary minus one it is still `i`. These facts handle both parities.

For right slot `s`, substituting `c=2s+2` or `2s+3` yields `n=2s` or `2s+1`, hence presence then data. For the left, `c=-2s-2` yields `n=2s+1` and presence, while `c=-2s-1` yields `n=2s` and data. Thus every integer is exactly a home cell or one member of one side's slot pair; there is no overlap.

The last possible slot is `zoneBase ℓ-1`. Its physical cells give the sharper containing interval

\[
[-2\operatorname{zoneBase}(\ell),\;2\operatorname{zoneBase}(\ell)+1].
\]

The stated symmetric bound is therefore safe, with one extra blank cell allowed on the left. At `ℓ=0`, only home cells 0 and 1 can be nonblank; the strict hypothesis `1<|c|` is sufficient. A blank home is represented by `(some false,some false)`, not physical blanks.

For a valid shift level, the lower capacity is `2*2^(i-1)`. Inward transfer gives lower length at most `2^(i-1)` and never increases upper length. Outward transfer from a full lower word gives exactly

\[
\begin{aligned}
|\text{new lower}|&=2^{i-1},\\
|\text{moved suffix}|&=2\cdot2^{i-1}-2^{i-1}=2^{i-1},\\
|\text{new upper}|&=2^{i-1}+|\text{old upper}|\le\operatorname{zoneCapacity}(i).
\end{aligned}
\]

The last inequality is precisely the necessary **outward** room premise. Disabled guards leave all lengths unchanged. The other side is unchanged. For either head move, the pushed word grows by exactly one, covered by its premise, and the popped word's tail cannot grow. These arguments discharge all six embedded capacity fields, without fullness assumptions.

## A-S2-1: locality failure and repair

The source comparison used the available [AB09 §1.7 excerpt](https://kubokovac.eu/zlozitost/arora.pdf), which states that stable zones are empty/half/full, paired occupancies sum to capacity, and a head move rebalances through the first nonempty donor zone. The following counterexamples and charge calculation are independent derivations from those rules and the attached definitions.

**Finite dead end.** Set `ℓ=2`, with right word lengths `(0,4)` and left lengths `(2,0)`. Fill the right outer word with, for example, four `some true` cells and take blank home. Each side fits, every zone is empty or full, and paired lengths are 2 at level 0 and 4 at level 1. A right head move needs the first cell of `R₁`, but the inward row at `i=1` requires

\[
4+2^0\le4,
\]

which is false. Outward shifting into `R₁` has the same impossible room premise. There is no level 2. Every legal provided shift therefore leaves `R₁` unchanged; home writes and head moves only access home/level zero. Calling `zoneMoveRight` directly would read blank instead of the required `some true`.

This is a domain defect, not an inconsistent capacity proof: `zoneShiftInW 1` itself would safely transform right lengths `(0,4)` into `(1,3)`.

**An extra outer zone does not preserve the claimed amortization.** For arbitrary `m≥1`, take `ℓ=m+2` and stable right lengths

\[
|R_0|=0,\qquad |R_j|=2^{j+1}\ (1\le j\le m),\qquad
|R_{m+1}|=2^{m+1},
\]

with left lengths complementary to the capacities. For each `1≤i≤m`, the full upper word makes the common room premise false. At level `m+1`, the lower word is full and the upper word half-full, so an outward shift is legal. Thus the **only initially enabled nonidentity right-side shift is level `m+1` outward**.

The intended right move has classical index 1, but obtaining any donor data via these rows first requires touching level `m+1`. That transformation changes physical cells at distance `Ω(2^m)` from home. A unit-speed physical head starting and ending at home must spend `Ω(2^m)` steps.

Now perform virtual directions `right, left, left, right`, restoring the classical representation after each move. Right lengths at levels 0 and 1 evolve as

\[
(0,4)\longrightarrow(1,2)\longrightarrow(2,2)
\longrightarrow(1,4)\longrightarrow(0,4),
\]

and all levels above 1 stay unchanged. The classical shift indices are `1,0,1,0`. Nevertheless, every repetition starts with the same blocked full chain and requires another `Ω(2^m)` excursion through the delivered API. This is an occupancy argument and does not depend on choosing distinguishable payload symbols.

The state is reachable from all-half initialization: `2^(m+1)-2` consecutive left moves make level 0 half-full and levels 1 through `m` full on the right; one right move empties level 0. This follows by induction on `m`: the next carry resets all lower levels to half-full, increments the next level, and the remaining lower-level moves repeat the smaller instance. Repeating the four-move cycle `2^m` times after this `O(2^m)` prefix gives

\[
T=\Theta(2^m),\qquad
\text{physical time}=\Omega(2^m\cdot2^m)=\Omega(T^2).
\]

This refutes the promised realization of the **classical stable discipline** with the delivered guarded rows. It is not a lower bound against every alternative zone invariant or a new machine that directly implements the raw inward operation. Either such a replacement would require a different, audited construction; the direct repair is to remove the unnecessary inward room condition.

**The pairwise decomposition itself works after that repair.** Consider a right move of classical index `j≥1`. Before it, `R₀,…,Rⱼ₋₁` are empty and `L₀,…,Lⱼ₋₁` full; the top donor `Rⱼ` is half-full or full. Use this schedule:

1. For `i=j,j-1,…,1`, apply inward-right and outward-left at level `i`.
2. Perform `zoneMoveRight` once.
3. For `i=1,2,…,j`, again apply inward-right and outward-left at level `i`.

On the descending pass, each lower receiving word becomes half-full; the upper word retains the remainder. On the ascending pass, the already-processed lower word is empty on the right and full on the left, so every guard fires again. Each intermediate outward target has the required room. At completion, all levels below `j` are half-full on both sides, and

\[
|R_j|'=|R_j|-2^j,\qquad |L_j|'=|L_j|+2^j.
\]

Exactly two inward and two outward operations occur per level. Order preservation of the raw operations and the single nonempty level-zero pop give the correct virtual word and home. Importantly, intermediate occupancies need not be empty/half/full; this justifies keeping fullness out of the carrier.

Let `c` dominate the four machine constants. Since `i+1≤2^i` for `i≥1`, the shift-row part of one cascade costs at most

\[
4c\sum_{i=1}^j(2^i+i+1)
\le8c\sum_{i=1}^j2^i
=16c(2^j-1).
\]

Finding the level and changing the unary level word between calls adds `O(2^j+j²)=O(2^j)` time. After an event reaching level `i`, all lower levels are half-full, so their total right length is `2^i-1`. Before another event reaching level `i`, that length must reach either 0 or `2*(2^i-1)`. Each intervening virtual move changes it by one; including the next triggering move requires at least `2^i` moves. Thus there are at most `T/2^i` such events from all-half initialization, and each level contributes `O(T)` time. Lazy blank-zone initialization and `O(log(T+1))` reached levels yield the intended `O(T log(T+1))` total.

## The machine rows and the guard semantics

The quantifiers are correctly uniform: for each fixed side, one machine and one coefficient work for **every** level count, level, contents, native input, and allowed starting native-input position. The machine need not discover `ℓ` or scan outer zones. It can ignore native input and emit nothing throughout.

A direct implementation tests the lower guard, stages the affected words on tape 1, and rewrites the two adjacent windows. Word ends are distinguishable because a stored virtual blank occupies two nonblank false cells. Staging may copy the whole two-zone window; its size is still `O(2^i)`. A false guard returns the original tape and scratch word unchanged. A true guard uses `take`/`drop` for inward motion or splits/prepends for outward motion. There are only constantly many scan/copy/erase/rewind phases, and no other contents need be changed.

Unary level input is a sound uniform design. Navigation counters and boundaries must be implemented with a geometric total ledger, rather than performing an `i`-cell counter scan for every cell moved. For example, counting down a binary power of two with its least significant bit anchored has total carry/borrow work

\[
\sum_{r=1}^{2^i}(1+v_2(r))<2^{i+1},
\]

up to a constant return-to-anchor factor; initializing the counter from unary `i` costs at most a polynomial in `i`, absorbed by `O(2^i)`. Bounded staging can use reserved invalid pair codes as temporary delimiters, saving overwritten boundary pairs in finite control and restoring them. This supplies a linear-scan construction route with a fixed controller; merely claiming that a naive single-tape unary-doubling subroutine is linear would not suffice. These are mathematical implementation arguments, not supplied Lean transition tables.

The entire affected data window is contained in

\[
[-2\operatorname{zoneBase}(i+1),\;2\operatorname{zoneBase}(i+1)+1],
\]

which lies inside the row's `±(2*zoneBase(i+1)+2)` interval. Temporary data-tape marks can be placed within the affected windows. Scratch staging is on **tape 1**, whose separate bound is `c*(2^i+i+1)`; the data-tape interval does not claim to bound tape 1. Every finite pass has a bounded stopping condition, cleanup restores the unary level and both heads, and choosing the first halt time supplies the no-earlier-halt clause. Initial state is live, so this halt time is positive.

For `i=0` or `i≥ℓ`, the raw operations are identity; the rows deliberately exclude these levels. For `1≤i<ℓ` but a false lower guard, the rows do **not** exclude the input: their exact final equality requires identity. The dependent proof argument to `zoneShift` does not let a caller smuggle through a false room inequality or alter computational behavior by choosing another proof.

## A-S2-2 and the three Z4 bounds

Take a fixed Boolean machine with one work tape, whose work head never moves, whose work tape stays blank, and which advances along its native input until the right boundary, then halts without output. It computes the constantly empty output with

\[
T(n)=n+1,\qquad S(n)=1,
\]

and its source space is 1 at **every** horizon, including after halt.

The attached `sweep_run_to_halt` places the received witness's work head, after `t` simulated steps, at

\[
-t\,M.k-1=-t-1.
\]

At the source's halt time `t=n+1`, this is `-(n+2)`. Its physical head began at 0 and moves at unit speed, so at least `n+3` distinct cells were visited. The promised space estimate for this particular witness would imply

\[
n+3\le c(S(n)+1)=2c\qquad\text{for every }n,
\]

a contradiction. This uses mapped valid inputs, so it does not rely on an invalid-alphabet corner case. The controller body explains the failure: `.growLeft` and `.growRight` add a blank interleaved block every macro-step, regardless of source head motion.

**The existential one-tape statement remains mathematically true.** Use a sweep machine that extends a boundary only when a simulated head first crosses it. If `I_h` is the interval visited by source tape `h`, each contains 0, and therefore

\[
\left|\bigcup_{h<M.k}I_h\right|
\le\sum_{h<M.k}|I_h|
=\operatorname{spaceUsed}_{M}.
\]

A product-track realization pays a constant number of extra boundary cells. A realization interleaving `M.k` tagged cells per coordinate pays an additional factor `M.k`; the attached received construction is of this latter kind. Either factor is fixed by `M` and can be absorbed into `c`. Mid-sweep visits, including a boundary extension for the next simulated transition, lie in the representation of source-visited intervals through that transition plus a constant boundary allowance. Each source step still uses `O(t+1)` physical steps, giving `O((T(n)+1)²)` total time.

There is an additional quantifier obligation: the space conclusion ranges over **all** words over the enlarged alphabet `Γ'`, whereas correctness ranges only over `x.map e`. When `Γ` is nonempty, choose a finite-control retraction from `Γ'` to `Γ` that fixes `e`; simulate the corresponding source input without materializing a copy. Its length is unchanged, so `hS` applies without monotonicity. When `Γ` is empty, every source input and output is empty; an immediately halting one-work-tape machine supplies the required statement. For `M.k=0`, the unused-tape embedding uses exactly one visited cell, covered by `c*(S+1)`.

**Alphabet reduction.** Let the fixed block width be `W=Fintype.card Γ+1`. The received `arTM`'s read pass can momentarily reach the first cell immediately beyond the current block; that boundary must be counted. For each source visited interval `I_h`, all corresponding physical visits lie between `W*min I_h` and `W*(max I_h+1)`, so

\[
\operatorname{spaceUsed}_{arTM}
\le W\sum_h|I_h|+M.k
\le (W+1)S(n).
\]

The final inequality uses the time-zero fact `M.k≤S(n)`. If there are zero tapes, both sides' work space is zero. The existing fixed-length macro-cycle supplies the linear time factor; enlarging one coefficient handles both time and space. The hypotheses apply on `x.map e`, which has the same length as `x`.

**Composition.** If the corrected first stage uses coefficient `c₁`, the second stage's space bound is

\[
c_2\bigl(c_1(S(n)+1)+1\bigr)
\le c_2(c_1+1)(S(n)+1).
\]

Writing `Q=(T(n)+1)²≥1`, its time is likewise at most

\[
c_2(c_1Q+1)\le c_2(c_1+1)Q.
\]

Thus one coefficient works for the binary composite. No argument compares `S(n)` with `S(n+1)` or with any other input length. No monotonicity premise is missing.

## Z3 record and scheme fidelity

The exact record order is:

| Component | Width |
|---|---:|
| Native-input move (`signBits`) | 2 |
| Work-0 optional write (`optOptBoolBits`) | 2 |
| Work-0 move | 2 |
| Work-1 optional write | 2 |
| Work-1 move | 2 |
| Output (`optBoolBits`) | 2 |
| Successor (`optStateBits`) | 1 for halt; `s.val+2` for successor `s` |

Hence each record has length 13 for halt, or `14+s.val` for a successor. The enumeration contains

\[
(numStates+1)\cdot3\cdot3\cdot3=27(numStates+1)
\]

records. The ND mirror has twice that many, with the choice bit outermost; it does not interleave choices per state. The deterministic body is exactly its single-table counterpart.

The exact serializer-length identity is

\[
\begin{aligned}
|M.serialize|={}&2|Nat.bits(M.numStates)|+M.tm.q_0.val+3\\
&+351(M.numStates+1)\\
&+\sum_{\text{records with successor }s}(s.val+1).
\end{aligned}
\]

In particular, `351*(numStates+1)` is a safe necessary table-length guard, versus `702*(numStates+1)` for ND. The header and initial-state word do not halve. At `numStates=0`, the minimum complete deterministic serialization is `2+1+27*13=354` bits, versus `2+1+54*13=705` for ND. There is still one initial state and 27 records.

All three scheme structures match their references. The algebraic scheme supplies total decoding and arbitrarily padded recovery. The effective extension targets the fixed serialization and imposes only an arbitrary length-dependent time bound. The uniform extension uses the deterministic `toFinTM`, the same nested pairing, the same **joint** polynomial, and genuinely complementary acceptance/rejection premises; it neither omits rejection nor replaces numeric `t` by `log t` in the budget.

For existence, parse and range-check the concrete grammar, accept only all-true suffix padding, and fall back to a fixed one-state halting machine on failure. A table has a fixed number of self-delimiting successor records; appended true bits cannot change already-parsed records. Finite tables over finite domains reconstruct the exact machine, including initial state. A terminating canonizer reserializes the result; a maximum over the finitely many strings of each length supplies its arbitrary time bound.

For the uniform version, check the table's lower-length guard in binary **before** expanding the stated number of states. On success the table/state administration is polynomial in code length; on failure use the fixed fallback. Simulate at most `t` transitions under a binary countdown and track output as empty / exactly `[true]` / permanently other, since output is append-only. Inspect the result after the `t`-th transition before declaring timeout. At `t=0`, the initial configuration is live and its output empty, so the answer is false. Fixed scan and lookup costs yield a polynomial jointly in `|α|+|x|+t+1`; increasing the degree/coefficient gives precisely the record's single-parameter bound.

`NDCodes.lean` contributes exactly `actionBits₂` and `workPair` to these definition bodies. No new body invokes `exists_effectiveNDMachineCode` or assumes ND acceptance. Its transitive import does make that module visible; this is not evidence that the new theorem proofs depend on its sorried existence statement. A fill-time axiom/dependency check remains appropriate.

## Every sorried declaration: literal truth assessment

These are mathematical arguments for the exact statements, not claims of Lean kernel certification.

| # | Declaration | Argument |
|---|---|---|
| 1 | `zoneIndex_eq_iff` | The even/odd division sandwich above is equivalent to the positive-argument logarithm sandwich. It includes `s=0`, every even boundary, and the last odd slot of each zone. |
| 2 | `zoneTape_empty` | Every word lookup into `[]` fails, irrespective of the level guard. Both side branches are therefore physical blank, while the home branches compute false presence and false default data. |
| 3 | `zoneTape_blank_outside` | Every owned slot is below `zoneBase ℓ`; its two cells lie in the sharper signed interval calculated above. A cell satisfying the stated strict inequality is neither home nor any owned slot, so the level guard returns blank. |
| 4 | `zoneSide_shiftInW` | A disabled guard gives identity. When enabled, the adjacent segment `[] ++ wᵢ` is replaced by `take q wᵢ ++ drop q wᵢ = wᵢ`, where the cutoff is the defined `2^(i-1)`; no capacity or fullness hypothesis is used. |
| 5 | `zoneSide_shiftOutW` | A disabled guard again gives identity. When enabled, the adjacent segment is reassociated as `take q wᵢ₋₁ ++ (drop q wᵢ₋₁ ++ wᵢ) = wᵢ₋₁ ++ wᵢ`; the rest of `finRange` is untouched. |
| 6 | `zoneShift` — both capacity fields | The inward lower prefix fits and its upper suffix cannot grow. The outward lower word is exactly twice the cutoff, so its moved suffix has cutoff length and the given room premise bounds the enlarged upper word; inactive/opposite words retain their existing bounds. The definition is inhabitable, although its inward domain is unnecessarily restricted. |
| 7 | `zoneTape_homeWrite` | For `c≠0,1`, neither home branch is used. The selected side families are unchanged, hence the physical value is unchanged. |
| 8 | `zoneMoveRight` — both capacity fields | The left level-zero length increases by one, exactly covered by `hroom`; the right level-zero tail has no greater length. All other levels retain their original bounds, including when the popped list is empty. |
| 9 | `zoneMoveLeft` — both capacity fields | Exchange left and right in the preceding proof. The premise covers the right push, and the left tail never increases length. |
| 10 | `zoneSide_moveRight` | `finRange ℓ` begins with zero because `hℓ` supplies `ℓ>0`. The left concatenation gains old home at its front; nonempty `R₀` ensures that taking the concatenation's tail removes exactly the head of `R₀`, giving the stated right equality. |
| 11 | `exists_zoneShiftInTM` | On the restricted domain, the uniform local implementation described above tests emptiness, stages/copies the required prefix and suffix, and cleans up within a constant number of geometric scans. It preserves arbitrary outer contents, input position, and empty output, and returns scratch/head positions exactly; its first halt and visited bounds follow from that bounded schedule. A-S2-1 is a failure of consumer coverage, not a false equality on this domain. |
| 12 | `exists_zoneShiftOutTM` | Test lower fullness, returning identity if false; otherwise stage the outer half, move the upper word outward, and prepend the staged cells. `hroom` ensures every final occupied slot remains inside the upper zone, and the same finite-pass cleanup and geometric interval/time ledger apply. |
| 13 | `MultiTapeTM.spaceUsedByTape_le_card_Icc` | Every member of the finite visited-head image has a time index `u≤t`; the premise places it inside the integer interval. Set inclusion and interval cardinality give `(hi+1-lo).toNat`; if `lo>hi`, the premise is impossible already at `u=0`. |
| 14 | `exists_effectiveMachineCode2` | The concrete parser/fallback/padding construction above defines a total scheme with exact round-trip. Its canonizer is an ordinary computable finite-string function, and maxima over finite length classes give the unrestricted time function required by the statement. |
| 15 | `exists_uniformMachineCode2` | Use the same concrete grammar with the binary minimum-length check and bounded simulator, not an arbitrary effective scheme's canonizer-time guarantee. The joint polynomial ledger and complementary output-status decision above supply both branches, including malformed codes and `t=0`. |
| 16 | `alphabet_reduction_spaceUsed` | The existing fixed-width witness has a constant-time macro-cycle and at most `W` physical cells per source visited cell plus one boundary position per tape. Applying `hS` to the same-length mapped input bounds every partial cycle and every post-halt horizon, with one enlarged coefficient. |
| 17 | `one_work_tape_spaceUsed` | The demand-grown construction above proves the existential shape with quadratic time and linear-in-source-space usage; a retraction handles all enlarged-alphabet inputs, with separate empty-alphabet and zero-tape cases. The supplied claim that the **received** `sweepTM` already has this property is false, and its replacement is a substantive fill obligation. |
| 18 | `one_work_tape_binary_spaceUsed` | Apply the corrected existential one-tape theorem, then alphabet reduction with the first stage's all-input/all-time bound. The explicit coefficient calculation above absorbs both additive ones into one common coefficient; tape count remains one. |

The three skeleton-time statements also have the intended semantics: the three optional-bit cases give `zoneCellOf_bits`; the telescope gives `zoneBase_succ`; and padding by zero gives `MachineCode2.decode_encode`. Their tactic scripts were not re-audited.

## Adversarial checks and missing sanity exports

| Instantiation | Result |
|---|---|
| `ℓ=0`, arbitrary home | Empty side functions; exactly the home pair can be nonblank. The extent theorem is correct. |
| `s=0,1,2,5,6,13,14` | Zone indices `0,0,1,1,2,2,3`, respectively; both parities and successive boundaries work. |
| Occupied virtual blank versus absent slot | Respectively `(some false,some false)` versus `(none,none)`; representation preserves the distinction. |
| `i=0` and `i≥ℓ` | Raw shifts are identity; `hroom` is vacuous only when `i≥ℓ`, not merely because the operation is inactive. |
| `i=1`, empty donor, empty lower zone | Inward operation is identity on both words, with provable capacity fields. |
| `i=1`, upper word of length 1 | Inward transfer moves all of it and leaves the upper zone empty. No half-full assumption is needed. |
| `i=1`, full upper word of length 4 | Safe raw inward transformation, but wrapper and machine row unavailable: A-S2-1. |
| Full lower zone, upper length exactly capacity minus cutoff | Outward result exactly fills the upper zone. One additional upper cell invalidates `hroom`, as it should. |
| Nonempty inward lower word / nonfull outward lower word | Pure operation is identity, and the literal machine row still requires that identity behavior. |
| Empty `R₀`, nonempty `R₁` | `zoneMoveRight` returns blank home, not the outer word's head. This is intentional only before imposing the consumer's refill condition; `zoneSide_moveRight` correctly excludes it. |
| Nonempty `R₀` containing a single virtual blank | `hne` holds, new home is blank, and right concatenation loses exactly that stored blank. |
| `numStates=0` | One state, 27 records, minimum serialization 354 bits. |
| Arbitrarily huge binary state count in a short code | Binary guard must reject before any state enumeration; the uniform construction supports this. |
| `t=0` for bounded acceptance | Live initial state means acceptance is false, including when the first transition would emit true and halt. |
| Work-space horizon 0; zero work tapes | Initial visited space is the tape count, or zero with no tapes; the `+1` accommodates the one unused tape in the one-tape conversion. |
| Stationary-work-head input scanner | Refutes the received Z4 witness, not the existential theorem: A-S2-2. |
| Nonmonotone `S`; arbitrary target-alphabet word | Same-length retraction and all-horizon source bounds suffice; no comparison between different lengths is needed. |

An independent executable finite model corroborated **310,169 checks**: 245,760 logarithm-sandwich checks; 9,459 physical-layout checks; 29,032 raw-shift concatenation checks; 24,262 guarded capacity checks; 1,632 head-tail checks; and 24 repaired cascades through level 12. Nine additional full-chain tests checked reachability, the four-move cycle, and the unique initial enabled right-side shift. Whitespace-normalized source comparisons also confirmed the deterministic/ND serialization correspondence and exact uniform-record correspondence. These checks are corroboration; the general arguments and counterexamples above carry the audit conclusions.

Recommended machine-checkable additions, in priority order:

1. **Required for the blocker repair:** inward realization from a full donor with no room premise; the descending/head/ascending cascade, its final lengths and represented tape, and the level-event separation/charge bound.
2. Fixed-`ℓ` injectivity of `zoneTape` on `ZoneContents ℓ`, recovering home and each word from occupied pairs. Do not claim injectivity over an unknown level count: empty outer zones are invisible.
3. `zoneSide` length equals the sum of zone-word lengths and is at most `zoneBase ℓ`; direct slot readout at `zoneBase i + offset`.
4. A named small-`s` index computation table, the sharper signed extent, and the guard-false identity specializations.
5. Home readout for both head moves, the mirrored `zoneSide_moveLeft`, and an explicit all-empty-side blank-extension lemma.
6. `actionBits₂` exact/minimum lengths, the serializer-length identity, the 351-per-state parser guard, and `numStates=0` regression.
7. For the replacement Z4 witness, a trajectory-containment theorem valid inside a sweep and on all target-alphabet inputs. Keep the stationary-head scanner as a regression showing why unconditional radius growth is forbidden.

**Evidence boundary.** The audit used the supplied source packet and public source excerpts, not repository development history or GitHub mutations. Direct web opens of the full textbook PDF were unavailable; the retrieved §1.7 text supplied the stated invariant and shift rule, while the arithmetic, counterexamples, and charge proof above were derived independently. No Lean kernel check was performed. The supplied two Robustness prefixes contain no `sorry` terms, and all three new Z4 statements lie in the declared appended sections; historical byte identity cannot be proved from a single version. The 1,029-line `SingleTape.lean` exception is explicitly recorded in the attached plan.

**Notation introduced in this report.** `r, ε`: quotient and remainder in `s=2r+ε`; `m`: highest level in the full-donor chain; `j`: classical cascade level; `c₁,c₂`: the two conversion coefficients; `I_h`: source tape `h`'s visited interval; `W`: fixed alphabet-code block width; `Q=(T(n)+1)²`; `q`: the already-defined transfer cutoff `2^(i-1)` in the list identities; `v₂(r)`: the exponent of 2 dividing the positive integer `r`. Other identifiers are from the audited source or pack.
