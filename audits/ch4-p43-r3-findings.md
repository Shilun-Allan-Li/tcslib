# P4.3 round-3 statement-gate audit

**Verdict: PASS — 0 blockers, 0 majors, 0 minors, 2 notes.**

The amended serialization bound removes R2-1. One shared constant suffices for the code width and all three formula-size bounds, uniformly over every input length and window radius. Independent width/size constants are unnecessary. The factorization iff and all five wording repairs resolve the remaining round-2 comments. The downstream hardness construction remains polynomial after counting every validity copy, variable renumbering, and unary index.

Input SHA-256 independently verified:

`6a04a9ccd659ef32b053e6158c294e91377f492aacb1dd8fd19e1ab3432f5ea0`

The bundle contains 33 attachments. Its asserted revision is `9a92fa1aeb377d568972e42229979cf81562ba41`, branch `complexity/arora-barak-ch3-4`. This audit covers the supplied two-file repair diff and its immediate semantic and size consequences. Unchanged declarations and previously accepted dispositions are context, not a renewed whole-phase audit. No repository sources were modified and no sub-agents were used. This is a mathematical statement/sketch audit, not a fresh Lean elaboration or a kernel certificate.

Paths below are relative to `TCSlib/Complexity/`; line numbers refer to the extracted round-3 files.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-1 | note | `ClassPSPACE/TQBF.lean:139–205,239–284` · codec and hardness sketches | The repaired statements have a viable construction and size ledger. | The construction and common-constant calculation below cover validity, adjacency, acceptance, padding, and unary indices, including the smallest instance. The existential package still does not supply an executable uniform emitter. | No further statement repair. Fill the existing codec, factorization, semantic-equivalence, uniform-emitter, and hardness obligations. |
| R3-2 | note | Repair diff and repository-side attestations | The packet supports the declared source changes and reports a clean elaboration. | All ten diff hunks reconstruct exactly; all four Git blob prefixes match; comment-stripped comparison finds precisely the advertised formal changes. The supplied sweep has 12 admission warnings and no `error:` lines. Actual commit membership, process exit statuses, and fresh `.olean` files are not independently established. | Retain build/commit claims as maintainer attestations. No gate repair required. |

The disposition of every round-2 item is:

| Round-2 item | Round-3 disposition |
|---|---|
| R2-1 — blocker | **Resolved.** All three description bounds use `C * (s + n + 2)^C`. The old contradiction fails, and the full construction fits one common constant by the calculation below. |
| R2-2 — minor | **Resolved.** At lines 180–182, same-input, windowed code equality is equivalent to `coreSum` equality. Canonical tracks give both directions. The pack correctly acknowledges its earlier overstatement. |
| R2-3 — minor | **Resolved.** Lines 47–50 and 247–250 allow live self-loops and retain the equality-or-adjacency base case. |
| R2-4 — minor | **Resolved.** Lines 155–169 account for pairwise one-hot exclusions and jointly guarded head-position/scanned-symbol cases. The polynomial construction below makes the constant-size-per-case reading precise. |
| R2-5 — minor | **Resolved.** `Hierarchy.lean:213–221` restricts the padded language to `x ∈ L`; the padding map is now a reduction for arbitrary `L`, including the empty language. |
| R2-6 — note | **Resolved in the sketch.** Lines 262–265 explicitly count validity copies and unary-index shifts. The quantitative ledger below includes both. |
| R2-7 — note | **Resolved as a specification of the intended construction.** `Hierarchy.lean:93–109,161–164` explicitly requires discarding output to finite information and forbids buffering. The unattached W1 implementation remains outside this audit. |
| R2-8 — note | **Unchanged posture; source evidence verified.** See R3-2 and the source checks below. |

**Literal restatement of the amended contract.** There are no new definitions. The unchanged `Cfg.InWindow s` says that every work head lies in `[-s,s]` and every work cell outside that interval is blank. It does not restrict output, assert reachability, or measure previously visited cells.

For each fixed finite machine, the amended theorem chooses one positive natural number `C` before choosing `n,s`. It then supplies a total code function and three CNFs. Write

\[
\ell=C(s+n+1).
\]

Every configuration, even outside the guarded domain, receives a word of length `ℓ`. On length-`n` inputs and windowed configurations, equal codes imply equal inputs; at the same input, equal codes are now **equivalent** to equal `coreSum`. On every length-`ℓ` word, validity holds exactly for the image of those guarded configurations. On guarded code pairs, adjacency is precisely equality between the source successor's `coreSum` and the target's; different inputs are rejected. Acceptance means halted state and summary `accept`. The variable bounds remain `ℓ,2ℓ,ℓ` for validity, adjacency, and acceptance, respectively. Each serialized length is at most `C(s+n+2)^C`.

The formulas are selected before the individual input. No algorithm for selecting these witnesses is asserted. Behavior of adjacency and acceptance on invalid words remains unrestricted, which the guarded hardness consumer permits.

**Replay of the round-2 Section-3 contradiction.** Use exactly the earlier configurations: empty input; halted state; input head at zero; blank work tapes and origin work heads; outputs `[]` and `[true]`, respectively. Both are in the radius-zero window. Their summaries differ, and the halted source steps to itself, so adjacency must distinguish the source-to-itself and source-to-other pairs.

The formerly decisive inference is now only

\[
\varphi_a.\mathrm{numVars}
\le |\mathrm{serialize}(\varphi_a)|
\le C2^C,
\qquad |\mathrm{code}\ []\ c|=C.
\]

It no longer implies `φa.numVars ≤ C`. The independent bound `φa.numVars ≤ 2C` permits inspecting the entire target block. Consequently the premise of the old evaluation-congruence argument is unavailable.

The exact supplied serialization grammar gives

\[
|\mathrm{serialize}(\varphi)|
=1+2\varphi.\mathrm{length}
 +\sum_{\text{clause}\in\varphi}\sum_{(v,b)\in\text{clause}}(v+3).
\]

For the cited singleton,

\[
|\mathrm{serialize}([[(C,\mathrm{true})]])|
=1+2+(C+3)=C+6
\le4C\le C2^C\quad(C\ge2).
\]

That singleton reads the target block alone. A genuine two-block check is equality of variables `0` and `C`, represented by

\[
[[(0,\mathrm{false}),(C,\mathrm{true})],
 [(0,\mathrm{true}),(C,\mathrm{false})]].
\]

Its serialized length is

\[
1+4+2\bigl(3+(C+3)\bigr)=2C+17
\le8C\le C2^C\quad(C\ge3).
\]

These checks locate the failure of the old contradiction. They do not by themselves establish the full codec bound; that requires the following construction and absorption argument.

**Full codec construction and uniform size calculation.** Fix the machine and its tape count `k`. For this calculation put `u=s+n+2`, so `u≥2` and `ℓ=C(u−1)`.

1. Encode the `n` input bits; the one-hot input head in `n+2` positions; the one-hot state including halt; each work cell in `[-s,s]` using two trit bits and one head bit; and the two-bit output summary. Before padding, the width is

   \[
   n+(n+2)+(|\mathrm{State}|+1)+3k(2s+1)+2
   =2n+|\mathrm{State}|+5+3k(2s+1).
   \]

   A machine-dependent coefficient bounds this by that coefficient times `s+n+1`. Append zeros to reach exactly `ℓ`. Wrong-length inputs may receive a fixed word of length `ℓ`; outside-window configurations at the correct input length may still be encoded by reading just the finite tracks. No test of the infinite outside-window blankness condition is needed to define this total function.

2. Validity enforces exactly one marker per head/state block, the allowed trit and summary patterns, and zero padding. An exactly-one block contributes one positive clause and one two-literal exclusion for each unordered pair. Each satisfying word reconstructs a windowed configuration: extend the work tracks by blanks and choose `[]`, `[true]`, or `[false]` for the represented summary. Thus validity characterizes the image in both directions, without introducing auxiliary variables.

3. For adjacency, include validity of both blocks, input-content equality, and per-cell copying when the source head marker is absent. Enumerate input-head positions and the work-head tuple, then the finitely many state, scanned-symbol, and summary cases. There are

   \[
   (n+2)(2s+1)^k\le 2^k u^{k+1}
   \]

   position tuples. Each case guard has machine-dependent constant width. It fixes the new finite state, marked-cell symbols, summary, and the selected target head markers according to the actual transition. Target one-hot validity forces all other head markers to be zero; the separate copy clauses handle unmarked tape cells. This is why a guarded update case needs only constantly many clauses even though a whole row has growing length. A work-head move outside the window makes its guard imply false. Halted cases enforce the identity update. These clauses give both directions of the adjacency equivalence and reject distinct input contents. No unchecked gate variables are added to the codec.

4. Acceptance is the conjunction of the halt bit and the fixed summary pattern. Equal same-input `coreSum` values yield exactly the same finite tracks and zero padding. Conversely, equality of the tracks recovers all core fields, since both work tapes are blank outside the window, and recovers the summary. This proves the new factorization iff. Input-content equality supplies the separate input-separation clause.

For every sufficiently large width coefficient `C`, the clause and literal-occurrence counts just described satisfy:

| Family | Clause count and literal-occurrence count |
|---|---|
| Validity | `O_M(Cu + u²)` |
| Adjacency, including both validity copies | `O_M(Cu + u² + u^(k+1))` |
| Acceptance | `O_M(1)` |

The constants in this table depend on the fixed machine, **not** on `C,n,s`. Padding accounts for the `Cu` term. One-hot exclusions account for the quadratic term. The target-block offset is accounted for by the variable-index bound: every literal index is less than `2ℓ`, hence

\[
v+3\le2\ell+2=2C(u-1)+2\le2Cu.
\]

Applying the exact serialization equation therefore gives machine-dependent integers `B≥1` and

\[
d=\max\{3,k+2\}
\]

such that, for every `C≥B` and every `n,s`, the raw tracks fit the width and all three serialized lengths are at most

\[
BC^2u^d.
\tag{1}
\]

Here `B` is enlarged once to cover both the raw-width coefficient and the finite constants in the displayed count bounds. Its independence of `C` is essential: enlarging `C` adds padding and increases indices, giving the explicit quadratic dependence already present in (1).

Choose the theorem's single witness constant to be

\[
C=\max\{4,d,B2^d\}.
\tag{2}
\]

For natural `C≥4`, `2^C≥C²`: equality holds at four, and the induction step follows from

\[
2C^2-(C+1)^2=C^2-2C-1\ge0.
\]

Consequently (2) implies

\[
2^{C-d}\ge\frac{C^2}{2^d}\ge BC,
\]

and, since `u≥2` and `C≥d`,

\[
BC^2u^d
\le C\,2^{C-d}u^d
\le C\,u^{C-d}u^d
=C(s+n+2)^C.
\tag{3}
\]

This chooses `C` before `n,s` and proves the required absorption at **every** pair, including `n=s=0`. All three families use the same `B,d,C`. Independent width and size constants are not needed.

**Hardness size ledger.** The guarded recursion and its path interpretation are unchanged. Its base recognizes valid paths of length zero or one. For a fixed valid midpoint, specializing the universal endpoint pair to the two requested subpaths proves the forward direction of the recursive equivalence; the reverse follows because every pair satisfying the guard is one of those two pairs. Splitting and concatenating paths proves the bound `2^i` by induction. At depth `ℓ`, the at-most-`2^ℓ` valid codes suffice. Input separation, cross-input rejection, and compatibility of `coreSum` with stepping keep these paths in the correct input component and lift them to actual computation vertices.

There are exactly `ℓ` recursive midpoint-validity occurrences, two base endpoint-validity occurrences, one adjacency occurrence, and one acceptance occurrence. Equality and implication scaffolding contributes `O(ℓ²)` ordinary Boolean syntax. The original quantified blocks use `3ℓ²+ℓ` Boolean variables: three blocks per level and the accepting target.

Let `N` bound the number of ordinary Boolean gates plus original variables before Tseitin conversion. The original serialized bounds also bound clause and literal counts, so

\[
N=O_M\!\left(\ell^2+(\ell+4)C u^C\right)
=O_M(u^{C+1}).
\]

Use fresh, consecutively numbered blocks when prenexing. Then place all existential gate variables after the original prefix. For each complete assignment of the original variables, the gate equivalences and root constraint have a satisfying extension exactly when the original matrix is true; thus this placement preserves quantified truth.

The resulting CNF has `O(N)` variables, clauses, and literal occurrences. Every shifted or newly introduced index is `O(N)`. Its **unary** serialized length is therefore `O(N²)`, not merely `O(N)`. The supplied QBF pair encoding gives

\[
|\mathrm{QBF.encode}|=2|\mathrm{prefix}|+2+|\mathrm{CNF.serialize}|,
\]

and hence

\[
|\mathrm{QBF.encode}|=O_M(N^2)=O_M(u^{2C+2}).
\]

With the sketch's `s=c₀(n^c+1)`, this is polynomial in `n+1`. All guards and literal records can be enumerated by polynomially bounded loops for the fixed machine; the larger base introduces no superpolynomial work. The Lean realization of this uniform emitter remains an explicit fill obligation, not a consequence of choosing arbitrary witnesses from the existential theorem.

**Other wording repairs and adversarial cases.** The padded language now satisfies

\[
\mathrm{pairEncode}(x,\mathrm{true}^{|x|^2})\in L'
\iff x\in L,
\]

because the pair encoding is injective. Its length calculation is unchanged:

\[
2n+2+n^2=n^2+2n+2.
\]

In particular, the empty language stays empty under padding. Discarding probe output preserves the intended space ledger; retaining the emitted word would not. A finite observer may use transient finite states while scanning, then return the advertised attempt summary. The wording does not require a buffer or a restriction on output length.

| Adversarial instance | Result under the amended surface |
|---|---|
| `n=s=0`, halted blank configurations with outputs `[]` and `[true]` | Distinct summaries require distinct codes; the adjacency formula can now inspect their target-block difference. Equations (1)–(3) cover the entire formula family. |
| Zero work tapes | Window conditions are vacuous and `(2s+1)^0=1`; the construction and constant choice still apply. |
| `s=0`, a nonblank origin cell | Valid. Radius zero permits an origin symbol; it does not assert zero visited space. The trit track represents it. |
| A transition moving a work head outside `[-s,s]` | No windowed target matches the successor core; the corresponding guard rejects. |
| Same core with outputs `[false]` and `[true,false]` | Both summaries are dead, so the new iff forces the same code. Canonical tracks satisfy this; the round-2 parity-alias construction no longer does. |
| Distinct one-bit inputs with otherwise matching data | Input-content tracks differ and the adjacency equality clauses reject the cross-input pair. |
| A live stationary silent loop | It is self-adjacent, as the new wording allows. Other live vertices may lack self-loops, so the explicit equality base case is still necessary. |
| A word with two head markers or nonzero canonical padding | Validity rejects it. The guarded recursion cannot use it as a path endpoint or midpoint. |
| Arbitrarily long dead outputs | They change neither the canonical code nor the observer's asymptotic space; only the finite summary is retained. |
| Padding the empty language, including the empty input | The padded language is empty; the empty input's padding image has length two and is not accidentally accepted. |

**Source and evidence checks.** I checked the 2009 Arora–Barak text at Claim 4.4(2), pp. 80–81; Theorem 4.13's reduction, pp. 84–85; §4.1.3, pp. 82–83; and Exercise 3.2, p. 77 ([book PDF](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf)). The input-carrying quotient codec, polynomial serialized bound, and explicit validity guards remain declared implementation adaptations. The repair does not claim the book's linear adjacency-formula bound. The common-constant calculation and the enlarged serialization ledger above are independent checks of this packet's concrete representation.

All ten diff hunks reverse exactly against the supplied current files. Reconstructed old and supplied new Git blob hashes match:

| File | Old blob | New blob |
|---|---|---|
| `ClassPSPACE/TQBF.lean` | `61c2d946f434161e4f1109a005459f334cda3446` | `f576d8f1213fdd836f79d79ee8fda800b735182f` |
| `SpaceComplexity/Hierarchy.lean` | `0d778a034c5ea76dda0ed0a83698881c6aac0c1c` | `1b963f8b413134d9443dc0a85bdc48fa3ac4f4ce` |

Comment-stripped comparison confirms that the only formal changes in those files are the quotient iff and the three size-bound bases. The seven-module inventory remains 15 definitions and 12 `sorry`s. The supplied sweep lists all seven modules, including both facades, has the expected 12 admission warnings and no `error:` lines, and ends with its completion marker. The three relevant lint summaries report 0 FAIL / 0 WARN over 5, 2, and 42 files. These checks establish packet consistency, with the attestation limits in R3-2.

An independent Python transcription checked the exact singleton and two-block equality serialization lengths for `C=1,…,256`, the stated threshold inequalities, and the explicit constant choice on 192 parameter pairs with 1,344 size comparisons. These finite checks support the arithmetic transcription; the universal argument is (1)–(3), not the enumeration.

**Gate decision:** the round-3 repairs close the remaining statement-gate blocker. No further statement or wording repair is required by this audit. The 12 admitted proofs and the already named implementation obligations remain to be filled.

**Notation glossary.** `M` is the fixed machine; `k` its work-tape count; `n,s` the input length and window radius; `C` the shared positive witness constant; `ℓ=C(s+n+1)` the code width. `u=s+n+2`; `B` is a machine-dependent integer covering raw width and serialization coefficients; `d=max{3,k+2}` is the intermediate serialization exponent. `N` bounds the Boolean gates and original variables in the hardness construction. `O_M` allows constants depending on the fixed machine. `φv,φa,φacc` are validity, adjacency, and acceptance CNFs; `v` in the serialization equations is a zero-based literal index. `c,d` when used for configurations are the earlier halted examples; the exponent `d` is used only in the size calculation. `c₀,c` in the hardness space bound are the packet's fixed multiplier and degree. `L'` is the corrected padded language. Other function names and notation are inherited from the audited packet.
