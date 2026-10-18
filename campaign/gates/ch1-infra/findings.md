**Chapter-1 infrastructure audit — findings**

**Gate: OPEN — 1 blocker, 2 majors, 4 minors.** One additional note records evidence limitations. The bounded-loop existence theorem is false as stated. The concrete universal-machine export and the Chapter-2 bridge derivation pass this source audit, conditional on the previously audited dependencies specified in the pack.

Audited input: `ch1-infra-bundle.md`, SHA-256 `2b73e447a4abec80a27ad8d50ceea169a39ed34121a2d47c8f8a014c65a3975f`. References below use the original repository paths and their file-local line numbers, not bundle line numbers. `Build/…` abbreviates `TCSlib/Complexity/TuringMachine/Build/…`; other bare machine-module filenames have prefix `TCSlib/Complexity/TuringMachine/`, and `TMSAT.lean` has prefix `TCSlib/Complexity/ClassNP/`. The supplied toolchain claim is Lean 4.25.0 / mathlib `029db123ddaa`; no Lean executable, complete dependency tree, historical source snapshots, or attestation-program sources were supplied in this workspace. This is an independent mathematical/source audit and a recount of supplied logs, not a fresh kernel run. The timed-interpreter internals and the unrelated epoch-2 proofs were not re-audited.

1. **[BLOCKER] `exists_loopTM` is false: a rejecting round may take zero steps.**

   **References:** `Build/Loop.lean:148–178`, especially the existential time at lines 157–162 and the advance equation at lines 170–173; `audits/ch1-infra-pack.md:80–92` (attestation 7).

   The no-mid-round-anchor condition does not require a round to occur. At `t = 0` it is vacuous, and an identity advance satisfies the endpoint equation without constraining what the machine actually does from the anchor.

   Here is a refutation using only computable functions and one-state machines. Choose:

   | Parameter | Value |
   |---|---|
   | `body.k`, `F.k` | `0` |
   | `body.State`, `F.State` | `Unit` |
   | `anchor`, both initial states | `()` |
   | Every body transition | Keep the input head stationary; emit `true`; halt. |
   | Every fuel-machine transition | Keep the input head stationary; emit nothing; halt. |
   | `R n`, `T n` | `0`, `1` |
   | `s0 x`, `stepF s` | `x`, `s` |
   | `acceptF s` | `s.getLast?.getD false` |

   All premises hold, step by step:

   - **Fuel:** `Nat.bits (R |x|) = Nat.bits 0 = []`, which `F` computes in one step.
   - **Startup:** choose `t = 0`. With zero work tapes, `stateWord 0 (s0 x)` is the unique empty-domain function. Thus `body.initCfg x = Cfg.ofWords anchor (stateWord 0 (s0 x))`; the earlier-anchor clause is vacuous.
   - **Accepting round:** if `acceptF s = true`, choose `t = 1`. The body halts with `[true]`. No natural number satisfies `0 < t' < 1`.
   - **Rejecting round:** if `acceptF s = false`, choose `t = 0`. Since `stepF s = s`, `runFrom cfg 0 = cfg` is exactly the required advance equation. Again the anchor clause is vacuous.

   The conclusion therefore supplies one `E` and one constant `c` such that, for **every** input `x`,

   \[
   E(x)=[x.\mathrm{getLast?}.\mathrm{getD}(\mathrm{false})]
   \quad\text{within}\quad c(1+1)(0+2)=4c\text{ steps}.
   \]

   This contradicts the machine model. Take the equal-length inputs

   \[
   x=\mathrm{replicate}(4c,\mathrm{false})\mathbin{++}[\mathrm{false}],
   \qquad
   y=\mathrm{replicate}(4c,\mathrm{false})\mathbin{++}[\mathrm{true}].
   \]

   Initially the input head is at position 1. Before transition `j + 1`, with `j < 4c`, its position is at most `j + 1 ≤ 4c`: every transition moves it by at most one. Positions 1 through `4c` contain `false` on both inputs, and position 0 is blank on both. Induction on `j = 0,…,4c` therefore gives identical control states, input-head positions, work tapes, work-head positions, and accumulated outputs in the two runs. The induction step uses identical read tuples and the deterministic transition table; the equal input lengths give identical clamping. Hence their outputs after `4c` steps are equal. The asserted outputs are `[false]` and `[true]`, a contradiction. This also covers `c = 0`.

   **Repair:** require `0 < t` in the round hypothesis. Merely requiring a work tape does not address the logical loophole: with one tape, a startup can copy `x` to the seam in `2|x| + 2` steps, the anchor can always halt with `[true]` in one step, and `stepF = id` still lets every falsely classified state use `t = 0`. The same hypotheses then allow an arbitrary, even undecidable, `acceptF`. The positive-duration repair must accompany the customer-domain repair in finding 2. Re-audit the repaired statement before any fill.

2. **[MAJOR] The round hypothesis quantifies over arbitrarily long state words at the empty-input budget; it cannot express the intended counter/enumerator rounds.**

   **References:** `Build/Loop.lean:41–52,115–119,157–173`; `machine-library-design.md:154–179`; the increment semantics at `Build/Convention.lean:113–120`.

   The premise is `∀ x s, ∃ t ≤ T x.length, …`, with no invariant connecting `s` to `x`, its length, or the bounded orbit. Consequently `x = []` demands the same fixed bound `T 0` for **all** state-word lengths.

   A concrete obstruction already occurs for an all-rejecting round that increments its fixed-width state. Set `acceptF s = false` and `stepF s = (incFixed s).getD []`. For a body with at least one tape, consider

   \[
   s=\mathrm{replicate}(T(0)+1,\mathrm{true})\mathbin{++}[\mathrm{false}].
   \]

   The target word is

   \[
   \mathrm{incFixed}(s)
   =\mathrm{some}\bigl(\mathrm{replicate}(T(0)+1,\mathrm{false})
   \mathbin{++}[\mathrm{true}]\bigr).
   \]

   In particular, tape cell `T 0 + 1` must change from `false` to `true`. Its head starts at zero and cannot reach and write that cell within `T 0` transitions (`Configuration.lean:199–213`). Thus no such body satisfies `hround`, regardless of its finite-control size or scratch-tape count. This obstruction remains after adding positive round duration.

   The intended enumerator instead has a width bounded in terms of the current input; padding search similarly has a bounded candidate domain. Neither fact appears in this premise. Encoding the original input inside `s` does not solve the problem: the universal quantifier also demands the same long encoded word be handled when the physical input is empty.

   **Repair:** restrict `hround` to the states on the specified bounded orbit, or add an input-indexed admissibility invariant with startup and advance-preservation hypotheses. Permit `stepF`/`acceptF` to depend explicitly on the input if needed, or relate an encoded copy to that input in the invariant. Supply actual enumerator and split-search instantiation statements to verify customer coverage.

3. **[MAJOR] D5's no-loss-of-coverage disposition is not supported by the interfaces: dynamic data assembly and result-bearing search are missing.**

   **References:** `machine-library-design.md:51–62,107–125,154–179,252–265`; `Build/Primitives.lean:119–177,224–244`; `Build/Loop.lean:163–178`; `TCSlib/Complexity/ClassNP/TMSAT.lean:919–926,1145–1152,1183–1190`; `audits/ch1-infra-pack.md:104–109`.

   There are two concrete customer mismatches, independent of the false loop theorem:

   - **P6 does not provide the required data-preserving assembly.** `pairEncodeFixed` fixes the entire first component before the machine is chosen. `pairFst` and `pairSnd` return one component and discard the other; they are not threaded transformations retaining both components. The attached D-WRAP obligation explicitly needs `pairEncode x u ↦ x ++ u` with a malformed-input branch. D-MEM needs `pairEncode (pairEncode (Nat.bits t) α) (pairEncode x (w.take n))`, with variable components; D-EMIT explicitly requires retaining `x` while generating the unary components. Neither a pair-to-concatenation contract nor a timed data-retaining assembly combinator is supplied. Sequential composition alone gives `g(f(x))`; it does not supply simultaneous access to two discarded results.
   - **The advertised P10 construction is not an instance of the loop's public result contract.** P10 must output the selected split, or `[]`. The loop accepts only a body that halts with `[true]`, and its public conclusion exposes only `[any …]`, with `[false]` on exhaustion. It exposes neither the successful state/candidate nor its payload. In particular, a body that emits `pairEncode (w.take i) (w.drop i)` as the P10 sketch instructs does not satisfy the loop's accepting endpoint. A Boolean existence answer does not identify the successful candidate. The original P10 catalog also described search for a supplied predicate, whereas the implemented P10 specializes to a fixed length equation; that narrowing is not listed in §9a.

   These observations do **not** refute the standalone `splitSolve` or parser computability statements: bespoke finite machines can implement them at the stated budgets. They refute the claimed coverage by the proposed public interfaces and the claimed direct P10 instantiation. New internal machinery could repair the situation, but it must be specified rather than counted as already covered.

   **Repair:** provide timed pair-to-concatenation and data-retaining mapping/assembly contracts sufficient for the named D-sites; provide a result-bearing bounded search/loop contract, or explicitly budget and specify P10's separate controller. Record the P10 narrowing. Re-issue D5 against concrete customer-to-contract mappings, including the absent E3/E4 obligations. P7's exact polynomial unary outputs and P8's original-input length check do match their stated narrow uses; that does not establish the whole disposition.

4. **[MINOR] The countdown sketch exhausts before checking the promised initial orbit point.**

   **References:** `Build/Loop.lean:107–110,121–146,175–178`.

   The supplied fuel is `R`, the sketch decrements on **each entry** into the anchor, and borrow-overflow rejects. Applied to the initial anchor entry, this permits only `R` body rounds. At `R = 0`, `Nat.bits 0 = []` immediately overflows and rejects, even when `acceptF (s0 x) = true`; the conclusion requires checking that point.

   **Repair:** run the initial round without debiting fuel and debit on subsequent anchor entries, or initialize the countdown to `R + 1`. Handle the initial anchor explicitly even when startup has time zero. This is a defect in the proposed construction, not a separate refutation of the desired `R + 1`-point semantics.

   The proposed asymptotic budget itself is adequate once the semantic defects are fixed. For successful decrements from `R` down to 1, the borrow length at value `m` is one plus the number of trailing binary zeros of `m`. Thus

   \[
   \sum_{m=1}^{R}\text{trailingZeros}(m)
   =\sum_{j\ge1}\left\lfloor\frac{R}{2^j}\right\rfloor
   \le R.
   \]

   Rewinding over the borrow path changes this only by a constant factor; the final underflow scans the counter width once. Moreover, `hF` and `output_length_le` give `|(Nat.bits (R n))| ≤ T n`. Even the simpler per-round bound `O(T n + counter width)` is therefore `O(T n)`. Fuel/startup, `R n + 1` body rounds, and exhaustion fit a constant multiple of `(T n + 1)(R n + 2)`, with no additional multiplicative logarithm. This validates the budget strategy; it is not a completed Lean construction.

5. **[MINOR] P5's harvest sketch emits the wrong polynomial degree.**

   **References:** `Build/Primitives.lean:84–100`; the supplied harvest interface at `TCSlib/Complexity/ClassNP/TMSAT.lean:500–509`.

   The contract requires exactly `C (n + 1)^e` trues, but its sketch prescribes `e + 1` nested loops of side length `n + 1`, each box point emitting `C` trues. That emits `C (n + 1)^(e + 1)`. The attached `poly_unary_computes c C` explicitly computes exponent `c + 1`, confirming the mismatch. For `C = 1`, `e = 0`, and `n = 1`, the contract wants one true and the described construction emits two.

   **Repair:** for `e > 0`, harvest with loop parameter `e - 1`; for `e = 0`, use the fixed constant-output machine. The available time allowance `c (n + 1)^(e + 1)` remains ample. Make the same indexing convention explicit in the binary-clause harvest. This is a repair to the new sketch, not an audit finding against the old generator's proof.

6. **[MINOR] Attestation 4 labels Unicode character counts as byte counts.**

   **References:** `audits/ch1-infra-pack.md:57–68`; `TCSlib/Complexity/ClassNP/TMSAT.lean:604–677,709–719`.

   The supplied UTF-8 text reproduces the advertised numbers as **character** counts:

   | Precisely delimited current-text region | Unicode characters | UTF-8 bytes |
   |---|---:|---:|
   | From `/-- The canonizer's completed serialization` through the blank separator before `/-- A single timed simulator` | 4,022 | 4,085 |
   | From `theorem timed_universal_quantitative` up to, but excluding, `:= by` (including its preceding space) | 625 | 651 |

   The discrepancy comes from multibyte symbols, including `α`, `∀`, `∃`, and `≤`. Excluding the final space gives 624 characters and 650 bytes for the second region; it does not give 625 bytes.

   **Repair:** correct the units and provide comparisons/hashes of actual byte slices at explicitly stated boundaries for both versions. The counting error does not prove that the relocation changed the lemmas, but the stated byte figures are incorrect and cannot certify byte identity. Historical equality remains unverified for the separate reason in finding 8.

7. **[MINOR] Attestation 5's literal import-leaf claim is false; its intended external-boundary claim needs narrower wording.**

   **References:** `audits/ch1-infra-pack.md:69–75`; `Build/Wrappers.lean:6`, `Build/Loop.lean:7`, `Build/Primitives.lean:7`; `TCSlib/Complexity/TuringMachine.lean:15–18`.

   `Convention` is imported by three other Build modules, so it is not an import leaf and the facade is not its only importer. Among the supplied files, the facade is the only importer **outside Build** of the new Build modules. The complete tree is not attached, so an unrestricted whole-tree grep claim cannot be repeated here.

   Import visibility also differs from theorem dependency: a facade can make admitted declarations available without any particular proved theorem depending on them. The supplied headline axiom prints support the latter, narrower claim for the named theorems.

   **Repair:** state the boundary claim as “outside the Build subgraph, the only direct importer is the facade,” and supply the whole-tree grep evidence. Retain the named theorem-dependency checks as the evidence that those proofs do not use the new admissions.

8. **[NOTE] Several requested historical and customer attestations cannot be independently verified from this bundle.**

   **References:** `audits/ch1-infra-pack.md:32–92,96–109,159–163,190–211`; `audits/logs/ch1-infra-axioms.log:13–21`; `machine-library-design.md:107–120`.

   The manifest correctly describes 19 attachments after the pack, but the following evidence is absent: the pre-export `Universal.lean` and `TMSAT.lean`; the original loop statement; run-A and run-B logs; the environment-traversal programs; the style-lint output and escalation records; the private definitions `stripCertificate`, `certificateSplit`, and `enumInc`; the batch-C promotion report; and the E3/E4 customer briefs. The supplied Lean files cover only part of the 57-module tree.

   Therefore this audit cannot certify either freeze claim, public declaration-order preservation, the claim that only `Loop.lean` changed between runs B and C, exact equality to the three absent private functions, or coverage of every E3/E4 obligation. A current source snapshot and clean axiom print cannot establish a historical byte comparison. The root log lists declaration names, not a reproducible traversal algorithm or per-site records; the three TMSAT `sorry` sites can, however, be checked directly in the attached source.

   **Disposition:** these claims remain **unverified**, not disproved merely because their evidence is missing. Supply the historical slices/diffs and the named source/interface evidence in the repair bundle. No repository access or unrelated proof audit was performed to fill these gaps.

**Statement-by-statement verdicts**

“Pass” below means no false statement or unrealizable stated budget was found by this statement-phase audit; it does not claim that a stub has been filled or kernel-checked. Findings 1–3 qualify customer coverage even where the standalone function is realizable.

| # | Contract and file lines | Truth / realizability verdict |
|---|---|---|
| 1 | `capture_run`, `Build/Wrappers.lean:135–144` | Pass. The capture correspondence commutes with every live source step, including a halting emission. |
| 2 | `redirectTM_computes`, `Build/Wrappers.lean:190–194` | Pass. The register updates before the source halt test; the matching branch halts silently within the same bound. |
| 3 | `redirectTM_live`, `Build/Wrappers.lean:206–211` | Pass. A mismatched final register, including no emission, enters the stationary live state. |
| 4 | `computesFunInTime_cond`, `Build/Wrappers.lean:226–233` | Pass. Separate tape banks preserve blank branch tapes; rewinding the input costs a constant multiple of the decider's run, and the selected branch sees the original input length. No monotonicity premise is needed. |
| 5 | `loop_run`, `Build/Loop.lean:83–96` | Pass, including `N = 0`. The first accepting segment or the final exhaustion segment supplies the verdict within `(N + 1) B`. Zero-length advances do not invalidate this finite summation lemma. |
| 6 | `exists_loopTM`, `Build/Loop.lean:148–179` | **False** (finding 1); intended round domains also excluded (finding 2); countdown sketch needs finding 4's correction. |
| 7 | `computesFunInTime_prepend`, `Build/Primitives.lean:66–69` | Pass. Emit the fixed prefix then copy the input; coefficient may depend on the prefix. |
| 8 | `computesFunInTime_lengthBits`, `Build/Primitives.lean:79–82` | Pass. Binary increments with return to the low-order end have linear total carry cost; empty input yields `[]` and still halts. |
| 9 | `computesFunInTime_polyUnary`, `Build/Primitives.lean:96–101` | Pass as a statement, including `C = 0`, `e = 0`, and empty input. The harvest indexing is wrong (finding 5). |
| 10 | `computesFunInTime_polyBits`, `Build/Primitives.lean:113–117` | Pass. Unary generation followed by linear-time length measurement preserves the stated polynomial degree in time. |
| 11 | `computesFunInTime_pairEncodeFixed`, `Build/Primitives.lean:131–134` | Pass for a fixed first component; does not supply dynamic assembly (finding 3). |
| 12 | `computesFunInTime_pairFst`, `Build/Primitives.lean:145–149` | Pass. Buffer decoded prefix until an aligned separator is found. Malformed input yields `[]`; valid empty first components also yield `[]` by design. |
| 13 | `computesFunInTime_pairSnd`, `Build/Primitives.lean:160–164` | Pass. After a valid aligned separator, every suffix is legal and may be emitted. No valid separator gives `[]`. |
| 14 | `computesFunInTime_pairValid`, `Build/Primitives.lean:173–177` | Pass. Aligned `00`/`11` blocks continue, `01` succeeds, and `10` or a missing/incomplete separator fails. Suffix contents are unrestricted. |
| 15 | `computesFunInTime_pairLenCheck`, `Build/Primitives.lean:191–198` | Pass. Measure decoded component lengths and compare with the exact polynomial; `|a| ≤ |input|` controls the stated budget. Malformed input returns `[false]`. |
| 16 | `computesFunInTime_stripLast`, `Build/Primitives.lean:212–222` | Pass. Buffer before deciding whether a last `true` exists. Validity failures and all-false regions produce `[]`; a successful empty witness still produces a nonempty encoded pair. Even linear-time direct scans suffice for the quadratic allowance. |
| 17 | `computesFunInTime_splitSolve`, `Build/Primitives.lean:237–244` | Pass as a standalone machine statement. Search at most `n + 1` candidates, each with `O((n + 1)^(e + 1))` allowance; output has length at most `2n + 2`. The claimed direct loop instantiation is unavailable (finding 3). |
| 18 | `computesFunInTime_incFixed`, `Build/Primitives.lean:258–261` | Pass. Detect overflow before emitting. Empty input overflows; every successful result is nonempty and has the input width, so `[]` is an unambiguous failure result here. A constant number of scans suffices. |

**Convention, wrapper, and primitive checks supporting those verdicts**

`Cfg.ofWords` and its two proved lemmas (`Build/Convention.lean:75–94`) agree with `Cfg.init` (`Configuration.lean:190–191`) and `bufferTape` (`Simulation.lean:465–488`). The input head is 1, each work head is 0, control is live at the anchor, and physical output is empty. For tape position `z`, the content is `w[z]` when `0 ≤ z < |w|`, and blank otherwise. The initial-configuration lemma reduces using `bufferTape [] = blank`; the tape projection is definitionally reflexive. The general constructor does not assert that every tape is scratch; the loop's `stateWord` assignment is what makes all tapes other than tape 0 blank.

For W1 (`Build/Wrappers.lean:86–143`), the agreement hypothesis supplies the same input move and first `k` tape actions. If the source emits `b`, the capture head at `|pre ++ source.output|` writes `b` and moves right once; `bufferTape_append` gives the next stored word. Otherwise both the word and head stay fixed. The host emits nothing. A live successor is mapped by `emb`, and a halted successor maps to `ret` **after that same transition's emission**. Induction consequently proves the stated correspondence through the first halt. The guard allows the halting endpoint and prevents taking an unconstrained transition from `ret` afterwards. An already halted source at `t = 0` is harmless. Neither injectivity of `emb` nor disjointness of `ret` is needed for this conditional theorem: `hagree` already imposes the necessary consistency. Agreement on all read tuples is stronger than reachable-state agreement, but is a valid compositional table condition.

For `loop_run`, take the least accepting index if one exists below `N`; preceding advance equations compose by `runFrom_add`. Its accepting segment uses at most one additional `B`. If no such index exists, compose all `N` advances and the final exhaustion segment. The respective bounds are at most `(N + 1) B`, and `List.range N` tests exactly indices `0,…,N−1`. At `N = 0`, the conclusion is precisely the exhaustion hypothesis with `[false]`.

The pure functions have the following semantics (`Build/Convention.lean:101–120`): `splitAtLastTrue [] = none`, every all-false word gives `none`, and `u ++ [true] ++ replicate r false` returns `some u`. The function defining `solveSplit` is strictly increasing because, for `i < j`,

\[
i+C(i+1)^e\le i+C(j+1)^e<j+C(j+1)^e.
\]

This remains valid for `C = 0` and `e = 0`. The search includes both endpoints. In particular, at `n = 0`, it succeeds with `i = 0` exactly when `C = 0`. `incFixed` preserves width on success, increments the little-endian value by one, and returns `none` on exactly the all-true words, including the empty word. These facts agree with the disciplines described in the pack; equality to the absent private definitions is not certified.

The pairing default `getD []` deliberately identifies parse failure with a valid empty extracted component. It is not a validity certificate; pipelines must use `pairValid` at the appropriate input stage. `stripLast` instead returns a full encoded pair on success, so even an empty witness is distinguishable from its `[]` rejection.

For `polyBits`, write the unary machine's time as `a(n+1)^(e+1)` and the length machine's time as `b(m+1)`. The latter is monotone. The existing composition theorem (`Composition.lean:367–389`, realized multiplier 2) gives

\[
\begin{aligned}
&2\bigl(a(n+1)^{e+1}+b(a(n+1)^{e+1}+1)+1\bigr)\\
&=2\bigl(a(b+1)(n+1)^{e+1}+b+1\bigr)\\
&\le 2(a+1)(b+1)(n+1)^{e+1},
\end{aligned}
\]

since `(n+1)^(e+1) ≥ 1`. Thus the composition overhead does not increase the claimed exponent.

**Completed-proof audit: export and bridge**

The five lemmas at `TCSlib/Complexity/ClassNP/TMSAT.lean:604–676` are mathematically sound on the supplied definitions. Let `L = (c.decode α).serialize.length` and `H = c.canonizerTime α.length`. The canonizer's completed output and `output_length_le` give `L ≤ H`. The serialized header contains the bit word and initial-state index; its table has a nonempty record for each of `numStates + 1` states. Consequently

\[
|(\mathrm{Nat.bits}\,(c.\mathrm{decode}\,\alpha).\mathrm{numStates})|\le L,
\quad (c.\mathrm{decode}\,\alpha).\mathrm{tm}.q_0.\mathrm{val}\le L,
\quad (c.\mathrm{decode}\,\alpha).\mathrm{numStates}+1\le L.
\]

The table proof uses just one of each state's nine nonempty records, which is a valid lower bound. The flattening induction and the two-bit input-move field establish the needed nonemptiness. No unsupported upper bound on the canonizer's running time is assumed.

Expanding `universalBlockBound` (`UniversalBlock.lean:750–751`), the displayed export coefficient is

\[
\begin{aligned}
&3|\alpha|+H+L+2|\mathrm{bits}(\mathrm{numStates})|+2q_0+16
  +3L+5(\mathrm{numStates}+1)+20+14\\
&=3|\alpha|+H+4L+2|\mathrm{bits}(\mathrm{numStates})|+2q_0
  +5(\mathrm{numStates}+1)+50\\
&\le 3|\alpha|+H+(4+2+2+5)L+50\\
&=3|\alpha|+H+13L+50\\
&\le 3|\alpha|+14H+50.
\end{aligned}
\]

Here `numStates` and `q₀` are the decoded machine's state-count parameter and initial-state index. Thus the thirteen bounded terms and all constants are accounted for: `1 + 3 + 2 + 2 + 5 = 13` and `16 + 20 + 14 = 50`.

The new export (`Universal.lean:2861–2899`) chooses `timedUniversalTM c` before `α`, `x`, and `t`. Its displayed coefficient is definitionally `timedStartupBound c α + universalBlockBound c α + 14`: the startup expression at lines 2666–2668 has exactly the same left-associated summands. The type ascription at lines 2882–2890 therefore uses the trusted `timed_computes` result directly, without an arithmetic rewrite or an existential-witness bound.

In the success branch, `computesInTime_iff` supplies the halted state and exact output at the deadline, and `timedAnswer` reduces to `true :: output`. In the timeout branch, a halted state would itself yield a completed output via `computesInTime_iff`; the quantified non-halting hypothesis excludes it, leaving `[false]`. Both clauses, including deadline-inclusive success and the zero-deadline timeout, retain the original theorem's meaning. The public proposition uses only Chapter-1 vocabulary. The explanatory docstring accurately describes this derivation.

The discharge (`TMSAT.lean:709–731`) retains the same single simulator, multiplies the coefficient inequality by the nonnegative natural `(t + 1)^2` using `Nat.mul_le_mul_right`, and applies `ComputesInTime.mono` separately to **both** clauses. It makes no inference about an arbitrary witness of `timed_universal`. No error was found in either completed proof under the pack's explicit dependency boundary.

**Numbered maintainer attestations and requested dispositions**

| Item | Independent disposition |
|---|---|
| Attestation 1 — elaboration | Run C's 57 headers are unique, numbered 1–57, and match the supplied module order exactly. Recount: 0 `error:` occurrences; 46 declaration-level admission warnings, 18 in Build and 28 elsewhere; final `SWEEP_PASS modules=57` at log line 930. Runs A/B, fresh-olean execution, toolchain pin, and historical admission changes are not independently verifiable from the supplied artifacts. |
| Attestation 2 — axioms | Exactly 21 axiom-print lines contain `sorryAx`: 18 Build contracts and the 3 TMSAT targets. The five named Chapter-1 headlines and both new completed theorems print only the standard triple. The source has exactly the three disclosed TMSAT sites: D-MEM at line 964 and D-WRAP/D-EMIT at lines 1152/1190; NP-completeness applies its two parents at line 1204. The displayed root lists match these claims, but the opaque-value traversal implementation and the historical “unchanged” claim cannot be independently checked. The 46 sweep warnings count declarations, not individual `sorry` expressions. |
| Attestation 3 — Universal freeze | **Unverified.** The new theorem is at the end of the namespace and its derivation passes, but no old source or commit diff is attached. This cannot establish zero deletions, one-hunk history, or byte identity of pre-existing declarations. |
| Attestation 4 — TMSAT freeze | **Incorrect byte counts; otherwise unverified historically.** See finding 6. The five current lemmas precede the bridge, and the new docstring retains the escalation paragraph followed by an explicitly historical discharge note. Neither relocation identity nor residual-file identity can be inferred without the baseline. |
| Attestation 5 — topology | **Literal claim false; narrower supplied-file claim supported.** See finding 7. The order has Convention/Wrappers/Loop at positions 9/10/11 after Composition (8), and Primitives at 26 after Encoding (25). |
| Attestation 6 — policy | All 18 current contracts have sketches; two sketches need findings 4/5's corrections, and P10 needs finding 3's interface correction. Current file sizes are 2,901 lines for Universal and 1,206 for TMSAT. Style-lint results, earlier sizes, and escalation records are not supplied. Wrappers' module prose at lines 27–29 also says “three contract theorems,” although it contains four; correct this bookkeeping typo. |
| Attestation 7 — loop repair | Both added hypotheses are present. The fuel-machine premise repairs arbitrary fuel materialization and bounds counter width. The anchor restriction still permits the zero-step refutation, and neither addition supplies the required state-domain invariant. The repaired theorem fails this audit. The original version and unchanged-other-contract claim remain historically unverified. |
| D4 — promotion subsumption | **Accept semantic/time-bound subsumption.** `|w| + n + 1 ≤ (|w| + 1)(n + 1)`, since the difference is `|w| n`. Likewise `2|α| + n + 3 ≤ (2|α| + 3)(n + 1)`, with difference `(2|α| + 2)n`. `pairEncode α x` is exactly prepend by the doubled `α` plus separator. These are weaker uniform linear budgets, not literally the same sharp contract. The absent private source/report prevents a historical harvest comparison. |
| D5 — catalog refinements | **Do not approve.** Findings 2/3 identify explicit customer-interface gaps. P7 covers the displayed exact polynomial emission values, and P8 checks the correct original-input length bound. General assembly, result-bearing search, and the status of clearing support still need explicit customer mappings. Full E3/E4 coverage cannot be certified without those briefs. |

**Notation glossary.** `++` denotes list concatenation; `|w|` is list length; `replicate(r,b)` is the list of `r` copies of bit `b`; `trailingZeros(m)` is the number of low-order zero bits of a positive integer; `O(f)` denotes a constant multiple of the displayed bound, with machine parameters fixed. In the counterexample, `x` and `y` are the two explicitly displayed equal-length inputs and `c` is the claimed loop-machine constant. In the composition calculation, `a` and `b` are the unary-generator and binary-length-machine time coefficients. In the bridge calculation, `L` is the decoded serialization length, `H` is its canonizer time bound, and `numStates`/`q₀` abbreviate the decoded machine's state-count parameter/initial-state index. Other names are those of the audited declarations.
