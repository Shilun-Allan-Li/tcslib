SHA-256: `a7e8c5049b94951ca58347b97c39760f8f68a359ffb26f8196e3b87129af71df`.

Confirmed: **exactly 36 sections** under `## ===== <path> =====` headers. Both match the requested input.

**RD-3 statement-gate verdict: PASS — 0 blockers, 0 majors, 4 minors.** The literal restatement is true as a mathematical specification, and the window route is a sound proof plan. This is not a certification of an implemented universal machine, runner, or Lean proof. H2, H3, H5 and the public `U₀` contract still require their own gates before consumer fill, as the supplied policy requires.

I inspected the supplied statements, definitions, sketches, records and evidence; independently replayed the supplied patch; and checked AB09's published Exercise 4.1, p. 93, the standing convention on p. 79, and Theorem 4.8, pp. 82–83. Exercise 4.1 requires the forward simulation and matching output; it does not demand the former failure verdict. Source: [Arora–Barak, *Computational Complexity: A Modern Approach* (2009), published-book PDF](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf#page=119).

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `SpaceComplexity/Hierarchy.lean:96–103,142` · `space_universal` | The forward statement retains avoidable input-device addends. | The logarithmic allowance is needed for the selected full-position-counter construction, not for the theorem. A restoring scan bounded by the encoded header length uses `O(s)` space on every qualifying run; the calculation below gives an addend-free route. The docstring already disclaims a lower bound, and the existing statement recovers the book's bound on its above-log domain, so this is an avoidable weakening rather than a false or materially misleading statement. | Prefer `C * s` at this gate and specify the bounded-prefix H5 device below. If retaining the current statement, record the stronger alternative's disposition as an implementation choice. The stronger route requires a changed H5 contract and sketch, not just deleting terms in Lean. |
| 2 | minor | `machine-library-design.md:1935` · §12.8a, “Per-consumer rows (updated)” | The design records consistently supersede the former hierarchy route. | This additional row still prescribes a “budget loop,” “success/cap,” budget comparison and resets, and says the hierarchy “does not use R8.7.” It directly contradicts §16b item 3, the revised earlier consumer row at line 1425, and the new sketch. The three earlier locations at lines 1321, 1395 and 1425 were updated; this fourth location was missed. | Mark the old row superseded and point to the H2/H3/H5 route using R8.7 initialization, test and step rows and a configuration-count clock. |
| 3 | minor | `machine-library-design.md:3674–3676`; audit pack, brief item 5 · runner exits | `counterLoopTMVia` “has one” exit. | `Build/CounterLoop.lean:614` has two stationary host exits: `.done` on counter exhaustion and `.escape` on its one optional early body exit. The attached `counterLoopTMVia_run_done` and `_run_escape` contracts certify both. H3 must distinguish three semantic outcomes, but the description of the existing host is inaccurate. | Say “one optional early body exit, plus clock exhaustion.” H3 can merge halt/window exit into the early escape and distinguish them from the retained record afterward; its public contract must expose all three outcomes. No new low-level three-anchor loop is forced. |
| 4 | minor | `Hierarchy.lean:51–53,126–130`; design §16b item 3 · Finding B | Unary tracking costs `Θ(input travel)`, and its premise fails “whenever `S = o(n)`.” | The marker tape measures the range reached by the simulated input head, not accumulated back-and-forth travel. A one-work-cell machine scanning the entire input gives the required linear-space counterexample; a machine that never scans far does not. Thus the obstruction to a uniform sublinear-space simulation is real, but the wording is overbroad. | State that the marker tape uses one plus the maximum simulated input position reached, and hence `Θ(n+1)` cells on full scans. Replace “whenever” by the failure to guarantee `O(S(n))` uniformly for sublinear `S`. |
| 5 | note | `Hierarchy.lean` · literal statement and source fidelity | **No findings**, apart from row 1's optional strengthening. | Quantifier order is correct: one `SU`, then a positive constant per code, uniform over budget, input, output and time. The premise bounds total visited work cells, including the final configuration. Time is existential; output is unchanged. Code dependence is appropriate for the available arbitrary effective representation interface; inclusive budgeting and the one-tape coding convention are disclosed. | Retain these conventions. Do not infer a space lower bound merely from `Universal.lean`'s time-based long-prefix argument; the independent space justification is given below. |
| 6 | note | `Hierarchy.lean` · failure clause and output | **No findings.** Dropping the failure clause loses no guarantee used by this route. | The diagonalizer supplies its own window and clock. Its contradiction uses only a qualifying forward run of `U₀`. Untagged output is exactly what its output-summary test needs. No declaration in the supplied Lean files consumes `space_universal`; the repository-wide reference log reports the same. | Preserve the distinction between this independently checked supplied-file result and the wider repository attestation in row 11. |
| 7 | note | `Hierarchy.lean` · inclusion and window diagonalization | **No findings.** The inclusion, fixed-machine window, record initialization, clock, finite output tag, uniform space ledger and contradiction fit together. | The detailed checks below cover the four-factor clock bound, the extra halt-testing round, restored scratch heads, fixed-code payload padding, visited-cell containment, and the flip. No uniform bound on all code-dependent canonizer constants is assumed. | Carry these invariants into H3's contract and the fill brief. |
| 8 | note | `Hierarchy.lean` · fill obligations and alphabet reduction | **No additional host is missing.** The named obligations are adequate at proof-plan level. | H2/H5 supply `U₀`; H3 supplies the record runner. The normal-form theorem is present and proved, whereas `exists_codeTM` exports only timed behavior, so its space extension is genuinely still needed. The all-times space bridge is needed too. Validation handles foreign rich inputs, and finite maxima of halting times supply the time function required by alphabet reduction. | Before fill, gate the public contracts and spell out the startup, head-reset, output and all-times refinements listed below. Treat these as contract requirements, not already available theorems. |
| 9 | note | `Hierarchy.lean`; freeze log and patch | **No findings.** The authorized freeze is respected. | Applying `hierarchy.patch` to the supplied base reproduces the supplied after-file exactly. Only `space_universal`'s executable declaration changes. The other three theorem declarations/bodies are identical; both corollaries' docstrings are also identical. There are four theorems, four `sorry` tokens, no new definitions or private declarations, and no import change. | The freeze log's `UNAUTHORIZED BODY CHANGE: space_hierarchy` is a docstring-detection artifact, resolved by the independent comparison. |
| 10 | note | `Hierarchy.lean` · documentation and policy | **No findings.** | Both revised theorem docstrings state their claims, give source locations, declare deviations and label proof work and the statement gate pending. The sketches are literal proof plans with named hosts. The file's longest line is 90 columns. This change introduces no copied proof material or private host. | Keep the pending labels until the corresponding gates and fills actually close. |
| 11 | note | Audit pack · elaboration, public names and no-consumer attestations | **No contradiction found; execution/provenance limits remain.** | Every concrete public declaration cited by the new sketches is present with public visibility in the supplied files. The elaboration log records exit 0 and exactly four sorry warnings, at lines 142, 259, 276 and 306, matching the after-file. I did not rerun Lean: this packet lacks the complete import closure, pinned build environment and resulting artifacts. Repository-wide greps and historical snapshot identity likewise remain maintainer attestations. | Preserve that evidence distinction. The supplied logs support the stated claims; they are not independent kernel replay or complete-repository certification. |
| 12 | note | Design §16b item 3; backlog RD-3; unchanged corollaries | **No findings beyond rows 2–4.** | These records correctly retain the pending gate, the unstatemented `U₀`/H3 work, H2/H5 dependencies and the two normal-form bridge obligations. The former P4.3 resolutions are historical records, not evidence that the new route has already been proved. Both unchanged corollaries remain mathematically supported by their recorded routes. | Update the stale/imprecise current descriptions without rewriting the preserved historical findings. |

The book comparison does not require a new failure clause. Under the stated above-log convention,

\[
1\le \operatorname{logSpace}(|x|)\le s
\quad\Longrightarrow\quad
s+\operatorname{logSpace}(|x|)+1\le 3s.
\]

Thus the present theorem gives the book's constant-factor conclusion on that domain. Representation-dependent constants are defensible for space independently of the earlier time argument: an arbitrary effective scheme can reserve codes whose interpretation selects between two fixed one-cell machines according to a decidable nonregular language of representations. A constant depending only on those two decoded machines would give a constant-space decider for that language, which a two-way finite-state input machine cannot provide. Restricting the coding scheme further could change this conclusion.

Row 1 has a concrete stronger route. Let the header length before the verbatim payload be

\[
\ell=2|\operatorname{bits}(s)|+2|\alpha|+4.
\]

Store a unary ruler of this length while parsing the header. Maintain the physical input head at `p = ℓ + i`, where `i` is the simulated position. To test whether `i = 0`, move exactly `ℓ` cells left, inspect the cell, and move exactly `ℓ` cells right. The probed position is `i`; since `0 ≤ i ≤ |x|+1 < ℓ+|x|+1`, it is blank exactly when `i = 0`. Neither sweep clamps, and the head returns exactly to `p`. Supply a simulated blank and suppress leftward movement at that boundary; elsewhere use the native symbol and right-boundary clamp. This also handles empty `x`.

Every qualifying coded run has `s ≥ 1`, because its one work tape already visits its origin. Consequently,

\[
|\operatorname{bits}(s)|\le s,
\qquad
\ell\le 2s+2|\alpha|+4\le(2|\alpha|+6)s.
\]

For a sufficiently large code-dependent constant `C_α`, startup, table administration and the restoring scans have total workspace bounded by `C_α + s + C_α ℓ`, hence

\[
C_\alpha+s+C_\alpha\ell
\le \bigl(1+C_\alpha(2|\alpha|+7)\bigr)s.
\]

This is an algorithm-level construction and space ledger, not a completed Lean proof. It establishes why the full `logSpace |x|` counter is unnecessary; it does not assert an absolute `O(1)` workspace bound independent of the header. The ruler is reused, so repeated probes do not accumulate visited cells.

The window-route arithmetic and interfaces check as follows.

1. **Inclusion.** At `A = 1`, the domination hypothesis gives `f n ≤ g n` above a threshold. Below it, use the maximum of the finitely many exceptional values, taking zero for an empty prefix. Since `g n ≥ 1`, one global multiplier bounds `f` by `g`, exactly as `SPACE.mono_const` requires.

2. **`U₀` and startup.** For fixed `α`, prefix extraction, buffered canonization and table capture have finite code-dependent space, independent of the payload. Native self-application avoids storing an input-position counter and avoids copying the full input. The startup contract must suppress administrative output, leave the table on a work tape and fresh simulated work cells, and reset the input to **`Cfg.init`'s position `1`**; “origin” must be implemented with this convention. H2 must restore administrative heads/scratch to fixed seams, so its per-round envelope yields a bound for the entire run. These requirements fit the named startup/H2/H5 obligations.

3. **Initialization and uniform space.** `inputFoldTM` can recognize the digit image without moving work heads and return the input head to position 1. Reject foreign rich input before running the lifted constructor. Capturing `bits (g n)` costs `O(g n)` because its output length is at most `g n` for positive `g n`. The radius word, initial record, counter width and finitely many work banks have bounds depending on the fixed `U₀` and constructor, not on the parsed code. Record initialization includes its explicit `+r` and radius-word terms; both are covered by `r = a·g n`. The record rows restore their work heads at return and blank their scratch, preventing a space cost proportional to the number of rounds. Finally, `posWidth n ≤ logSpace n + 1 ≤ 2g n` absorbs the input-position fields.

4. **Clock.** The four factors in `configBound` satisfy

   \[
   \begin{aligned}
   |Q_0|+1&\le 2^{|Q_0|},\\
   n+2&\le 2^{\operatorname{posWidth}(n)},\\
   3^{k_0(2r+1)}&\le 2^{2k_0(2r+1)},\\
   (2r+1)^{k_0}&\le 2^{k_0(2r+1)}.
   \end{aligned}
   \]

   Multiplication gives `configBound U₀ n r ≤ 2^(W−1) < 2^W−1`. Here `W ≥ 3`, since `U₀` has an initial state and `posWidth n ≥ 1`. The strict inequality matters: with halt tested before stepping, a halt after `configBound` transitions may need one additional body round to be recognized. The proposed counter permits that round. No factor for the output tag is needed: the bound shortens a halting run of `U₀` by its output-independent core, not a run of the augmented record machine.

5. **Tag and exits.** Encode the three output summaries in `Fin 3`, with update for `none` equal to the identity and update for `some b` induced by appending `[b]`. The supplied congruence proves the invariant; `accept` means exactly `[true]`, not merely a word beginning with `true`. Halt, window exit and exhaustion all yield a final bit. The clock gives totality even on malformed pair inputs, divergent decodings, or runs with indefinitely growing output. No output word is buffered.

6. **Normal form and contradiction.** The halt-time space bound extends to every time by monotonicity before halting and the frozen run afterward. `ComputesInTime.of_spaceUsed_le` supplies a length-dependent time function, so the proved one-work-tape binary normal form applies. State relabelling preserves every work-head trajectory, but the corresponding existential coding theorem must still export that space clause. With the sketch's constants,

   \[
   C_{\alpha_M}\bigl(c(c_0 f(n)+1)+1\bigr)
   \le C_{\alpha_M}(cc_0+c+1)f(n)=A f(n),
   \]

   using `1 ≤ f(n)`. Apply `hfg` once at this fixed `A`, and choose payload length `N₀`; then `n = 2|α_M|+2+N₀ ≥ N₀`. The code and its canonization constant stay fixed. Total visited space at most `r` bounds every tape's visited-set size by `r`. The two cited visited-cell lemmas therefore put every intermediate head and every nonblank cell in the window, including the final configuration. The configuration-count theorem gives the halt before exhaustion. The recorded summary then makes `D` return the opposite of its alleged decider's answer.

7. **Alphabet reduction.** Its hypothesis bounds all times and all rich inputs, not just encoded Boolean inputs. Validation supplies the foreign-input branch; monotonicity and freezing extend the halting bounds on valid inputs. For its required `ComputesFunInTimeVia` hypothesis, take the maximum first halting time over the finitely many Boolean inputs of each length. This time function need not be efficient or computable. The reduction's constant and `+1` are absorbed by `g n ≥ 1`. Thus the stated packaging obligation is sufficient, without a further simulation theorem.

There are no new definitions to restate. The four theorem specifications have the following mathematical content and justification. `space_universal` asserts forward reproduction of every halting coded computation under its stated visited-cell bound; buffered canonization, a suitable H5 device and a space-accounted H2 loop give the advertised ledger. It neither asserts nor needs anything about failed budgets or nonhalting sources. `space_hierarchy` asserts proper containment under eventual domination of every constant multiple; inclusion and the bounded diagonalizer above establish its proof plan. Only the floor from `hf`, and both the floor and witness from `hg`, are used.

`LOGSPACE_ssubset_PSPACE` asserts strict containment of logarithmic space in polynomial space. Apply the hierarchy at `logSpace` and `n+1`, then include linear space in PSPACE. `SPACE_linear_ne_NP` asserts inequality, without choosing an inclusion direction. Its unchanged sketch correctly uses quadratic padding to turn equality with NP into `SPACE(n²+1) ⊆ SPACE(n+1)`, contradicting the hierarchy; the NP pullback and padding-machine obligations remain explicitly named.

Adversarial cases checked:

- **Zero budget and empty input:** at `s = 0`, the forward premise is impossible for a coded one-work-tape machine; it is not a missing failure obligation. At `n = 0`, `posWidth n = logSpace n = 1`, the initial input position is 1, and neither the record nor clock degenerates.
- **Constant source space, long input scan:** a coded machine that keeps its sole work head at zero and scans right to the input boundary uses one work cell. In `universalInterpreter`, `.start` writes the tape-3 marker at zero and moves that head to 1; `.applyRecord` moves it with the source input head. A full scan visits marker positions `0,…,n+1`, hence `n+2` cells. This verifies the substantive Finding B.
- **Unbounded or misleading output:** `[]`, `[false]`, `[true]` and `[true,true]` are treated respectively as empty, dead, accept and dead. A divergent emitter exhausts the clock; a completed `[true,true]` run is not misclassified as accepting.
- **Oversized code / expensive canonizer:** no input-uniform canonizer constant is inferred. The outer window can stop startup itself, while the contradiction fixes a single code and pads only its payload.
- **Halt on the last transition and a final head move:** visited space includes the final configuration; the strict clock surplus pays for the next halt test. These prevent the two relevant off-by-one failures.

Independent finite checks found no failure in 10,500 clock-factor instances and 28,800 bounded-prefix restoration instances, including empty payloads. These are sanity checks only; the general arguments are the inequalities and head invariant above. No tactic proof was audited or replaced.

Suggested permanent sanity obligations for the forthcoming host gates: a restoring suffix-boundary test including empty input; `U₀` startup with empty output and input position 1; all-time space preservation under state relabelling; and an H3 run that halts on its final simulated transition while emitting the deciding bit. These belong with the public hosts and bridges, not as private reconstructions inside `space_hierarchy`.

Notation glossary: `ℓ` is the encoded header length; `i` is the simulated input position; `p = ℓ+i` is its physical position in the prefixed input. In the strengthening calculation, `C_α` is a sufficiently large constant covering fixed-code administration and the ruler implementation. All other symbols retain the bundle's meanings.
