# Chapters 3–4, P0 reception audit

Date: 2026-10-08. Scope: the supplied audit pack and its 50 attachments, including all 44 modules in `scripts/ab_ch34_received_order.txt`.

Bundle SHA-256, independently recomputed: `69f84b8d7194081e3b7749467f41f2c77fc3f09409e655badac32a4ae6b3d05b`.

**Disposition: P0 does not close. Findings: 0 blockers, 1 major, 7 minors, 2 notes.** The major finding concerns the meaning of unrestricted `SPACE s`, particularly the plan's literal `SPACE(n)` target. It is not a claim that an attached Lean theorem is false. The principal time hierarchy, configuration count, and compiler statements withstand the adversarial checks below under their actual hypotheses.

This is a definition, statement, and documentation audit. No tactic proof was audited for correctness. The 244 definition-like declarations were first read in comment-stripped sources and restated in a separate record; docstrings were compared afterward. Appendix A includes every such restatement, including private definitions, structures, inductive types, and abbreviations. Appendix B checks every advertised headline result, grouping closely related results where their contracts have the same comparison. The two facade modules introduce no definitions. An explicit finite-type instance is accounted for separately.

## Findings table

File names below are relative to `TCSlib/Complexity/`, except the audit log and plan. Line numbers refer to the extracted attachments, not to the enclosing bundle.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `SpaceComplexity/Basic.lean:110` · `SPACE`; `AroraBarakChapters3-4Plan.md` · Ex. 3.2 target | Multiplicative absorption with no positivity convention supplies the ordinary asymptotic space classes for the planned chapter statements. | Every work tape contributes its initially visited origin. If `s(n₀)=0`, the uniform deciding machine must have `k ≤ spaceUsed ≤ c·s(n₀)=0`, hence `k=0` on **all** inputs. Consequently `SPACE s = SPACE (fun _ => 0)` whenever `s` has any zero. In particular literal `SPACE (fun n => n)` is the zero-work-tape class, not the intended linear-space class. Finite exceptional lengths cannot be absorbed by increasing `c`. See Q2 and sanity targets S1–S3. | Establish a positive-bound convention before adoption: retain the frozen definition but explicitly use `SPACE (fun n => s n + 1)` or an equivalent positive normalization in every asymptotic chapter statement, including Ex. 3.2; alternatively revise the class definition and re-gate it. Document the zero-bound characterization. Merely saying “constants are absorbed” does not resolve this. |
| 2 | minor | `TuringMachine/CounterProgRun.lean:308–313` · `sim_run` | The advertised bound applies whenever the registers stay at most `B` during a run. | The delivered theorem instead assumes `s.pos ≤ x.length` and `∀ r, s.regs r + t ≤ B`. A one-register `goto` loop starting at value `B`, run for one step, stays within `B` but fails `B+1 ≤ B`. The parenthetical sufficient condition in the docstring accurately describes the formal hypothesis; the broader opening is not the delivered interface. `exists_tm` from zero initialization is unaffected. | State the actual sufficient hypothesis in the headline, or add a theorem taking a bound on each intermediate register valuation. |
| 3 | minor | `SpaceComplexity/Machines/Program.lean:42–45,68–72` · `Mode`, `callSegs` | A `whole` call always gives `pairEncode x _`, and a `unaryFst` call gives a corresponding pair. | Empty argument lists are allowed by `CallSpec` and satisfy the distinctness condition. With `x=[]`, mode `whole`, and no arguments, `vword (callSegs …)=[]`; every `pairEncode x w` contains the two-bit separator. More generally the singleton segment has no separator. | Qualify the pair description by “with at least one argument.” Keep the legitimate zero-argument behavior, or explicitly restrict it if pair shape is intended. |
| 4 | minor | `SpaceComplexity/Machines/ARM.lean:69–72` · `Ins.valP`, `Ins.valQ` | These instructions merely check the displayed pairing shape. | `astep` checks `ValidPlain`/`ValidPair`, which additionally require canonical binary payloads. `pairEncode [] [false]` has the advertised plain pair shape but is rejected: `[false]` is not canonical. This is a useful restriction, but part of the public instruction contract. | Say that the payload word, or both inner payload words, must be canonical `Nat.bits` encodings. |
| 5 | minor | `ClassNP/PClosure.lean:160–167` · `lenEq_mem_P`, `lenLe_mem_P` | The accepted languages consist of pairs with the respective length relation. | Both projections default to `[]` on malformed input. Thus `z=[]`, which is not a pair encoding, belongs to both displayed languages. The theorems are valid for these totalized predicates, and their well-formed-pair preimage corollaries are fine. | Describe the default behavior explicitly; if the intended language rejects malformed words, add a successful-decoding guard and prove that variant. |
| 6 | minor | `SpaceComplexity/Machines/ParseCmp.lean:302–307` · `ReachesB` | The register head lies in the interval “throughout” the run, including the reached configuration. | Bounds are quantified only over `t<T`. Choosing `T=0` proves reflexive `ReachesB` even for a configuration whose head lies outside the interval. The endpoint is not bounded by this relation alone. Similar half-open conventions occur in `AReach`, `AHalt`, and `Dbl.Rch`; the main compiler obtains its inclusive bounds separately. | Say “strictly before the endpoint”; add an endpoint-bound hypothesis to any consumer needing an inclusive bound. No compiler counterexample was found. |
| 7 | minor | `audits/logs/ch34-p0-sweep.log:1439` · repository-side attestation | The attached fresh sweep attests the stated Lean-source baseline `84b79daf`. | The log identifies its revision as `e64cec9e`, whereas the pack identifies `84b79daf` and claims a documentation-only relation to `99b187fc`. No supplied revision relation or source diff binds the log to that baseline. The numerical success counts do agree with the log. | Supply the revision relationship and a Lean-source equivalence attestation, or a replacement sweep tied to `84b79daf`. Correct the pack's provenance wording. This is an evidence discrepancy, not a finding about proof correctness. |
| 8 | minor | `SpaceComplexity/Machines/ARMSim.lean:29`; `Machines/Compile.lean:28` · advertised exports | The received API exports `Complexity.LogProg.arm_step` and `Complexity.LogProg.CallsOK`. | Neither declaration occurs in the received surface. The actual interfaces are the instruction-specific `sim_*` results, the later `arm_run`, and singular `CallOK` quantified along a run. `Layout.lean:22` also points to an unattached `Machines.Gadget` module. This concerns missing referents, not naming style. | Update the result/definition lists to the declarations actually supplied; correct or supply the referenced module. |
| 9 | note | `TimeHierarchy/Diagonal.lean` · hierarchy family | The received theorem has the declared quadratic-overhead strength. | The exact scale is `(f(n)+n+1)²`; it becomes an `f²` scale under suitable lower bounds on `f`. The lower theorem uses arbitrarily large numerical domination points, while the class conclusion is ordinary nonmembership/strict inclusion. The book-strength result is explicitly deferred. | No theorem change required. Preserve the explicit hypothesis and the distinction from book strength in downstream citations. |
| 10 | note | `SpaceComplexity/ImplicitPoly.lean`; `UnaryLogspace.lean`; `CounterProgSimRun.lean` | The received function results are usable without asserting general composition. | `ImplicitlyLogspaceComputable` includes polynomial output length; `UnaryLogspace` alone does not. Its conversion theorem requires that extra bound. The counter-program result is a restricted closure theorem. General Lemma 4.17 is not delivered and the plan says so. | No change required. Do not treat these results as the missing general composition theorem. |

## Evidence and source boundary

The local bundle contains 865,996 bytes, 50 unique attachment paths, and exactly the manifest's 44 Lean files. Literal whole-word searches of those 44 files find neither `sorry` nor `axiom`. The attached sweep lists 71 distinct modules, includes the received set, and contains no `error:` lines or admission warnings. The style log records the claimed zero failures/warnings for the 34 non-facade TimeHierarchy/SpaceComplexity files; the size warnings elsewhere are not received files. The attachments do not establish the exception-file history.

There is no `lean` or `lake` executable in this audit environment. I did not independently elaborate the files, reproduce CI, inspect the purported 71 fresh `.olean` files, verify the scratch tree was wiped, regenerate snapshots, or verify the three-way commit relationship. These limits do not invalidate the supplied proofs; they limit independent confirmation of the repository attestations. Finding 7 records the concrete discrepancy.

The primary comparison text was the 2009 book itself, read from a [PDF mirror of AB09](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf). Printed pages, not PDF page indices, are used below. The following compact baseline supplies the book comparisons throughout the report:

| Source | Book baseline used in this audit |
|---|---|
| Theorem 3.1, pp. 68–69 | Constructible bounds with `f log f = o(g)` yield strict deterministic time inclusion. |
| Definition 4.1 and convention, pp. 78–79 | Deterministic space counts visited work locations; the nondeterministic wording counts nonblank locations. Work space excludes input. The chapter assumes `S(n)>log n`. |
| Claim 4.4 and Theorem 4.2, pp. 80–82 | Configurations have `O(S)`-bit encodings under that convention; counting yields exponential simulation. Adjacency also has a small CNF description. |
| Definition 4.5 | Logarithmic space defines `L`. |
| Definition 4.16 and Lemma 4.17, pp. 88–89 | Polynomial output length and logspace bit/length queries define implicit computation, using one-based indices. Reductions compose and logspace preimages preserve `L`. |
| Theorem 4.8 | Constructible space bounds with a little-o gap give strict space inclusion. |

Implementation types and microcode do not have numbered textbook counterparts. Their comparisons below concern their own documented contracts and whether they implement the relevant construction without weakening the final statement. Imported definitions such as `FinTM`, `DTIME`, `TimeConstructible`, pairing, and the vendored space measure are not re-audited as upstream designs; their relevant interface consequences are identified explicitly.

## Answers to the seven numbered questions

### 1. Hierarchy hypothesis, constants, positivity, and `P ⊊ EXP`

The quantifier order is right. Fix an alleged smaller-class decider, its time constant, its normal-form simulation constants, and its chosen code `α`. Only then obtain the universal simulation constant for `α` and combine these into `A`. The hypothesis supplies a threshold depending on that `A`; it does not demand a threshold uniform over machines. The code-dependent order `∀ α, ∃ C, ∀ x` in `univTM_spec` is sufficient. It is not a uniform-over-all-codes claim.

The exact hypothesis controls `(f(n)+n+1)²`, not `f(n)²` for arbitrary functions. If `f(n)≥n` and `f(n)≥1`, then

`f(n)² ≤ (f(n)+n+1)² ≤ 9f(n)²`.

Without those lower bounds, the input-length overhead matters. For example, even constant `f` requires the eventual domination of every constant multiple of `n²`. No constructibility assumption on `f` is needed for this delivered separation. Constructibility is imposed on `g` to build the clock. The book's narrower time gaps remain unavailable.

`diagLang_not_mem_DTIME` needs only `∀ A N, ∃ n≥N, A·(T(n)+n+1)²≤g(n)`. Padding a fixed code supplies **every** length `n≥2|α|+2` by choosing a payload of length `n−2|α|−2`; it does not restrict usable lengths to an arithmetic progression. The eventual hypothesis of `time_hierarchy` is stronger and suffices both for its lower bound and its inclusion. The phrase “infinitely-often separation” in the pack should be read with care: the exported conclusion is ordinary class nonmembership, with an infinitely-often numerical sufficient condition, not a definition of an infinitely-often complexity class.

The `+1` in `DTIME (g+1)` has a real boundary purpose. Under the imported all-length multiplicative time convention, a zero value of a time bound leaves no time even to emit a deciding bit; that class is empty. By contrast, constructibility uses a normalized computational budget and need not forbid `g(0)=0`. Thus one cannot erase `+1` unconditionally. If `∀n,0<g(n)`, then `g≤g+1≤2g`, so the classes coincide by constant absorption. `time_hierarchy_of_pos` has exactly the needed additional hypothesis. A finite alteration setting an otherwise exponential `g` to zero at length zero illustrates why eventual growth alone is insufficient for the unnormalized conclusion.

For the polynomial/exponential instance, put `a=(n+1)^(k+1)`. For every natural `n,k`, including zero, `n^k≤a`, `n+1≤a`, and `1≤a`. Therefore

`A·(n^k+1+n+1)² ≤ 9A·(n+1)^(2k+2)`.

This checks the actual exponent `2k+2` in `eventually_poly_sq_le_two_pow`. For an independent eventual-domination calculation, let `d=K+1` and `m=floor(n/d)`. Once `m≥A·d^K`, use `n+1≤d(m+1)` and `m+1≤2^m` to get

`A(n+1)^K ≤ A d^K (m+1)^K ≤ m·2^(mK) ≤ 2^(m(K+1)) ≤ 2^n`.

The case `A=0` is immediate. This is a numerical check, not a review of the Lean proof.

`twoPowTM` outputs `n` false bits followed by true in `n+1` steps, the canonical little-endian representation of `2^n`, and `n+1≤2^n+1`. Thus the constructibility instance is nonvacuous. Finally, `P_ssubset_EXP` uses the **same** `diagLang (fun n => 2^n)` against every polynomial exponent. Merely knowing a separate strict inclusion for each exponent would not suffice to separate their union; the common diagonal witness does. Its upper bound is in the exponent-one part of `EXP`, with the harmless factor from `2^n+1≤2·2^n` absorbed. The claimed separation is delivered.

### 2. Unrestricted `SPACE`, zero bounds, and short inputs

No received configuration-count or compiler theorem silently needs `s≥log n`: the count retains an explicit input-head factor, and compiler bounds are stated directly. `LOGSPACE_subset_P` is robust at lengths zero and one because `logSpace 0 = logSpace 1 = 1`.

The important exceptional behavior is stronger than “zero space permits only finite control.” `Clean.visited_interval` explicitly entails that each tape's visited set contains the origin, even at time zero. Consequently, for any machine and input,

`M.k ≤ M.tm.spaceUsed (M.tm.initCfg x) t`.

If `s(n₀)=0`, choose `x` to be `n₀` false bits and instantiate its space-deciding contract. It forces `M.k=0`. This is one fixed machine for every input, so the loss of work tapes is global. Conversely, a zero-tape decider uses zero work space for every input. Hence

`SPACE s = SPACE (fun _ => 0)` whenever `∃n, s n=0`.

The exact machine characterization is the languages decided by total, finite-state, zero-work-tape machines with a two-way read-only input and unread append-only output. This is the regular-language class: the one-bit output condition can be tracked in finite control, and two-way finite automata recognize the same languages as one-way automata ([Rabin–Scott 1959, Theorem 15, p. 123](https://www.cs.miami.edu/~burt/learning/csc427.222/docs/rabin-scott.pdf)). This last identification is mathematical, not a theorem linking the received definition to a formal regular-language predicate in this bundle.

In particular, `SPACE(n)` and `SPACE(n^d)` for positive `d` collapse to that class because of length zero. Literal `SPACE(n)≠NP` would then concern the wrong linear-space class. A zero at any other length has the same effect. This is finding 1. Positive normalizations remove this obstruction; merely requiring an eventual lower bound does not. The plan's proposed `n^c+1` normalization for polynomial space avoids it.

Neither `SPACE 0` nor `SPACE s` is empty: the constant languages have zero-tape machines that emit one Boolean and halt. Length parity is a nonconstant zero-space example. A zero-tape parity scanner takes `n+1` steps, so below logarithmic space one cannot remove the input factor and claim a `2^{O(s)}` time bound. A constant-time decider could not distinguish two sufficiently long all-false inputs of opposite length parity before reaching their ends. This does not challenge the received count, which retains `n+2`.

### 3. Independent configuration count and its actual halting premise

Fix the input, a machine with `k` work tapes and `q` live states, and a bound `s` on total visited work cells through a halting time. Each head starts at zero and moves by at most one. Reaching a coordinate requires visiting all intervening coordinates. Every nonblank cell was written at a visited coordinate. Thus the much larger window `[-s,s]` contains each relevant head and all nonblank tape content.

| Factor | Independent reason | Boundary behavior |
|---|---|---|
| `q+1` | Live state or halted marker. | Counts an extra terminal choice; it cannot undercount. |
| `n+2` | Input symbols plus two boundary positions. | Still two positions on the empty input. |
| `3^(k(2s+1))` | `Option Bool` has three values at each cell in each tape window. | Allows arbitrary contents in windows, including unreachable combinations. |
| `(2s+1)^k` | A head coordinate in the window for every tape. | For `k=0` both tape factors are one; for `s=0` the window has one coordinate. |

Multiplication gives exactly `configBound`. Using a radius `s` for **every** tape when the sum of visited cells is bounded by `s` overcounts. `posCode` is not globally injective: it clamps. The count only needs its injectivity on the bounded reachable coordinates, with blankness outside the window.

The counted object is a **core**, omitting output, not the full configuration including an arbitrarily long output list. This is legitimate for time-to-halt because output is unread. Equal cores have equal future core evolutions; a repeated live core before the first halt would make that evolution periodic and prevent a first halt. The final output is recovered at the same halting computation, not reconstructed from the core code.

`ComputesInTime.of_spaceUsed_le` explicitly assumes both an already-halting computation `h : M.ComputesInTime x y t` and its bound `spaceUsed … t ≤ s`. It moves that computation to the configuration-count budget. It does **not** assert that every space-bounded machine halts. A zero-tape stationary loop is a counterexample to that stronger assertion. Bounding space at time `t` also bounds earlier prefixes by monotonicity. These are the right hypotheses for the deterministic count-to-time implication; the nondeterministic simulation and adjacency CNF are not supplied here.

The logarithmic specialization can be checked uniformly, including short inputs. For natural `s`,

`3^(k(2s+1)) ≤ 2^(4ks+2k)` and `(2s+1)^k ≤ 2^(k(s+1))`.

Writing `ℓ=Nat.log 2 n` and `s=c(ℓ+1)`, use `2^ℓ≤n+1` and `n+2≤2(n+1)` to obtain

`configBound M n s ≤ (q+1)·2·2^(5kc+3k)·(n+1)^(5kc+1)`.

This is a fixed polynomial for fixed `M,c`. The factor also covers `n=0`, `c=0`, and `k=0`. There is no hidden logarithmic lower-bound premise in `LOGSPACE_subset_P`.

### 4. `LogProg` and ARM: what the contracts buy

The contracts are sufficient, and the restrictions are usable for the supplied examples. They are not a theorem for arbitrary oracle programs or arbitrary configurations.

`CleanRun` requires a finite halting run with exactly `[b]`, all work tapes blank at return, all work heads restored to zero, and inclusive head bounds through the halting time. It intentionally leaves the final input head unrestricted. The compiler's return phases restore the real input head to position one and the selected argument heads to zero. In particular, the input return begins by moving left; it does not mistake the right blank on an empty input for an already-restored left boundary.

`CallOK` separately requires: a duplicate-free argument list; real input position one; actual buffer encodings on argument tapes; argument heads at zero; intervals including `-1` and each word's right boundary; and a `CleanRun` with the **same** oracle answer used in the abstract step. Therefore `tapeWord`'s arbitrary-tape default cannot introduce an unrealizable oracle into the compilation theorem. Duplicate arguments are semantically definable abstractly, but the theorem deliberately rejects them because one physical head cannot independently track two argument segments.

The exact conclusion of `compile_correct` is finite-prefix simulation: for the supplied abstract step count `N`, some physical time reaches its `seam`, with inclusive head bounds. There is no halting premise or unconditional halting conclusion in that statement. If the abstract endpoint halts, its seam halts; `compile_space` explicitly adds that premise and the output equality. Thus the conditional docstring follows from the stronger prefix interface. The module's shorthand must be read with those conditions.

`compile_space` charges

`sum_r (hi(r)−lo(r)+1).toNat + kD·(2B+1)`.

The `+1` counts inclusive endpoints and therefore tape origins. At ARM level, intervals `[-1,W]` contribute `m(W+2)`. A bank has twice the maximum component tape count, accounting for data and cleanup markers. Its radius is at least one, even when the selected original decider has zero space; idle padded tapes still visit their origins. Cleaning between calls restores a reusable seam. Repeated calls do not enlarge the union of visited coordinates beyond the fixed charged windows.

`arm_decides` fixes finite decidable labels, a finite family of globally correct `LOGSPACE` languages, and a single ARM. For every input, `hcorr` must give `AHalt` from the live initial label, zero registers, and no answer, ending with the target membership bit. Its pre-endpoint invariant is `PreS` plus

`length (Nat.bits (register_value+1)) ≤ K·logSpace(input_length)`.

The successor in this bound budgets increment carry, including zero-to-one. `PreS` requires distinct equality operands, canonical valid inputs for input-component comparisons, and distinct call arguments. Validation instructions can reject malformed input without requiring the input to have been valid beforehand. A reflexive zero-step `AHalt` of an already answered configuration cannot falsify this theorem: its specified initial state is live and unanswered.

Virtual inputs have length at most `2n+2+m(2W+2)`, with `W=K·logSpace n`. This is `O(n+1)` for a fixed program. Logarithmic space in the virtual-input length therefore stays logarithmic in the original length. `arm_decides_poly` replaces the bit-width invariant with a uniform polynomial bound on numeric register values; it does not bound the run's time. Halting plus the eventual compiled space bound supplies polynomial time by configuration counting when needed.

The restrictions have concrete consequences: a self-comparison instruction must be simplified or implemented using a different fragment; repeated call arguments require separate copies; input comparison requires validation. None creates a gap between the antecedent and the compiled conclusion. The noncomputable abstract oracle and choice operations are specification devices; finite deciders discharge them before a `FinTM` class witness is produced.

### 5. Implicit computation, indexing zero, and composition

The index convention preserves the intended notion. The translation is `j=i+1`: `i<length(f(x))` corresponds exactly to the book's positive index bound. Canonical binary successor/predecessor translations are logarithmic-space operations; the supplied binary toolkit supports this, although the general reduction/composition theorem is still future work.

Pairing is `dbl x ++ [false,true] ++ Nat.bits i`. Inverting the pair recovers `x` and `Nat.bits i`; applying `bitsVal` recovers `i`. Thus the map `(x,i) ↦ pairEncode x (Nat.bits i)` is injective. At `i=0`, `Nat.bits 0=[]`, but the separator remains: for `x=[]` the encoding is `[false,true]`, not the empty word. A noncanonical payload such as `[false]` does not encode zero in `indexLang`: no natural has that canonical expansion.

The bit language returns false out of range. The length language separately distinguishes a valid zero bit from absence: for `f(x)=[false]`, the bit query at zero rejects while the length query at zero accepts. For `f(x)=[]`, both reject every index. No ambiguity or collision appears at the boundary.

The polynomial output-length conjunct is indispensable when composing implicit computations: relevant indices have logarithmic bit length relative to the original input. A future composition proof must also reject malformed or oversized query encodings, rather than silently assuming they were generated by a well-formed caller. `UnaryLogspace` intentionally omits this output bound; it is not itself interchangeable with `ImplicitlyLogspaceComputable`. For example, `g(n)=true^(2^n)` has simple unary bit/length predicates, since for a canonical index `i`, `i<2^n` is equivalent to `length(bits i)≤n`. The output is not polynomially bounded. This is why the conversion theorem's explicit length hypothesis matters.

The received `ImplicitlyLogspaceComputable.computesInSpace` gives a whole-output machine, and the time consequence follows from the count. It is one direction of the relevant equivalence, not all of Exercise 4.8 or Lemma 4.17. The received counter-program closure works for the stated one-way input model. None asserts general implicit composition.

### 6. Clock budgets and prefix preparation

`ctrVal` is ordinary little-endian value on arbitrary bit lists; canonicality is not required. In particular `[]` and an all-false list both have value zero. For canonical words, `ctrVal (Nat.bits v)=v`. Thus the clock budget generated for `g(length x)` is numerically the same budget used by `diagLang`.

The loop decrements before executing each simulated step. A positive budget permits exactly that many simulated steps; halting on the final permitted step is detected on that step, before another underflow check. The Boolean answer is false exactly when the completed output is the singleton `[true]`. An initial live machine cannot already have computed that output at time zero, so a zero budget correctly produces true without a simulated step. A machine that outputs multiple bits is distinguished by `OutReg`; it is not accepted merely because its first bit is true.

For an independent amortized check, let a positive counter word of length `l` have `j` initial false bits and `p` true bits. A successful decrement preserves length, decreases value by one, and changes the popcount to `p+j−1`. Therefore the decrease in

`4·value + 2(l−popcount) + l + 1`

is `4+2(j−1)=2j+2`. This pays for the `j` borrow moves, one simulated-machine step, and `j+1` return moves when simulation continues. Early halting only shortens the cycle. A zero-valued length-`l` counter underflows after `l+1` moves, at most its potential `3l+1`. Redundant high zeros are paid for by the length term.

Setup costs at most `tK+l+n+5`; the loop costs at most `4v+3l+1`. Their sum is the stated `tK+4l+n+4v+6`. No one-step deficit remains.

For prefix preparation, `scanPre (pairEncode α w)=dbl α ++ [false,true]`. Appending the original input gives exactly `pairEncode α (pairEncode α w)`, the self-application required by `diagSim`. The zero-work-tape preparer scans the prefix, rewinds, and copies the input within `3n+5`; empty input is covered. The total scanner also stops at an unequal `10` pair on arbitrary malformed input. That default does not affect the lemma about genuine pair encodings.

### 7. Fitness for the next chapter phases

**The convention in finding 1 is the present adoption wall.** Make every asymptotic space bound positive at every formal input length, or deliberately redefine the class. This must happen before assigning book meaning to linear space or a general hierarchy statement. Little-o hierarchy gaps can absorb machine-dependent multiplicative constants; exact constant-factor separations would require different statements. Constructibility and logarithmic lower bounds must be written into the future theorems, not inferred from unrestricted `SPACE`.

The per-input existential time in `ComputesInSpace` is appropriate. It asserts total computation by a single finite machine, and the configuration theorem derives a uniform time bound from a uniform space bound. No uniform-time existential has to be added to the definition.

For future `NSPACE`, the path quantifiers must be chosen and documented: accepting-path existence, correctness on rejecting inputs, and whether the space bound and halting requirement apply to all branches are separate obligations. The campaign's declared visited-cell convention is a reasonable basis for the intended count. A definition using only nonblank support could not reuse the present bounded-head encoding without a head-position/visited-range justification; arbitrarily long blank excursions are otherwise uncharged. The announced convention is therefore suitable for the intended theory, but should not be described as a proved equivalence to an unrestricted nonblank-only measure. No such equivalence is received. This observation does not audit a nonexistent NSPACE definition.

Configuration graphs need two additional explicit constructions. First, the current count is not an efficient vertex encoding/decoding or an adjacency CNF theorem. Second, `core` deliberately discards output, so it is insufficient by itself to label a terminal vertex as accepting. Two configurations with the same core and outputs `[true]` and `[false]` have the same core code. Acceptance must be represented in finite control or a separately bounded output summary. `CleanRun` also does not reset the input head; blank work tapes and zero work heads alone do not supply a unique terminal configuration. A normalizing return phase can provide one.

The ARM architecture is not a wall for polynomial space: `arm_space` already takes a general width `W` and bank radius `B`; the `LOGSPACE` wrapper specializes those parameters. A new nondeterministic compiler, graph-access primitives, and general implicit composition remain real work. The one-way `CounterProg.rd` is an explicit limitation and cannot simply be treated as random input access. These are unproved future interfaces, not hidden capabilities of the received toolkit.

## Adversarial instantiations

These are concrete mathematical substitutions into the received definitions and contracts. They are not presented as newly kernel-checked Lean examples.

| Test | Instantiation and calculation | Outcome |
|---|---|---|
| A1 | `s(n)=0`; use any input and `k≤spaceUsed≤c·0`. | Forces `k=0`; zero-space class is nonempty but restricted to finite-state input computation. |
| A2 | `s(n)=n`, input `[]`; the zero at this single length forces the same machine to have `k=0` everywhere. | Material collapse of intended linear space; finding 1. The same occurs for a bound positive everywhere except length seven. |
| A3 | A zero-tape machine emits a fixed Boolean and halts in one step, on every input. | Empty and universal languages belong to `SPACE s` for every `s`, even with `c=0`. No hidden positive-tape requirement. |
| A4 | A zero-tape parity scanner on `n` symbols, halting at the end in `n+1` steps. | Nonconstant language in zero space; refutes dropping the input factor below log space. |
| A5 | A zero-tape, one-state stationary self-loop, never emitting. | Space remains zero forever, but `ComputesInTime.of_spaceUsed_le` cannot be applied: its halting hypothesis fails. |
| A6 | `n=0` or `1` in `LOGSPACE`; `k=0` in the count. | `logSpace=1`; `configBound=(q+1)(n+2)`. Neither theorem divides by zero or loses the input positions. |
| A7 | `indexLang`, with `x=[]`, `i=0` and `i=1`. | Encodings are `[false,true]` and `[false,true,true]`, respectively. They are distinct; `[]` and noncanonical payload `[false]` do not enter accidentally. |
| A8 | `f(x)=[]` versus `f(x)=[false]`, query index zero. | The bit answers coincide (false), but length answers differ. The two-language definition preserves output length. |
| A9 | `g(n)=true^(2^n)` in `UnaryLogspace`. | The bit/length queries remain simple canonical-index comparisons; polynomial length fails. The extra hypothesis in its conversion theorem is necessary. |
| A10 | One register constantly equal to `B`, one abstract `goto` step. | Register stays bounded by `B`, but `sim_run`'s actual hypothesis `B+1≤B` fails. Finding 2, not a failure of `exists_tm`. |
| A11 | `whole` call, `x=[]`, empty argument list; compare with duplicate arguments `[r,r]`. | The first is permitted and has empty virtual input, not a pair. The second is excluded by `CallOK`/`PreS`. Findings 3 and the compiler's aliasing guard. |
| A12 | `valP` on `pairEncode [] [false]`; `.jeq r r`; `.jeqIn` on malformed `[]`. | Validation rejects the noncanonical payload. Self-comparison and malformed input comparison fail `PreS`, even when their abstract branch is meaningful. No application of `arm_decides` escapes those checks. |
| A13 | `ReachesB` at `T=0` with the distinguished head at `L+1`, for `L≥0`. | Relation holds reflexively; no endpoint bound follows. Finding 6. |
| A14 | Clock words `[]` and `false^l`. | Both allow zero simulated steps; the latter pays `l+1` underflow moves within `3l+1`. |
| A15 | Clock word `[true]`; machine halts with `[true]` after exactly one step, or instead needs two steps. | First case returns false; second times out and returns true. The final allowed step is included. |
| A16 | Budget two; machine emits true, then false and halts. | Completed output is `[true,false]`; clock returns true. A first-bit-only acceptance bug is absent. |
| A17 | `lenEq_mem_P` and `lenLe_mem_P` at malformed `z=[]`. | Both accept via default empty projections. Finding 5. |
| A18 | `AHalt` with `K=0`, at least one register, and the prescribed live zero-register start in `arm_decides`. | `T=0` cannot halt; at time zero `length(bits(0+1))=1`, so `1≤0` fails. The degenerate invariant does not prove every language logspace. With no registers this particular obstruction is legitimately absent. |

## Proposed machine-checkable sanity targets

These are requested follow-up statements, not claims of fresh elaboration. S1–S3 isolate the major finding using the existing visited-set API; the mathematical derivation above settles its substance. No change to tactic proofs is requested.

| ID | Exact mathematical target | Purpose |
|---|---|---|
| S1 | For every `M : FinTM Bool`, `x`, `t`, prove `M.k ≤ M.tm.spaceUsed (M.tm.initCfg x) t`. | Make the initially visited origins visible at the public interface. |
| S2 | From `M.ComputesInSpace f s` and `∃n, s n=0`, derive `M.k=0`. | Verify the zero-at-one-length propagation. |
| S3 | From `∃n, s n=0`, prove `SPACE s = SPACE (fun _ => 0)`; instantiate with `s(n)=n`. | Make the adoption convention impossible to overlook. |
| S4 | For everywhere-positive `s`, prove `SPACE s = SPACE (fun n => s n+1)`; separately prove `SPACE (fun n => s n+1)=SPACE (fun n => max 1 (s n))` for arbitrary `s`. | Document exactly when finite additive normalization is harmless. Use `s+1≤2s` or `s+1≤2 max(1,s)`. |
| S5 | `pairEncode x (Nat.bits i) = pairEncode y (Nat.bits j) ↔ x=y ∧ i=j`. | Package canonical index injectivity, including zero, from pair decoding and `bitsVal_bits`. |
| S6 | Exhibit a zero-tape constant Boolean decider and a zero-tape parity decider with the stated space and time contracts. | Bind the semantic zero-space characterization to the repository model. Full equivalence with a formal regular-language class requires an automata bridge not included here. |
| S7 | Produce the three clock cases: zero budget; exactly-one-step accepting halt with budget one; two-bit completed output with budget two. | Small executable regressions for the endpoint and output-shape contracts. |
| S8 | Prove the no-argument virtual-input identity and show `¬ValidPlain (pairEncode [] [false])`; exhibit reflexive `ReachesB` outside the box. | Lock in the boundary meanings underlying findings 3, 4, and 6. |
| S9 | Add an optional reachable-register-bound version of `CounterProg.sim_run`, retaining `s.pos≤length x` and assuming each pre-step register is at most `B`. | Deliver the broader run-bound interface if the opening docstring is retained. |

The bundle suffices to settle the numerical and logical checks in Q1–Q6 by inspection of definitions and theorem contracts. It does not settle S6's identification with a repository regular-language predicate, revision provenance, or the future graph/NSPACE interfaces. Those limits are stated rather than assumed away.

## Appendix A. All blind definition restatements

Coverage: 217 `def`, 6 `abbrev`, 17 `inductive`, and 4 `structure` declarations: **244 total**. Compiler-generated recursors and constructor functions are covered by their parent type, not counted as additional source declarations. Structure fields and instruction alternatives are included in the parent restatement. Names are local to the module shown, including nested namespaces and private definitions.

“Matches; auxiliary” means the independently obtained meaning agrees with its implementation docstring; the module-level source comparison explains why it is not being equated to a numbered book definition. A total helper outside its guarded simulation hypotheses is not thereby a correctness theorem.

### `TCSlib/Complexity/TuringMachine/UnaryTape.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ones` · 44 | The integer-indexed tape contains true precisely at positions 0 through m−1 and blanks elsewhere. | Matches; auxiliary. |
| `wrT` · 78 | An absent write request preserves the tape; a present request replaces the addressed cell, possibly with blank. | Matches; auxiliary. |

### `TCSlib/Complexity/TuringMachine/CounterProg.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Instr` · 71 | Instructions halt, jump, emit a bit, increment/decrement a natural register, test zero, print a register's many true bits, or read the next input bit. Register operands belong to Fin R. | Matches; unary-print is one abstract step, not one TM step. One-way input is explicit. |
| `St` · 93 | An abstract configuration stores an optional instruction label, natural-valued registers, a natural input cursor, and an accumulated output list. | Matches; arbitrary states need the separate cursor/register simulation preconditions. |
| `step` · 106 | Halted configurations are fixed. Otherwise execute the selected instruction, with truncated subtraction, append-only output, and input advance only when rd finds a bit; an exhausted input leaves the cursor unchanged. | Matches; auxiliary. |
| `run` · 125 | Iterate the abstract step function exactly t times, including stationary steps after halting. | Matches; auxiliary. |
| `init` · 129 | Start at the supplied label with all registers zero, input cursor zero, and empty output. | Matches; auxiliary. |
| `TSt` · 185 | Compiled control states distinguish instruction entry, decrement/zero-test return, and the outward/return scans for unary printing. | Matches; auxiliary. |
| `act` · 199 | Construct an action that changes only the selected register tape, together with the specified input move, optional output, and next state. | Matches; auxiliary. |
| `ctl` · 204 | Construct an action affecting input, output, and control only; every work tape remains stationary and unwritten. | Matches; auxiliary. |
| `tr` · 208 | Compile each instruction using a unary tape whose head is at the register's right boundary. Tests and decrement inspect the preceding cell; printing scans left while emitting true and returns right. | Matches; auxiliary. |
| `toTM` · 237 | Bundle that transition table into a finite machine with R work tapes and the selected entry label, requiring finite decidable labels. | Matches; finite labels are required here even though the raw program type is unrestricted. |
| `enc` · 246 | Represent each register by its unary tape and right-boundary head, map the optional label to compiled entry, preserve output, and clamp cursor+1 to the right input endmarker. | Matches; auxiliary. |

### `TCSlib/Complexity/TuringMachine/CounterProgRun.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Goes` · 65 | For every initial output prefix, some run of at most b abstract steps reaches the specified label, register values and cursor, appending exactly e. | Matches; universal quantification over the old output prefix supports composition. |
| `MOp` · 204 | An output-template operation either emits one fixed bit or prints one register in unary. | Matches; auxiliary. |
| `MOp.exec` · 211 | Interpret one output-template operation as a bit list at the supplied register valuation. | Matches; auxiliary. |
| `tmplInstr` · 217 | At an in-range template index emit its operation and continue to the next indexed label; out of range jump to next. | Matches; auxiliary. |
| `LinE` · 262 | A nonnegative linear expression is a list of register references, allowing repetitions, together with a natural constant. | Matches; auxiliary. |
| `LinE.val` · 265 | Evaluate the expression by summing the referenced register values with multiplicity and adding its constant. | Matches; auxiliary. |
| `linOps` · 268 | Print each referenced register, then emit one true bit per unit of the constant. | Matches; auxiliary. |
| `bitsOps` · 290 | Convert a fixed bit list into consecutive single-bit output operations. | Matches; auxiliary. |

### `TCSlib/Complexity/ClassNP/CounterProgPolyTime.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

No definition-like declarations. Its received contribution consists of theorem statements, checked in Appendix B.

### `TCSlib/Complexity/ClassNP/ExpPoly.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ExpPoly` · 42 | There are fixed natural K and k such that T(n) is at most 2 raised to K(n+1)^k for every n. | Matches this implementation normal form; not an exact restatement of a numbered chapter-3/4 definition. |

### `TCSlib/Complexity/ClassNP/PolyTimePairing.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `pairMapSnd` · 77 | Decode a pair, apply g to its second component, and re-encode; return the empty word on malformed input. | Matches; malformed input is deliberately totalized to the empty word. |
| `pairFstD` · 206 | Return the decoded first component, with the empty word as the malformed-input default. | Matches definition docstring; the later language prose needs finding 5. |
| `pairSndD` · 209 | Return the decoded second component, with the empty word as the malformed-input default. | Matches definition docstring; the later language prose needs finding 5. |

### `TCSlib/Complexity/ClassNP/PClosure.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

No definition-like declarations. Its received contribution consists of theorem statements, checked in Appendix B.

### `TCSlib/Complexity/ClassNP/Transducer.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `transduce` · 51 | Scan left to right, updating a finite-state accumulator and emitting zero or one bit for each input bit; emit nothing at the end. | Matches; auxiliary. |
| `transducerTr` · 67 | On a bit, emit the transducer's optional bit, advance input, and update state; on blank, halt without output or work-tape activity. | Matches; auxiliary. |
| `transducerTM` · 73 | Bundle the transducer as a finite machine with zero work tapes and the given initial state. | Matches; zero work tapes are permitted, including on empty input. |

### `TCSlib/Complexity/SpaceComplexity/Basic.lean`

Source comparison: Definitions 4.1, 4.5, and 4.16, with the explicit conventions examined in Q2 and Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ComputesInSpace` · 85 | For every input there exists a finite time by which M has halted with output f(x), and the total work-tape space visited through that same time is at most s(length x). No uniform time bound is required. | Matches the deterministic measure of Def. 4.1 and the declared function/output adaptation. Q2 explains the zero-bound effect. |
| `DecidesInSpace` · 91 | Compute exactly the singleton Boolean membership indicator of L under ComputesInSpace. | Matches the declared singleton-indicator convention; both answers require halting. |
| `SPACE` · 110 | Choose one natural constant c and one finite machine, uniformly over all inputs, that decides L within c·s(n) visited work cells. No positivity, constructibility, or eventual-bound qualification is included. | Finding 1: dropping the standing lower-bound convention makes even one zero globally consequential. |
| `logSpace` · 120 | The bound is Nat.log 2 n plus one, including value one at n=0 and n=1. | Positive normalization is explicit and safe at n=0,1; it supplies the Def. 4.5 asymptotic scale. |
| `LOGSPACE` · 125 | Apply SPACE to logSpace. | Matches Def. 4.5 with the documented positive normalization; Q3 checks its time consequence. |
| `indexLang` · 129 | A word is accepted exactly when it is the pairing of some x and the canonical binary expansion of some natural i for which p(x,i) holds. Other encodings are rejected. | Matches the declared canonical pairing convention; malformed/noncanonical words are excluded, including at index zero. |
| `ImplicitlyLogspaceComputable` · 138 | Require a uniform polynomial output-length bound C(length x+1)^c, a LOGSPACE language for true output bits with false outside the list, and a LOGSPACE language for indices strictly below its length. | Def. 4.16 with the declared zero-based translation and all-length polynomial normalization; Q5 finds no lost strength. |

### `TCSlib/Complexity/SpaceComplexity/ConfigCount.lean`

Source comparison: implementation of the deterministic configuration argument in Claim 4.4/Theorem 4.2; the explicit input factor and omitted output are examined in Q3.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `core` · 73 | Discard output from a configuration, retaining optional control state, input position, work-tape contents, and work-head positions. | Matches; adequate for time-to-halt, but acceptance/output reconstruction needs extra data in a future graph. |
| `posCode` · 258 | Translate an integer by B, truncate below zero, and clamp above 2B to obtain a code in Fin(2B+1). It is not globally injective. | Matches; injectivity is only asserted on the bounded interval, not globally. |
| `coreCode` · 269 | Encode the core by recording each work tape on the window from −B through B and clamping each work-head coordinate into that window's finite index set. | Matches; finite-window completeness relies on reachable bounded cores and blankness outside. |
| `configBound` · 311 | Multiply the number of optional states, n+2 input positions, three symbols at every cell of every length-(2s+1) tape window, and 2s+1 head choices per work tape. Output is omitted. | Matches the displayed formula; conservative deterministic count with explicit n factor. Q3 supplies the independent derivation. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Seg` · 63 | A segment is a bit list paired with a Boolean indicating whether to double each bit. | Matches; auxiliary. |
| `render` · 66 | Return the underlying word or its bit-doubled version according to the segment flag. | Matches; auxiliary. |
| `rlen` · 69 | Return the underlying length, multiplied by two precisely when the segment is doubled. | Matches; auxiliary. |
| `vword` · 81 | Render segments in order with the separator false,true between consecutive segments; the empty list renders to empty. | Matches; auxiliary. |
| `off` · 87 | Compute a segment offset by adding each preceding rendered length plus two. Beyond the supplied list it is a total recursive default, not a validity certificate. | Matches; auxiliary. |
| `seg` · 93 | Retrieve a segment by index, defaulting to the empty undoubled segment. | Matches; auxiliary. |
| `TPos` · 197 | A virtual input position is a left boundary, a word-cell index with a parity bit, or a right boundary. | Matches; auxiliary. |
| `wlen` · 204 | Return the undoubled word length of the selected segment, using seg's default. | Matches; auxiliary. |
| `TPos.Valid` · 207 | Only cell positions are constrained: their index must be below the segment's undoubled length. Both boundaries are always valid. | Matches; segment-index range is a separate premise in the movement/symbol theorems. |
| `cellOff` · 212 | For a doubled segment use twice the cell index plus its parity bit; otherwise use the cell index and ignore parity. | Matches; auxiliary. |
| `vpos` · 217 | Translate a segment-local position to the global input coordinate: left at its offset, cells at offset+1+cellOff, right at offset+1+rendered length. | Matches; auxiliary. |
| `tmove` · 233 | Move one virtual cell, handling doubled-bit parity, empty segments, separators, and saturated exterior endmarkers; correctness is restricted to valid segment positions. | Matches its guarded movement contract; total default behavior outside valid positions is not a simulation claim. |
| `vsym` · 370 | A cell exposes its underlying bit. Interior left/right boundaries expose true/false respectively; the two exterior boundaries expose blank. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Program.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Mode` · 67 | Call input modes select either the whole input with bit doubling, or the initial run of true bits without doubling. | Finding 3: paired-input prose needs the nonempty-argument qualification. |
| `Mode.seg0` · 76 | Construct that first virtual segment from x; unaryFst takes the maximal initial run of true bits literally. | Matches the function; the general pair-shape shorthand has finding 3. |
| `argSegs` · 81 | Turn argument words into segments, doubling all except the last. | Matches; auxiliary. |
| `CallSpec` · 114 | A call records a finite decider index, input mode, ordered list of register arguments, and yes/no continuation labels; distinct arguments are not a field-level requirement. | Matches; distinctness is deferred to CallOK, not enforced by this structure. |
| `RProg` · 128 | A program consists of a raw multitape machine and an optional call specification at each label. The raw model imposes no finiteness on labels. | Matches; the raw semantic model is broader than the finite class-witness interface. |
| `callSegs` · 135 | Prepend the mode-selected input segment to the argument-register words rendered by argSegs. | Matches; zero arguments produce one segment and no separator, as in finding 3. |
| `CSt` · 147 | Compiled states distinguish ordinary execution, decider simulation with virtual-head bookkeeping and first output bit, input rewind, and register rewind phases. | Matches; auxiliary. |
| `gstep` · 166 | Update virtual segment/parity/direction bookkeeping and the physical head motion for one requested virtual move, using character/boundary and endpoint flags. | Matches; auxiliary. |
| `toFin` · 179 | Clamp the natural segment number to m to obtain an element of Fin(m+1). | Matches; auxiliary. |
| `segDbl` · 182 | Segment zero is doubled exactly in whole mode; subsequent segments are doubled except the last argument. | Matches; auxiliary. |
| `segReg` · 186 | Select the argument register for a positive segment number; out-of-range requests default to register zero, requiring m>0. | Matches; the m>0 witness and call-validity hypotheses prevent misuse of the default register. |
| `isCharRead` · 191 | In the unary prefix segment only true is a character; in other segments any nonblank symbol is a character. | Matches; auxiliary. |
| `virtSym` · 195 | Translate a physical symbol plus segment/boundary information into the symbol the decider sees, inserting virtual separators and endmarkers. | Matches; auxiliary. |
| `regMove` · 201 | Move only the selected register head, writing no cells. | Matches; auxiliary. |
| `nextRet` · 206 | Continue restoring argument heads while both argument and register indices are in range; otherwise resume the yes/no continuation. | Matches; auxiliary. |
| `dIdle` · 216 | The decider-bank action neither writes nor moves any head. | Matches; auxiliary. |
| `ctr` · 224 | Run ordinary program steps on one tape bank; at calls simulate a decider on a virtual concatenation, retain its first output bit, then rewind input and argument heads. Decider-bank erasure is delegated to the decider's clean-run contract. | Matches; taking only the first output bit is sound at calls because CleanRun requires exactly one bit. |
| `compileTM` · 284 | Build the raw compiled machine with m+kD tapes and initial ordinary-program state at l₀. | Matches; a raw machine, with finite-state bundling deferred to compileFinTM. |
| `seam` · 291 | Embed a program configuration into the compiled machine, preserving input, registers and output while adding blank decider tapes at head position zero. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `trackPos` · 52 | Translate local left/cell/right positions into physical coordinates −1/c/undoubled word length. | Matches; auxiliary. |
| `TPos.isCell` · 58 | Test whether a virtual position is a cell rather than a boundary. | Matches; auxiliary. |
| `Consistent` · 63 | Left/right boundaries require the corresponding direction flag; doubled cells require the stored parity to agree. Undoubled-cell parity is unconstrained. | Matches; auxiliary. |
| `regPos` · 202 | For argument registers, put already-passed segments at their right boundary, future segments at −1, and the active segment at its current physical position; preserve other register heads. | Matches; auxiliary. |
| `inPos` · 210 | Use the current physical input coordinate when segment zero is active; otherwise park input at the end of its selected prefix. | Matches; auxiliary. |
| `TrackRel` · 216 | Relate a compiled and decider configuration by virtual input position, unchanged register tapes, matching decider-bank tapes/heads, correct register/input heads, and preserved caller output. | Matches; caller output and all register tapes are preserved while virtual heads move. |
| `SimRel` · 231 | A live compiled simulation and a live decider have the same decider state, TrackRel, and an accumulator equal to the decider output's first bit. | Matches; auxiliary. |
| `HaltRel` · 238 | A compiled return-entry state corresponds to a halted decider satisfying TrackRel; its result is the first decider output bit, defaulting false. | Matches; singleton output is a stronger call-level premise, not part of this general relation. |

### `TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `mkCfg` · 43 | Assemble a compiled configuration from separate register and decider tape/head banks and the supplied control, input position, and output. | Matches; auxiliary. |
| `leftSide` · 271 | Determine whether a particular argument lies to the right of the virtual head or is the active argument approached from its left boundary. | Matches; auxiliary. |
| `retPos` · 387 | Reset heads of argument registers already processed by the restoration loop to zero; retain all other positions. | Matches; auxiliary. |
| `RegBox` · 392 | Nonargument heads retain their original positions; argument heads lie between −1 and the corresponding word's length, inclusively. | Matches; argument bounds are inclusive and include the empty-buffer boundaries. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Call.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `CleanRun` · 53 | From blank tapes at zero and the specified state/input, a finite run halts with exactly [b], blanks every work tape, resets every work head to zero, and keeps each head within [−B,B] throughout. Final input position is unrestricted. | Matches; final input position is intentionally unrestricted and caller return restores it. Q4. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `tapeWord` · 52 | If the entire tape is the buffer encoding of a finite word, choose that word; otherwise return empty. This is a mathematical, noncomputable decoder. | Matches; mathematical choice, with actual buffer shape required before an atomic call is compiled. |
| `regWords` · 68 | Decode each register tape using tapeWord. | Matches; auxiliary. |
| `rstep` · 73 | Halted configurations stay fixed; noncall states take an ordinary step; calls atomically choose a continuation from the oracle on the virtual input, reset input to position one, and preserve registers/output. | Matches; atomic oracle semantics are discharged by CallOK rather than asserted free of cost. |
| `rrun` · 87 | Iterate the atomic-call step n times. | Matches; auxiliary. |
| `CallOK` · 100 | At any actual call require distinct argument registers, input at position one, valid buffer tapes and zero argument heads, adequate register intervals, and a clean decider run with the prescribed oracle answer and radius B. | Matches its declaration; module list has the nonexistent plural spelling in finding 8. |
| `compileFinTM` · 214 | Bundle compileTM as a finite machine when both program and decider control types are finite and decidable. | Matches; finite decidable program and decider labels are explicit. |

### `TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `CPh` · 41 | Cleanup phases mark the final head cell, seek the right boundary, erase leftward, and return to the marked origin. | Matches; auxiliary. |
| `CleanSt` · 53 | Control states initialize tracking, simulate the original state, or clean one selected tape in one cleanup phase. | Matches; auxiliary. |
| `idleK` · 65 | A bank action with no writes or head movement. | Matches; auxiliary. |
| `clAct` · 69 | Apply the specified data/marker writes and common head motion to one matching pair of tapes, leaving every other tape and input/output unchanged. | Matches; auxiliary. |
| `clNext` · 75 | Advance to cleanup of the next tape, or halt after the final tape. | Matches; auxiliary. |
| `cleanTM` · 80 | Double the tape bank, mark the origin and visited interval during simulation, preserve emitted output, and upon halting erase data/markers and restore each head to zero. Zero-tape simulation needs no cleanup loop. | Matches; doubles the data bank for markers, including correct k=0 behavior. |
| `ccfg` · 112 | Assemble a cleanup-machine configuration from separate data and marker banks. | Matches; auxiliary. |
| `wr` · 137 | Perform an optional cell update, distinguishing no write from writing blank. | Matches; auxiliary. |
| `markI` · 180 | Mark the origin by true, other points in the inclusive interval by false, and all remaining points blank. The origin is marked even if outside the interval. | Matches the total definition; the origin marker is unconditional, while meaningful interval uses contain zero. |
| `PB` · 184 | Every work head has absolute coordinate at most the supplied integer B. | Matches; pointwise head-radius predicate, not a total visited-space predicate. |
| `eraseAbove` · 275 | Keep cells at coordinates at most p and blank all cells above p. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `markSet` · 54 | Mark origin true, other members of a finite set false, and all remaining coordinates blank. | Matches; auxiliary. |
| `simSt` · 58 | Map a live state to simulation mode; map a halted state to first cleanup, or directly to halt when there are no tapes. | Matches; auxiliary. |
| `visB` · 68 | Collect head positions at times strictly below t in the original run from state q on V. | Matches; the strict time cutoff differs from the inclusive visited-space measure and is used for marker bookkeeping. |
| `simCfg` · 72 | Embed the original run at time t with matching heads, output and input, plus marker tapes for visB and the origin. | Matches; auxiliary. |
| `stSt` · 220 | Select cleanup of tape i when i<k; otherwise use the halted state. | Matches; auxiliary. |
| `stg` · 223 | Represent a cleanup stage with all tape pairs of index below i blank and their heads at zero, preserving the remaining banks, input and output. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `padTM` · 50 | Run an original transition on the first k tracks of a K-track machine, supplying blanks for absent tracks and idling extra tracks. Semantic simulation requires k≤K separately. | Matches; k≤K is a theorem premise, not a condition on the total construction. |
| `padCfg` · 58 | Keep original tracks whose indices exist and fill additional tracks with blank tapes/zero heads; copy control, input and output. | Matches; auxiliary. |
| `sigmaTM` · 110 | Combine machines with a common tape count using an optional tagged control state. Its default state halts; a tagged state runs the corresponding machine. | Matches; auxiliary. |
| `sigCfg` · 120 | Embed a component configuration by tagging its live state with the component index; preserve other configuration fields. | Matches; auxiliary. |
| `bankK` · 151 | Take the maximum work-tape count of the finite decider family, with zero for an empty family. | Matches; finite maximum is zero for an empty family. |
| `BankS` · 158 | Use an optional dependent tagged union of the component machines' state types as the bank state type. | Matches; auxiliary. |
| `bankTM` · 161 | Pad all deciders to bankK, combine their state spaces, and apply the cleanup transformation, using twice bankK tapes. | Matches; its tape count includes the extra cleanup-marker bank. |
| `bankStart` · 165 | Start the cleanup wrapper at the tagged initial state of a chosen component decider. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `bitsVal` · 44 | Evaluate a bit list in little-endian binary; the empty list evaluates to zero. | Matches; auxiliary. |
| `incW` · 50 | Increment a little-endian bit list by propagating carry through initial true bits, extending an all-true word. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `regCfg` · 66 | Replace one register tape/head and set a live control label, preserving the rest of the configuration. | Matches; auxiliary. |
| `regAct` · 76 | Write and move only one selected register tape and continue to a specified live label; input/output are unchanged. | Matches; auxiliary. |
| `incCAct` · 139 | Propagate increment carry by turning true into false and moving right; at false or blank write true and begin leftward return. | Matches; auxiliary. |
| `incBAct` · 145 | Move left through nonblank cells and then step right from the first blank to the continuation. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `decW` · 42 | Implement binary predecessor on canonical little-endian words, with empty fixed at zero; its total behavior on noncanonical words is merely the given recursion. | Matches the canonical predecessor contract; no general normalization claim for arbitrary bit lists. |
| `Canon` · 49 | A word is empty or its final, most significant bit is true. | Matches; zero is empty, so a nonempty all-false word is excluded. |
| `decDAct` · 114 | Borrow through false bits, change the first true to false, or start returning on blank; a follow-up phase determines whether the top bit must be removed. | Matches; auxiliary. |
| `decLAct` · 122 | Inspect the cell after the changed bit; at blank return to erase the top bit, otherwise return without erasure. | Matches; auxiliary. |
| `decEAct` · 129 | Erase the current bit and move left to the decrement-return phase. | Matches; auxiliary. |
| `toEndAct` · 317 | Scan right through a register word, then step left from the blank to the supplied continuation. | Matches; auxiliary. |
| `clrEAct` · 382 | Erase nonblank cells moving left; at blank step right and continue. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `halfLAct` · 47 | Move left, replacing the current bit by the carried optional bit and carrying its previous bit; at blank step right and finish. | Matches; auxiliary. |
| `halfSt` · 65 | Select the no-carry, false-carry, or true-carry phase according to an optional bit. | Matches; auxiliary. |
| `eqCfg` · 205 | Set a live state and both selected register heads to the same integer position; preserve all tapes, input and output. | Matches; auxiliary. |
| `mv2Act` · 210 | Move each selected head by the supplied direction once, even when the two indices coincide; write nothing. | Matches the total action; two-independent-register simulation additionally assumes distinct indices. |
| `eqCAct` · 229 | Compare the two current symbols, scan right while equal and nonblank, then start the appropriate leftward return for equality or inequality. | Matches; auxiliary. |
| `eqBAct` · 234 | Return both heads left while the first tape is nonblank, then step right to the chosen continuation. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ValidPlain` · 46 | The input is a pairing of a unary true word and a canonical binary word. | Matches this definition docstring; the instruction-level shorthand omits canonicality (finding 4). |
| `ValidPair` · 50 | The input pairs a unary true word with a pair of two canonical binary words. | Matches this definition docstring; the instruction-level shorthand omits canonicality (finding 4). |
| `xCfg` · 63 | Set a live control state, input position, and one work-head coordinate, preserving tape contents, other heads and output. | Matches; auxiliary. |
| `xAct` · 72 | Move input and one selected work head without writing, and choose a live continuation. | Matches; auxiliary. |
| `rejAct` · 76 | Emit false and halt, leaving input/work positions and tapes unchanged. | Matches; auxiliary. |
| `inSym` · 99 | Coordinate zero is blank; positive coordinate q reads the zero-based input index q−1 with out-of-range blank. | Matches; auxiliary. |
| `tRun` · 220 | Count the maximal initial run of true bits. | Matches; auxiliary. |
| `valUAct` · 280 | Scan an initial true run while toggling parity; accept a false delimiter only at even parity and reject other endings. | Matches; auxiliary. |
| `valSAct` · 287 | Require the next delimiter symbol to be true; otherwise reject. | Matches; auxiliary. |
| `valWAct` · 293 | Scan a binary word remembering its last bit; reject if the final remembered bit is false, otherwise begin input rewind. Empty words pass. | Matches; auxiliary. |
| `FragOK` · 339 | On a good input, a finite call-free fragment returns to next with original data/output and reset input; on a bad input it halts after appending false. Intermediate configurations only change control/input and retain the selected head at p. | Matches; intermediate obligations are half-open, with separate target/rejection equalities. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `skipAct` · 117 | Skip initial true symbols and then advance past the first nontrue symbol into the second skip phase; standalone malformed-input behavior is not validation. | Matches a fragment action; it is not itself a total validator. |
| `cmpAct` · 123 | Compare input and register symbols, advancing both while equal and nonblank; otherwise begin register return with the equality result. | Matches; auxiliary. |
| `backAct` · 128 | Return a register head left to its first blank, then one step right to the continuation. | Matches; auxiliary. |
| `rewAct` · 134 | Return the input head left to blank, then one step right to the continuation. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `scanPairs` · 47 | Parse repeated equal-bit pairs up to a false,true delimiter, rejecting malformed pairs and noncanonical preceding words; return the suffix after the delimiter. | Matches; tests both pair shape and canonicality of the decoded first word. |
| `Rejects` · 105 | Some finite run halts after appending false and preserving designated head positions; every earlier configuration has the prescribed unchanged data/output shape and makes no calls. | Matches the separate endpoint condition plus strict-prefix invariant. |
| `Reaches` · 112 | Some finite run reaches the exact target, with every earlier configuration preserving the prescribed data/output/head shape and making no calls. A zero-step witness imposes no intermediate conditions. | Matches the formal relation; its zero-step case does not certify the target invariant. |
| `wSt` · 215 | Choose the word-validation phase for no previous bit, previous false, or previous true. | Matches; auxiliary. |
| `valP1Act` · 301 | Read the first bit of a doubled pair and remember it; reject blank. | Matches; auxiliary. |
| `valP2Act` · 307 | Recognize the delimiter subject to canonicality of the previous word, or require the second bit to equal the first and continue with updated last bit; reject other input. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `pskip1Act` · 42 | Remember whether the first bit of the next candidate pair is true, advancing input; nontrue defaults to the false phase. | Matches; auxiliary. |
| `pskip2Act` · 48 | At a false,true pair finish skipping; otherwise advance to scan the next pair. Correct use presupposes valid encoding. | Matches; well-formed-input hypotheses justify skipping without full validation. |
| `dcmp1Act` · 116 | Read and remember the first bit of a doubled input pair, advancing input. | Matches; auxiliary. |
| `dcmp2Act` · 122 | At the delimiter test that the register word is exhausted; otherwise compare its current symbol with the remembered first bit, advancing or returning. Validation of equal input pairs is a separate precondition. | Matches; auxiliary. |
| `ReachesB` · 303 | Some run reaches the exact target while all earlier configurations make no calls, preserve tape contents/output and other heads, and keep the selected head in [−1,L]. | Finding 6: the docstring must distinguish the strict prefix from the endpoint. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Ins` · 50 | Register instructions increment, decrement, clear, halve, test zero/oddness/equality, call a decider, return a Boolean, validate encoded input, or compare a register with encoded input components. The syntax itself carries no safety proofs. | Finding 4 concerns validation payloads; comparison/call restrictions are separately supplied by PreS. |
| `ARM` · 81 | An abstract register machine is a function from labels to instructions. | Matches; auxiliary. |
| `plainWord` · 84 | Drop the initial true run and the following two symbols, regardless of whether they form valid encoding. | Matches on the advertised format; total malformed-input behavior is guarded by PreS at comparisons. |
| `pairWords` · 87 | Decode the suffix after that same prefix as a pair, defaulting to two empty words on failure. | Matches on the advertised format; default empty components are guarded by PreS at comparisons. |
| `AConf` · 107 | Store an optional current label, natural-valued registers, and an optional final Boolean answer; there is no abstract input head or output stream. | Matches; auxiliary. |
| `astep` · 111 | Execute the specified arithmetic/test/call instruction with fixed input x; return or failed validation halts with a Boolean. Input comparisons use totalized parsers even on invalid inputs. Halted configurations are fixed. | Matches; mathematical oracle semantics need compilation preconditions to become executable. |
| `arun` · 134 | Iterate astep exactly n times. | Matches; auxiliary. |
| `Ph` · 141 | A finite phase type enumerates entry, arithmetic scans, comparison returns, validation, and parsing subphases of compiled instructions. | Matches; auxiliary. |
| `goAct` · 155 | Change only the control state to the given live state. | Matches; auxiliary. |
| `retAct` · 158 | Emit one Boolean and halt without other changes. | Matches; auxiliary. |
| `rw2Act` · 161 | Rewind input left while nonblank, then step right to the continuation; the selected work head stays fixed. | Matches; auxiliary. |
| `junkAct` · 167 | Halt without output or any tape/input change. | Matches; auxiliary. |
| `insTr` · 171 | Implement each instruction by finite phases over canonical binary register buffers. Inapplicable phases and ordinary execution of a call halt via junkAct; calls are handled by the separate call map. | Matches; canonical buffers and instruction preconditions are theorem hypotheses, not field-level guarantees. |
| `armTr` · 275 | At a label and phase, use insTr for the instruction stored at that label. | Matches; auxiliary. |
| `insCall` · 280 | Only a call instruction at its start phase produces a call specification, with continuations lifted to start phases. | Matches; auxiliary. |
| `armCall` · 289 | Look up insCall from a paired instruction label and phase. | Matches; auxiliary. |
| `armProg` · 294 | Combine armTr and armCall into an RProg initialized at the selected label's start phase. | Matches; auxiliary. |
| `aseam` · 300 | Represent a live abstract configuration with canonical binary register tapes, all heads zero, input at one, chosen output prefix, and control at the instruction's start phase. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Mid` · 44 | Every live control state is noncall, and each register head lies between −1 and W; tape contents/output are otherwise unrestricted. | Matches; no canonical-buffer claim is hidden in this intermediate head/call invariant. |
| `SimTo` · 131 | A finite atomic-call run reaches c′ exactly and satisfies Mid at every strictly earlier time. | Matches; strict-prefix invariant only, with endpoint facts supplied by the target configuration. |
| `HaltsWith` · 136 | A finite run halts after appending exactly b; all final register heads are bounded, and every strictly earlier configuration satisfies Mid. | Matches; unlike SimTo alone, this relation explicitly bounds final heads. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Pre` · 44 | At equality tests require distinct registers; at input comparisons require the appropriate valid encoding; at calls require distinct arguments and a clean bounded decider run with the correct oracle answer; other instructions impose nothing. | Matches; this contains oracle realizability as well as syntactic restrictions. |
| `Inv` · 72 | All register heads lie in [−1,W], and the current configuration satisfies CallOK with that interval and decider radius B. | Matches; combines inclusive head positions with call preconditions at this configuration. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `AReach` · 45 | Some finite abstract run reaches a′ and satisfies G at every strictly earlier time; the endpoint is not required to satisfy G. | Matches the compositional half-open convention; no endpoint invariant is implied. |
| `AHalt` · 50 | Some finite abstract run halts with answer b and satisfies G at every strictly earlier time; a previously halted input configuration may have a zero-step witness. | Matches; the class theorem fixes a fresh live initial state, preventing a vacuous pre-answered witness. |
| `PreS` · 137 | Retain only the syntactic/input-validity portions of Pre: distinct equality operands, valid inputs for input comparison, and duplicate-free call arguments. No oracle correctness is asserted. | Matches; equality aliasing, malformed input comparisons, and duplicate arguments are excluded explicitly. |

### `TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean`

Source comparison: auxiliary machinery for Definition 4.16 and the restricted composition construction. General Lemma 4.17 is not received; see Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `St` · 59 | Finite phases ask output length, ask the current bit, emit either bit, increment the index with return, and finish. | Matches; auxiliary. |
| `tm` · 64 | Emit the selected bit and increment one binary index register; the ask/bit/done labels otherwise halt in the raw table. | Matches; auxiliary. |
| `prog` · 75 | Use two oracle deciders: ask whether the current index is in range, then ask its output bit; raw transitions emit it and increment. | Matches; auxiliary. |
| `cfg` · 83 | Represent the chosen phase/index with one canonical binary register, zero head, input at one, and the supplied output prefix. | Matches; auxiliary. |
| `Shape` · 123 | Either the configuration is an ask/bit seam with index at most F, or it is noncall with its register head in [−1,W]. | Matches its permissive invariant purpose; it is not an exact characterization of reachable configurations. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

No definition-like declarations. Its received contribution consists of theorem statements, checked in Appendix B.

### `TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `dblLang` · 45 | Accept exactly pairings of a unary true word of length n with the canonical binary expansion of 2n. | Matches the worked implementation example; it is a helper language, not the textbook EVEN example verbatim. |
| `St` · 51 | Finite states validate the input, count its doubled unary prefix, rewind, compare the binary suffix, and accept/reject. | Matches; auxiliary. |
| `tr` · 59 | Validate the encoding, count every true in the doubled unary prefix using one binary register, compare that count with the suffix, and return a Boolean. | Matches; auxiliary. |
| `prog` · 83 | Use that one-register raw machine with no calls. | Matches; auxiliary. |
| `o` · 88 | The unique empty-family oracle function, since there are zero deciders. | Matches; auxiliary. |
| `K` · 94 | Construct a one-register configuration containing bits(v), with the supplied input/head positions and state and empty output. | Matches; auxiliary. |
| `Rch` · 111 | A finite atomic-call run reaches the target while its single work head stays in [−1,W] at every earlier time. | Matches its strict-prefix formal contract; endpoint facts must be read from the separate target. |
| `nilTM` · 273 | A zero-work-tape, one-state machine that halts in one step without output. | Matches; empty output means it is a dummy machine, not itself a Boolean-language decider. |

### `TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean`

Source comparison: auxiliary machinery for Definition 4.16 and the restricted composition construction. General Lemma 4.17 is not received; see Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `uBit` · 53 | Accept canonical pairs (unary n,bits i) exactly when output bit i of g(n) is true; missing bits default false. | Matches; auxiliary. |
| `uLen` · 57 | Accept those canonical pairs exactly when i is strictly less than the length of g(n). | Matches; auxiliary. |
| `UnaryLogspace` · 61 | Require the unary bit and length languages to be in LOGSPACE. No output-length bound is included. | Matches the expressly weaker auxiliary notion; polynomial output length is absent (note 10, Q5). |
| `unaryExt` · 96 | Extend g to all bit strings by using g(length x) on all-true words and the empty word otherwise. | Matches; extension rejects nonunary arguments by producing empty output. |
| `ltLang` · 162 | Accept canonical pairs (unary n,bits i) exactly when i<n. | Matches; auxiliary. |
| `Lb` · 168 | Finite labels validate input, test a doubled counter by an oracle, compare the other counter to input, increment, and return. | Matches; auxiliary. |
| `A` · 175 | Validate; enumerate a counter and its double from zero, stopping at doubled n using dblLang, and accept if the input index is encountered before n. | Matches; auxiliary. |
| `vv` · 186 | A two-register valuation assigning a to register zero and b to register one. | Matches; auxiliary. |
| `orc` · 202 | The sole oracle answers membership in dblLang. | Matches; auxiliary. |
| `G` · 214 | Require PreS and bound both register values by 2(length y+1). | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean`

Source comparison: auxiliary machinery for Definition 4.16 and the restricted composition construction. General Lemma 4.17 is not received; see Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `rg` · 55 | Embed an original register among the first R of R+3 registers. | Matches; auxiliary. |
| `rP` · 57 | Reserve register R for the simulated input cursor. | Matches; auxiliary. |
| `rO` · 59 | Reserve register R+1 for the simulated output count. | Matches; auxiliary. |
| `rT` · 61 | Reserve register R+2 for a temporary print counter. | Matches; auxiliary. |
| `ev` · 65 | Combine original register values with the three cursor/output/temporary counters. | Matches; auxiliary. |
| `Lb` · 119 | Finite-control constructors represent validation, simulated instruction entry, output counting, print/read substeps, and either Boolean answer. Finiteness requires finite original labels. | Matches; finite control is obtained from finite original labels by the explicit instance. |
| `A` · 172 | Build an ARM deciding an output bit or length query of a CounterProg run. Simulate arithmetic directly, replace reads by unary bit/length oracle calls, and count output until the queried position is reached. | Matches the restricted unary-query simulator; no random-access input or general composition theorem is asserted. |
| `ans` · 219 | In length mode return whether p is in range of O; in bit mode return O's bit at p with false as the default. | Matches; auxiliary. |
| `cf` · 223 | Construct a live abstract configuration with supplied simulator label/values and no answer yet. | Matches; auxiliary. |
| `G` · 233 | Require the simulator's PreS condition and bound every register by B. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean`

Source comparison: auxiliary machinery for Definition 4.16 and the restricted composition construction. General Lemma 4.17 is not received; see Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Bd` · 57 | Every original register value, input cursor, and output length is at most B. | Matches; bounds numeric values, cursor, and total output length, rather than merely register bit widths. |

### `TCSlib/Complexity/SpaceComplexity.lean`

Source comparison: import facade for the received §4.1/§4.3 implementation, with the same declared deviations as its constituent modules.

No definition-like declarations. This is an import facade.

### `TCSlib/Complexity/TimeHierarchy/ClockMachine.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `OutReg` · 82 | Summarize an output word as empty, exactly one specified Boolean, or at least two bits. | Matches the required output summary. Its three constructors give four values because the singleton constructor carries a Boolean. |
| `OutReg.ofList` · 89 | Classify a list by that summary, preserving the unique bit only for singleton lists. | Matches; auxiliary. |
| `OutReg.push` · 95 | Update the summary when an optional next output bit is appended. | Matches; auxiliary. |
| `ctrVal` · 123 | Evaluate an arbitrary little-endian bit list as a natural binary value, allowing noncanonical high zero bits. | Matches; permits redundant high zero bits and agrees with natural value on canonical bits. |
| `ctrPop` · 128 | Count true bits in a bit list. | Matches; auxiliary. |
| `ClockState` · 220 | Finite control tracks budget computation, counter/input rewind, and alternating decrement/simulation-return phases carrying the simulated state and output summary. | Matches; auxiliary. |
| `ctrIdx` · 230 | Select the one counter tape between K's work-tape bank and W's work-tape bank. | Matches; auxiliary. |
| `ctrAction` · 233 | Operate only on that counter tape and control state; input, output, and the other banks remain unchanged. | Matches; auxiliary. |
| `clockTr` · 238 | Simulate K while redirecting its output to a binary counter tape; rewind counter/input; decrement before each W step. A zero-budget underflow returns true; W halting returns the negation of having output exactly [true]. | Matches; final permitted halt is detected before another underflow, and full singleton output is checked. |
| `clockTM` · 275 | Bundle clockTr with K.k+1+W.k tapes and initial control simulating K's initial state. | Matches; auxiliary. |
| `kCfg` · 295 | Embed a K configuration, placing its output on the counter tape at its right boundary and leaving W's work tapes blank; the clock's output is empty. | Matches; auxiliary. |
| `ctrCfg` · 373 | Assemble a clock configuration from frozen K banks, a counter tape/head, W's configuration, and explicit clock state/output. | Matches; auxiliary. |
| `cScanCfg` · 435 | Represent the counter rewind at coordinate j−1 with counter word s, frozen K banks, and blank W work tapes. | Matches; auxiliary. |

### `TCSlib/Complexity/TimeHierarchy/ClockLoop.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ctrBound` · 215 | The loop budget is 4·ctrVal(s)+2(length(s)−ctrPop(s))+length(s)+1. | Matches; Q6 independently checks the decrement potential and zero case. |
| `loopAnswer` · 219 | Negate the conjunction that W is halted after v steps from c and its full accumulated output is exactly [true]. | Matches; tests the whole accumulated output, not just its first bit. |

### `TCSlib/Complexity/TimeHierarchy/CodePrefix.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `scanPre` · 63 | Copy input pairs until and including the first unequal pair; if there is no such pair, copy the entire input, including a possible final unpaired bit. | Matches; malformed inputs have a total default, while the self-pairing lemma assumes a genuine pair. |
| `PreState` · 87 | Finite states scan a paired prefix, rewind input, and copy the whole input. | Matches; auxiliary. |
| `preTr` · 98 | Emit scanned prefix bits, rewind to the beginning, emit all input bits, and halt. It uses no work tapes. | Matches; auxiliary. |
| `preTM` · 113 | Bundle preTr as a finite zero-work-tape machine starting at prefix scan. | Matches; auxiliary. |

### `TCSlib/Complexity/TimeHierarchy/Diagonal.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `code` · 107 | Choose one witness of the existing EffectiveMachineCode existence theorem; no efficient evaluation of this Lean choice is asserted. | Matches; choice fixes an existing witness and does not introduce an axiom or computational-cost promise. |
| `univTM` · 110 | Choose the finite universal machine supplied for that fixed code system. | Matches; its simulation constant is code-dependent, as declared. |
| `diagSim` · 124 | Compose prefix preparation with the chosen universal machine using buffered composition. | Matches; auxiliary. |
| `diagLang` · 129 | Accept x exactly when diagSim fails to halt with the singleton output [true] within g(length x) steps. This includes timeout, rejection, and nonsingleton output. | Matches; timeout and non-singleton output are included in diagonal acceptance. Upper computability needs constructible g. |

### `TCSlib/Complexity/TimeHierarchy/Separation.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `twoPowTM` · 45 | A private zero-work-tape machine emits false for every input bit, then true at the first blank and halts, producing the little-endian representation of 2^(input length). | Matches; output includes the final true bit at n=0 as well as for nonempty inputs. |

### `TCSlib/Complexity/TimeHierarchy.lean`

Source comparison: import facade for the received §3.1 implementation at the explicitly declared quadratic-overhead strength.

No definition-like declarations. This is an import facade.

The anonymous `Fintype (Lb Λ)` instance in `CounterProgSim.lean:134` supplies a finite enumeration of the simulator labels when the original label type is finite. It adds no unbounded register/state resource or new semantic oracle. Automatically derived finite/decidable instances similarly concern the displayed finite control types.

## Appendix B. Headline delivered-strength checks

The “book comparison” column refers to the compact source baseline above. “Auxiliary” explicitly means that the named result is an implementation theorem without a separately stated textbook version. Matching such a theorem to its own docstring does not promote it to the entire chapter theorem. Every item in the modules' “Main results” lists is covered below; a few important additional interfaces are included. The absent advertised `arm_step` is recorded as absent, not silently replaced with an invented theorem.

### Time hierarchy and exponential separation

| File · headline theorem(s) | Book comparison | Delivered statement and docstring check |
|---|---|---|
| `ClockMachine` · `clockTM_setup` | Auxiliary for Theorem 3.1. | Given the actual computation of budget word `s` in `tK`, reaches the loop with that counter and a fresh simulated initial configuration in at most `tK+length(s)+length(x)+5`. Frozen budget-machine tapes may remain nonblank; they are not reused as simulated tapes. Matches. |
| `ClockLoop` · `clockTM_loop` | Auxiliary for Theorem 3.1. | From an arbitrary **live** simulated configuration, halts within `ctrBound s` and emits `loopAnswer` for the value of `s`. No assumption that `s` is canonical. The live-state hypothesis is explicit; Q6 checks the potential and endpoint. Matches. |
| `ClockLoop` · `clockTM_spec` | Auxiliary for Theorem 3.1. | Given `K.ComputesInTime x s tK`, computes the negation of `W.ComputesInTime x [true] (ctrVal s)` within `tK+4 length(s)+length(x)+4 ctrVal(s)+6`. Tests halting and the exact singleton output. Matches. |
| `CodePrefix` · `preTM_computes` | Auxiliary self-application preparation. | Computes `scanPre x ++ x` within `3 length(x)+5` on all words, including malformed encodings and empty input. Matches. |
| `CodePrefix` · `scanPre_pairEncode_append` | Auxiliary self-application identity. | On genuine `pairEncode α w`, the prepared word is `pairEncode α (pairEncode α w)`. It requires no efficient code recognizer or infinite set of codes for one machine. Matches. |
| `Diagonal` · `univTM_spec` | Existing universality interface consumed by the construction. | For each code separately there is a fixed simulation constant valid on all inputs. This is the declared code-dependent constant, not a universal constant across codes. Matches. |
| `Diagonal` · `diagLang_mem_DTIME` | Upper-bound part of the received version of Theorem 3.1. | `TimeConstructible g` implies `diagLang g ∈ DTIME (fun n => g n+1)`. This is a total decider, even when the inner simulation never halts. Matches the documented normalization. |
| `Diagonal` · `diagLang_not_mem_DTIME` | Lower-bound part of the received version. | For every constant and lower threshold, a larger length satisfying the quadratic domination inequality suffices to exclude `diagLang g` from `DTIME T`. Constructibility is not needed for this purely lower-bound assertion. It proves class nonmembership, not an exported per-input disagreement-count formula. Matches when “infinitely often” refers to its numerical hypothesis. |
| `Diagonal` · `time_hierarchy` | Compare Theorem 3.1 baseline. | Constructible `g` and eventual domination of every `A(f+n+1)²` imply `DTIME f ⊂ DTIME (g+1)`. No constructibility of `f`. This is weaker in the growth gap and different at zero from the book baseline, as prominently declared. Q1 finds no undeclared weakening. |
| `Diagonal` · `time_hierarchy_of_pos` | Same comparison. | Adds `∀n,0<g n` and concludes strict inclusion into `DTIME g`. Positivity is exactly what permits all-length multiplicative removal of `+1`. Matches. |
| `Separation` · `timeConstructible_two_pow` | Constructible exponential example used by the separation. | The function `n↦2^n` meets the imported constructibility interface, including empty input. The displayed zero-tape generator emits its binary value in `n+1` steps. Matches. |
| `Separation` · `eventually_poly_le_two_pow`, `eventually_poly_sq_le_two_pow` | Auxiliary numerical domination. | Every `A(n+1)^K`, and then every `A(n^k+1+n+1)²`, is eventually at most `2^n`, uniformly after a threshold depending on the fixed parameters. The square uses exponent `2k+2` and factor `9A`; Q1 independently derives them. Matches. |
| `Separation` · `dtime_poly_ssubset_dtime_two_pow` | Polynomial/exponential instance of the hierarchy. | For each natural `k`, strictly separates `DTIME(n^k+1)` from `DTIME(2^n)`. Includes `k=0`; the positive normalization is intentional. Matches. |
| `Separation` · `P_ssubset_EXP`, `P_ne_EXP` | Chapter-3 polynomial/exponential consequence. | The common exponential diagonal language lies outside every polynomial member class, so the union is strictly smaller than `EXP`. `P_ne_EXP` follows from strictness. It does not rely on the invalid inference that a union of proper subclasses must be proper. Matches. |

### Space classes, configuration counting, and compilation

| File · headline theorem(s) | Book comparison | Delivered statement and docstring check |
|---|---|---|
| `Basic` · `ComputesInSpace.mono`, `SPACE.mono` | Elementary consequences of the declared space definition. | Pointwise domination at **all** lengths weakens the bound. Neither theorem asserts eventual-bound equivalence. Valid as stated; finding 1 concerns interpretation of the underlying unrestricted class. |
| `ConfigCount` · `abs_pos_lt_card_visited` | Auxiliary to Claim 4.4. | For a position actually in one tape's visited set from initialization, absolute coordinate is strictly below that set's cardinality. The interval starts around zero; it is not a claim about arbitrary configurations. Matches. |
| `ConfigCount` · `ComputesInTime.of_spaceUsed_le` | Deterministic count-to-time part of Claim 4.4/Theorem 4.2. | A computation already known to halt by `t`, with total visited space through `t` at most `s`, computes the same output within `configBound M (length x) s`. Halting is explicit and essential. The theorem is not a nondeterministic search or a CNF-adjacency result. Matches. |
| `ConfigCount` · `LOGSPACE_subset_P` | Def. 4.5 specialization of the count/time baseline. | Every language in the positive-normalized `LOGSPACE` is in `P`. Fixed tape/state counts and space multiplier produce the polynomial in Q3. Short inputs and zero tapes are covered. Matches. |
| `ConfigCount` · `ComputesInSpace.computesFunInTime`, `polyTimeComputable_of_computesInSpace` | Function version of the same implication. | A function computed by one finite machine in a constant multiple of `logSpace` is computed by that same machine within the explicit polynomial from Q3, and hence is polynomial-time computable. Unread output cannot postpone a first halt without distinct cores. Matches. |
| `Machines/Layout` · `vpos_tmove`, `inputSymbol_vpos` | Auxiliary for §4.3 virtual-input simulation. | Under segment-index and local-validity hypotheses, translated head movement and symbols agree with the real virtual word, including separators, empty segments, and clamped endmarkers. No correctness outside those hypotheses is asserted. Matches. |
| `Machines/Program` · `step_seam_prog` | Auxiliary compiler correspondence. | A live noncall program transition and its compiled transition agree at the seam; decider tapes remain idle. Explicitly excludes call nodes. Matches. |
| `Machines/Sim` · `gstep_tmove`, `sim_step` | Auxiliary virtual-input correspondence. | Guarded bookkeeping follows virtual movement; a related live decider step yields the corresponding continuing or returning compiled simulation configuration. Register data and caller output are preserved. It is local simulation, not a complete clean-call theorem. Matches. |
| `Machines/CallReturn` · `ret2_run`, `retR_run`, `regs_run` | Auxiliary return discipline. | With the specified return states, tracking relation, and valid buffers, restores input and then argument heads within the stated register box. Does not claim to erase arbitrary dirty decider tapes. Empty buffers/endmarkers are included. Matches. |
| `Machines/Call` · `call_run` | Auxiliary realization of one virtual-input oracle call. | Given clean decider termination, buffer/position validity and distinct arguments, a compiled call returns to the selected continuation, restoring heads and respecting the charged boxes. It does not realize an arbitrary uncomputable oracle. Matches. |
| `Machines/Compile` · `compile_correct` | Compiler infrastructure for the §4.3 construction. | For a bounded abstract prefix whose actual calls satisfy `CallOK`, reaches exactly the endpoint's seam with inclusive physical head bounds. A halting abstract endpoint therefore gives halting. The formal result is more general than the conditional halting description, not weaker. Q4. |
| `Machines/Compile` · `compile_space` | Same infrastructure with visited-space accounting. | Adds abstract halt/output hypotheses and finite label types, yielding a finite machine computation with bound `sum (hi−lo+1).toNat+kD(2B+1)`. All banks and endpoints are counted. Matches. |
| `Machines/CleanSweep` · `goR_run`, `erase_run`, `back_run` | Auxiliary cleanup construction. | Given the specified marked interval, control phase, and tape shapes, each sweep reaches its stated endpoint, blanks the intended region, and preserves the radius bound. They do not promise cleanup of arbitrary tapes without those interval premises. Matches. |
| `Machines/Clean` · `cleanTM_run` | Auxiliary space-preserving normalization. | Given a halt and a per-tape visited-cardinality bound `s`, the doubled-bank machine halts with the same output, blank work tapes, zero work heads, and inclusive radius `s`. Input head normalization is not in the conclusion. Matches the main-result description. |
| `Machines/Bank` · `bank_cleanRun` | Auxiliary finite family of reusable deciders. | From actual space-deciding contracts, each chosen bank entry returns its membership bit cleanly with radius `max(s_j(length V),1)`. Padding and marker tapes explain the extra one and doubled bank. Matches. |
| `Machines/ARMRun` · `arm_run` | Auxiliary abstract-to-register-machine compilation. | A live-start abstract run that halts with answer `b`, meeting `Pre` and the successor bit-width bound at every earlier step, yields a halting program with old output followed by `[b]`, bounded final heads, and the intermediate call/head invariant. Endpoint bounds are explicit here. Matches. |
| `Machines/ARMRun` · `arm_space` | Same construction composed with the concrete compiler. | From zero-register initialization and the same run premises, gives a finite machine computation using at most `m(W+2)+kD(2B+1)` cells. It is parametrized by general widths, not restricted to logarithmic widths. Matches. |
| `Machines/ARMProof` · `arm_decides` | Implementation route to the Def. 4.5 class. | One finite ARM, fixed logspace oracle languages, and all-input `AHalt` correctness under `PreS` plus `length(bits(v+1))≤K logSpace n` imply language membership in `LOGSPACE`. No polynomial abstract-time premise. The oracle contracts are discharged, not retained in the result. Matches. |
| `Machines/ARMKit` · `arm_decides_poly` | Same class wrapper with a convenient numeric invariant. | Replaces the successor bit-width bound by `v≤C₀(n+1)^c₀` and retains the other `arm_decides` requirements. Computes a suitable logarithmic width. It is about register values, not about polynomially many abstract steps. Matches. |

### Binary, parser, and implicit-computation toolkit

| File · headline theorem(s) | Book comparison | Delivered statement and docstring check |
|---|---|---|
| `Machines/Bin` · `bitsVal_bits`, `bits_injective` | Auxiliary canonical index arithmetic. | Natural binary encoding is decoded exactly and is injective; no claim that arbitrary noncanonical words are injectively decoded. Empty representation of zero is included. Matches. |
| `Machines/Bin` · `bits_succ`, `length_bits_le`, `length_bits_mono` | Auxiliary register-width arithmetic. | `incW(bits n)=bits(n+1)`; `n<2^m` bounds width by `m`; numeric monotonicity bounds canonical width. Matches. |
| `Machines/Lib` · `inc_run` | Auxiliary register operation. | Under the supplied transition/no-call conditions and initial buffer/head shape, increments a canonical register, restores its head, and stays in `[-1,length(bits(n+1))]`. The extra width for carry is present. Matches. |
| `Machines/FragDec` · `dec_run`, `toEnd_run`, `clr_run` | Auxiliary register operations. | Canonical predecessor is truncated at zero; scanning/clearing has the specified buffer and head preconditions and returns the promised tape/head shapes. The head may visit the blank boundary. Matches. |
| `Machines/Frag` · `half_run`, `eq_run`; re-exported `dec_run`, `clr_run` | Auxiliary register operations. | Halving produces canonical integer division by two; equality chooses the corresponding branch and restores heads, with **distinct-register** premise. Imported predecessor/clear results are not new proofs in this module. Matches. |
| `Machines/ParsePlain` · `rewind_x`, `validPlain_iff`, `valPlain_run` | Auxiliary guarded input format. | Rewind returns to the specified input position; validity includes canonicality and unary-prefix parity; validation either returns to its continuation with the input reset or halts with false. It rejects malformed inputs. Matches these definitions; instruction shorthand has finding 4. |
| `Machines/Parse` · `canon_eq_bits`, `jeqPlain_run` | Auxiliary input/register comparison. | Canonical words equal the bits of their value. On a valid plain encoding, the comparison reaches the selected branch with restored positions under its stated buffer/transition hypotheses. Not a theorem that the fragment safely handles arbitrary malformed inputs without validation. Matches. |
| `Machines/Parse2` · `valPair_run` | Auxiliary nested-pair validator. | Checks the outer unary prefix and both canonical inner components; success preserves the promised data and returns, failure appends false and halts. Matches. |
| `Machines/ParseCmp` · `jeqPairSnd_run`, `jeqPairFst_run` | Auxiliary nested-pair comparisons. | With valid encoded input and canonical register buffer, reaches the branch corresponding to the selected component equality within the specified prefix bounds. Finding 6 concerns what the helper relation alone says about its endpoint, not these explicit target configurations. |
| `Machines/ARMSim` · advertised `arm_step`; actual `sim_inc`, `sim_dec`, `sim_clr`, `sim_half`, `sim_jz`, `sim_jodd`, `sim_jeq`, `sim_call`, `sim_ret`, `sim_valP`, `sim_valQ`, `sim_jeqIn`, `sim_jeqFst`, `sim_jeqSnd` | Auxiliary instruction simulation. | No theorem named `arm_step` is received. The individual simulations supply the arithmetic, validation, branch, call, and return cases, with their validity/aliasing/decider hypotheses; whole-run assembly is in `arm_run`. Finding 8. |
| `Machines/ARMKit` · `vword_unary₁`, `vword_unary₂` | Auxiliary virtual-input identities. | For **one or two** arguments on a correctly paired unary-prefix input, produces the stated single/nested pair exactly. These identities are sound and do not claim the zero-argument case. Matches. |
| `Machines/DblLang` · `dblLang_mem` | Auxiliary worked logspace language. | Decides all encodings of unary `n` paired with `bits(2n)` and rejects malformed/noncanonical encodings, in `LOGSPACE`. The intermediate `run_valid` reaches a yes/no continuation; `ret_step` supplies the final output/halt. The class theorem supplies the full claim. Matches. |
| `ImplicitPoly` · `ImplicitlyLogspaceComputable.computesInSpace` | Constructive consequence of Def. 4.16; one direction of the associated equivalence. | Given the entire definition, including polynomial output length, produces some finite machine and constant with the whole function computed in logarithmic visited space. Empty outputs halt and do not emit an extra bit. Does not claim the converse or general composition. Matches. |
| `ImplicitPoly` · `ImplicitlyLogspaceComputable.polyTimeComputable` | Function time consequence. | The same hypothesis implies polynomial-time computability using the previous result and deterministic counting. Matches. |
| `UnaryLogspace` · `UnaryLogspace.implicitlyLogspaceComputable` | Restricted unary-domain conversion. | Requires `UnaryLogspace g` **and** a polynomial bound on `length(g n)`; concludes implicit computability of `unaryExt g`. Nonunary inputs have empty output. Matches the explicit extra premise. |
| `UnaryLogspace` · `ltLang_mem`, `unaryLogspace_replicate` | Auxiliary unary example. | Canonical unary/index pairs satisfying `i<n` form a logspace language; hence `n↦true^n` has logspace unary bit and length languages. Covers zero and rejects bad encodings. Matches. |
| `CounterProgSim` · `CPSim.sim_step` | Auxiliary for the restricted closure construction. | With correct unary input-query oracles, a bounded counter-program step either yields the correctly encoded successor simulator state or answers the requested output-position question. Requires the declared current/next bounds and cursor/output-position conditions. Matches. |
| `CounterProgSimRun` · `CPSim.sim_run` | Same restricted construction. | From a live counter state whose output has not passed the query, a halting bounded counter run yields `AHalt` with its bit/length answer, maintaining the simulator's polynomial-value invariant. The two input-query oracle contracts are explicit. Matches. |
| `CounterProgSimRun` · `UnaryLogspace.counterProg` | Special case related to the Lemma 4.17 construction, not the general lemma. | Unary-logspace input family plus one finite counter program halting in `C(n+1)^c` abstract steps with output `g n` implies `UnaryLogspace g`. The polynomial is in the unary parameter `n`, not an unconstrained output or virtual-input length. One-way reads are retained. Matches. |
| `CounterProgSimRun` · `CounterProg.length_out_le` | Auxiliary size bound. | A polynomial step bound from zero initialization yields a polynomial output-length bound, despite a unary-print instruction emitting a whole register in one abstract step. It does not grant polynomial length to arbitrary `UnaryLogspace` functions. Matches. |

### Counter programs and polynomial/exponential supporting results

| File · headline theorem(s) | Book comparison | Delivered statement and docstring check |
|---|---|---|
| `TuringMachine/UnaryTape` · `update_ones_succ`, `update_ones_pred` | Auxiliary unary-register representation. | Writing the next unary cell extends the represented natural; erasing its last occupied cell represents predecessor under the corresponding index hypotheses. Blank and zero cases use the stated guarded form. Matches. |
| `TuringMachine/CounterProg` · `sim_step` | Auxiliary finite-machine compilation. | For a live abstract state with cursor at most input length and registers at most `B`, produces the encoded one-step successor within `2B+3` concrete steps. This charges unary printing and return scans; it does not price every instruction as one concrete step. Matches. |
| `TuringMachine/CounterProgRun` · `sim_run` | Auxiliary run compilation. | Requires the cursor bound and **initial** values plus `t` at most `B`, and simulates `t` abstract steps within `t(2B+3)`. Finding 2 records the broader docstring wording. |
| `TuringMachine/CounterProgRun` · `exists_tm` | Auxiliary whole-program compilation. | A run from all-zero initialization that has halted at abstract time `t` is computed by the finite machine within `t(2t+3)` steps, with exactly the abstract output. Finite decidable labels are required. Matches; unaffected by finding 2. |
| `TuringMachine/CounterProgRun` · `Goes.trans`, `goes_loop` | Auxiliary program algebra. | Sequential bounds add and emitted suffixes concatenate, uniformly over existing output prefixes. The loop theorem assumes the stated body/control contracts and countdown invariant and yields its finite accumulated bound; it is not arbitrary-loop termination. Matches. |
| `TuringMachine/CounterProgRun` · `goes_tmpl`, `flatMap_exec_linOps` | Auxiliary output templates. | Installed template instructions emit their specified micro-operation list and continue; a linear-expression template emits a unary list of the sum with multiplicity plus constant. Matches. |
| `TuringMachine/CounterProgRun` · `run_pos_le`, `run_out`, `run_init_out_le` | Auxiliary growth bounds. | Cursor increases by at most one per abstract step; output only gains a suffix; a zero-initialized run emits at most `t(t+1)` bits. Arbitrary preloaded large registers are not covered by the last bound. Matches. |
| `ClassNP/CounterProgPolyTime` · `polyTimeComputable`, `polyTimeComputable_of_goes` | Auxiliary route to polynomial-time function witnesses. | Uniform finite program and all-input halting/output contract within `C(n+1)^c` imply polynomial-time computability; compilation gives a bound `(2C²+3C)(n+1)^(2c)`. The `Goes` variant retains the same halting/output obligations. Matches. |
| `ClassNP/ExpPoly` · `ExpPoly.of_le`, `ExpPoly.add`, `ExpPoly.mul`, `ExpPoly.comp_poly`, `expPoly_exp`, `expPoly_poly` | Auxiliary exponential-bound algebra. | The all-length `2^(K(n+1)^k)` envelope is downward closed, closed under sum/product and polynomial reindexing, and contains the indicated polynomial and exponential examples with suitable fixed parameters. Does not claim closure under arbitrary function composition. Matches. |
| `ClassNP/ExpPoly` · `ExpPoly.mem_EXP` | Supporting `EXP` normalization. | A language in `DTIME T` with such an envelope belongs to the repository `EXP`; fixed constants and finite short lengths are absorbed with positive exponential budgets. Matches. |
| `ClassNP/PolyTimePairing` · `polyTimeComputable_of_linear`, `polyTimeComputable_const` | Auxiliary FP constructions. | A uniform linear-time machine contract gives an FP witness; any one fixed finite word is a constant FP function. No constant may depend on the input. Matches. |
| `ClassNP/PolyTimePairing` · `PolyTimeComputable.pairMapSnd`, `.pairEncode`, `.append` | Auxiliary FP closure. | Under polynomial-time hypotheses, maps a decoded payload, pairs two computed outputs, or concatenates them in polynomial time. Pair-map malformed input uses its explicit empty default. Matches. |
| `ClassNP/PolyTimePairing` · `polyTimeComputable_unary`, `polyTimeComputable_polyUnary` | Auxiliary bounded output generators. | Produces true strings of length `length x` or `C(length x+1)^d` in polynomial time for fixed `C,d`, including empty input. Matches. |
| `ClassNP/PolyTimePairing` · `polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`, `polyTimeComputable_pairSwap`, `polyTimeComputable_pairConcat`, `polyTimeComputable_prepend` | Auxiliary encoding operations. | The specified total projections, rearrangements, and fixed prefix operation are polynomial-time computable. Default behavior on malformed encodings belongs to the total function being proved computable. Matches. |
| `ClassNP/PolyTimePairing` · `polyTimeComputable_ite`, `polyTimeComputable_and`, `polyTimeComputable_lenLe`, `polyTimeComputable_lenEq` | Auxiliary tests/branching. | Polynomial tests and branches compose to the displayed Boolean and length-test functions, with the actual totalized projections. No arbitrary uncomputed predicate is promoted to polynomial time. Matches the formal interfaces. |
| `ClassNP/PClosure` · `mem_P_iff_polyTimeComputable`, `mem_P_of_test`, `test_of_mem_P` | Supporting language/function bridge. | Membership in `P` is equivalent to polynomial computation of the singleton membership bit, with the supplied Boolean-test formulations. The output is exactly one bit. Matches. |
| `ClassNP/PClosure` · `preimage_mem_P`, `inter_mem_P`, `union_mem_P`, `empty_mem_P`, `univ_mem_P`, `mem_P_of_atoms` | Supporting `P` closure. | Polynomial preimages and finite Boolean combinations preserve `P`; the finite atom family has a fixed size, so its truth function is finite data. Includes the constant languages. Matches. |
| `ClassNP/PClosure` · `lenEq_mem_P`, `lenLe_mem_P` | Supporting length predicates. | The predicates of total decoded projections are in `P`; malformed words with both defaults empty are accepted. Finding 5 records the mismatch with “pairs whose …”. |
| `ClassNP/PClosure` · `lenEq_preimage_mem_P`, `lenLe_preimage_mem_P` | Supporting comparisons of computed outputs. | For polynomial-time functions `f,g`, equality or the stated inequality of their output lengths defines a language in `P`. Actual pairing in the reduction makes the malformed-input default irrelevant. Matches. |
| `ClassNP/Transducer` · `transducerTM_computes`, `polyTimeComputable_transduce` | Auxiliary finite-state streaming construction. | A finite-state, at-most-one-output-bit-per-input-bit transducer computes its recursively defined output within `length x+1` concrete steps using zero work tapes; therefore the function is in FP. The last step halts and emits no extra bit. Matches. |

Both facade modules contain imports and documentation only. No additional theorem strength is inferred from their names.

## Notation glossary

| Notation used in this report | Meaning |
|---|---|
| `[]`, `[b]`, `++` | Empty bit list, singleton bit list, list concatenation. |
| `length x`, `n` | Input length; `n` is a natural unless stated otherwise. |
| `k`, `q` | Fixed work-tape count and number of live control states in the counting discussion. |
| `s`, `B`, `W` | Space function or numerical space bound; head radius; register bit-width/range parameter, as specified locally. |
| `A,C,K,c` | Fixed natural constants or exponents, quantified as stated; their roles are local to each calculation. |
| `ℓ` | `Nat.log 2 n` in the logarithmic configuration-bound calculation. |
| `bits i`, `Nat.bits i` | Canonical little-endian binary word for natural `i`; zero is encoded by the empty word. |
| `dbl x`, `pairEncode x w` | Repeat each bit of `x` twice; then append separator `[false,true]` and `w` to encode a pair. |
| `true^n`, `false^n` | A list of `n` copies of that Boolean, not exponentiation of a Boolean. |
| `⊂`, `⊆` | Proper inclusion and inclusion. The report uses `⊂` in the Lean statement's strict sense. |
| “core” | State, input head, work tapes, and work heads, with output omitted. |
| “seam” | A program configuration embedded in the compiled machine with blank, reset decider tapes. |
| “half-open” invariant | Required at times `0≤t<T`; the endpoint at `T` needs a separate assertion. |

Audit ends. No source modification or gate closure is asserted.
