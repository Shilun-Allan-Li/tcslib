# Gate 03a, round 2: external audit findings

**Verdict: DO NOT CLOSE — 0 blockers, 2 majors, 3 minors.**

The two new public interfaces match their statements and survive the adversarial instantiations below. The outstanding majors concern false claims in the repaired documentation: uniform `Computes` still does not characterize computation of an arbitrary string function on its entire domain, and the inversion example does not establish the claimed bound for `ofString` after padding. Neither finding is a counterexample to a Lean theorem. Both can be repaired without changing the existing theorem statements. The previously acknowledged duplication remains scheduled debt, not a new major.

**Pin:** `e28773ef3bda6f7b4b112ec1657427bfef01e374`; comparison base `a3c5fa8b72e50939822f22364647dc844a3914a0`. Audit brief: the bundle's first section, `03a-pack-r2.md`, with the round-1 statement-audit brief and severity guide.

**Materials and limits.** I examined the resolutions, review, section A of the repair diff, the eleven current Lean files, DESIGN, policy, duplication ledger, and the four `evidence/a2/` records. Section B was checked where a resolution relies on it. I read the attached source at book pp. 23–24, 26–28, 69–73, 181 and 189 (PDF pages are 12 greater), including a rendered check of p. 189's formula. I also checked the relevant omitted dependency/interface excerpts at the exact pin through GitHub; links are below. This is a definitions, statements, docstrings and proof-sketch audit, not a tactic-proof audit. I did not run Lean or independently reproduce the maintainer's execution logs.

## Findings

Paths below are relative to `TCSlib/` unless they begin with `briefs/`.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | major | `Complexity/Randomized/PPT.lean:40`, `:234` · `NUPPT.Computes`; DESIGN D3; resolution 1 | The repair identifies `∃ A, A.Uniform ∧ A.Computes f` with efficient computation of `f` and calls it Definition 24.6 proper. This remains false for arbitrary `f : List Bool → List Bool`. | `Computes` constrains `f` only on `advInput n y`. A uniform constant-output machine therefore satisfies it for functions that are uncomputable off that domain. Counterexample 1 gives explicit equations. The cited converse, `Closure.lean:417`, correctly proves polynomial-time computability only of `z ↦ f (advInput (pairFstD z).length (pairSndD z))`. Source Definition 24.6 quantifies over every input string. | Qualify the new prose, including DESIGN D3: uniform `Computes` expresses computation on the canonical parameter/argument encodings. State the actual normalized converse, rather than a converse for unrestricted `f`. If a full-domain interface is needed later, add it separately; no such addition is required to repair this documentation. |
| R2-2 | major | `Cryptography/Asymptotic/OneWay.lean:196` · `FunFamily.ofString`, section B1; resolution 15 | The new example claims that the typed inversion success is at most the success against a length-preserving one-way `g` plus `2^{-n/2}`. That claim does not hold for the documented `ofString f p`, which also pads/truncates `f`'s output. | Take `p(n)=n` and the length-preserving one-way function `g(x)=h(x.take ⌈n/2⌉) ‖ 0^{⌊n/2⌋}`, conditional on a length-preserving one-way `h`, exactly the kind of existence assumption already used by the docstring. For the docstring's special-preimage `f`, every padded output at length `2k` is `z ‖ 0^k`, and the length-`2k` preimage `0^k ‖ z` always works. Typed success is 1. See Counterexample 2. The pinned definition confirms that output is read with `getD i false`. | State separately the costs of output padding and of rejecting wrong-length preimages. Restrict the quantitative example explicitly to the raw experiment with a length restriction on the inverter, not to `ofString f p`; or replace it with an example proved for the padded family. In `Adversary.lean:104`, retain the precise condition that output length determines input length; the parenthetical “non-constant output length” needs the `PolyExpr` qualification. |
| R2-3 | minor | `Cryptography/Asymptotic/Ensembles.lean:119` · `Ensemble`; review §#2 | “The efficiently samplable ensembles … are the dyadic ones” overstates the characterization; the review also says that an ensemble whose seed type is `Fin 3` is never samplable. | Dyadic laws need not have a uniform efficient sampler: the point mass at an uncomputable bit `H(n)` is dyadic, but exact samplability would compute `H`. Conversely, a constant map from `Fin 3` is a point mass and is samplable. A law with an atom of mass `1/3`, rather than the seed type by itself, gives the intended obstruction. | Say “every efficiently samplable ensemble has dyadic laws; the converse need not hold.” Correct the review's `Fin 3` sentence to specify a sampler with a non-dyadic output law. The rational-law and fixed-length repairs themselves are correct. |
| R2-4 | minor | `briefs/pass-shelat-ch5-8/duplication-ledger.md:36` · DL-9; resolutions 8/M1 | The ledger's enumeration omits the very `Ensemble.blocks` copy named in finding 8. | `Ensembles.lean:197` explicitly describes its private `blocks` as a copy of `FunFamily.blocks`. DL-9 says “six copies plus an inverse” but lists only six locations including the inverse, and omits `Ensemble.blocks`. The payback text also omits its removal in 03a. | Add `Ensemble.blocks`, its file, and its removal/re-pointing to DL-9. Family-level acknowledgment and clean-up part 2 after #195 are already recorded; this is incomplete accounting, not unacknowledged duplicate debt. |
| R2-5 | minor | `Cryptography/Asymptotic/Ensembles.lean:189` · `Ensemble.push`; resolution 18 | Padding is described as “lossy otherwise” when the output length is not exactly the target length. Loss is possible, not inevitable. | If the output is one bit and the target length is two, `padFin 2 [b]=[b,false]` is injective on the possible outputs. Even the variable-length support `{[],[true]}` is preserved injectively by padding to one bit. | Replace “lossy otherwise” with “can be lossy otherwise” and state that exact target length is a sufficient condition for faithful representation. The definition and `Indist.push` theorem need no change. |

The two major classifications concern materially misleading new source/interface claims. I found no downstream theorem shown false by either example, so neither is a blocker. R2-2 is included to verify the expressly claimed resolution of row 15, not to reopen the rest of gate 03b.

## Counterexamples supporting the findings

Here `⟨a,b⟩` denotes the existing `pairEncode a b`; `fst` and `snd` denote its existing total projections. Bits `0,1` mean `false,true`.

### 1. Uniform `Computes` can hold for an uncomputable full-domain function

Choose a noncomputable function `H : ℕ → Bool`, and define

\[
f_{\mathrm{bad}}(w)=
\begin{cases}
[H(|\operatorname{snd}w|)]&\operatorname{fst}w=[0],\\
[]&\text{otherwise}.
\end{cases}
\]

Let `A` be `ofPolyTimeUniform` of the constant function `[]`, with zero coins. Then `A.Uniform` and `A.runAt n y r=[]`. For every `n,y`,

\[
\operatorname{fst}(\operatorname{advInput}(n,y))=1^n\ne[0],
\qquad
f_{\mathrm{bad}}(\operatorname{advInput}(n,y))=[]=A.\operatorname{runAt}(n,y,r).
\]

Consequently `A.Computes f_bad`. On the other hand, for every `m`,

\[
f_{\mathrm{bad}}(\langle[0],0^m\rangle)=[H(m)].
\]

A computable full-domain evaluator for `f_bad` would compute `H`, a contradiction. Thus adding `Uniform` removes the advice counterexample but does not remove the domain restriction. The stated theorem `Computes.polyTimeComputable` remains correct: its normalized argument always lies in that domain. This example uses only the published pair-projection equations, not malformed-pair behavior.

### 2. Padding invalidates the repaired inversion example

This is a mathematical counterexample conditional on the same existence of length-preserving one-way functions assumed by the docstring; it is not a claim to have proved that such functions exist or constructed a Lean certificate.

Let `h` be a length-preserving one-way function. For `|x|=n`, define

\[
g(x)=h(x.\operatorname{take}\lceil n/2\rceil)\mathbin{\|}0^{\lfloor n/2\rfloor}.
\]

Then `g` is polynomial-time and length-preserving. It is one-way: at either length `n=2k` or `n=2k-1`, an inverter given `h(u) ‖ 0^{n-k}` yields, by taking the first `k` bits of its successful answer, a preimage of `h(u)`. The input prefix `u` is uniform. A non-negligible success sequence for `g` has a non-negligible even- or odd-length subsequence, giving a polynomial-time non-uniform inverter for `h` on that subsequence. The change from `n` to `k` is linear.

Now use precisely the special-preimage function from the repair:

\[
f(x)=
\begin{cases}
w&x=0^k\mathbin{\|}w,\ |w|=k,\\
g(x)&\text{otherwise}.
\end{cases}
\]

Its raw, unrestricted experiment is indeed inverted by `y ↦ 0^{|y|} ‖ y`. But the actual `ofString f .var` family, denoted here by `F_n`, is

\[
F_n(x)=\operatorname{pad}_n(f(x)),\qquad |x|=n.
\]

At `n=2k`, all its outputs have the form `z ‖ 0^k`: the special branch pads `w` to `w ‖ 0^k`, and the other branch already has this form by the definition of `g`. Moreover, for every `z∈{0,1}^k`,

\[
F_{2k}(0^k\mathbin{\|}z)
=\operatorname{pad}_{2k}(z)
=z\mathbin{\|}0^k.
\]

The inverter that returns `0^k ‖ y.take k` therefore has the required input length and succeeds with probability **1 on every even parameter**. Success against one-way `g`, even allowing a reduction to another efficient inverter, is negligible; adding `2^{-k}` cannot bound 1 eventually. The claimed bound concerns the unpadded length-restricted experiment, and cannot be transferred to this wrapper without an additional argument.

### 3. Dyadic and padding edge cases

For the dyadic issue, take `ℓ=1`, seed type `Unit`, and output `[H(n)]`. If it were `Samplable`, every coin string of its exact sampler would yield that bit: each string has positive probability in the finite uniform coin space. Running the polynomial-time sampler on the all-zero coin string would compute `H(n)`. Thus even a point-mass ensemble can fail `Samplable`.

For the opposite seed-type issue, `σ n=Fin 3` with constant output `[false]` has a dyadic point-mass law and a zero-coin constant sampler. For the padding issue, `[false]` and `[true]` become the distinct strings `[false,false]` and `[true,false]`; padding to a longer fixed length need not lose information.

## New public declarations: independent restatement

### `NUPPT.exists_compParam` (`Closure.lean:209`)

Given a machine `A` and polynomial-time string functions `pre,post`, there is a machine `B` with exactly the same coin polynomial, advice-bound polynomial and advice function, satisfying, for every `n` and every string `y,r`,

\[
B.\operatorname{runAtL}(n,y,r)
=\operatorname{post}\!\left(
 \left\langle1^n,
 A.\operatorname{runAtL}\bigl(n,\operatorname{pre}(\langle1^n,y\rangle),r\bigr)
 \right\rangle\right).
\]

**Matches the docstring.** Both processors receive the parameter; neither receives advice or coins directly. The equation is for arbitrary list coins, not merely correctly sized lists. Advice equality also preserves uniformity in both directions. The statement does not claim to retain `A`'s time constants, nor should it.

The new sketch assembles these functions from polynomial-time projections, pairing and `A.output`, then packages the result with the unchanged advice and coins. This gives precisely the displayed equation. `exists_comp` has its original statement and is the special case where both processors discard the first component.

### `polyTimeComputable_stateFind` (`Repetition.lean:241`)

For each input `x`, the state is initialized by `start x`; its next value is `step ⟨x,current state⟩`. Assume `start`, `step`, the Boolean acceptance test and the output reader are polynomial-time. If:

- the first accepting index `N x` is at most `R(|x|)`;
- every state through index `N x`, including that index, has length at most `B(|x|)`;
- the test is false before `N x` and true at `N x`;

then `x ↦ out ⟨x, orbit start step x (N x)⟩` is polynomial-time computable.

**Matches the docstring.** The state-length bound is on the second component, not the whole encoded pair. No bound after the first success is required. `N` need not be supplied as a computable function: the machine discovers its value by the polynomial-time test. The first-success hypotheses prevent `N` from acting as an arbitrary oracle.

The sketch's guarded orbit supplies the arbitrary-word bound required by `iterateFind`. Precomposing with `⟨x,start x⟩` enlarges the fuel bound harmlessly: monotonicity of `R` ensures the search still includes `N x`. Publicizing this theorem changes visibility, not its mathematical statement. The independently checked `StateLoop.orbit` equations agree with this reading.

### Moved declaration: `TCSlib.Cryptography.negligible_zero`

Its full name and statement are unchanged. For every exponent, choose threshold 1; for `n≥1`, `|0|=0<1/n^c`. Moving it to `Foundations/Negligible.lean` is appropriate, and DESIGN D2 now records the one-lemma exception. The remaining duplicate is explicitly deferred as DL-13.

## Adversarial instantiations of the changed interfaces

The first two counterexamples above are also attacks on changed documentation. The following additionally test the new public statements themselves.

1. **Parameter dependence, including `n=0`, empty advice and zero coins.** Let `A` return its argument, and let both `pre` and `post` return the first component of their encoded inputs. The composition equation gives `B.runAtL n y r=1^n`. At `n=0` this is `[]`. Thus the added lemma really permits parameter-dependent processing even for a fixed empty `y`; it does not silently reduce to the old argument-only interface. Zero coins form a singleton sample space, not an empty one. **Pass.**

2. **Uncomputable advice and deliberately wrong-length list coins.** Let `A` return advice `[H(n)]`, take `pre=snd`, and take `post` to be the identity on the pair it receives. The promised output is `⟨1^n,[H(n)]⟩`; `B` retains precisely `A`'s advice. There is no accidental uniformity or computability claim. The same identity holds for `r=[]` or any longer list because `runAtL` quantifies over all lists and this `A` ignores them. **Pass.**

3. **Immediate success with growth after the stopping point.** In `stateFind`, set `start x=[]`, `N x=0`, `R=B=const 0`, `acc=true`, and `out=snd`. The step can append a bit on every call, so its unguarded later orbit grows, but `hbound` concerns only index 0. The output is `[]`, including at `x=[]`. The theorem does not impose an unintended post-success invariant or skip index 0. **Pass.**

4. **Success exactly at the budget endpoint.** Set `start x=[]`, let `step ⟨x,s⟩=true::s`, let `N x=|x|`, `R=B=var`, let `acc ⟨x,s⟩` test `|x|≤|s|`, and let `out=snd`. The orbit is `1^i`, the test is false for `i<|x|` and true at `|x|`, and the output is `1^{|x|}`. The search includes the final index. This also verifies the empty-input case, where the first and final index are both zero. **Pass.**

5. **Attempt to smuggle an uncomputable stopping time.** Fix `start`, `step` and `acc`, and try assigning `N x` independently. Two distinct values cannot both meet the hypotheses: if `N₁<N₂`, acceptance at `N₁` contradicts the required rejection at all indices below `N₂`. The bounded search determines the unique permitted value. A test that never accepts cannot satisfy `hlast`. **Pass.**

6. **Constant and zero ensemble lengths.** For constant length `L`, each fixed point test is a literal uniform distinguisher. Literal indistinguishability makes each of the finitely many point-probability gaps negligible; their sum bounds every randomized test's advantage, even when its advice varies with `n`. For `L=0` there is one possible string and every gap is zero. The new constant-length explanation is valid, although the generalized Lean theorem remains unproved as disclosed. **Pass.**

## Round-1 resolutions

These lines distinguish checked fixes from accepted records and scheduled work. A deferred family is not treated as repaired merely because its schedule is accepted.

- **1: not resolved** — the advice/uniformity distinction is repaired, but the new identification with full-domain efficient computation is false; R2-1.
- **2: fixed** — `Indist.copies` now explains the sampling-based reduction and explicitly leaves the stronger non-uniform version unproved. The advice-hybrid argument is valid; its auxiliary review claim about `Fin 3` needs R2-3's correction.
- **3: fixed / scheduled** — `exists_compParam` has exactly the proposed parameter-aware interface, and `exists_comp` retains its statement. The missing `runAtL_eq`/`advInput_eq` reading lemmas are explicitly scheduled for clean-up part 2; they are not silently represented as present.
- **4: fixed / scheduled** — the host theorem is public with the same statement. The public/private prose was checked in `Repetition`, pinned `StringLoops` and pinned `HardCoreLoops`; the pinned three-coloring call explicitly names `EncodingMachines.polyTimeComputable_stateFind`. Re-pointing the remaining copies and the fixed-round variant is still DL-11's part-2 work.
- **5: fixed** — the per-parameter lemma and module prose now distinguish individual polynomial-time evaluators from a uniform polynomial description-size bound. `advice_length` is correctly identified as essential additional information.
- **6: fixed** — the source's bound is `(1−p²)/(mε²)`; the repaired comparison with `1/(4mε²)` is correct for `0≤p≤1`. The statement's nonempty index set supplies this range for `p`. The variance bound implies both since `p(1−p)≤1/4` and `p(1−p)≤1−p²`.
- **7: not resolved in full** — rational probabilities and fixed output length are now accurately stated; the dyadic characterization still needs R2-3's one-way wording.
- **8: scheduled; accounting not fully resolved** — G3-5 and DL-9–DL-14 explicitly acknowledge all six duplicate families and name clean-up part 2 after #195. The copies remain, as declared. DL-9's omitted 03a location is R2-4; no new acceptance of debt is needed.
- **9: fixed** — all changed closure-catalogue tags distinguish the inventory identifier from a source theorem number, and `exists_reparam_advice` has its tag.
- **10: fixed** — `StatClose` and the reference list cite Definition 181.1, whose unrestricted deterministic tests are equivalent to the stated test-set form on these finite-support laws.
- **11: recorded** — the resolution explicitly records G3-6 approval of the eleven named attributes; the attributes remain unchanged. I accept this declared ruling as the brief permits.
- **12: fixed / scheduled** — the facade import is replaced, including the two section-B import edits; `negligible_zero` is moved under its original full name. `Ensembles` transparently retains `NonUniform` for the downstream transitive-import dependency. Dropping it after the consumer's direct import and deleting DL-13's duplicate remain scheduled.
- **13: fixed** — `Authors:`, the heartbeat option and the `Main definitions: None` section are all present.
- **14: fixed as documentation** — the constant-length finite-point-test argument is sound. The text explicitly says this case is not formalized, and the theorem still assumes injectivity.
- **15: not resolved** — the distinction between wrong-length rejection and the source experiment is now disclosed, but the new `ofString` example overlooks output padding; R2-2. Its precise injective-output-length condition is sound when the wrapper represents `f` exactly.
- **16: fixed** — the common seed-type restriction is stated. Finitely many nonempty finite seed spaces can be embedded in their product, using a coordinate projection for each hybrid.
- **17: fixed** — the new `PolyExpr` paragraph accurately explains the absence of subtraction and the displayed nonrepresentable lengths. Majorants and advice-based reparameterization are identified as alternatives, not new polynomial constructors.
- **18: not resolved in full** — output padding/truncation and its possible collision are disclosed, but “lossy otherwise” is too strong; R2-5.
- **19: fixed** — section B adds the eleven requested prints and the moved lemma's print; all twelve also occur in the bundled current axiom log with standard axioms only.
- **20: recorded** — DESIGN D11 and Q5 now name the actual optional admission and record that `ofPartial` was never written. The admission inventory and axiom log agree. Older prose describing the proposed clocking construction does not constitute a second admission.
- **21: fixed as an added sanity statement; execution recorded** — section B contains the zero ensemble and `not_indist_uniform_zeros`. The first-bit distinguisher has advantage `1/2` at every positive parameter, which is not negligible. The separate claimed #201 `Checks` axiom output is not among the four bundled `a2` logs; I do not claim to have independently replayed it.
- **22: fixed** — the closing brief identifies `EnsemblesLemmas` as context and assigns its audit to 03i. Its full file is not bundled here; this audit does not extend to all its declarations.
- **23: fixed** — section B contains the five inventory supersession banners; the closing brief corrects the stale Q1.
- **24: fixed** — the ill-typed `φ := length` suggestion is removed, and `Indist.push` cites finding 3 instead of the nonexistent P2-4 record.
- **25: recorded, with direct source comparison completed** — the PDF is available in this round. The relevant source definitions and bounds were read directly; R2-1 and R2-2 state the remaining repaired-prose fidelity issues.
- **26: fixed** — the empty-seed zero-measure convention is accurately described. Against a nonempty-seeded law, the universal event has probabilities 0 and 1, excluding `StatClose … 0`.
- **M1: scheduled** — the wider six-family duplication is explicitly accepted and assigned to part 2, with DL-11's promotion already done. The DL-9 enumeration needs R2-4's correction.
- **M2: fixed** — section B replaces both additional facade imports with named modules.
- **M3: fixed** — `exists_reparam_advice` now carries the source/inventory distinction.
- **M4: fixed** — `Samplable` cites the source's p. 72 example, and identifies the multicopy sampling reduction as the Garg lemma rather than a nonexistent Pass–shelat corollary. I verified the Pass–shelat attribution directly; the Garg text was not supplied for a new independent audit.
- **M5: fixed** — fixed-length support is explicit, distinguishing Definitions 69.3 and 69.4.
- **M6: fixed** — the three named public/private prose corrections were checked, including the two omitted files at the pin.
- **M7: recorded / location verified** — the pinned `CollectionsHelpers.lean` contains the helpers under their unchanged `Complexity.NUPPT.*` names. They did not move into 03a's directory, so their omission from section A is appropriate; this is not a fresh audit of those helpers.
- **M8: recorded** — the review's downstream zero-use result is explicitly retained. I did not repeat the five-worktree search. No change in this repair creates a new downstream use of `Computes`.

## Changed-surface and regression coverage

| File or surface | Result |
|---|---|
| `PolyExpr.lean` | Documentation-only change; the natural-coefficient limitation is accurately stated. |
| `PPT.lean` | Definitions and theorem headers unchanged. The repaired uniformity warning is useful, but R2-1 limits the new converse claim. |
| `Primitives.lean` | No section-A delta; no new claim to re-audit. |
| `Closure.lean` | The added declaration is audited above; the original `exists_comp` statement is preserved. Reparameterization, advice, splitting and sequence statements are unchanged, and their revised tags match their intended source status. |
| `Repetition.lean` | The promoted declaration is audited above. The replacement sketch correctly distinguishes the actual-pair machine invariant from `LoopInv`, names the public host and five modules, and gives the request/fuel bounds. The treatment of verdict words agrees with the pinned dependency's `stepWord`/`outWord` descriptions. The `BlockLoop` to `BlockMapLoop` references match the renamed context. No old public theorem header changes. |
| `NonUniform.lean` | Revised theorem prose matches a fixed-parameter claim. The sole optional admitted theorem is unchanged. |
| `Adversary.lean` | The new wrong-length warning is mathematically appropriate for exact representations. The paired `ofString` resolution needs R2-2, and “non-constant” should be qualified as a `PolyExpr` length. |
| `Sampling.lean` | Revised `StatClose` attribution and empty-seed convention match the definition; no statement changes. |
| `Ensembles.lean` | The revised hybrid seed restriction, sampling explanation, constant-length indistinguishability argument and pairwise-sampling cost are valid. The two residual wording defects are R2-3 and R2-5. The moved zero lemma has no name/statement regression. |
| `SamplingFinDist.lean` | Header-only changes; the bridge continues to require nonempty finite seeds and a finite output type. |
| `Negligible.lean` | Only the moved helper and its documentation are added. No preexisting statement changes. |

The original nonempty-ensemble guard remains in the structure; `predict_eq` retains its nonempty seed/coin hypotheses. The `iterateFind` statement retains its inclusive range `0,…,R(|x|)`, the orbit bound, and the empty-output exhaustion case. `iterateEmit` retains `R(|x|)+1` emissions, and `blockMap` retains zero blocks at block size zero. The repairs did not weaken these previously accepted boundary protections.

## Evidence checks and provenance

- The bundle has **24 sections**. Its computed SHA-256 is `521e59d8b8be31ba94dbeeb981f3c18144f75834ea35d023e8cf195f492724a6` (no independent expected bundle hash was supplied).
- Removing only the bundle separator's extra final newline recovers the recorded round-1 findings SHA-256, `9dd9195111dfc8aca6748405f2730ca98c8f61f3ae51b2858b2fe87e8cfa5f92`.
- All ten changed Lean-file snapshots match the new Git-blob prefixes in section A. Reverse-applying section A succeeds, and all reconstructed base files match the old blob prefixes. This checks the internal correspondence of diff and snapshots, not the authenticity of the maintainer's whole branch history.
- A comment-insensitive declaration-header comparison finds exactly the stated changes: added `exists_compParam`, `private` removed from `polyTimeComputable_stateFind`, and `negligible_zero` moved. No surviving old declaration changes its statement header. The diff is also consistent with the claimed unchanged definitions.
- `replay.log`: **64** module rows, all `rc=0` and `errors=0`; **18** `sorry` warnings in their sum. This is a combined/overlaid record as the brief explains, not evidence that I ran a single fresh 64-module replay at this pin.
- `axioms.log`: **164** entries; **163** use only `propext`, `Classical.choice`, and/or `Quot.sound`. The only `sorryAx` entry is `NUPPT.decides_of_decidesWithAdviceInTime`. Both newly public declarations and `negligible_zero` have standard-only entries.
- `admissions.txt`: one declaration, the same optional bridge. `lint.log`: **0 findings in 11 files**. These reports are mutually consistent. They do not certify the repaired mathematical prose, which is why R2-1 and R2-2 can coexist with clean theorem axiom reports.
- The user rulings and part-2 schedule are accepted as explicit declarations in the resolutions and ledger. The primary decision-log/QUEUE excerpts and the separate downstream execution logs are not included; they are not claimed as independently authenticated here.

Supplementary code read at the exact audit pin, limited to resolving named dependencies/resolutions:

- [OneWay.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/TCSlib/Cryptography/Asymptotic/OneWay.lean): the repaired docstring and actual `ofString` padding definition.
- [StateLoop.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/TCSlib/Complexity/Randomized/Build/StateLoop.lean), [IterateFind.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/TCSlib/Complexity/Randomized/Build/IterateFind.lean), and [StringLoops.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/TCSlib/Complexity/Randomized/Build/StringLoops.lean): orbit/guard definitions and construction/publicity prose.
- [HardCoreLoops.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/TCSlib/Cryptography/Asymptotic/HardCoreLoops.lean), [ThreeColoring/Machines.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean), and [CollectionsHelpers.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean): the specifically claimed prose, name qualification and helper locations.

## Notation used in the counterexamples

`⟨a,b⟩` is `pairEncode a b`; `fst,snd` are `pairFstD,pairSndD`; `|w|` is string length; `a ‖ b` is concatenation; `0^k,1^k` are repeated bits. `H` is a noncomputable Boolean function and `f_bad` is the full-domain counterexample defined in §1. In §2, `h` is the assumed length-preserving one-way function, `g` its padded-prefix derivative, `f` the docstring's special-preimage function, `F_n` the length-`n` slice of `ofString f .var`, and `pad_n` false-pads or truncates to length `n`. `n,k,m,i,L` are natural-number indices, lengths or round counts; `x,y,z,u,w,s,r` are strings or the stated coin/state arguments. Other identifiers retain their Lean meanings from the audited declarations.
