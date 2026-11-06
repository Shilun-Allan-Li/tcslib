## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack-r3.md =====

# Gate 03a ([PS10] ch. 2–4, probabilistic machines, closure, ensembles: the interface), round 3: delta audit pack

**What is audited:** the repair of round 2, on `cryptography/pass-shelat-ch2-4` at
`3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e`. That is the merge of
[Shilun-Allan-Li/tcslib#205](https://github.com/Shilun-Allan-Li/tcslib/pull/205); its Lean files are
#205's head `0cebd6aa`, which also contains #204.
- **Round 2** audited `e28773ef` and found **0 blockers, 2 majors, 3 minors**, all documentation
  (`gate03a-r2-findings.md`, in the bundle, verbatim). The new public interfaces
  (`exists_compParam`, the public `polyTimeComputable_stateFind`) were confirmed.
- **The repair:**
  - #205 changes four docstrings: in `Complexity/Randomized/PPT.lean`, the module docstring and
    `NUPPT.Computes`; in `Cryptography/Asymptotic/Adversary.lean`, the inverter deviation; in
    `Cryptography/Asymptotic/Ensembles.lean`, `Ensemble` and `Ensemble.push`.
  - #204 corrected `FunFamily.ofString`'s example (R2-2's main part, shared with gate 03b). Gate
    03b round 3 verified that correction, and gate 03b is closed.
  - The records changes: DESIGN D3, ledger DL-9, and an erratum in the 03a review.
  - The diff is `evidence-repairs/03a-r2/repair.diff.txt`, the resolutions
    `resolutions-03a-r2.md` (both in the bundle).
- **The deliverable:** **`gate03a-r3-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12). Book pp. 23–24 (Defs 23.4, 23.5, 24.6) and pp. 69–73 (Defs 69.3, 69.4, Lemma 71.5) are the
relevant pages.

## Brief for the auditor

1. **Verify the five round 2 resolutions:** fixed, or not resolved and why.
   - **R2-1 (major):** do `PPT.lean`'s two docstrings and DESIGN D3 now state exactly what
     `A.Uniform ∧ A.Computes f` gives: efficient computation of `f` on the encodings `⟨1^n, y⟩`,
     with the converse `Computes.polyTimeComputable` for `z ↦ f ⟨1^{|fst z|}, snd z⟩`? Is any
     claim about `f` off those encodings left?
   - **R2-2 (major):** `Adversary.lean`'s parenthetical; and `FunFamily.ofString`'s example
     (`OneWay.lean`, as corrected in #204; context, already verified at gate 03b round 3).
   - **R2-3, R2-4, R2-5 (minors):** `Ensemble`'s dyadic sentence; ledger DL-9's `Ensemble.blocks`;
     and the 03a review's erratum and `Ensemble.push`'s "can be lossy".
2. **Check that nothing else changed:** no statement and no other docstring. The diff is the whole
   Lean change.

Pack 03a's severity guide applies. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Round 2 findings, resolutions, the diff | `findings/gate03a-r2-findings.md`, `resolutions-03a-r2.md`, `evidence-repairs/03a-r2/repair.diff.txt` |
| Under audit, at the pin | `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Ensembles}.lean` (the changed docstrings) |
| Records under audit | `briefs/pass-shelat/DESIGN.md` (D3), `briefs/pass-shelat-ch5-8/duplication-ledger.md` (DL-9), `review/gate03a-review.md` (the `Fin 3` erratum) |
| Context | `TCSlib/Cryptography/Asymptotic/OneWay.lean` (the corrected `ofString`), `resolutions-03a-r1.md`, `03a-pack-r2.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03a-r2/`)

- **Elaboration** (`replay.log`): the 79 modules downstream of the three files (facades excluded),
  then `audits/pass-shelat/Checks`, each checked alone into a copy of the tree at #203's merge:
  **80 of 80 pass, 0 errors**. The `sorry` warnings are unchanged (63 before, 63 after).
- **Lint** (`lint.log`): `scripts/style_lint.py` reports 0 findings on each of the three files.
- **Axioms:** no statement changed. The round 2 print stands: 164 prints, one `sorryAx` (D11's
  optional `decides_of_decidesWithAdviceInTime`) (`evidence/a2/axioms.log`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 2 finding: `R2-<n>: fixed / not resolved — <reason>`.

The gate closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03a-r2-findings.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03a-r2.md =====

# Gate 03a (probabilistic machines, closure, ensembles: the interface): round 2 resolutions

- **Round 2:** findings `findings/gate03a-r2-findings.md`, verbatim, SHA-256
  `573714c93cd3f163c75b085b7e7c1ef4ebf35c5ab50fefc7118b48687a064b6b`; pin
  `e28773ef3bda6f7b4b112ec1657427bfef01e374`; bundle SHA-256 `521e59d8…` (24 sections). Verdict
  **DO NOT CLOSE: 0 blockers, 2 majors, 3 minors**. All are documentation claims; neither major
  is a counterexample to a Lean theorem. The new public interfaces (`exists_compParam`, public
  `polyTimeComputable_stateFind`) are confirmed.
- **Round 1 rows not resolved in round 2:** #1 (R2-1), #7 (R2-3), #15 (R2-2) and #18 (R2-5).
  The others are fixed, recorded or scheduled.
- **Repair:** docstrings only, in `Complexity/Randomized/PPT.lean`,
  `Cryptography/Asymptotic/Adversary.lean` and `Cryptography/Asymptotic/Ensembles.lean` (PR
  below), plus records: DESIGN D3, the 03a review's erratum and ledger DL-9. R2-2's `ofString`
  part was already fixed by #204 (gate 03b round 2, R2-1).

| Finding | Severity | Resolution |
|---|---|---|
| R2-1 | major | **Fixed** (maintainer: true; `Computes` constrains `f` only on `advInput n y`, so the auditor's `f_bad` is computed by a uniform constant machine). The module docstring and `Computes`' docstring in `PPT.lean`, and DESIGN D3, now say that `A.Uniform ∧ A.Computes f` is efficient computation of `f` **on the encodings `⟨1^n, y⟩`**, not on every string. They also say that `Computes` says nothing about `f` off those encodings, and that the converse `Computes.polyTimeComputable` gives polynomial-time computability of `z ↦ f ⟨1^{|fst z|}, snd z⟩`. No statement changes, and no full-domain interface is added (none is needed). |
| R2-2 | major | **Fixed.** The `ofString` example was corrected in #204 for gate 03b round 2's R2-1, the same defect: `p = var`, `g(x ‖ b) := h(x) ‖ 1`, marked informal, with the role of the final `1` stated. `Adversary.lean`'s parenthetical now reads "length-regular `f` whose output length is a non-constant `PolyExpr`, hence injective in the input length". |
| R2-3 | minor | **Fixed.** `Ensemble`'s deviation now says every efficiently samplable ensemble has dyadic laws but not every dyadic one is samplable (the point mass at an uncomputable bit), and gives the non-dyadic example as three seeds mapped to distinct strings. The 03a review's `Fin 3` sentence carries an erratum (records). |
| R2-4 | minor | **Fixed** (records). DL-9 lists the private `Ensemble.blocks` (`Asymptotic/Ensembles.lean`) and its removal and re-pointing; clean-up part 2's brief draft includes it. |
| R2-5 | minor | **Fixed.** `Ensemble.push`'s docstring says the padding "can be lossy otherwise" and that the exact target length is a sufficient condition. |

**Round 3** is a delta audit of the four rewritten docstrings (`PPT.lean`: the module docstring and
`Computes`; `Adversary.lean`; `Ensembles.lean`: `Ensemble` and `Ensemble.push`) and the records
lines.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03a-r2/repair.diff.txt =====

diff --git a/TCSlib/Complexity/Randomized/PPT.lean b/TCSlib/Complexity/Randomized/PPT.lean
index 2fdfe96c..3416d340 100644
--- a/TCSlib/Complexity/Randomized/PPT.lean
+++ b/TCSlib/Complexity/Randomized/PPT.lean
@@ -41,9 +41,13 @@ empty advice (`NUPPT.Uniform`); `Complexity.PPT` is the subtype. `Computes` does
 `Uniform`: [PS10, Definition 24.6] is about a randomized algorithm, i.e. a PPT, and is the case
 `A.Uniform ∧ A.Computes f`; for a non-uniform `A`, `Computes` is the advice analogue and holds
 for uncomputable `f` (advice `[h n]` for an arbitrary `h : ℕ → Bool`, read back by the machine).
-So `∃ A : NUPPT, A.Computes f` does not say that a PPT computes `f`; efficient computation is
-`∃ A, A.Uniform ∧ A.Computes f` (`NUPPT.exists_uniform_computes`, and conversely
-`NUPPT.Computes.polyTimeComputable` of `TCSlib.Complexity.Randomized.Closure`). The
+So `∃ A : NUPPT, A.Computes f` does not say that a PPT computes `f`. Efficient computation of
+`f` on the encodings `⟨1^n, y⟩` is `∃ A, A.Uniform ∧ A.Computes f`
+(`NUPPT.exists_uniform_computes`, and conversely `NUPPT.Computes.polyTimeComputable` of
+`TCSlib.Complexity.Randomized.Closure`, which gives polynomial-time computability of
+`z ↦ f ⟨1^{|fst z|}, snd z⟩`). `Computes` says nothing about `f` off those encodings, so it is
+not [PS10, Definition 24.6] for an arbitrary `f : {0,1}* → {0,1}*`, which constrains every
+input string (gate 03a, round 2, R2-1). The
 input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8] is `NUPPT.runLit`; the
 lemmas about it and about uniformity are in `TCSlib.Complexity.Randomized.NonUniform`.
 
@@ -238,7 +242,12 @@ parameter `n` for an arbitrary `h : ℕ → Bool` (`ofPolyTime` of the advice pr
 computes `w ↦ [h |fst w|]`. So `∃ A : NUPPT, A.Computes f` does **not** mean "a PPT computes
 `f`"; where the text means efficient computation, the form is `A.Uniform ∧ A.Computes f`
 (`exists_uniform_computes`; conversely `NUPPT.Computes.polyTimeComputable` of
-`TCSlib.Complexity.Randomized.Closure`, which assumes `Uniform`). -/
+`TCSlib.Complexity.Randomized.Closure`, which assumes `Uniform`).
+
+`Computes f` constrains `f` only on the encodings `advInput n y = ⟨1^n, y⟩`: off them `f` is
+arbitrary, even uncomputable, so `A.Uniform ∧ A.Computes f` is efficient computation of `f` on
+those encodings, not of `f` on every string (the converse gives polynomial-time computability of
+`z ↦ f ⟨1^{|fst z|}, snd z⟩`; gate 03a, round 2, R2-1). -/
 def Computes (f : List Bool → List Bool) : Prop :=
   ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
 
diff --git a/TCSlib/Cryptography/Asymptotic/Adversary.lean b/TCSlib/Cryptography/Asymptotic/Adversary.lean
index 174e38fb..f80ac042 100644
--- a/TCSlib/Cryptography/Asymptotic/Adversary.lean
+++ b/TCSlib/Cryptography/Asymptotic/Adversary.lean
@@ -103,8 +103,8 @@ theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x
 a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
 another length, so the typed experiment can count fewer successes and typed one-wayness is
 implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
-with non-constant output length; with constant output length neither notion is
-satisfiable). The proviso is stated where string functions enter the typed world,
+whose output length is a non-constant `PolyExpr`, hence injective in the input length; with
+constant output length neither notion is satisfiable). The proviso is stated where string functions enter the typed world,
 `FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
 def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
     (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
diff --git a/TCSlib/Cryptography/Asymptotic/Ensembles.lean b/TCSlib/Cryptography/Asymptotic/Ensembles.lean
index e5b14f80..b4a411a9 100644
--- a/TCSlib/Cryptography/Asymptotic/Ensembles.lean
+++ b/TCSlib/Cryptography/Asymptotic/Ensembles.lean
@@ -117,8 +117,10 @@ the `ℓ(n)`-bit strings, the distribution `X_n` being the pushforward of the un
 length `ℓ` is a syntactic polynomial (D9).
 
 **Deviation:** each `X_n` is the pushforward of the uniform distribution on a finite nonempty
-seed set, so its probabilities are rational (not necessarily dyadic: seeds `Fin 3` give mass
-`1/3`; the efficiently samplable ensembles, `Samplable`, are the dyadic ones, D6), and it lives
+seed set, so its probabilities are rational (not necessarily dyadic: three seeds mapped to
+distinct strings give masses `1/3`; every efficiently samplable ensemble, `Samplable`, has dyadic
+laws, D6, but not every dyadic ensemble is samplable, e.g. the point mass at an uncomputable bit;
+gate 03a, round 2, R2-3), and it lives
 on strings of the fixed length `ℓ(n)` that Definition 69.4 requires (Definition 69.3 allows
 arbitrary distributions over `{0,1}^*`). Every ensemble of chapters 3 and 4 is of this form;
 the non-dyadic ideal distributions (primes, `Z_q`, permutations) appear only inside
@@ -188,7 +190,8 @@ and coins for `M`, run `M(1^n, X_n)` and pad or truncate the output to `ℓ'(n)`
 output length `ℓ'` is an explicit syntactic polynomial so that the padding is itself
 polynomial-time (`polyTimeComputable_unaryPoly`). The padding (`padFin`: `false`-padding or
 truncation) is lossless when `M` outputs exactly `ℓ'(n)` bits, the only case Definition 69.4
-can type, and lossy otherwise (`[1]` and `[1, 0]` both pad to `[1, 0, …]`): variable-length
+can type (a sufficient condition), and can be lossy otherwise (`[1]` and `[1, 0]` both pad to
+`[1, 0, …]`; gate 03a, round 2, R2-5): variable-length
 outputs (ciphertexts, views, transcripts) are not ensembles of this kind. -/
 def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ' where
   σ n := X.σ n × M.Coins n

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03a-r2/replay.log =====

# maintainer re-check at 0cebd6aad24ad0c79a3b2917bfa9f8158c59af75: the 79 modules downstream of PPT.lean, Adversary.lean and Ensembles.lean (downstream2.py, facades excluded), then audits/pass-shelat/Checks, on a copy of the tree at #203's merge
TCSlib/Complexity/Randomized/PPT rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 1s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 59s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 44s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 59s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 20s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 8s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 6s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 3s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 2s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 101s errors=0 sorry=0
# done 2026-11-06T00:04:29Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03a-r2/lint.log =====

# scripts/style_lint.py on the three changed files, at 0cebd6aad24ad0c79a3b2917bfa9f8158c59af75
TCSlib/Complexity/Randomized/PPT.lean: 0 findings in 1 files
TCSlib/Cryptography/Asymptotic/Adversary.lean: 0 findings in 1 files
TCSlib/Cryptography/Asymptotic/Ensembles.lean: 0 findings in 1 files

## ===== TCSlib/Complexity/Randomized/PPT.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic polynomial-time machines, uniform and non-uniform

The randomized machine model of [PS10, §2.1]: the probabilistic polynomial-time Turing
machine (PPT) [PS10, Definition 23.4] with the worst-case running-time convention
[PS10, Definition 23.5], the notion "computes `f` with probability one"
[PS10, Definition 24.6], and the non-uniform PPT of [PS10, Definition 26.8] in its advice
formulation ("a uniform p.p.t. machine `A` that receives an advice string for each input
length"). One structure, `Complexity.NUPPT`, carries all of them (foundation decisions D3
and D4 of `PassShelatChapter2-4Plan.md`):

* a finite binary machine `M : Turing.FinTM Bool` that halts on **every** input `z` within
  `Ct * (|z| + 1) ^ ct` steps;
* an explicit coin polynomial `coins : PolyExpr` (`coins.eval n` uniform coins at parameter
  `n`) and an advice polynomial `adv : PolyExpr` with an advice function `advice : ℕ → List Bool`
  of length `≤ adv.eval n`;
* the single semantic primitive `output z` (the output tape when the budget expires), which is
  `PolyTimeComputable` (`NUPPT.polyTimeComputable_output`), and conversely every
  `PolyTimeComputable` function is the output of some `NUPPT` (`NUPPT.ofPolyTime`).

The activation at security parameter `n` on argument `y` with coins `r` is
`runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`
(pairs are `Turing.pairEncode`, `1^n = List.replicate n true`). The random tape is part of the
input, so the time bound holds for every coin string, which is exactly the worst-case
convention of [PS10, Definition 23.5]; "`A` computes `f` with probability 1"
[PS10, Definition 24.6] is `NUPPT.Computes`: equality for every coin string (on the finite
uniform coin space, probability one is the same as every coin string, see
`TCSlib.Cryptography.Asymptotic.Adversary`). A PPT [PS10, Definition 23.4] is an `NUPPT` with
empty advice (`NUPPT.Uniform`); `Complexity.PPT` is the subtype. `Computes` does not require
`Uniform`: [PS10, Definition 24.6] is about a randomized algorithm, i.e. a PPT, and is the case
`A.Uniform ∧ A.Computes f`; for a non-uniform `A`, `Computes` is the advice analogue and holds
for uncomputable `f` (advice `[h n]` for an arbitrary `h : ℕ → Bool`, read back by the machine).
So `∃ A : NUPPT, A.Computes f` does not say that a PPT computes `f`. Efficient computation of
`f` on the encodings `⟨1^n, y⟩` is `∃ A, A.Uniform ∧ A.Computes f`
(`NUPPT.exists_uniform_computes`, and conversely `NUPPT.Computes.polyTimeComputable` of
`TCSlib.Complexity.Randomized.Closure`, which gives polynomial-time computability of
`z ↦ f ⟨1^{|fst z|}, snd z⟩`). `Computes` says nothing about `f` off those encodings, so it is
not [PS10, Definition 24.6] for an arbitrary `f : {0,1}* → {0,1}*`, which constrains every
input string (gate 03a, round 2, R2-1). The
input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8] is `NUPPT.runLit`; the
lemmas about it and about uniformity are in `TCSlib.Complexity.Randomized.NonUniform`.

## Deviations (DESIGN.md §5, items 1–2)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional
   module).

In detail (D3): a machine that is polynomial-time on well-formed inputs can be clocked by
`Turing.timed_universal` into one that halts on every input, so requiring totality does not
change the class of behaviours (the optional lemma `NUPPT.ofPartial` doing this is not needed
by any theorem of chapters 2–4); the time bound is measured in the length of the machine
input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`, a polynomial in `n + |y|`, so the classes "polynomial in
`n`" (for `|y|` polynomial in `n`, the only case the experiments produce) and "polynomial in
the machine input" coincide.

**Interdefinability of the `1^n`-indexed and the input-length-indexed forms (D3/D4).** The
text indexes advice and coins by the input length (`A_{|x|}(x)`), while `NUPPT` indexes
them by the parameter `n` read from the unary prefix `1^n`. The two are interdefinable in
every experiment of the text: (i) an `NUPPT` run at `n := |y|` is exactly the text's
`A_{|y|}(y)`, by definition (`NUPPT.runLit`; the prefix `1^{|y|}` carries no information);
(ii) conversely, every experiment of the text hands the adversary strings
whose length is a fixed polynomial `ℓ(n)` of the parameter, and an input-length-indexed
machine at length `ℓ(n)` becomes a `1^n`-indexed one by hard-wiring its advice at `ℓ(n)` and
evaluating its coin polynomial at `ℓ(n)` (`exists_reparam_advice` with `φ := ℓ.eval`); for
injective `ℓ` the converse hard-wires `1^n` into the advice at length `ℓ(n)`. The `1^n`
indexing is what makes one random tape per `n` well-typed for the oracle and interactive
layouts of chapters 3–4, where the machine is activated several times at one parameter on
inputs of varying length. Both forms are kept side by side where the text uses the literal
one (Definitions 26.1 and 69.4) and are related by explicit lemmas, never unified silently.

## Main definitions

* `Complexity.NUPPT` — non-uniform PPT [PS10, Definition 26.8, advice formulation]; a PPT
  [PS10, Definition 23.4] is the case `NUPPT.Uniform` (empty advice).
* `Complexity.NUPPT.output` — the output of the machine on a raw input (the semantic
  primitive); `NUPPT.timeBound`, `NUPPT.coinLen`, `NUPPT.adviceLen`.
* `Complexity.NUPPT.advInput` — the adversary input `⟨1^n, y⟩`; `NUPPT.Coins` — the coin type
  at parameter `n`; `NUPPT.runAt`, `NUPPT.runAtL`, `NUPPT.runLit` — activations.
* `Complexity.NUPPT.Uniform` — no advice (a PPT); `Complexity.PPT` — the subtype.
* `Complexity.NUPPT.Computes` — computes `f` with probability one: [PS10, Definition 24.6] for a
  uniform `A` (`NUPPT.Uniform`), the advice analogue otherwise.
* `Complexity.NUPPT.ofPolyTime`, `Complexity.NUPPT.ofPolyTimeUniform` — the `NUPPT` with a
  given polynomial-time output function, with and without advice.

## Main results

* `Complexity.NUPPT.output_spec`, `NUPPT.computesFunInTime`,
  `NUPPT.polyTimeComputable_output` — the output function is computed by the machine within
  its budget, hence is polynomial-time computable.
* `Complexity.NUPPT.output_eq_of_computesInTime` — determinism: any completed computation of
  the machine names `output`.
* `Complexity.NUPPT.output_ofPolyTime`, `NUPPT.ofPolyTimeUniform_uniform` — the converse
  direction: `ofPolyTime hf` outputs `f`, and `ofPolyTimeUniform` is uniform.
* `Complexity.NUPPT.exists_uniform_computes` — every polynomial-time computable function is
  computed with probability one by a PPT [PS10, Definition 24.6, non-vacuity].
* `Complexity.NUPPT.nonempty` — the class is inhabited.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1: Definitions 23.4, 23.5, 24.6 and 26.8.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definition 1.3, time-bounded computation; §6.3, advice.)
-/

namespace Complexity

open Turing

/-- A non-uniform probabilistic polynomial-time machine [PS10, Definition 26.8, advice
formulation]: a finite binary machine halting on **every** input `z` within
`Ct (|z|+1)^ct` steps, the explicit polynomial `coins` giving the number of uniform coins at
parameter `n`, and an advice string of length at most `adv.eval n` per parameter.
A PPT [PS10, Definition 23.4] is the case of empty advice (`Uniform`); the time bound holds
for every coin string, the worst-case convention of [PS10, Definition 23.5].

**Deviation:** `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time
in the machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
**Deviation:** `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core
(optional module). -/
structure NUPPT where
  /-- The underlying deterministic finite machine; coins and advice are input components. -/
  M : FinTM Bool
  /-- Coefficient of the running-time bound `Ct * (|z| + 1) ^ ct`. -/
  Ct : ℕ
  /-- Degree of the running-time bound. -/
  ct : ℕ
  /-- The coin polynomial: `coins.eval n` uniform coins at parameter `n`. -/
  coins : PolyExpr
  /-- The advice polynomial: `|advice n| ≤ adv.eval n`. -/
  adv : PolyExpr
  /-- The advice string per parameter (empty for a uniform machine). -/
  advice : ℕ → List Bool
  /-- The advice is polynomially bounded. -/
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  /-- The machine halts on every input within its polynomial budget. -/
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT

variable (A : NUPPT)

/-- The running-time budget of `A` on inputs of length `m`: `Ct * (m + 1) ^ ct`. -/
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct

/-- The number of coins of `A` at parameter `n`. -/
def coinLen (n : ℕ) : ℕ := A.coins.eval n

/-- The advice-length bound of `A` at parameter `n`. -/
def adviceLen (n : ℕ) : ℕ := A.adv.eval n

/-- The output of `A` on the raw machine input `z`: the output tape when the budget expires
(the machine has halted by then, `output_spec`). This is the single semantic primitive; all
activations are instances of it. -/
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output

/-- The machine halts on `z` within its budget with `output z` on the output tape. -/
theorem output_spec (z : List Bool) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length) := by
  obtain ⟨out, h⟩ := A.halts z
  obtain ⟨hs, -⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  exact (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩

/-- The machine computes the function `output` within the budget `timeBound`. -/
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound :=
  fun z => A.output_spec z

/-- The output function of an `NUPPT` is polynomial-time computable: the black box through
which every reduction of the campaign is exhibited as a machine (D2). -/
theorem polyTimeComputable_output : PolyTimeComputable A.output :=
  ⟨A.M, A.Ct, A.ct, A.computesFunInTime⟩

/-- Determinism: any completed computation of the machine on `z` produces `output z`
(`Turing.FinTM.ComputesInTime.output_unique`). -/
theorem output_eq_of_computesInTime {z w : List Bool} {t : ℕ} (h : A.M.ComputesInTime z w t) :
    A.output z = w :=
  (A.output_spec z).output_unique h

/-- The output is no longer than the budget (a machine emits at most one symbol per step,
`Turing.MultiTapeTM.output_length_le`). -/
theorem output_length_le (z : List Bool) : (A.output z).length ≤ A.timeBound z.length :=
  A.M.tm.output_length_le z (A.timeBound z.length)

/-- The adversary input `⟨1^n, y⟩`: the unary security parameter paired with the argument,
exactly as the text writes `A(1^n, y)` [PS10, Definition 27.3]. -/
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y

/-- The length of the adversary input `⟨1^n, y⟩` is `2n + 2 + |y|`. -/
theorem length_advInput (n : ℕ) (y : List Bool) : (advInput n y).length = 2 * n + 2 + y.length := by
  simp [advInput, length_pairEncode]

/-- The coin type of `A` at parameter `n`: `coins.eval n` uniform bits
[PS10, Definition 23.4, "each bit of the random tape is uniformly and independently chosen"]. -/
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool

/-- Activation at parameter `n` on argument `y` with coins `r`: machine input
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The sampler `r ↦ runAt n y r` on the uniform coin type
`Coins n` is the distribution `A(1^n, y)` of the text. -/
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))

/-- Activation with an untyped coin string (the interactive and oracle layouts of
chapters 3–4 hand the machine a coin string of the right length as a list). -/
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)

/-- The typed activation is the untyped one on `List.ofFn r`. -/
theorem runAt_eq (n : ℕ) (y : List Bool) (r : A.Coins n) :
    A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl

/-- The input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8]: the
parameter is the input length (the `1^{|y|}` prefix carries no information). It is the layout
of the literal forms of [PS10, Definition 26.1] and [PS10, Definition 69.4] (D5). -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r

/-- `A` is *uniform* — a PPT [PS10, Definition 23.4] — when its advice is empty at every
parameter. -/
def Uniform : Prop := ∀ n, A.advice n = []

/-- `A` computes `f` with probability one [PS10, Definition 24.6]: at every parameter `n`,
on every argument `y` and for **every** coin string `r`, `A(1^n, y; r) = f(⟨1^n, y⟩)`. On
the finite uniform coin space "probability one" is the same as "every coin string"
(`TCSlib.Cryptography.Asymptotic.Adversary`, `NUPPT.computes_iff_uprob`).

The definition does not require `A.Uniform`. [PS10, Definition 24.6] is about a randomized
algorithm, i.e. a PPT, and is the case `A.Uniform ∧ A.Computes f`. For a non-uniform `A` this
is the advice analogue, which holds for uncomputable functions: with advice `[h n]` at
parameter `n` for an arbitrary `h : ℕ → Bool` (`ofPolyTime` of the advice projection), `A`
computes `w ↦ [h |fst w|]`. So `∃ A : NUPPT, A.Computes f` does **not** mean "a PPT computes
`f`"; where the text means efficient computation, the form is `A.Uniform ∧ A.Computes f`
(`exists_uniform_computes`; conversely `NUPPT.Computes.polyTimeComputable` of
`TCSlib.Complexity.Randomized.Closure`, which assumes `Uniform`).

`Computes f` constrains `f` only on the encodings `advInput n y = ⟨1^n, y⟩`: off them `f` is
arbitrary, even uncomputable, so `A.Uniform ∧ A.Computes f` is efficient computation of `f` on
those encodings, not of `f` on every string (the converse gives polynomial-time computability of
`z ↦ f ⟨1^{|fst z|}, snd z⟩`; gate 03a, round 2, R2-1). -/
def Computes (f : List Bool → List Bool) : Prop :=
  ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)

/-- A machine that computes `f` returns `f ⟨1^n, y⟩` on every activation. -/
theorem Computes.runAt_eq {f : List Bool → List Bool} (h : A.Computes f) (n : ℕ)
    (y : List Bool) (r : A.Coins n) : A.runAt n y r = f (advInput n y) :=
  h n y r

/-- The `NUPPT` whose machine is a polynomial-time machine for `f` (chosen from the
`PolyTimeComputable` witness), with the given coin polynomial and advice. Its output function
is `f` (`output_ofPolyTime`). This is how every reduction of the campaign is packaged: the
reduction is an FP function of the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` (D2). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool)
    (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT where
  M := Classical.choose hf
  Ct := Classical.choose (Classical.choose_spec hf)
  ct := Classical.choose (Classical.choose_spec (Classical.choose_spec hf))
  coins := coins
  adv := adv
  advice := advice
  advice_length := hα
  halts := fun z => ⟨f z, Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z⟩

/-- The output function of `ofPolyTime hf …` is `f` (determinism of completed outputs). -/
theorem output_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).output = f := by
  funext z
  exact (ofPolyTime hf coins adv advice hα).output_eq_of_computesInTime
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z)

/-- The coin polynomial of `ofPolyTime hf coins adv advice hα` is `coins`. -/
@[simp] theorem coins_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).coins = coins := rfl

/-- The advice polynomial of `ofPolyTime hf coins adv advice hα` is `adv`. -/
@[simp] theorem adv_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).adv = adv := rfl

/-- The advice of `ofPolyTime hf coins adv advice hα` is `advice`. -/
@[simp] theorem advice_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).advice = advice := rfl

/-- The untyped activation of `ofPolyTime hf …` is `f` on the raw layout. -/
theorem runAtL_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (n : ℕ) (y r : List Bool) :
    (ofPolyTime hf coins adv advice hα).runAtL n y r =
      f (pairEncode (pairEncode (advInput n y) (advice n)) r) := by
  simp [runAtL, output_ofPolyTime]

/-- The uniform `NUPPT` with output function `f`: `ofPolyTime` with empty advice. -/
noncomputable def ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : NUPPT :=
  ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

/-- `ofPolyTimeUniform hf coins` is uniform. -/
theorem ofPolyTimeUniform_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).Uniform := fun _ => rfl

/-- The output function of `ofPolyTimeUniform hf coins` is `f`. -/
theorem output_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).output = f :=
  output_ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

/-- The coin polynomial of `ofPolyTimeUniform hf coins` is `coins`. -/
@[simp] theorem coins_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).coins = coins := rfl

/-- The untyped activation of `ofPolyTimeUniform hf coins` is `f` on the raw layout with
empty advice. -/
theorem runAtL_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (n : ℕ) (y r : List Bool) :
    (ofPolyTimeUniform hf coins).runAtL n y r =
      f (pairEncode (pairEncode (advInput n y) []) r) := by
  simp [runAtL, ofPolyTimeUniform, output_ofPolyTime]

/-- **Non-vacuity of [PS10, Definition 24.6].** Every polynomial-time computable function
`f` is computed with probability one by a PPT (a uniform `NUPPT`): the machine for
`f ∘ pairFstD ∘ pairFstD` applied to the raw input `⟨⟨⟨1^n, y⟩, []⟩, r⟩` ignores the advice
and the coins and returns `f ⟨1^n, y⟩`. (This is the direction "`PolyTimeComputable f` gives a
PPT computing `f`" of the equivalence behind Deviation 3, `FunFamily.Easy`.) -/
theorem exists_uniform_computes {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : ∃ A : NUPPT, A.Uniform ∧ A.coins = coins ∧ A.Computes f := by
  have hF : PolyTimeComputable fun z => f (pairFstD (pairFstD z)) :=
    hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  refine ⟨ofPolyTimeUniform hF coins, ofPolyTimeUniform_uniform hF coins, rfl, fun n y r => ?_⟩
  rw [runAt_eq, runAtL_ofPolyTimeUniform]
  simp

end NUPPT

/-- PPT [PS10, Definition 23.4] = non-uniform PPT with empty advice: the subtype of uniform
`NUPPT`s. -/
def PPT : Type 1 := {A : NUPPT // A.Uniform}

/-- Non-vacuity: the class is inhabited (the identity machine with no coins). -/
theorem NUPPT.nonempty : Nonempty NUPPT :=
  ⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0)⟩

/-- Non-vacuity: the class of PPTs is inhabited. -/
theorem PPT.nonempty : Nonempty PPT :=
  ⟨⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0),
    NUPPT.ofPolyTimeUniform_uniform _ _⟩⟩

end Complexity

## ===== TCSlib/Cryptography/Asymptotic/Adversary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as adversaries of the concrete experiments

The bridge between the machine layer (`Complexity.NUPPT`, strings `List Bool`) and the
concrete security experiments of `TCSlib.Cryptography.Foundations.Experiments` (typed
inputs `Fin m → Bool`, adversaries as functions of the input and of a uniform coin string).
An `NUPPT` `A` activated at parameter `n` becomes

* an *inverter* `A.inverter n ℓ m : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)`
  [PS10, Definitions 27.3, 28.4]: `A(1^n, y)` with the output decoded as an `ℓ`-bit string;
* its literal variant `A.inverterLit ℓ m` for [PS10, Definition 26.1] (`A(f(x))`, activation
  at the input length `m`, no `1^n`);
* a *distinguisher* / *predictor* `A.distinguisher n m`, `A.predictor n m`
  [PS10, Definitions 69.4, 75.2, 78.3]: `A(1^n, t) = 1`, i.e. the output is the string `[true]`;
  `A.distinguisherL n` takes an untyped sample.

Inversion with a possibly failing decoder is `invProbOpt` (the probability that the decoded
output is a preimage); it is bridged to the concrete `invProb` by `invProbOpt_le_invProb`
(any default for a failure can only increase the probability) and `invProbOpt_some` (a total
inverter has the same probability). Foundation decision D5: inverses are sought in the
domain at the current parameter, and a wrong-length output counts as failure.

The file also records that "computes `f` with probability one" [PS10, Definition 24.6]
is, on the finite uniform coin space, the same as "for every coin string"
(`Complexity.NUPPT.computes_iff_uprob`), which justifies the frozen form of
`Complexity.NUPPT.Computes`.

**Deviation:** `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable
by `ifEq`).

## Main definitions

* `TCSlib.Cryptography.decodeFin` — decode a string as an `ℓ`-bit string, failure on a wrong
  length; `TCSlib.Cryptography.padFin` — pad/truncate (for samplers).
* `Complexity.NUPPT.inverter`, `Complexity.NUPPT.inverterLit` — an `NUPPT` as an inverter
  (with `1^n`, and literal).
* `Complexity.NUPPT.distinguisher`, `Complexity.NUPPT.distinguisherL`,
  `Complexity.NUPPT.predictor` — an `NUPPT` as a distinguisher / predictor.
* `TCSlib.Cryptography.invProbOpt` — inversion probability of a possibly failing inverter.

## Main results

* `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
  padding invert `List.ofFn`.
* `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
  bridges to the concrete `invProb`.
* `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
* `Complexity.NUPPT.computes_iff_uprob` — probability one is every coin string
  [PS10, Definition 24.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1–2.2: Definitions 24.6, 26.1, 27.3; §3.1–3.3: Definitions 69.4, 75.2, 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the concrete experiments).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- Decode a string as an `ℓ`-bit string: `some` of its bits if the length is exactly `ℓ`,
`none` otherwise (a wrong-length answer of an inverter is a failure, D5). -/
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

/-- Pad with `false` or truncate a string to exactly `ℓ` bits (the output convention of
samplers, where no failure is possible). -/
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- Decoding the encoding of an `ℓ`-bit string returns it. -/
theorem decodeFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : decodeFin ℓ (List.ofFn x) = some x := by
  simp [decodeFin]

/-- A decoded string has exactly the decoded length. -/
theorem length_eq_of_decodeFin_eq_some {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : w.length = ℓ := by
  by_contra hw
  simp [decodeFin, hw] at h

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x) = x := by
  funext i
  simp [padFin]

/-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].

**Deviation:** wrong-length output = failure (D5). For a typed family this loses nothing. For
a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
another length, so the typed experiment can count fewer successes and typed one-wayness is
implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
whose output length is a non-constant `PolyExpr`, hence injective in the input length; with
constant output length neither notion is satisfiable). The proviso is stated where string functions enter the typed world,
`FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- The literal inverter `A(y)` of [PS10, Definition 26.1]: activation at parameter `|y| = m`
(the text gives the adversary `f(x)` only; the `1^{|y|}` prefix carries no information). -/
def _root_.Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt m (List.ofFn y) r)

/-- `A(1^n, t)` as a distinguisher: accepts iff the output is the string `[true]`
[PS10, Definition 69.4]. -/
def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

/-- `A(1^n, w)` as a distinguisher of untyped samples (ciphertexts, views, histories). -/
def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

/-- `A(1^n, y)` as a predictor of a bit: the same verdict convention as a distinguisher
[PS10, Definitions 75.2 and 78.3]. -/
def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

/-- The literal inverter is the inverter at parameter `m`. -/
theorem _root_.Complexity.NUPPT.inverterLit_eq (A : NUPPT) (ℓ m : ℕ) :
    A.inverterLit ℓ m = A.inverter m ℓ m := rfl

/-- The typed distinguisher is the untyped one on `List.ofFn t`. -/
theorem _root_.Complexity.NUPPT.distinguisher_eq (A : NUPPT) (n m : ℕ) (t : Fin m → Bool)
    (r : A.Coins n) : A.distinguisher n m t r = A.distinguisherL n (List.ofFn t) r := rfl

/-- The predictor is the distinguisher. -/
theorem _root_.Complexity.NUPPT.predictor_eq (A : NUPPT) (n m : ℕ) :
    A.predictor n m = A.distinguisher n m := rfl

/-- The inverter succeeds on `(y, r)` iff the machine's output is the encoding of some `x'`. -/
theorem _root_.Complexity.NUPPT.inverter_eq_some_iff (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) (x' : Fin ℓ → Bool) :
    A.inverter n ℓ m y r = some x' ↔ A.runAt n (List.ofFn y) r = List.ofFn x' := by
  constructor
  · intro h
    have hw : (A.runAt n (List.ofFn y) r).length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [NUPPT.inverter, decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    show decodeFin ℓ _ = _
    rw [h, decodeFin_ofFn]

/-- The probability that a possibly failing inverter `A`, given `f x` for uniform `x` and
uniform coins, outputs `some x'` with `f x' = f x` (the typed experiment of
[PS10, Definition 27.3] with a wrong-length output counted as failure, D5). -/
noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

/-- Replacing a failure by any default can only increase the inversion probability: the
bridge from `invProbOpt` to the concrete `invProb` [Gar26, Definition 2.1]. -/
theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

/-- A total inverter has the same probability under both conventions. -/
theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt invProb
  congr 1
  funext z
  simp

/-- The inversion probability is nonnegative. -/
theorem invProbOpt_nonneg {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : 0 ≤ invProbOpt f A :=
  uprob_nonneg _

/-- The inversion probability is at most one. -/
theorem invProbOpt_le_one {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : invProbOpt f A ≤ 1 :=
  uprob_le_one _

/-- An event of probability one holds everywhere (private copy of
`TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one`, which lives in a frozen file). -/
private theorem forall_of_uprob_eq_one {Ω : Type*} [Fintype Ω] {p : Ω → Prop}
    (h : uprob p = 1) (ω : Ω) : p ω := by
  classical
  rw [uprob_eq_card_filter] at h
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    intro h0; rw [h0, div_zero] at h; exact zero_ne_one h
  have hcard : (univ.filter p).card = Fintype.card Ω := by
    have := (div_eq_one_iff_eq hc).1 h
    exact_mod_cast this
  have := Finset.eq_univ_of_card _ hcard
  have hω : ω ∈ univ.filter p := by rw [this]; exact mem_univ ω
  exact (mem_filter.1 hω).2

/-- **"With probability one" is "for every coin string"** [PS10, Definition 24.6]: `A`
computes `f` in the frozen sense (`Complexity.NUPPT.Computes`, equality for every coin
string) iff at every parameter and argument the event `A(1^n, y; r) = f(⟨1^n, y⟩)` has
probability one over the uniform coins. (On a finite uniform space an event of probability
one is the whole space.) -/
theorem _root_.Complexity.NUPPT.computes_iff_uprob (A : NUPPT) (f : List Bool → List Bool) :
    A.Computes f ↔
      ∀ n y, uprob (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = 1 := by
  constructor
  · intro h n y
    have hp : (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = fun _ => True :=
      funext fun r => propext ⟨fun _ => trivial, fun _ => h n y r⟩
    rw [hp, uprob_true]
  · intro h n y r
    exact forall_of_uprob_eq_one (h n y) r

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Ensembles.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
-- `NonUniform` is not used here. It replaces, for downstream files, the former import of the
-- facade `TCSlib.Complexity.Randomized`: `ZeroKnowledge/ThreeColoring/SimulatorMachine.lean`
-- uses `NUPPT.Uniform.advice_eq` and reaches `NonUniform` only through this file (gate 03a,
-- finding 12). Drop it once that file imports `NonUniform` itself.
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Ensembles and computational indistinguishability

The asymptotic notion of [PS10, §3.1]: *ensembles* of probability distributions over
`{0,1}^{ℓ(n)}` and *computational indistinguishability* `{X_n} ≈ {Y_n}` against non-uniform
PPT distinguishers, with the three properties the rest of chapters 3 and 4 use over and over:
closure under efficient operations (Lemma 71.5), the hybrid lemma (Lemma 71.6) and the
prediction lemma (Lemma 73.8).

Foundation decision D6: an ensemble is a family of samplers `X n : σ n → (Fin (ℓ n) → Bool)`
from arbitrary finite nonempty seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`); every
length is a syntactic polynomial `Complexity.PolyExpr` (D9). "Efficiently samplable" is the
distribution-level predicate `Ensemble.Samplable`: a polynomial-time sampler from `s n`
uniform bits whose output law is exactly `X n` (`StatClose … 0`). The headline form of
Definition 69.4 gives the distinguisher the input `1^n` (`Ensemble.Indist`, D5); the literal
form `Ensemble.IndistLit` (the distinguisher receives the sample `t` only, activation at
parameter `|t| = ℓ n`) is stated next to it with the bridges `Indist.toLit` and
`IndistLit.toIndist` (injective, i.e. non-constant, `ℓ`; for constant `ℓ` the two forms
coincide as well, by point tests, which is not formalized), never unified silently.

Every asymptotic statement is proved by instantiating a concrete reduction of
`TCSlib.Cryptography.Pseudorandom.Indistinguishability` [Gar26, §3.2] at each `n`, exhibiting
the reduction as a `Complexity.NUPPT` by the closure catalogue of
`TCSlib.Complexity.Randomized.Closure`, and finishing with negligible-function arithmetic
(`not_negligible_iff`, the "infinitely many `n` with `1/p(n)`" idiom of the text,
`not_negligible_iff_exists_polyExpr`).

**Deviation:** `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n`
(literal form `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the
constant case by point tests, not formalized).

The machine constructions and the probability bookkeeping behind the proofs (the negated,
padded-image and multicopy reductions as `NUPPT`s, coin-splitting bijections, the exactness
transfer `StatClose … 0` through `copies`) live in the sibling file
`TCSlib.Cryptography.Asymptotic.EnsemblesLemmas` (inner namespace `EnsembleLemmas`), which
exists only to keep this file within the repository's size limit.

**Repair (run-3 audit P2-2):** `Ensemble` carries the field `nonempty` (an empty seed type is
not a distribution), which restores the frozen shapes of `prediction_lemma` and
`Ensemble.NextBitUnpredictable.pseudorandom` (`NextBit.lean`); the nonemptiness instances
of `predict_eq` are discharged automatically for ensemble seeds and machine coins.

## Main definitions

* `TCSlib.Cryptography.Ensemble` — an ensemble over `{0,1}^{ℓ(n)}` [PS10, Definition 69.3];
  `Ensemble.uniform` — the uniform ensemble `{U_{ℓ(n)}}`.
* `TCSlib.Cryptography.Ensemble.Samplable` — efficiently samplable (distribution level, D6).
* `TCSlib.Cryptography.Ensemble.Indist`, `TCSlib.Cryptography.Ensemble.IndistLit` —
  computational indistinguishability [PS10, Definition 69.4], headline and literal forms;
  `TCSlib.Cryptography.Distinguishes`, `TCSlib.Cryptography.Ensemble.DistinguishesWith` —
  "`D` distinguishes with probability `ε` / `μ(·)`".
* `TCSlib.Cryptography.Ensemble.Pseudorandom` — indistinguishable from uniform
  [PS10, Definition 74.1].
* `TCSlib.Cryptography.Ensemble.push` — the image ensemble `{M(X_n)}` under an `NUPPT`;
  `TCSlib.Cryptography.Ensemble.copies` — `t(n)` independent copies.
* `TCSlib.Cryptography.mixEnsemble` — the sampler of `b ← {0,1}; t ← X^b_n` [PS10, Lemma 73.8].

## Main results

* `TCSlib.Cryptography.Ensemble.Indist.refl`, `Indist.symm`, `Indist.trans` — `≈` is an
  equivalence relation (transitivity is the two-step hybrid lemma, [PS10, §3.1.1]).
* `TCSlib.Cryptography.Ensemble.Indist.push` — closure under efficient operations
  [PS10, Lemma 71.5].
* `TCSlib.Cryptography.hybrid_lemma` — the hybrid lemma [PS10, Lemma 71.6], concrete.
* `TCSlib.Cryptography.Ensemble.Indist.copies` — polynomially many copies (the multicopy
  corollary of the hybrid lemma, [Gar26, Lemma 3.3]).
* `TCSlib.Cryptography.predict_eq` — predicting is distinguishing, the identity behind
  [PS10, p. 73 ("show this!") and Lemma 73.8].
* `TCSlib.Cryptography.prediction_lemma` — the prediction lemma [PS10, Lemma 73.8].
* `TCSlib.Cryptography.not_negligible_iff_exists_polyExpr` — "for infinitely many `n`,
  advantage `≥ 1/p(n)`" is non-negligibility [PS10, §3.1, the ubiquitous contradiction idiom].
* `TCSlib.Cryptography.pairwise_sampling_ineq` — the pairwise-independent sampling
  inequality [PS10, Appendix A, p. 189].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.1: Definitions 69.3, 69.4; §3.1.1: Lemmas 71.5, 71.6, 73.8; §3.2.1: Definition 74.1;
  Appendix A, p. 189.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2 (Definition 3.4, Lemmas 3.2 and 3.3), Theorem 2.4.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Ensembles -/

/-- An **ensemble** of probability distributions over `{0,1}^{ℓ(n)}` [PS10, Definition 69.3]:
at each `n` a sampler `X n` from a finite seed type `σ n` (uniformly distributed seeds) into
the `ℓ(n)`-bit strings, the distribution `X_n` being the pushforward of the uniform seed. The
length `ℓ` is a syntactic polynomial (D9).

**Deviation:** each `X_n` is the pushforward of the uniform distribution on a finite nonempty
seed set, so its probabilities are rational (not necessarily dyadic: three seeds mapped to
distinct strings give masses `1/3`; every efficiently samplable ensemble, `Samplable`, has dyadic
laws, D6, but not every dyadic ensemble is samplable, e.g. the point mass at an uncomputable bit;
gate 03a, round 2, R2-3), and it lives
on strings of the fixed length `ℓ(n)` that Definition 69.4 requires (Definition 69.3 allows
arbitrary distributions over `{0,1}^*`). Every ensemble of chapters 3 and 4 is of this form;
the non-dyadic ideal distributions (primes, `Z_q`, permutations) appear only inside
experiments, approximated by the rejection samplers of `Asymptotic/Sampling.lean` (D6, D10).

**Repair (run-3 audit P2-2):** the field `nonempty` was added to the frozen structure of
DESIGN.md §2.11. An empty seed type is not a distribution (every event has probability `0`),
and without the field `NextBitUnpredictable` was vacuous for an empty-seed ensemble that is
not pseudorandom, so `prediction_lemma` and `NextBitUnpredictable.pseudorandom` needed ad hoc
nonemptiness hypotheses. Machine coin types `Fin k → Bool` and every seed type of the campaign
are nonempty, so constructions fill the field by instance resolution. -/
structure Ensemble (ℓ : PolyExpr) where
  /-- The seed type at parameter `n`. -/
  σ : ℕ → Type
  /-- Seed types are finite. -/
  [fintype : ∀ n, Fintype (σ n)]
  /-- Seed types are nonempty: the sampler defines a probability distribution. -/
  [nonempty : ∀ n, Nonempty (σ n)]
  /-- The sampler at parameter `n`. -/
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)

attribute [instance] Ensemble.fintype Ensemble.nonempty

namespace Ensemble

variable {ℓ : PolyExpr}

/-- The uniform ensemble `{U_{ℓ(n)}}` [PS10, §3.2.1]: seeds are the strings themselves. -/
def uniform (ℓ : PolyExpr) : Ensemble ℓ where
  σ n := Fin (ℓ.eval n) → Bool
  X _ := id

/-- **Efficiently samplable** ensemble (distribution level, D6): there is a syntactic
polynomial `s` and a polynomial-time sampler `S` such that at every `n` the law of
`S(⟨1^n, r⟩)` for `s(n)` uniform bits `r` (padded or truncated to `ℓ(n)` bits) is exactly the
law of `X n` (`StatClose … 0`). This is the "efficiently sample" of [PS10, p. 72, Example];
the multicopy lemma that assumes it is [Gar26, Lemma 3.3] (`Indist.copies`). -/
def Samplable (X : Ensemble ℓ) : Prop :=
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool =>
      padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0

/-- **Computational indistinguishability** `{X_n} ≈ {Y_n}` [PS10, Definition 69.4], headline
form: for every non-uniform PPT `D`, the advantage
`|Pr[t ← X_n : D(1^n, t) = 1] − Pr[t ← Y_n : D(1^n, t) = 1]|` is a negligible function of
`n`. (The text's "there exists a negligible `ε` with advantage `< ε(n)` for all `n`" is
equivalent, `indist_iff_exists_negligible`.)

**Deviation:** `D` receives `1^n` in addition to the sample (D5); the literal form is
`IndistLit`, and the two are related by `Indist.toLit` and `IndistLit.toIndist`. -/
def Indist (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))

/-- **Computational indistinguishability, literal form** [PS10, Definition 69.4]: the
distinguisher receives the sample `t` only, i.e. is activated at parameter `|t| = ℓ(n)`
(`D_{|t|}(t)` in the machine-sequence reading of [PS10, Definition 26.8]). -/
def IndistLit (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n =>
    distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))

/-- A **pseudorandom ensemble** [PS10, Definition 74.1]: indistinguishable from the uniform
ensemble `{U_{ℓ(n)}}`. -/
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)

/-- The image ensemble `{M(X_n)}` of [PS10, Lemma 71.5]: at parameter `n`, draw a seed of `X`
and coins for `M`, run `M(1^n, X_n)` and pad or truncate the output to `ℓ'(n)` bits. The
output length `ℓ'` is an explicit syntactic polynomial so that the padding is itself
polynomial-time (`polyTimeComputable_unaryPoly`). The padding (`padFin`: `false`-padding or
truncation) is lossless when `M` outputs exactly `ℓ'(n)` bits, the only case Definition 69.4
can type (a sufficient condition), and can be lossy otherwise (`[1]` and `[1, 0]` both pad to
`[1, 0, …]`; gate 03a, round 2, R2-5): variable-length
outputs (ciphertexts, views, transcripts) are not ensembles of this kind. -/
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ' where
  σ n := X.σ n × M.Coins n
  X n z := padFin (ℓ'.eval n) (M.runAt n (List.ofFn (X.X n z.1)) z.2)

/-- The blockwise bijection `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q` (private copy of the frozen
`FunFamily.blocks` of `Asymptotic/OneWay.lean`, which this file does not import). -/
private def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- `t(n)` independent copies of `X_n`, concatenated into one `t(n)·ℓ(n)`-bit string: the
ensemble `{X_n^{(1)} ‖ ⋯ ‖ X_n^{(t(n))}}` of the multicopy corollary of the hybrid lemma
[PS10, Lemma 71.6; Gar26, Lemma 3.3]. -/
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ) where
  σ n := Fin (t.eval n) → X.σ n
  X n s := (blocks (t.eval n) (ℓ.eval n)).symm (TCSlib.Cryptography.copies (t.eval n) (X.X n) s)

/-- Unfolding of `copies`: bit `i` of the concatenation is bit `i mod ℓ` of copy `i / ℓ`
(through `finProdFinEquiv`). -/
theorem copies_X (t : PolyExpr) (X : Ensemble ℓ) (n : ℕ) (s : Fin (t.eval n) → X.σ n)
    (i : Fin (t.eval n * ℓ.eval n)) :
    (X.copies t).X n s i = X.X n (s (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2 :=
  rfl

/-- The uniform ensemble is efficiently samplable: `s := ℓ` and the sampler returns its coins
(`pairSndD` of `⟨1^n, r⟩`). Non-vacuity of `Samplable` (the case `U_n` of D6). -/
theorem uniform_samplable (ℓ : PolyExpr) : (uniform ℓ).Samplable := by
  refine ⟨ℓ, pairSndD, polyTimeComputable_pairSndD, fun n => ?_⟩
  have h : (fun r : Fin (ℓ.eval n) → Bool =>
      padFin (ℓ.eval n) (pairSndD (NUPPT.advInput n (List.ofFn r)))) = (uniform ℓ).X n := by
    funext r
    simp [NUPPT.advInput, padFin_ofFn, uniform]
  rw [h]
  exact StatClose.refl _

end Ensemble

/-! ### The "distinguishes with probability" notations of Definition 69.4 -/

/-- `D` **distinguishes** the distributions `X` and `Y` **with probability `ε`**
[PS10, p. 70, after Definition 69.4]: `|Pr[t ← X : D(t) = 1] − Pr[t ← Y : D(t) = 1]| > ε`. -/
def Distinguishes {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) (ε : ℝ) : Prop :=
  ε < distAdv X Y D

/-- `D` **distinguishes the ensembles** `{X_n}` and `{Y_n}` **with probability `μ(·)`**
[PS10, p. 70]: for all `n`, `D` distinguishes `X_n` and `Y_n` with probability `μ(n)`. -/
def Ensemble.DistinguishesWith {ℓ : PolyExpr} (X Y : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ) :
    Prop :=
  ∀ n, Distinguishes (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) (μ n)

/-- The text's form of Definition 69.4 — "there exists a negligible `ε` with advantage
`< ε(n)` for all `n`" — is equivalent to the frozen form "the advantage is negligible"
[PS10, Definition 69.4]: the advantage lies in `[0, 1]`, so one direction is `Negligible.mono`
and the other takes `ε(n) := advantage(n) + 2^{-n}`. -/
theorem Ensemble.indist_iff_exists_negligible {ℓ : PolyExpr} (X Y : Ensemble ℓ) :
    X.Indist Y ↔ ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) < ε n := by
  constructor
  · intro h D
    refine ⟨fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) + (2 : ℝ)⁻¹ ^ n,
      (h D).add negligible_two_pow_neg, fun n => ?_⟩
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    linarith
  · intro h D
    obtain ⟨ε, hε, hlt⟩ := h D
    refine hε.mono ⟨0, fun n _ => ?_⟩
    have h0 : 0 ≤ distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
    rw [abs_of_nonneg h0]
    exact (hlt n).le.trans (le_abs_self _)

/-- **The contradiction idiom of the text** [PS10, §3.1, Lemma 71.5's proof and passim]:
"assume for contradiction that there is a polynomial `p` such that for infinitely many `n` the
advantage is at least `1/p(n)`" is exactly non-negligibility (`not_negligible_iff`), with the
polynomial a syntactic `PolyExpr` with positive values.

**Proof sketch.** (⇒) `not_negligible_iff` gives an exponent `c`; take `p := (n+1)^c`
(`PolyExpr.normal 1 c`), which is positive and dominates `n^c`. (⇐) `p(n) ≤ C(n+1)^c`
(`PolyExpr.eval_le`) and `(n+1)^c ≤ 2^c n^c`, so `p(n) ≤ n^{c+1}` once `n ≥ C·2^c`; the
exponent `c + 1` witnesses `not_negligible_iff`. -/
theorem not_negligible_iff_exists_polyExpr {μ : ℕ → ℝ} :
    ¬ Negligible μ ↔ ∃ p : PolyExpr, (∀ n, 0 < p.eval n) ∧
      ∀ n₀, ∃ n ≥ n₀, 1 / (p.eval n : ℝ) ≤ |μ n| := by
  rw [not_negligible_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨.normal 1 c, fun n => by simp [PolyExpr.eval_normal], fun n₀ => ?_⟩
    obtain ⟨n, hn, h⟩ := hc (max n₀ 1)
    refine ⟨n, le_trans (le_max_left _ _) hn, le_trans ?_ h⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    rw [PolyExpr.eval_normal]
    push_cast
    rw [one_mul]
    exact one_div_le_one_div_of_le (pow_pos (by linarith) c)
      (pow_le_pow_left₀ (by linarith) (by linarith) c)
  · rintro ⟨p, hp, h⟩
    obtain ⟨C, c, hC⟩ := p.eval_le
    refine ⟨c + 1, fun n₀ => ?_⟩
    obtain ⟨n, hn, hμ⟩ := h (max n₀ (C * 2 ^ c + 1))
    refine ⟨n, le_trans (le_max_left _ _) hn, le_trans ?_ hμ⟩
    have hn' : C * 2 ^ c + 1 ≤ n := le_trans (le_max_right _ _) hn
    have key : p.eval n ≤ n ^ (c + 1) := by
      calc p.eval n ≤ C * (n + 1) ^ c := hC n
        _ ≤ C * (2 * n) ^ c := by gcongr; omega
        _ = C * 2 ^ c * n ^ c := by rw [mul_pow, mul_assoc]
        _ ≤ n * n ^ c := by gcongr; omega
        _ = n ^ (c + 1) := by ring
    have hpos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
    exact one_div_le_one_div_of_le hpos (by exact_mod_cast key)

/-! ### Properties of computational indistinguishability [PS10, §3.1.1] -/

/-- **Reflexivity of `≈`** (non-vacuity of `Indist`): every ensemble is indistinguishable
from itself, the advantage being identically zero. -/
theorem Ensemble.Indist.refl {ℓ : PolyExpr} (X : Ensemble ℓ) : X.Indist X := by
  intro D
  have h : (fun n => distAdv (X.X n) (X.X n) (D.distinguisher n (ℓ.eval n))) =
      fun _ => (0 : ℝ) := by
    funext n
    simp [distAdv]
  rw [h]
  exact negligible_zero

/-- **Symmetry of `≈`**: the advantage is symmetric in the two distributions. -/
theorem Ensemble.Indist.symm {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) : Y.Indist X := by
  intro D
  have e : (fun n => distAdv (Y.X n) (X.X n) (D.distinguisher n (ℓ.eval n))) =
      fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) :=
    funext fun n => abs_sub_comm _ _
  rw [e]
  exact h D

/-- **Bridge from the `1^n` form to the literal form** of Definition 69.4: if `{X_n} ≈ {Y_n}`
against distinguishers receiving `1^n`, then also against distinguishers receiving the sample
only [PS10, Definition 69.4; D5].

**Proof sketch.** A literal distinguisher `D` activated at parameter `ℓ(n)` is, as a function
of `n`, the activation of the machine `B := NUPPT.exists_reparam D ℓ` (advice
`D.advice (ℓ n)`, coins `D.coins.subst ℓ`), whose `runAtL n t r` equals `D.runAtL (ℓ n) t r`;
`B` ignores `1^n`. The coin types `B.Coins n` and `D.Coins (ℓ n)` correspond along
`PolyExpr.eval_subst` (`finCongr`), so the acceptance probabilities of
`B.distinguisher n (ℓ n)` and `D.distinguisher (ℓ n) (ℓ n)` agree
(`EnsembleLemmas.acceptProb_reparam`); hence the two advantage functions are equal and `h B`
gives negligibility. -/
theorem Ensemble.Indist.toLit {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) :
    X.IndistLit Y := by
  intro D
  obtain ⟨B, hBc, -, hB⟩ := D.exists_reparam ℓ
  refine (h B).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  unfold distAdv
  rw [EnsembleLemmas.acceptProb_reparam hBc hB, EnsembleLemmas.acceptProb_reparam hBc hB]

/-- **Bridge from the literal form to the `1^n` form** for injective `ℓ` (every ensemble of
the text): if `{X_n} ≈ {Y_n}` against literal distinguishers, then also against distinguishers
receiving `1^n` [PS10, Definition 69.4; D5].

The hypothesis `hℓ` excludes only constant `ℓ`: a `PolyExpr` has natural-number coefficients,
so `ℓ.eval` is constant or strictly increasing. For constant `ℓ ≡ L` the two forms coincide as
well (not formalized, no consumer): the `2^L` point tests `t ↦ [t = t₀]` are advice-free
literal distinguishers, so `IndistLit` makes `Σ_{t₀} |Pr[X_n = t₀] − Pr[Y_n = t₀]|`, hence the
statistical distance of `X_n` and `Y_n`, negligible, and that bounds every distinguisher
(`distAdv_le_of_statClose`). So D5's "`D` receives `1^n`" costs nothing for ensembles.

**Proof sketch.** `ℓ.eval` is monotone (`PolyExpr.eval_mono`) and injective, hence strictly
increasing, so `n ≤ ℓ n` for all `n`. Let `φ m := n` if `m = ℓ n` (`Classical.choose` of the
preimage, unique by injectivity) and `φ m := 0` off the image; then `φ m ≤ m`, so
`NUPPT.exists_reparam_advice D φ .var` gives a machine `B` with coins `D.coins.subst var =
D.coins` that at parameter `m = ℓ n` runs `D` at parameter `φ m = n` on its first
`D.coinLen n` coins, with the advice `⟨1^n, D.advice n⟩` hard-wired at length `ℓ n`. Hence
`B.distinguisher (ℓ n) (ℓ n)` and `D.distinguisher n (ℓ n)` have equal advantages after
discarding the unread coins (`EnsembleLemmas.acceptProb_reparam_advice`: the coin split
`EnsembleLemmas.coinsEquiv` built on `Fin.appendEquiv`, then
`EnsembleLemmas.acceptProb_coins_fst`), and `h B` gives negligibility. -/
theorem Ensemble.IndistLit.toIndist {ℓ : PolyExpr} {X Y : Ensemble ℓ}
    (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y := by
  classical
  intro D
  have hsm : StrictMono ℓ.eval := ℓ.eval_mono.strictMono_of_injective hℓ
  have hle : ∀ n, n ≤ ℓ.eval n := fun n => hsm.id_le n
  let φ : ℕ → ℕ := fun m => if hm : ∃ n, ℓ.eval n = m then hm.choose else 0
  have hφ : ∀ m, φ m ≤ PolyExpr.var.eval m := by
    intro m
    simp only [φ, PolyExpr.eval_var]
    split_ifs with hm
    · exact (hle _).trans_eq hm.choose_spec
    · exact Nat.zero_le _
  have hφn : ∀ n, φ (ℓ.eval n) = n := by
    intro n
    have hm : ∃ n', ℓ.eval n' = ℓ.eval n := ⟨n, rfl⟩
    simp only [φ, dif_pos hm]
    exact hℓ hm.choose_spec
  obtain ⟨A, hAc, hA⟩ := D.exists_reparam_advice φ .var hφ
  refine (h A).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  have hle' : D.coinLen (φ (ℓ.eval n)) ≤ D.coinLen (PolyExpr.var.eval (ℓ.eval n)) := by
    rw [hφn, PolyExpr.eval_var]
    exact D.coins.eval_mono (hle n)
  unfold distAdv
  rw [EnsembleLemmas.acceptProb_reparam_advice hAc hA (ℓ.eval n) hle',
    EnsembleLemmas.acceptProb_reparam_advice hAc hA (ℓ.eval n) hle', hφn]

/-- **Closure under efficient operations** [PS10, Lemma 71.5]: if `{X_n} ≈ {Y_n}` then for every
non-uniform PPT `M` (and every explicit output length `ℓ'`), `{M(X_n)} ≈ {M(Y_n)}`.

**Proof sketch.** Fix a distinguisher `D` of the image ensembles. The machine
`D' := EnsembleLemmas.exists_pushRed M D ℓ'` (coins `M.coins + D.coins`, advice
`combineAdvice (M.advice n) (D.advice n)`, built as `NUPPT.ofPolyTime` of a raw function of
the layout `⟨⟨⟨1^n, t⟩, α⟩, r⟩` as in `NUPPT.exists_seq`) runs `M` on `t` with the first
`M.coins n` coins, pads the result to `ℓ'(n)` bits *inside the layout*, where `1^n` is
available (`NUPPT.exists_comp` sees only `y`, gate 03a finding 3; the padding is
`EnsembleLemmas.polyTimeComputable_padL`, a typed cut `pairTakePoly ℓ'` of the output
followed by `0^{ℓ'(n)}`), and hands it to `D` with the remaining coins. Its distinguisher at
`n` is the concrete `sunglassRed P (D.distinguisher n (ℓ' n))` with
`P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` up to the coin split
`EnsembleLemmas.coinsEquiv` (`Fin.appendEquiv`), so by `acceptProb_bind`
(`EnsembleLemmas.acceptProb_pushRed`) its acceptance probabilities on `X_n`, `Y_n` are those
of `D` on `pushSampler P (X.X n) = (X.push M ℓ').X n` and `(Y.push M ℓ').X n`. Hence the
advantage function of `D` on the images is that of `D'` on `X, Y`, negligible by `h D'`. -/
theorem Ensemble.Indist.push {ℓ ℓ' : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) :
    (X.push M ℓ').Indist (Y.push M ℓ') := by
  intro D
  obtain ⟨B, hBc, hB⟩ := EnsembleLemmas.exists_pushRed M D ℓ'
  refine (h B).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  unfold distAdv
  rw [EnsembleLemmas.acceptProb_pushRed hBc hB (X := X.X n),
    EnsembleLemmas.acceptProb_pushRed hBc hB (X := Y.X n)]
  rfl

/-- **The hybrid lemma** [PS10, Lemma 71.6], at one parameter: if `D` distinguishes `X^0` and
`X^m` with advantage `ε` then some consecutive pair `X^i, X^{i+1}` (`i < m`) is distinguished
by `D` with advantage at least `ε / m`. (The text indexes `X^1, …, X^m` and loses the factor
`m` where `m − 1` steps would do; harmless.) This is the concrete `exists_hybrid_gap` applied to
the acceptance probabilities `g_i = Pr[t ← X^i : D(t) = 1]`. All hybrids share one seed type
`σ` (`X : ℕ → σ → γ`); hybrids with seeds of different shapes are first embedded into a
common product seed. -/
theorem hybrid_lemma {σ γ ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (X : ℕ → σ → γ) (D : γ → ρ → Bool) :
    ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i + 1)) D := by
  obtain ⟨i, hi, h⟩ := exists_hybrid_gap (fun i => acceptProb (X i) D) hm
  exact ⟨i, hi, h⟩

/-- **Transitivity of `≈`** [PS10, §3.1.1, "Transitivity – The Hybrid Lemma"]: the two-step
case of the hybrid lemma. The advantage between `X` and `Z` is at most the sum of the
advantages between `X, Y` and `Y, Z` (triangle inequality), and sums of negligible functions
are negligible. -/
theorem Ensemble.Indist.trans {ℓ : PolyExpr} {X Y Z : Ensemble ℓ} (h₁ : X.Indist Y)
    (h₂ : Y.Indist Z) : X.Indist Z := by
  intro D
  refine ((h₁ D).add (h₂ D)).mono ⟨0, fun n _ => ?_⟩
  have h0 : 0 ≤ distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) +
      distAdv (Y.X n) (Z.X n) (D.distinguisher n (ℓ.eval n)) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [abs_of_nonneg h0]
  unfold distAdv
  rw [abs_abs]
  exact abs_sub_le _ _ _

/-- **Polynomially many copies** (the multicopy corollary of the hybrid lemma,
[PS10, Lemma 71.6; Gar26, Lemma 3.3]): if `{X_n} ≈ {Y_n}` and both ensembles are efficiently
samplable, then `t(n)` independent copies remain indistinguishable for every syntactic
polynomial `t`.

The samplability hypotheses are those of [Gar26, Lemma 3.3]'s uniform reduction, which
samples the other copies (D6). Against non-uniform distinguishers they can be dropped: hard-wire
the hybrid index and the other `t(n) − 1` copies that keep the gap as advice
(`NUPPT.exists_withAdvice`). That form is not proved, since no consumer needs copies of a
non-samplable ensemble (gate 03a, finding 2).

**Proof sketch.** Fix a distinguisher `D` of the `t(n)`-fold products. At each `n` with
`t(n) > 0`, `exists_multicopyRed_ge` (through the block bijection `blocks`) gives a hybrid
index `k_n < t(n)` such that the concrete reduction `multicopyRed (X.X n) (Y.X n) (t n) k_n D'`
(sample `k_n` copies of `Y`, `t(n) − k_n − 1` copies of `X`, plant the challenge at position
`k_n`, call `D` once) has advantage at least `ε(n) / t(n)`; the index is chosen per `n`
(`choose`; for `t(n) = 0` any index, both products being the one-point distribution,
`EnsembleLemmas.distAdv_eq_zero_of_subsingleton`) and `1^{k_n}` is hard-wired into the
advice (`NUPPT.exists_withAdvice`). The reduction is the `NUPPT` of
`EnsembleLemmas.exists_copiesRed`: the `Samplable` evaluators of `X` and `Y` are run on the
`t(n)` chunks of fresh coins by the state loop `EnsembleLemmas.CopiesLoop`
(`polyTimeComputable_iterateEmit`, coins cut by `pairTakePoly`/`pairDropPoly`, the challenge
planted at the hard-wired position), and `D` is called through `NUPPT.exists_seq`. The laws
of the sampled copies equal the ideal `X.X n`, `Y.X n` (`StatClose … 0`, lifted to the product
by `EnsembleLemmas.statClose_copies` and `StatClose.prod`), so the acceptance probabilities
coincide exactly (`EnsembleLemmas.acceptProb_multicopyRed_congr`). Hence
`distAdv ((X.copies t).X n) ((Y.copies t).X n) D ≤ t(n) · distAdv (X.X n) (Y.X n) B_n` with
the reduction `B` independent of `n` up to the advice, and `t(n) ≤ C (n+1)^c`
(`PolyExpr.eval_le`) makes the right-hand side negligible
(`EnsembleLemmas.negligible_polyExpr_mul`, from `Negligible.mul_pow` and
`Negligible.const_mul`); `Negligible.mono` concludes. -/
theorem Ensemble.Indist.copies {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y)
    (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) :
    (X.copies t).Indist (Y.copies t) := by
  classical
  obtain ⟨sX, SX, hSX, hXc⟩ := hX
  obtain ⟨sY, SY, hSY, hYc⟩ := hY
  intro D
  -- the distinguisher of `t(n)`-tuples behind `D`
  obtain ⟨D', hD'⟩ : ∃ D' : ∀ n, (Fin (t.eval n) → Fin (ℓ.eval n) → Bool) → D.Coins n → Bool,
      ∀ n v r, D' n v r = D.distinguisher n ((PolyExpr.mul t ℓ).eval n)
        ((EnsembleLemmas.blocks (t.eval n) (ℓ.eval n)).symm v) r := ⟨_, fun _ _ _ => rfl⟩
  have hadv : ∀ n, distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) =
      distAdv (TCSlib.Cryptography.copies (t.eval n) (X.X n))
        (TCSlib.Cryptography.copies (t.eval n) (Y.X n)) (D' n) := by
    intro n
    have e : ∀ Z : Ensemble ℓ, acceptProb ((Z.copies t).X n)
        (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) =
        acceptProb (TCSlib.Cryptography.copies (t.eval n) (Z.X n)) (D' n) := by
      intro Z
      refine OneWay.uprob_congr fun z => ?_
      rw [hD']
      exact Iff.rfl
    unfold distAdv
    rw [e, e]
  -- the hybrid index at each `n` (any index when `t(n) = 0`)
  have hex : ∀ n, ∃ k, k ≤ t.eval n ∧ (0 < t.eval n → k < t.eval n ∧
      distAdv (TCSlib.Cryptography.copies (t.eval n) (X.X n))
        (TCSlib.Cryptography.copies (t.eval n) (Y.X n)) (D' n) / t.eval n ≤
        distAdv (X.X n) (Y.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) k (D' n))) := by
    intro n
    by_cases ht : 0 < t.eval n
    · obtain ⟨k, hk, hge⟩ := exists_multicopyRed_ge (X.X n) (Y.X n) ht (D' n)
      exact ⟨k, hk.le, fun _ => ⟨hk, hge⟩⟩
    · exact ⟨0, Nat.zero_le _, fun h' => absurd h' ht⟩
  choose k hk using hex
  obtain ⟨B, hBc, hB⟩ := EnsembleLemmas.exists_copiesRed D hSX hSY sX sY ℓ t k fun n => (hk n).1
  -- the machine's advantage is the concrete reduction's advantage
  have hBadv : ∀ n, distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) =
      distAdv (X.X n) (Y.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) (k n) (D' n)) := by
    intro n
    have hlen : B.coinLen n = (t.eval n * sX.eval n + t.eval n * sY.eval n) + D.coinLen n := by
      simp [NUPPT.coinLen, hBc]
    obtain ⟨e, he⟩ : ∃ e : ((Fin (t.eval n) → Fin (sX.eval n) → Bool) ×
        (Fin (t.eval n) → Fin (sY.eval n) → Bool)) × D.Coins n ≃ B.Coins n,
        ∀ c, e c = EnsembleLemmas.coinsEquiv hlen
          (EnsembleLemmas.coinsEquiv rfl ((EnsembleLemmas.blocks _ _).symm c.1.1,
            (EnsembleLemmas.blocks _ _).symm c.1.2), c.2) :=
      ⟨((((EnsembleLemmas.blocks _ _).symm.prodCongr (EnsembleLemmas.blocks _ _).symm).trans
        (EnsembleLemmas.coinsEquiv rfl)).prodCongr (Equiv.refl _)).trans
          (EnsembleLemmas.coinsEquiv hlen), fun _ => rfl⟩
    have hpt : ∀ (z : Fin (ℓ.eval n) → Bool) c, B.distinguisher n (ℓ.eval n) z (e c) =
        multicopyRed
          (fun r : Fin (sX.eval n) → Bool => padFin (ℓ.eval n) (SX (NUPPT.advInput n (List.ofFn r))))
          (fun r : Fin (sY.eval n) → Bool => padFin (ℓ.eval n) (SY (NUPPT.advInput n (List.ofFn r))))
          (t.eval n) (k n) (D' n) z c := by
      intro z c
      rw [he]
      simp only [NUPPT.distinguisher, NUPPT.runAt_eq, EnsembleLemmas.ofFn_coinsEquiv, hB,
        multicopyRed, hD']
    have hdist : ∀ Z : Ensemble ℓ, acceptProb (Z.X n) (B.distinguisher n (ℓ.eval n)) =
        acceptProb (Z.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) (k n) (D' n)) := by
      intro Z
      rw [← EnsembleLemmas.acceptProb_coins_equiv e, ← EnsembleLemmas.acceptProb_multicopyRed_congr
        (hXc n) (hYc n)]
      congr 1
      funext z c
      exact hpt z c
    unfold distAdv
    rw [hdist, hdist]
  -- the hybrid bound at each `n`
  have hbound : ∀ n, distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) ≤
      (t.eval n : ℝ) * distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) := by
    intro n
    rw [hBadv, hadv]
    by_cases ht : 0 < t.eval n
    · obtain ⟨-, hk2⟩ := (hk n).2 ht
      have htR : (0 : ℝ) < t.eval n := by exact_mod_cast ht
      rw [div_le_iff₀ htR] at hk2
      linarith
    · have ht0 : t.eval n = 0 := Nat.eq_zero_of_not_pos ht
      have hsub : Subsingleton (Fin (t.eval n) → Fin (ℓ.eval n) → Bool) := by
        rw [ht0]
        infer_instance
      rw [EnsembleLemmas.distAdv_eq_zero_of_subsingleton]
      exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  refine (EnsembleLemmas.negligible_polyExpr_mul t (h B)).mono ⟨0, fun n _ => ?_⟩
  have h₁ : (0 : ℝ) ≤ distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) := abs_nonneg _
  have h₂ : (0 : ℝ) ≤ distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) := abs_nonneg _
  rw [abs_of_nonneg h₁, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) h₂)]
  exact hbound n

/-! ### Distinguishing versus predicting [PS10, p. 73, Lemma 73.8] -/

/-- The sampler of the prediction experiment `b ← {0,1}; t ← X^b_n` [PS10, Lemma 73.8]: output
the bit `b` together with a sample of `X¹_n` if `b = 1` and of `X⁰_n` otherwise (both seeds are
drawn; the unused one is ignored). -/
def mixEnsemble {ℓ : PolyExpr} (X₀ X₁ : Ensemble ℓ) (n : ℕ) :
    Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool) :=
  fun z => (z.1, if z.1 then X₁.X n z.2.2 else X₀.X n z.2.1)

/-- **Predicting is distinguishing** — the identity behind [PS10, p. 73 ("any such predictor
would be a valid distinguisher (show this!)") and the proof of Lemma 73.8]: for samplers
`X⁰, X¹` and any `D` (used as a predictor of the bit `b` in `b ← {0,1}; t ← X^b`),
`Pr[D(t) = b] = 1/2 + (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2`. In particular a predictor with
success `1/2 + δ` is a distinguisher with advantage `2δ`, and conversely.

**Repair (run-3 audit P2-2):** the seed types and the coin type carry `Nonempty` instances
(with an empty `ρ`, `σ₀` or `σ₁` the left-hand side is the probability over an empty space,
`0`, while the right-hand side is `1/2`); for ensemble seeds (`Ensemble.nonempty`) and machine
coins (`Fin k → Bool`) they are found by instance resolution.

**Proof sketch.** Split on `b` (`uprob_bool_prod` after regrouping the sample space): for
`b = 1` the event is `D(X¹) = 1`, for `b = 0` it is `D(X⁰) ≠ 1`, whose probability is
`1 − Pr[D(X⁰) = 1]` (`uprob_not`); the unused seed is an ignored uniform coordinate
(`acceptProb_fst`, `acceptProb_snd`). -/
theorem predict_eq {ℓ : ℕ} {σ₀ σ₁ ρ : Type*} [Fintype σ₀] [Fintype σ₁] [Fintype ρ]
    [Nonempty σ₀] [Nonempty σ₁] [Nonempty ρ]
    (X₀ : σ₀ → (Fin ℓ → Bool)) (X₁ : σ₁ → (Fin ℓ → Bool)) (D : (Fin ℓ → Bool) → ρ → Bool) :
    uprob (fun z : (Bool × (σ₀ × σ₁)) × ρ =>
        D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) =
      1 / 2 + (acceptProb X₁ D - acceptProb X₀ D) / 2 := by
  rw [← uprob_comp_equiv (Equiv.prodAssoc Bool (σ₀ × σ₁) ρ).symm, uprob_bool_prod]
  have hA : uprob (fun c : (σ₀ × σ₁) × ρ => D (X₀ c.1.1) c.2 = false) =
      1 - acceptProb X₀ D := by
    rw [← acceptProb_fst (τ := σ₁) X₀ D, acceptProb, ← uprob_not]
    congr 1
    funext c
    simp
  have hB : uprob (fun c : (σ₀ × σ₁) × ρ => D (X₁ c.1.2) c.2 = true) = acceptProb X₁ D := by
    rw [← acceptProb_snd (τ := σ₀) X₁ D]
    rfl
  simp only [Equiv.prodAssoc_symm_apply, Bool.false_eq_true, if_false, if_true]
  rw [hA, hB]
  ring

/-- **The prediction lemma** [PS10, Lemma 73.8]: if a non-uniform PPT `D` distinguishes
`{X⁰_n}` and `{X¹_n}` with probability `μ(n)` for infinitely many `n`, then there is a
non-uniform PPT `A` with `Pr[b ← {0,1}; t ← X^b_n : A(1^n, t) = b] > 1/2 + μ(n)/2` for
infinitely many `n`.

**Repair (run-3 audit P2-2):** the ad hoc hypotheses `h₀ h₁ : ∀ n, Nonempty (X.σ n)` of the
run-2 statement were dropped; they are the field `Ensemble.nonempty`, and the frozen shape of
DESIGN.md §2.11 is restored.

**Proof sketch.** By `predict_eq` at each `n`, `D` itself predicts with probability
`1/2 + (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2` and the negated machine `D'` (output `[true]`
iff `D`'s output is not `[true]`: `EnsembleLemmas.exists_negRed`, i.e. `NUPPT.exists_comp`
with the FP-level `polyTimeComputable_ite` on `pairEq`) predicts with probability
`1/2 − (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2`. On the infinite set of `n` where
`μ(n) < |Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]|`, the sign of the difference is positive infinitely
often or negative infinitely often (pigeonhole on an infinite set, no advice needed); take
`A := D` in the first case and `A := D'` in the second. The seed-space reindexing between the
experiment of the statement and `predict_eq` is `uprob_comp_equiv`. -/
theorem prediction_lemma {ℓ : PolyExpr} (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ)
    (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ.eval n))) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1 / 2 + μ n / 2 <
      uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
        A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1 := by
  -- the signed advantage of `D`
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ n, δ n = acceptProb (X₁.X n) (D.distinguisher n (ℓ.eval n)) -
      acceptProb (X₀.X n) (D.distinguisher n (ℓ.eval n)) := ⟨_, fun _ => rfl⟩
  have hkey : ∀ n, distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ.eval n)) = |δ n| := fun n => by
    rw [hδ]
    exact abs_sub_comm _ _
  -- predicting is distinguishing, for any machine `A`
  have hpred : ∀ (A : NUPPT) n, (uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
      A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1) =
      1 / 2 + (acceptProb (X₁.X n) (A.distinguisher n (ℓ.eval n)) -
        acceptProb (X₀.X n) (A.distinguisher n (ℓ.eval n))) / 2 := fun A n =>
    predict_eq (X₀.X n) (X₁.X n) (A.distinguisher n (ℓ.eval n))
  by_cases hpos : ∀ n₀, ∃ n ≥ n₀, μ n < δ n
  · -- the difference is positive infinitely often: `D` itself predicts
    refine ⟨D, fun n₀ => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hpos n₀
    refine ⟨n, hn, ?_⟩
    rw [hpred, ← hδ]
    linarith
  · -- otherwise it is negative infinitely often: the negated machine predicts
    push_neg at hpos
    obtain ⟨n₁, hn₁⟩ := hpos
    have hneg : ∀ n₀, ∃ n ≥ n₀, μ n < -δ n := by
      intro n₀
      obtain ⟨n, hn, hlt⟩ := h (max n₀ n₁)
      refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
      have h1 := hn₁ n (le_trans (le_max_right _ _) hn)
      rw [hkey] at hlt
      rcases le_or_gt 0 (δ n) with h0 | h0
      · rw [abs_of_nonneg h0] at hlt
        linarith
      · rw [abs_of_neg h0] at hlt
        exact hlt
    obtain ⟨A, hAc, hA⟩ := EnsembleLemmas.exists_negRed D
    refine ⟨A, fun n₀ => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hneg n₀
    refine ⟨n, hn, ?_⟩
    rw [hpred, EnsembleLemmas.acceptProb_negRed hAc hA, EnsembleLemmas.acceptProb_negRed hAc hA]
    have := hδ n
    linarith

/-! ### The pairwise-independent sampling inequality [PS10, Appendix A, p. 189] -/

/-- **Pairwise-independent sampling inequality** [PS10, Appendix A, p. 189]: for pairwise
independent bits `X_1, …, X_m`, each `true` with probability `p`, and `ε > 0`,
`Pr[|∑ᵢ X_i / m − p| ≥ ε] ≤ 1 / (4 ε² m)`. The concrete lemma is
`HardcoreBit.chebyshev_pairwise_ident` [Gar26, Theorem 2.4], restated with the empirical mean.

**Deviation:** the text states the inequality for real random variables with `|X_i| ≤ 1` and
mean `μ` with the bound `(1 − μ²)/(m ε²)`; here the variables are bits (the only case used in
the campaign) and the bound is the variance bound `p(1−p) ≤ 1/4` of the concrete layer. Bits
satisfy the text's hypothesis, and `1/4 > 1 − p²` exactly when `p > √3/2`, so for such `p`
this bound is weaker than the text's (at `p = 1` the text gives `0`); the variance form
`p(1−p)/(m ε²)` would imply both. -/
theorem pairwise_sampling_ineq {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    {X : ι → Ω → Bool} (hX : HardcoreBit.PairwiseIndep X) {p : ℝ}
    (hp : ∀ i, uprob (fun ω => X i ω = true) = p) {ε : ℝ} (hε : 0 < ε)
    (hm : 0 < Fintype.card ι) :
    uprob (fun ω => ε ≤ |(∑ i, HardcoreBit.ind (X i ω)) / Fintype.card ι - p|) ≤
      1 / (4 * ε ^ 2 * Fintype.card ι) := by
  have hm' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
  refine le_of_eq_of_le ?_ (HardcoreBit.chebyshev_pairwise_ident hX hp hε hm)
  apply OneWay.uprob_congr
  intro ω
  rw [show (∑ i, HardcoreBit.ind (X i ω)) / (Fintype.card ι : ℝ) - p =
      (∑ i, HardcoreBit.ind (X i ω) - p * Fintype.card ι) / Fintype.card ι by
        field_simp, abs_div, abs_of_pos hm', le_div_iff₀ hm']

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/OneWay.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.OneWayYao
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Amplification
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-way functions, asymptotic layer

The one-way function definitions of [PS10, §2.2] and the hardness amplification theorems of
[PS10, §2.4], stated over the machine layer `Complexity.NUPPT` and the typed concrete
experiments of `TCSlib.Cryptography.Foundations.Experiments` (foundation decisions D2, D3,
D5 of `PassShelatChapter2-4Plan.md`).

A *function family* `FunFamily` is `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with syntactic
polynomial lengths (the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p`, parameter =
input length; exact for length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding to
`p(n)` bits is lossy); `FunFamily.invProbAt 𝓕 A n` is the experiment
`Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y]` for the machine `A`, its output decoded as an
`inLen n`-bit string. The three one-wayness notions of [PS10, Definitions 26.1, 27.3, 28.4]
follow — Definition 26.1 in its `1^n` form `FunFamily.WorstCaseOneWay` (headline) and its
literal form `FunFamily.WorstCaseOneWayLit` (`A(f(x))` only), related by
`WorstCaseOneWay.toLit` and `WorstCaseOneWayLit.toParam` (D5, run-3 audit P3-2) —
then the direct product `FunFamily.prod` with the parameters `yaoBlocks`/`yaoRounds`
(`m = 2nq(n)`, `T = 2nm(n)n^c`) of [PS10, §2.4.3], the theorems `weak_to_strong`
[PS10, Theorem 35.1], `strong_prod_two` [PS10, Theorem 35.2], `claim_38_2` (the parameter
instantiation of the concrete `OneWay.yao_amplification_exp` [Gar26, Theorem 2.1]), the sanity
results `FunFamily.StrongOneWay.weak` and `not_strongOneWay_id`, `not_weakOneWay_id`,
`not_worstCaseOneWay_id` (the adversary classes are not vacuous), and
`PermFamily`/`OneWayPermutation` (the single-function form of [PS10, Definition 55.1], as used
in Theorems 79.4 and 126.4). Every
asymptotic theorem is proved by (i) instantiating the concrete reduction at every `n`,
(ii) exhibiting the reduction as a `Complexity.NUPPT` by the closure calculus of
`TCSlib/Complexity/Randomized/`, (iii) negligible-function arithmetic (`not_negligible_iff`).

**Deviation:** domains are typed at each parameter (D5): the direct product `𝓕.prod q` is the
family at parameter `n` with input length `q(n)·inLen(n)` and its adversaries receive `1^n`
where the text's adversary of `f'` receives `1^{n·m(n)}`; the two are interderivable
(`1^{n·m(n)}` is computed from `1^n` by `polyTimeComputable_unaryPoly`, and `n` is recovered
from `n·m(n)` by a polynomial search, `m` being monotone), so the classes coincide. The
deviations of `Easy`, `invProbAt` and `WeakOneWay` are recorded on the declarations.

## Main definitions

* `TCSlib.Cryptography.FunFamily` (`Easy`, `invProbAt`, `ofString`, `LengthRegular`, `blocks`,
  `prod`); `FunFamily.StrongOneWay`, `FunFamily.WeakOneWay`, `FunFamily.WorstCaseOneWay`
  (`1^n` form, headline) and `FunFamily.WorstCaseOneWayLit` (literal form)
  [PS10, Definitions 27.3, 28.4, 26.1].
* `TCSlib.Cryptography.yaoBlocks`, `yaoRounds` — `m = 2nq(n)`, `T = 2nm(n)n^c` [PS10, §2.4.3].
* `TCSlib.Cryptography.PermFamily`, `TCSlib.Cryptography.OneWayPermutation`.

## Main results

* `TCSlib.Cryptography.weak_to_strong` [PS10, Theorem 35.1], `strong_prod_two`
  [PS10, Theorem 35.2], `claim_38_2` (parameter instantiation, [PS10, §2.4.3]),
  `OneWay.invProb_prodFun_le_yaoTry` (concrete one-call planting, lemma C2 of the inventory).
* `TCSlib.Cryptography.FunFamily.StrongOneWay.weak`, `TCSlib.Cryptography.not_strongOneWay_id`,
  `not_weakOneWay_id`, `not_worstCaseOneWay_id`,
  `TCSlib.Cryptography.FunFamily.invProbAt_ofString_id_eq_one` — sanity and non-vacuity.
* `TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit`,
  `TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam` — the two forms of
  [PS10, Definition 26.1] (always / for injective `outLen`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Function families -/

/-- A family `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with explicit polynomial lengths: the
typed reading (D5) of the textbook `f : {0,1}* → {0,1}*` at security parameter `n`
[PS10, §2.2]. A string function `f` gives the family `ofString f p`, exact for length-regular
`f` (`ofFn_ofString_f`); otherwise the `false`-padding to `p(n)` bits is lossy. -/
structure FunFamily where
  /-- The input length at parameter `n`. -/
  inLen : PolyExpr
  /-- The output length at parameter `n`. -/
  outLen : PolyExpr
  /-- The function at parameter `n`. -/
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily

/-- `𝓕` is *easy to compute*: a polynomial-time string function computes `f n x` from
`⟨1^n, x⟩` [PS10, Definitions 26.1 (1) and 27.3 (1)].

**Deviation:** `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead
of a PPT computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`). -/
def Easy (𝓕 : FunFamily) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)

/-- The inversion probability of the machine `A` against `𝓕` at parameter `n`:
`Pr[x ← {0,1}^{inLen n}; y ← f(x); r : f(A(1^n, y; r)) = y]` with the output of `A` decoded as
an `inLen n`-bit string [PS10, Definitions 27.3 and 28.4, the displayed experiment].

**Deviation:** `inverter`: wrong-length output = failure (D5). -/
noncomputable def invProbAt (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))

/-- `𝓕` is a *strong one-way function*: easy to compute, and every non-uniform PPT inverts it
with negligible probability [PS10, Definition 27.3]. -/
structure StrongOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: negligible inversion probability for every `A`. -/
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n

/-- `𝓕` is a *weak one-way function*: easy to compute, and there is a polynomial `q` such
that every non-uniform PPT inverts it with probability at most `1 - 1/q(n)` for all
sufficiently large `n` [PS10, Definition 28.4].

**Deviation:** `WeakOneWay`: `0 < q n` made explicit (`1 - 1/0 = 1` would make the clause
vacuous). -/
structure WeakOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert with probability `1 - 1/q(n)`. -/
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)

/-- `𝓕` is a *worst-case one-way function*: easy to compute, and no non-uniform PPT inverts
it on every input with probability one [PS10, Definition 26.1], in the `1^n` form: the
adversary receives `1^n` and `f(x)` (`inverter`, D5) and must return an `inLen n`-bit
preimage. This is the headline form of the definition; the literal form (the adversary
receives `f(x)` only) is `WorstCaseOneWayLit`, and the two are related by
`WorstCaseOneWay.toLit` (always) and `WorstCaseOneWayLit.toParam` (injective `outLen`), as
`Ensemble.Indist`/`Ensemble.IndistLit` for [PS10, Definition 69.4].

Repair (run-3 audit P3-2): the frozen headline was the literal form (now `WorstCaseOneWayLit`),
which can be vacuously satisfied by families whose output length does not determine `n` (e.g.
the constant family `x ↦ ε`, trivially invertible in the text); the `1^n`
form is now the headline, mirroring D5's treatment of Definition 69.4.

**Deviation:** the adversary receives `1^n` where the text writes `A(f(x))` (D5; the literal
reading is `WorstCaseOneWayLit`); inverses are sought in the domain at the current parameter
(`inverter`, wrong-length output = failure). -/
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: no `A` with `∀ x, Pr[A(1^n, f(x)) ∈ f⁻¹(f(x))] = 1`. -/
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

/-- `𝓕` is a *worst-case one-way function in the literal form* of [PS10, Definition 26.1]:
easy to compute, and no non-uniform PPT inverts it on every input with probability one, the
adversary receiving `f(x)` only (activation at the output length, `inverterLit`, D5) and
returning an `inLen n`-bit preimage.

Repair (run-3 audit P3-2): renamed from `WorstCaseOneWay`; the `1^n` form `WorstCaseOneWay` is
the headline, and `WorstCaseOneWay.toLit`/`WorstCaseOneWayLit.toParam` relate the two.

**Deviation:** when `outLen` is constant, so that `|f(x)|` does not determine `n`, the literal
form can hold for families that are trivially invertible given `1^n`, an artefact of D5's
typed inverse (the literal adversary cannot know `n`): e.g. the constant family `x ↦ ε` with
`inLen = var`, `outLen = 0` (the adversary cannot know the required output length `inLen n`),
or `f n b = b ⊕ [n odd]` on one bit (it cannot know the parity of `n`; gate 03b, finding 9).
The `1^n` form is the headline; `toParam` applies whenever `outLen` is non-constant (for
`PolyExpr` lengths, injective ⇔ non-constant), so for families with non-constant `outLen` the two
forms coincide (`toLit`, `toParam`); with constant `outLen` they can differ, as above (gate 03b,
round 2, R2-2). -/
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: no `A` with `∀ x, Pr[A(f(x)) ∈ f⁻¹(f(x))] = 1`. -/
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

/-- The output length of a string function on inputs of length `n`, read off at `0^n`. -/
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ := (f (List.replicate n false)).length

/-- The textbook `f : {0,1}* → {0,1}*` with the output length `p`: parameter = input length,
the output padded or truncated to `p(n)` bits (exact when `f` is `LengthRegular f p`).

Inversion is typed (D5, `NUPPT.inverter`): an inverter of `ofString f p` at parameter `n` must
return a preimage of length `n`, while [PS10, Definition 27.3] accepts a preimage of any
length. The two experiments agree when `f` is length-regular with non-constant `p` (then
`|f(x)|` determines `|x|`); with constant `p` neither notion is satisfiable. Otherwise the typed
notion can be strictly weaker. An informal example (not formalized; gate 03a, note 15): let `h` be
a length-preserving one-way function and `g(x ‖ b) := h(x) ‖ 1` on non-empty inputs (again
length-preserving and one-way, with every output ending in `1`); put `f(0^k ‖ w) := w` for
`|w| = k ≥ 1` and `f(x) := g(x)` elsewhere, and take `p = var`. In the text's experiment
`y ↦ 0^{|y|} ‖ y` inverts `f` with probability one. In the typed experiment on `ofString f .var`
the special outputs are padded with zeros, so they end in `0` and cannot equal an ordinary output;
an inverter succeeds on an ordinary challenge only by inverting `g`, so its success is at most
its success against `g` plus `O(2^{-n/2})`. The final `1` matters: without it the zero padding can
make special outputs collide with ordinary ones, and the typed experiment is then not harder
(gate 03b, round 2, R2-1). -/
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily where
  inLen := .var
  outLen := p
  f _ x i := (f (List.ofFn x)).getD i false

/-- `f` is *length-regular* with output length `p`: `|f x| = p(|x|)` for every `x`. -/
def LengthRegular (f : List Bool → List Bool) (p : PolyExpr) : Prop :=
  ∀ x, (f x).length = p.eval x.length

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation. -/
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The direct product `f'_n = (f_n)^{q n}` of [PS10, Theorem 35.1]:
`f'(x₁, …, x_{q(n)}) = (f(x₁), …, f(x_{q(n)}))` on blocks, encoded as concatenations;
`OneWay.prodFun` [Gar26, Theorem 2.1] blockwise. -/
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily where
  inLen := .mul q 𝓕.inLen
  outLen := .mul q 𝓕.outLen
  f n x := (blocks (q.eval n) (𝓕.outLen.eval n)).symm
    (TCSlib.Cryptography.OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x))

/-! ### Unfolding lemmas -/

/-- The inversion probability is nonnegative. -/
theorem invProbAt_nonneg (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : 0 ≤ 𝓕.invProbAt A n :=
  invProbOpt_nonneg _ _

/-- The inversion probability is at most one. -/
theorem invProbAt_le_one (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : 𝓕.invProbAt A n ≤ 1 :=
  invProbOpt_le_one _ _

/-- The inversion probability unfolded: the probability over `x` and the coins `r` that the
activation `A(1^n, f(x); r)` is the encoding of some `x'` with `f(x') = f(x)`. -/
theorem invProbAt_eq_uprob (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) :
    𝓕.invProbAt A n = uprob fun z : (Fin (𝓕.inLen.eval n) → Bool) × A.Coins n =>
      ∃ x', A.runAt n (List.ofFn (𝓕.f n z.1)) z.2 = List.ofFn x' ∧ 𝓕.f n x' = 𝓕.f n z.1 := by
  unfold invProbAt invProbOpt
  congr 1
  funext z
  simp only [NUPPT.inverter_eq_some_iff]

/-! ### The two forms of Definition 26.1 -/

/-- **The `1^n` form implies the literal form** of [PS10, Definition 26.1] (repair of the
run-3 audit, P3-2; the analogue of `Ensemble.Indist.toLit`): a literal inverter `A`, activated at
the output length `|f(x)| = outLen n`, is the `1^n`-inverter `NUPPT.exists_reparam A outLen`,
so if no `1^n`-inverter succeeds on every input, no literal inverter does.

**Proof sketch.** `NUPPT.exists_reparam A 𝓕.outLen` gives `B` with
`B.runAtL n y r = A.runAtL (outLen n) y r` and `B.coins = A.coins.subst outLen`, so
`B.Coins n ≃ A.Coins (outLen n)` (`PolyExpr.eval_subst`, `finCongr`); `uprob_comp_equiv`
transports the success event, and `NUPPT.inverter`/`NUPPT.inverterLit` unfold to the same
`decodeFin` of the same activation (`List.ofFn_congr`). -/
theorem WorstCaseOneWay.toLit {𝓕 : FunFamily} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit := by
  refine ⟨h.easy, ?_⟩
  rintro ⟨A, hA⟩
  obtain ⟨B, hBc, -, hB⟩ := A.exists_reparam 𝓕.outLen
  refine h.hard ⟨B, fun n x => ?_⟩
  have hlen : B.coinLen n = A.coinLen (𝓕.outLen.eval n) := by
    simp only [NUPPT.coinLen, hBc, PolyExpr.eval_subst]
  let e : A.Coins (𝓕.outLen.eval n) ≃ B.Coins n :=
    Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)
  rw [← uprob_comp_equiv e]
  refine (OneWay.uprob_congr fun r => ?_).trans (hA n x)
  have hofn : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen.symm r).symm
  simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hB, hofn]

/-- **The literal form implies the `1^n` form when the output length determines the
parameter** (injective `outLen`, the case of every family of the text; repair of the run-3
audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a `1^n`-inverter `B` is the literal
inverter `NUPPT.exists_reparam_advice B φ var` with `φ (outLen n) = n`, which hard-wires `1^n`
and `B.advice n` at the output length and leaves its extra coins unread.

**Proof sketch.** An injective monotone `outLen.eval` (`PolyExpr.eval_mono`) is strictly
monotone (`Monotone.strictMono_of_injective`), so `n ≤ outLen n` (`StrictMono.id_le`) and
`φ m := the n with outLen n = m` (`0` if none) is majorised by `var`.
`NUPPT.exists_reparam_advice B φ var` gives `A` with
`A.runAtL m y r = B.runAtL (φ m) y (r.take (B.coinLen (φ m)))`; at `m = outLen n` we have
`φ m = n` and `A.Coins m ≃ B.Coins n × (Fin (B.coinLen m − B.coinLen n) → Bool)`
(`Fin.appendEquiv`, `finCongr`, `PolyExpr.eval_mono`); `List.ofFn_fin_append` and
`List.take_left'` identify the literal event with the `1^n` event on the first factor
(`uprob_comp_equiv`, `uprob_fst`). -/
theorem WorstCaseOneWayLit.toParam {𝓕 : FunFamily} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay := by
  classical
  refine ⟨h.easy, ?_⟩
  rintro ⟨B, hB⟩
  have hsm : StrictMono 𝓕.outLen.eval := 𝓕.outLen.eval_mono.strictMono_of_injective hinj
  have hle : ∀ n, n ≤ 𝓕.outLen.eval n := fun n => hsm.id_le n
  let φ : ℕ → ℕ := fun m => if hm : ∃ n, 𝓕.outLen.eval n = m then hm.choose else 0
  have hφ : ∀ m, φ m ≤ PolyExpr.var.eval m := by
    intro m
    simp only [φ, PolyExpr.eval_var]
    split_ifs with hm
    · exact (hle _).trans_eq hm.choose_spec
    · exact Nat.zero_le _
  have hφn : ∀ n, φ (𝓕.outLen.eval n) = n := by
    intro n
    have hm : ∃ n', 𝓕.outLen.eval n' = 𝓕.outLen.eval n := ⟨n, rfl⟩
    simp only [φ, dif_pos hm]
    exact hinj hm.choose_spec
  obtain ⟨A, hAc, hA⟩ := B.exists_reparam_advice φ .var hφ
  refine h.hard ⟨A, fun n x => ?_⟩
  have hAlen : A.coinLen (𝓕.outLen.eval n) =
      B.coinLen n + (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) := by
    have h1 : A.coinLen (𝓕.outLen.eval n) = B.coinLen (𝓕.outLen.eval n) := by
      simp only [NUPPT.coinLen, hAc, PolyExpr.eval_subst, PolyExpr.eval_var]
    have h2 : B.coinLen n ≤ B.coinLen (𝓕.outLen.eval n) := B.coins.eval_mono (hle n)
    omega
  let e : B.Coins n × (Fin (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) → Bool) ≃
      A.Coins (𝓕.outLen.eval n) :=
    (Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hAlen.symm) (Equiv.refl Bool))
  rw [← uprob_comp_equiv e]
  have key : ∀ z : B.Coins n × (Fin (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) → Bool),
      (∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) (e z) = some x' ∧
        𝓕.f n x' = 𝓕.f n x) ↔
      ∃ x', B.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) z.1 = some x' ∧
        𝓕.f n x' = 𝓕.f n x := by
    intro z
    have hofn : List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
      rw [← List.ofFn_fin_append]
      exact (List.ofFn_congr hAlen.symm (Fin.append z.1 z.2)).symm
    simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hA, hφn, hofn,
      List.take_left', List.length_ofFn]
  rw [OneWay.uprob_congr key]
  exact (uprob_fst fun r : B.Coins n => ∃ x',
    B.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
      𝓕.f n x' = 𝓕.f n x).trans (hB n x)

/-- On a length-regular `f`, the family `ofString f p` is exactly `f` on encoded strings. -/
theorem ofFn_ofString_f {f : List Bool → List Bool} {p : PolyExpr} (hf : LengthRegular f p)
    (n : ℕ) (x : Fin n → Bool) : List.ofFn ((ofString f p).f n x) = f (List.ofFn x) := by
  have hlen : (f (List.ofFn x)).length = p.eval n := by rw [hf, List.length_ofFn]
  refine List.ext_get (by simp [ofString, hlen]) fun i h₁ h₂ => ?_
  simp [ofString, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- The identity family is the identity at every parameter. -/
theorem ofString_id_f (n : ℕ) (x : Fin n → Bool) : (ofString id .var).f n x = x := by
  have h := ofFn_ofString_f (f := id) (p := .var) (fun x => by simp) n x
  exact List.ofFn_injective (by simpa using h)

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (blocks q ℓ).symm t k = t k.divNat k.modNat := rfl

/-- The encoding of a tuple of blocks is the concatenation of the encodings of the blocks. -/
theorem ofFn_blocks_symm (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) :
    List.ofFn ((blocks q ℓ).symm t) = (List.ofFn fun i => List.ofFn (t i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  rw [blocks_symm_apply]
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
  congr 1
  · refine Fin.ext ?_
    simp only [Fin.coe_divNat]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt j.2, zero_add]
  · refine Fin.ext ?_
    simp only [Fin.coe_modNat]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

/-- The input length of the direct product is `q · inLen`. -/
@[simp] theorem prod_inLen (𝓕 : FunFamily) (q : PolyExpr) : (𝓕.prod q).inLen = .mul q 𝓕.inLen :=
  rfl

/-- The output length of the direct product is `q · outLen`. -/
@[simp] theorem prod_outLen (𝓕 : FunFamily) (q : PolyExpr) :
    (𝓕.prod q).outLen = .mul q 𝓕.outLen := rfl

/-- The direct product unfolded: `prodFun` between the block bijections. -/
theorem prod_f (𝓕 : FunFamily) (q : PolyExpr) (n : ℕ) (x : Fin (q.eval n * 𝓕.inLen.eval n) → Bool) :
    (𝓕.prod q).f n x = (blocks (q.eval n) (𝓕.outLen.eval n)).symm
      (OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x)) := rfl

/-- The inversion probability of the direct product is the concrete `invProbOpt` of
`OneWay.prodFun (f n) (q n)` against the inverter that encodes its challenge tuple by
`blocks` and decodes its answer: the bridge from `𝓕.prod q` to [Gar26, Theorem 2.1].

**Proof sketch.** Reindex the uniform input `x : {0,1}^{q·ℓ}` by the bijection `blocks`
(`uprob_comp_equiv` on the first coordinate); `f'` is `blocks⁻¹ ∘ prodFun ∘ blocks` by
`prod_f`, and `blocks⁻¹` is injective, so the success events coincide pointwise. -/
theorem invProbAt_prod_eq (𝓕 : FunFamily) (q : PolyExpr) (A : NUPPT) (n : ℕ) :
    (𝓕.prod q).invProbAt A n =
      invProbOpt (OneWay.prodFun (𝓕.f n) (q.eval n)) fun ys r =>
        (A.inverter n (q.eval n * 𝓕.inLen.eval n) (q.eval n * 𝓕.outLen.eval n)
          ((blocks (q.eval n) (𝓕.outLen.eval n)).symm ys) r).map (blocks (q.eval n) (𝓕.inLen.eval n)) := by
  unfold invProbAt invProbOpt
  rw [← uprob_comp_equiv (Equiv.prodCongr (blocks (q.eval n) (𝓕.inLen.eval n)) (Equiv.refl _))]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq, prod_f,
    Option.map_eq_some_iff]
  apply propext
  constructor
  · rintro ⟨x', hx', hf⟩
    refine ⟨blocks _ _ x', ⟨x', hx', rfl⟩, ?_⟩
    have := congrArg (blocks (q.eval n) (𝓕.outLen.eval n)) hf
    simpa using this
  · rintro ⟨t, ⟨x', hx', rfl⟩, hf⟩
    exact ⟨x', hx', by simp [hf]⟩

/-- **The direct product is easy to compute.** If `𝓕` is easy then so is `𝓕.prod q`
[PS10, Theorem 35.1, "`f'` is easy to compute"].

**Proof sketch.** Let `F` be the evaluator of `𝓕`. The evaluator of `𝓕.prod q` is the
blockwise evaluator `OneWay.exists_prodEval F inLen q` (an instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := q` on the state word `⟨⟨1^n, cnt⟩, rest⟩`:
while the unary counter `cnt` is shorter than `1^{q(n)}` a round emits `F ⟨1^n, rest.take (inLen n)⟩`
and drops `inLen n` bits, afterwards it emits `[]`; `q` is evaluated at the state-word length
`≥ n`, so exactly `q(n)` rounds emit). Its specification gives the concatenation over `i < q(n)`
of `F ⟨1^n, block i⟩`, which is the concatenation of `List.ofFn (f n (blocks x i))`
(`ofFn_blocks_symm`, the hypothesis on `F`). -/
theorem Easy.prod {𝓕 : FunFamily} (h : 𝓕.Easy) (q : PolyExpr) : (𝓕.prod q).Easy := by
  obtain ⟨F, hF, hFx⟩ := h
  obtain ⟨F', hF', hspec⟩ := OneWay.exists_prodEval hF 𝓕.inLen q
  refine ⟨F', hF', fun n x => ?_⟩
  rw [NUPPT.advInput, hspec, prod_f, ofFn_blocks_symm]
  congr 2
  funext i
  exact hFx n (blocks (q.eval n) (𝓕.inLen.eval n) x i)

end FunFamily

/-! ## Yao's parameters and the concrete one-call reduction -/

/-- The number of blocks `m = 2 n q(n)` of [PS10, §2.4.3] ("we pick `m = 2nq(n)`"), as a
syntactic polynomial. -/
def yaoBlocks (q : PolyExpr) : PolyExpr := .mul (.const 2) (.mul .var q)

/-- The number of repetitions `T = 2 n m(n) n^c` of the one-call inverter [PS10, §2.4.3, the
definition of `A`]: the text's `2nm²p(n)` with `p(n) = n^c` and one factor `m` saved by the
threshold `θ = μ₀/(2m)` of `OneWay.yao_amplification_exp`. -/
def yaoRounds (q : PolyExpr) (c : ℕ) : PolyExpr :=
  .mul (.const 2) (.mul .var (.mul (yaoBlocks q) (.pow .var c)))

/-- `m(n) = 2 n q(n)`. -/
@[simp] theorem eval_yaoBlocks (q : PolyExpr) (n : ℕ) : (yaoBlocks q).eval n = 2 * (n * q.eval n) :=
  rfl

/-- `T(n) = 2 n m(n) n^c`. -/
@[simp] theorem eval_yaoRounds (q : PolyExpr) (c : ℕ) (n : ℕ) :
    (yaoRounds q c).eval n = 2 * (n * ((yaoBlocks q).eval n * n ^ c)) := rfl

/-- `m(n)` is positive for `n ≥ 1` and positive `q`. -/
theorem yaoBlocks_pos (q : PolyExpr) (hq : ∀ n, 0 < q.eval n) {n : ℕ} (hn : 0 < n) :
    0 < (yaoBlocks q).eval n := by
  simp only [eval_yaoBlocks]
  exact Nat.mul_pos (by norm_num) (Nat.mul_pos hn (hq n))

namespace OneWay

/-- **One-call planting reduction** (lemma C2 of the Chapter 2 inventory, the concrete
content of [PS10, Theorem 35.2]): for every fixed position `i`, the inverter that samples
fresh inputs `xs`, plants the challenge `y` at position `i` of `(f(x₁), …, f(x_q))`, calls `B`
and returns the `i`-th component of the answer (`yaoTry` at the fixed position `i`) inverts
`f` with at least the probability with which `B` inverts `prodFun f q`. [PS10, Theorem 35.2,
proof]; the text's test "`f(a) = u`" is unnecessary for the inequality.

**Proof sketch.** In the planted experiment `(x, xs, r)` the tuple `update xs i x` is uniform
(`OneWay.uprob_update`), so the planted experiment is the direct-product experiment with the
answer projected to position `i`; an inverse of the whole tuple inverts every coordinate
(`uprob_mono`). -/
theorem invProb_prodFun_le_yaoTry {α β ρ : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    [Fintype ρ] {q : ℕ} (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (i : Fin q) :
    invProb (prodFun f q) B ≤ invProb f fun y c => yaoTry f B y (i, c) := by
  unfold invProb
  have h := uprob_update (α := α) (ρ := ρ) i fun xs r => f (B (prodFun f q xs) r i) = f (xs i)
  simp only [prodFun_update, Function.update_self] at h
  simp only [yaoTry]
  rw [h]
  apply uprob_mono
  rintro ⟨xs, r⟩ hxs
  exact congrFun hxs i

end OneWay

/-- Polynomial times `2^{-n}` is eventually below one. -/
private theorem eventually_poly_mul_two_pow_lt_one (p : PolyExpr) :
    ∃ n₀, ∀ n ≥ n₀, (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n < 1 := by
  obtain ⟨C, e, hCe⟩ := p.eval_le
  have hneg : Negligible fun n => ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow e).const_mul _
  have hμ : Negligible fun n => (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n := by
    refine hneg.mono ⟨1, fun n hn => ?_⟩
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have h1 : (p.eval n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ e := by exact_mod_cast hCe n
    have h2 : ((n : ℝ) + 1) ^ e ≤ (2 * (n : ℝ)) ^ e := by
      apply pow_le_pow_left₀ (by positivity)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ (C : ℝ) * (2 * (n : ℝ)) ^ e * (2 : ℝ)⁻¹ ^ n :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
            (by positivity)
      _ = ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * (2 : ℝ)⁻¹ ^ n) := by push_cast; ring
  obtain ⟨n₀, h⟩ := hμ 0
  refine ⟨n₀, fun n hn => lt_of_le_of_lt (le_abs_self _) ?_⟩
  simpa using h n hn

/-- `e^{-n} ≤ 2^{-n}`. -/
private theorem exp_neg_le_two_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (2 : ℝ)⁻¹ ^ n := by
  have h1 : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h1]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg]
  have := Real.add_one_le_exp (1 : ℝ)
  exact inv_anti₀ (by norm_num) (by linarith)

/-- **Parameter instantiation** [PS10, §2.4.3, Claim 38.2 of the inventory]: with
`m(n) = 2nq(n)` blocks (`yaoBlocks q`) and `T(n) + 1 = 2nm(n)n^c + 1` repetitions
(`yaoRounds q c`), for all large `n` and every `f`, `B` such that `B` inverts `prodFun f (m n)`
with probability at least `1/n^c`, `yaoInverter f B (T n + 1)` inverts `f` with probability
exceeding `1 - 1/q(n) + (T(n) + 1)·2^{-n}` (the margin is the statistical term of the
rejection-sampled positions that `weak_to_strong` subtracts). The concrete inequality is
`OneWay.yao_amplification_exp` [Gar26, Theorem 2.1].

**Deviation:** the text takes `T = 2nm²p(n)` and the threshold `1/(2m²p(n))`; with the
threshold `μ₀/(2m)` of `yao_amplification_exp` one factor `m` is saved. The statistical margin
is absent from the text (exact sampling of `i ← [m]`).

**Proof sketch.** Apply `OneWay.yao_amplification_exp` with `α' := 1/q(n) ≤ 1`, `q := m(n)`
(so `α' m(n) = 2n`), `μ₀ := 1/n^c`, `T' := T(n) + 1` (so `μ₀ T' ≥ 2n m(n)`); it needs
`2e^{-n} < 1/n^c` and yields `invProb f (yaoInverter …) ≥ 1 - 1/(2q(n)) - e^{-n}`. Both this
and the tail bound `e^{-n} + (T(n) + 1) 2^{-n} < 1/(2q(n))` follow from `e^{-n} ≤ 2^{-n}` and
`eventually_poly_mul_two_pow_lt_one` (polynomial times `2^{-n}` is negligible,
`negligible_two_pow_neg`, `Negligible.mul_pow`). `NeZero (m n)` is `yaoBlocks_pos`. -/
theorem claim_38_2 (q : PolyExpr) (hq : ∀ n, 0 < q.eval n) (c : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, ∀ {α β ρ : Type} [Fintype α] [Inhabited α] [DecidableEq β] [Fintype ρ]
      [Nonempty ρ] (f : α → β) (B : (Fin ((yaoBlocks q).eval n) → β) → ρ → (Fin ((yaoBlocks q).eval n) → α)),
      1 / (n : ℝ) ^ c ≤ invProb (OneWay.prodFun f ((yaoBlocks q).eval n)) B →
      1 - 1 / (q.eval n : ℝ) + ((yaoRounds q c).eval n + 1) * (2 : ℝ)⁻¹ ^ n <
        invProb f (OneWay.yaoInverter f B ((yaoRounds q c).eval n + 1)) := by
  obtain ⟨n₁, h₁⟩ := eventually_poly_mul_two_pow_lt_one (.mul (.const 2) (.pow .var c))
  obtain ⟨n₂, h₂⟩ := eventually_poly_mul_two_pow_lt_one
    (.mul (.add (yaoRounds q c) (.const 2)) (.mul (.const 2) q))
  refine ⟨max 1 (max n₁ n₂), fun n hn => ?_⟩
  set m : ℕ := (yaoBlocks q).eval n with hm
  set T : ℕ := (yaoRounds q c).eval n with hT
  intro α β ρ _ _ _ _ _ f B hμ
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hqR : (1 : ℝ) ≤ q.eval n := by exact_mod_cast hq n
  have hexp := exp_neg_le_two_pow n
  have hb := h₁ n (le_of_max_le_left (le_of_max_le_right hn))
  have hc := h₂ n (le_of_max_le_right (le_of_max_le_right hn))
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow, PolyExpr.eval_var,
    PolyExpr.eval_add] at hb hc
  push_cast at hb hc
  have hμ₀ : 2 * Real.exp (-(n : ℝ)) < 1 / (n : ℝ) ^ c := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < 2⁻¹ by norm_num) n, pow_pos (show (0:ℝ) < n by linarith) c]
  haveI : NeZero m := ⟨(yaoBlocks_pos q hq hn1).ne'⟩
  have hmR : (m : ℝ) = 2 * (n * q.eval n) := by rw [hm, eval_yaoBlocks]; push_cast; ring
  have hTR : (T : ℝ) = 2 * (n * (m * (n : ℝ) ^ c)) := by rw [hT, eval_yaoRounds]; push_cast; ring
  have hα₁ : 1 / (q.eval n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hqR
  have hq' : 2 * (n : ℝ) ≤ 1 / (q.eval n : ℝ) * (m : ℝ) := by
    have : 1 / (q.eval n : ℝ) * (2 * (n * q.eval n)) = 2 * n := by field_simp
    rw [hmR, this]
  have hT' : 2 * (n : ℝ) * (m : ℝ) ≤ 1 / (n : ℝ) ^ c * ((T + 1 : ℕ) : ℝ) := by
    push_cast
    rw [hTR]
    have hpos : (0 : ℝ) < (n : ℝ) ^ c := by positivity
    have : 1 / (n : ℝ) ^ c * (2 * (n * (m * (n : ℝ) ^ c)) + 1) = 2 * n * m + 1 / (n : ℝ) ^ c := by
      field_simp
    rw [this]
    linarith [show 0 < 1 / (n : ℝ) ^ c by positivity]
  have hmain := OneWay.yao_amplification_exp f B (n := n) (α' := 1 / (q.eval n : ℝ))
    (μ₀ := 1 / (n : ℝ) ^ c) (T + 1) hα₁ hq' hT' hμ₀ hμ
  have htail : Real.exp (-(n : ℝ)) + ((T : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n < 1 / (q.eval n : ℝ) / 2 := by
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    rw [lt_div_iff₀ (by norm_num), lt_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ## Hardness amplification -/

/-- The block bijection of this file is the one of `OneWayLemmas`/`OneWayYao`. -/
private theorem blocks_eq_blocksE (q ℓ : ℕ) : FunFamily.blocks q ℓ = OneWay.blocksE q ℓ := rfl

/-- **Yao's hardness amplification** [PS10, Theorem 35.1]: for every weak one-way function
`𝓕` there is a polynomial `m` (the proof takes `m(n) = 2nq(n)`, `q` the polynomial of weak
one-wayness) such that the direct product `𝓕.prod m`, `f'(x₁, …, x_{m(n)}) = (f(x₁), …,
f(x_{m(n)}))`, is strongly one-way.

**Deviation:** `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's
`m = 2nq(n)` and a rejection-sampled position (statistical term absorbed). The direct product
is a family at parameter `n` whose adversaries receive `1^n` (module docstring); the text's
`T = 2nm²p(n)` repetitions become `T(n) + 1`, `T(n) = 2nm(n)n^c` (`yaoRounds`).

**Proof sketch.** Let `q_w` be the polynomial of `h.hard` and `m := yaoBlocks q_w`
(`m(n) = 2nq_w(n)`). *Easy:* `FunFamily.Easy.prod`. *Hard:* fix `A' : NUPPT` and suppose
`fun n => (𝓕.prod m).invProbAt A' n` is not negligible; `not_negligible_iff` gives `c` with
`1/n^c ≤ (𝓕.prod m).invProbAt A' n` for infinitely many `n` (the function is nonnegative,
`invProbAt_nonneg`). Put `T := yaoRounds q_w c`.

*The reduction `A`* (Algorithm 38.5 repeated) is the machine of `OneWay.exists_yaoReduction`
(`TCSlib.Cryptography.Asymptotic.OneWayYao`, sub-machines in `OneWayLemmas`), applied to the
evaluator `F` of `h.easy` and to `A'`. It is `NUPPT.ofPolyTime` of the loop
`YaoMachine.yaoRaw'` (`Complexity.polyTimeComputable_iterateFind`) with coins
`(T + 1)·ρ`, `ρ(n) = n·m(n) + m(n)·inLen(n) + A'.coins(n)` the coins of one round, and advice
`⟨A'.advice n, 1^{kk}⟩`, `kk = kkOf (m n) = ⌊log₂ m(n)⌋ + 1` (so `m(n) < 2^{kk} ≤ 2m(n)`).
Round `t` consumes the `t`-th block of `ρ(n)` coins: it reads `n·kk` of its `n·m(n)` position
bits and samples the
position `i ← [m(n)]` by rejection (`n` trials of `kk` bits, D10), evaluates `f` on the `m(n)`
fresh inputs, plants `y` at block `i`, calls `A'` on the planted tuple, takes block `i` of the
answer padded with `true` to `inLen(n)` bits (the total inverter `OneWay.yaoB`), and tests
`f(z_i) = y`; the machine returns the first success and `1^{inLen n}` on exhaustion.

*Functional identity.* On `⟨⟨⟨1^n, y⟩, ⟨A'.advice n, 1^{kk}⟩⟩, r⟩` the machine returns
`OneWay.yaoInverter (𝓕.f n) (yaoB … A' n) (T n + 1) y (sampleAll r)` (`YaoMachine.yaoRaw'_layout`),
where `sampleAll r` reads the typed coins of the `T(n) + 1` rounds (position, inputs, coins of
`A'`) off `r`.

*Probability.* Each round's position is within `(1 − m/2^{kk})^n ≤ 2^{-n}` of uniform
(`statClose_rejectionSample`); `YaoMachine.statClose_sampleAll` and
`StatClose.abs_uprob_sub_le_prod` give, for `n ≥ 1`,
`𝓕.invProbAt A n ≥ invProb (𝓕.f n) (yaoInverter (𝓕.f n) (yaoB … A' n) (T n + 1)) − (T n + 1)·2^{-n}`
(`exists_yaoReduction`).

*Conclusion.* `yaoB` inverts the direct product at least as often as `A'` (when `A'`'s answer
decodes, `yaoB` returns its blocks: `invProbAt_prod_eq`, `NUPPT.inverter_eq_some_iff`,
`OneWay.padTrue_drop_ofFn`), so at the infinitely many `n` with
`1/n^c ≤ (𝓕.prod m).invProbAt A' n`, also `1/n^c ≤ invProb (prodFun (𝓕.f n) (m n)) (yaoB … A' n)`.
There `claim_38_2` (which packages `OneWay.yao_amplification_exp` with `α' = 1/q_w(n)`,
`μ₀ = 1/n^c`, `T' = T n + 1`) gives
`invProb (𝓕.f n) (yaoInverter …) > 1 − 1/q_w(n) + (T n + 1)·2^{-n}`, hence
`𝓕.invProbAt A n > 1 − 1/q_w(n)` for infinitely many `n`, contradicting `h.hard` for `A`
(`∃ n₀, ∀ n ≥ n₀, … ≤ 1 − 1/q_w(n)`). -/
theorem weak_to_strong {𝓕 : FunFamily} (h : FunFamily.WeakOneWay 𝓕) :
    ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q) := by
  obtain ⟨qw, hqw, hhard⟩ := h.hard
  refine ⟨yaoBlocks qw, h.easy.prod _, fun A' => ?_⟩
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.1 hneg
  obtain ⟨F, hF, hFx⟩ := h.easy
  have hFe_spec : ∀ n (a : Fin (𝓕.inLen.eval n) → Bool),
      F (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (𝓕.f n a) :=
    fun n a => hFx n a
  have hm : ∀ n, 1 ≤ n → 0 < (yaoBlocks qw).eval n := fun n hn => yaoBlocks_pos qw hqw hn
  -- the reduction machine of Algorithm 38.5
  obtain ⟨A, hA⟩ := OneWay.exists_yaoReduction 𝓕.inLen 𝓕.outLen (yaoBlocks qw) (yaoRounds qw c)
    𝓕.f hF hFe_spec A' hm
  obtain ⟨n₀, hn₀⟩ := hhard A
  obtain ⟨n₁, hn₁⟩ := claim_38_2 qw hqw c
  obtain ⟨n, hn, hlow⟩ := hc (max 1 (max n₀ n₁))
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnn₀ : n₀ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnn₁ : n₁ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hlow
  -- the total inverter `yaoB` inverts the direct product at least as often as `A'`
  have hB : 1 / (n : ℝ) ^ c ≤ invProb (OneWay.prodFun (𝓕.f n) ((yaoBlocks qw).eval n))
      (OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n) := by
    refine hlow.trans ?_
    rw [FunFamily.invProbAt_prod_eq]
    unfold invProbOpt invProb
    apply uprob_mono
    rintro ⟨xs, r⟩ ⟨xs', hxs', hf⟩
    rw [Option.map_eq_some_iff] at hxs'
    obtain ⟨x'', hx'', rfl⟩ := hxs'
    rw [NUPPT.inverter_eq_some_iff, blocks_eq_blocksE] at hx''
    have hyB : OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n
        (OneWay.prodFun (𝓕.f n) ((yaoBlocks qw).eval n) xs) r =
        FunFamily.blocks ((yaoBlocks qw).eval n) (𝓕.inLen.eval n) x'' := by
      funext j
      simp only [OneWay.yaoB]
      rw [hx'', OneWay.padTrue_drop_ofFn]
      rfl
    rw [hyB]
    exact hf
  -- the parameter instantiation and the reduction's bound
  have hclaim := @hn₁ n hnn₁ (Fin (𝓕.inLen.eval n) → Bool) (Fin (𝓕.outLen.eval n) → Bool)
    (A'.Coins n) _ ⟨fun _ => true⟩ _ _ _ (𝓕.f n)
    (OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n) hB
  have hred := hA n hn1
  have hup := hn₀ n hnn₀
  unfold FunFamily.invProbAt at hup
  rw [one_div] at hred
  linarith

/-- `blocks q ℓ x i j` reads position `ℓ·i + j` of `x`. -/
private theorem blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) := rfl

/-- Two blocks: the encoding of `blocks⁻¹ t` is `ofFn (t 0) ++ ofFn (t 1)`. -/
private theorem ofFn_blocks_two_symm (ℓ : ℕ) (t : Fin 2 → Fin ℓ → Bool) :
    List.ofFn ((FunFamily.blocks 2 ℓ).symm t) = List.ofFn (t 0) ++ List.ofFn (t 1) := by
  rw [FunFamily.ofFn_blocks_symm, OneWay.flatten_ofFn_two]

/-- **The simple security reduction** [PS10, Theorem 35.2]: if `𝓕` is a strong one-way
function then `g(x, y) = (f(x), f(y))`, the direct product with two blocks (input length
`2·inLen(n)`), is a strong one-way function.

**Deviation:** `g` is `𝓕.prod (const 2)` (two blocks of the typed domain), a family at
parameter `n` whose adversaries receive `1^n` rather than `1^{2n}` (module docstring).

**Proof sketch.** *Easy:* `FunFamily.Easy.prod`. *Hard:* fix `A' : NUPPT`. The reduction `A`
of the text ("choose a random `y`, compute `v ← f(y)`, submit `(u, v)` to `A'`, output `a`")
is `NUPPT.ofPolyTime` of an FP function of the raw input `⟨⟨⟨1^n, u⟩, A'.advice n⟩, r⟩` with
coins `add (mul (const 2) inLen) A'.coins` and advice `A'.advice`: cut the first `2·inLen n`
coins as a fresh pair of blocks whose second block is `y` (`polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly` on `⟨1^n, r⟩`; the first block is the overwritten coordinate of
the planting lemma), evaluate `v := F ⟨1^n, y⟩` with the evaluator of `h.easy`, call `A'.output`
on the layout `⟨⟨⟨1^n, u ++ v⟩, A'.advice n⟩, r'⟩` (`PolyTimeComputable.append`,
`polyTimeComputable_layout`, `A'.polyTimeComputable_output`) and return the first `inLen n`
bits of the answer (`polyTimeComputable_pairTakePoly inLen`; no length test is needed for an
upper bound). Functional identity: `A.runAt n u (xs, r') = (A'.runAt n (u ++ f (xs 1)) r').take (inLen n)`
after reindexing `A.Coins n ≃ (Fin 2 → Fin (inLen n) → Bool) × A'.Coins n` (`blocks`,
`Fin.appendEquiv`, `uprob_comp_equiv`, `ofFn_blocks_symm`). Probability: `invProbAt_prod_eq`
writes `(𝓕.prod 2).invProbAt A' n` as `invProbOpt (prodFun (f n) 2) B'`, the planting lemma
`OneWay.invProbOpt_prodFun_le_yaoTryOpt` at position `0` bounds it by the planted experiment, and
`uprob_mono` (a `2·inLen n`-bit answer of `A'` decodes to the first block of `A`'s answer,
`ofFn_block_eq_take_drop`) gives `(𝓕.prod 2).invProbAt A' n ≤ 𝓕.invProbAt A n`; conclude by
`h.hard A` and `Negligible.mono` (`invProbAt_nonneg`). -/
theorem strong_prod_two {𝓕 : FunFamily} (h : FunFamily.StrongOneWay 𝓕) :
    FunFamily.StrongOneWay (𝓕.prod (.const 2)) := by
  classical
  obtain ⟨F, hF, hFx⟩ := h.easy
  refine ⟨h.easy.prod _, fun A' => ?_⟩
  -- the reduction: cut two fresh blocks, evaluate `f` on the second, plant, call `A'`, return
  -- the first block of the answer
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hxs := (polyTimeComputable_pairTakePoly (.mul (.const 2) 𝓕.inLen)).comp hcut
  have hr' := (polyTimeComputable_pairDropPoly (.mul (.const 2) 𝓕.inLen)).comp hcut
  have hy2 := (polyTimeComputable_pairDropPoly 𝓕.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hxs)
  have hv := hF.comp (NUPPT.polyTimeComputable_inParam.pairEncode hy2)
  have hout := A'.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (NUPPT.polyTimeComputable_inArg.append hv) NUPPT.polyTimeComputable_inAdvice hr')
  have hG := (polyTimeComputable_pairTakePoly 𝓕.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hout)
  let A : NUPPT := NUPPT.ofPolyTime hG (.add (.mul (.const 2) 𝓕.inLen) A'.coins) A'.adv A'.advice
    A'.advice_length
  refine (h.hard A).mono ⟨0, fun n _ => ?_⟩
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _), abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
  set ℓ := 𝓕.inLen.eval n with hℓ
  set f := 𝓕.f n with hf
  -- the coin bijection `(xs, r') ↦ ⟨xs⟩ ++ r'`
  have hlen : 2 * ℓ + A'.coinLen n = A.coinLen n := rfl
  let e : (Fin 2 → Fin ℓ → Bool) × A'.Coins n ≃ A.Coins n :=
    (Equiv.prodCongr (FunFamily.blocks 2 ℓ).symm (Equiv.refl _)).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)))
  have hofn : ∀ (xs : Fin 2 → Fin ℓ → Bool) (r' : A'.Coins n),
      List.ofFn (e (xs, r')) = (List.ofFn (xs 0) ++ List.ofFn (xs 1)) ++ List.ofFn r' := by
    intro xs r'
    rw [← ofFn_blocks_two_symm, ← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen (Fin.append ((FunFamily.blocks 2 ℓ).symm xs) r')).symm
  -- the functional identity of the reduction
  have hrun : ∀ (y : Fin (𝓕.outLen.eval n) → Bool) (xs : Fin 2 → Fin ℓ → Bool) (r' : A'.Coins n),
      A.runAt n (List.ofFn y) (e (xs, r')) =
        (A'.runAt n (List.ofFn y ++ List.ofFn (f (xs 1))) r').take ℓ := by
    intro y xs r'
    rw [NUPPT.runAt_eq]
    show (NUPPT.ofPolyTime hG _ _ _ _).runAtL n _ _ = _
    rw [NUPPT.runAtL_ofPolyTime]
    simp only [Function.comp, NUPPT.advInput, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
      NUPPT.inCoins, NUPPT.layout, pairFstD_pairEncode, pairSndD_pairEncode, hofn,
      PolyExpr.eval_mul, PolyExpr.eval_const, List.length_replicate]
    have h2 : (List.ofFn (xs 0) ++ List.ofFn (xs 1)).length = 2 * ℓ := by simp; ring
    rw [List.take_left' h2, List.drop_left' h2,
      List.drop_left' (by simp only [List.length_ofFn]; try exact hℓ)]
    have := hFx n (xs 1)
    simp only [NUPPT.advInput] at this
    rw [this]
    rfl
  -- the planting bound
  let B' : (Fin 2 → Fin (𝓕.outLen.eval n) → Bool) → A'.Coins n → Option (Fin 2 → Fin ℓ → Bool) :=
    fun ys r => (A'.inverter n (2 * ℓ) (2 * 𝓕.outLen.eval n)
      ((FunFamily.blocks 2 (𝓕.outLen.eval n)).symm ys) r).map (FunFamily.blocks 2 ℓ)
  have h1 : (𝓕.prod (.const 2)).invProbAt A' n = invProbOpt (OneWay.prodFun f 2) B' :=
    FunFamily.invProbAt_prod_eq 𝓕 (.const 2) A' n
  have h2 := OneWay.invProbOpt_prodFun_le_yaoTryOpt f B' 0
  refine h1.trans_le (h2.trans ?_)
  unfold FunFamily.invProbAt invProbOpt
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl _) e)]
  apply uprob_mono
  rintro ⟨x, xs, r'⟩ ⟨x', hx', hfx⟩
  refine ⟨x', ?_, hfx⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
  rw [Option.map_eq_some_iff] at hx'
  obtain ⟨xs', hxs', rfl⟩ := hx'
  simp only [B', Option.map_eq_some_iff] at hxs'
  obtain ⟨x'', hx'', rfl⟩ := hxs'
  rw [NUPPT.inverter_eq_some_iff, ofFn_blocks_two_symm, Function.update_self,
    Function.update_of_ne (by decide), OneWay.prodFun] at hx''
  rw [NUPPT.inverter_eq_some_iff, hrun, hx'']
  have hblk := OneWay.ofFn_block_eq_take_drop x'' 0
  simp only [Fin.val_zero, Nat.zero_mul, List.drop_zero] at hblk
  rw [← hblk]
  rfl

/-- **Strong implies weak** (sanity, [PS10, §2.2, the remark after Definition 28.4]): a strong
one-way function is a weak one-way function with `q = 2`.

**Proof sketch.** Negligibility with `c = 1` gives `invProbAt A n < 1/n ≤ 1/2 = 1 - 1/2` for
all `n ≥ max n₀ 2`. -/
theorem FunFamily.StrongOneWay.weak {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay := by
  refine ⟨h.easy, .const 2, fun _ => by simp, fun A => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.hard A 1
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2 : 1 / (n : ℝ) ^ 1 ≤ 1 / 2 := by
    rw [pow_one]; exact one_div_le_one_div_of_le (by norm_num) hn2
  simp only [PolyExpr.eval_const, Nat.cast_ofNat]
  linarith [le_abs_self (𝓕.invProbAt A n)]

/-- A machine that returns its argument exists: `A(1^n, y; r) = y` (`ofPolyTimeUniform` of the
argument projection, no coins). -/
private theorem exists_runAt_eq_arg : ∃ A : NUPPT, ∀ n y (r : A.Coins n), A.runAt n y r = y :=
  ⟨NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inArg (.const 0), fun n y r => by
    rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
    exact NUPPT.inArg_layout _ _ _ _⟩

/-- **A machine that returns its argument inverts the identity with probability one**: if
`A(1^n, y; r) = y` for all `n`, `y`, `r`, then `(ofString id var).invProbAt A n = 1` at every
parameter `n` (the common step of the non-vacuity results below and of
`FunFamily.not_toCollection_oneWay_id`).

**Proof sketch.** By `invProbAt_eq_uprob` the event is that `A(1^n, x)` is the encoding of a
preimage of `x`; it holds for every `(x, r)` with the preimage `x` itself (`ofString_id_f`), so
the probability is `uprob True = 1`. -/
theorem FunFamily.invProbAt_ofString_id_eq_one {A : NUPPT}
    (hA : ∀ n y (r : A.Coins n), A.runAt n y r = y) (n : ℕ) :
    (FunFamily.ofString id .var).invProbAt A n = 1 := by
  rw [FunFamily.invProbAt_eq_uprob]
  have hp : (fun z : (Fin ((FunFamily.ofString id .var).inLen.eval n) → Bool) × A.Coins n =>
      ∃ x', A.runAt n (List.ofFn ((FunFamily.ofString id .var).f n z.1)) z.2 = List.ofFn x' ∧
        (FunFamily.ofString id .var).f n x' = (FunFamily.ofString id .var).f n z.1) =
      fun _ => True := by
    funext z
    refine propext ⟨fun _ => trivial, fun _ => ⟨z.1, ?_, rfl⟩⟩
    rw [hA, FunFamily.ofString_id_f]
  rw [hp, uprob_true]

/-- **The identity is not one-way** (non-vacuity of the adversary class, [PS10, §2.2]): the
machine that returns its argument inverts `FunFamily.ofString id var` with probability one at
every parameter, and the constant `1` is not negligible.

**Proof sketch.** `A := NUPPT.ofPolyTimeUniform polyTimeComputable_inArg (const 0)` returns
`y` on `⟨⟨⟨1^n, y⟩, []⟩, r⟩` (`runAtL_ofPolyTimeUniform`, `inArg_layout`), so
`invProbAt … A n = 1` (`FunFamily.invProbAt_ofString_id_eq_one`); `Negligible (fun _ => 1)`
fails at `c = 0`. -/
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var) := by
  intro h
  obtain ⟨A, hA⟩ := exists_runAt_eq_arg
  obtain ⟨n₀, hn₀⟩ := h.hard A 0
  have := hn₀ n₀ le_rfl
  simp [FunFamily.invProbAt_ofString_id_eq_one hA] at this

/-- **The identity is not weakly one-way** (non-vacuity of [PS10, Definition 28.4]; gate 03b,
finding 13): the machine that returns its argument inverts `FunFamily.ofString id var` with
probability `1 > 1 − 1/q(n)` at every parameter, for every positive polynomial `q`.

**Proof sketch.** As `not_strongOneWay_id`: `invProbAt … A n = 1`
(`FunFamily.invProbAt_ofString_id_eq_one`), and `1 ≤ 1 − 1/q(n₀)` contradicts `q(n₀) > 0`. -/
theorem not_weakOneWay_id : ¬ FunFamily.WeakOneWay (FunFamily.ofString id .var) := by
  intro h
  obtain ⟨q, hq, hhard⟩ := h.hard
  obtain ⟨A, hA⟩ := exists_runAt_eq_arg
  obtain ⟨n₀, hn₀⟩ := hhard A
  have h1 := hn₀ n₀ le_rfl
  rw [FunFamily.invProbAt_ofString_id_eq_one hA] at h1
  have h2 : (0 : ℝ) < 1 / (q.eval n₀ : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr (hq n₀))
  linarith

/-- **The identity is not worst-case one-way** (non-vacuity of [PS10, Definition 26.1], `1^n`
form; gate 03b, finding 13): the machine that returns its argument inverts
`FunFamily.ofString id var` on every input with probability one.

**Proof sketch.** On `⟨1^n, x⟩` the machine returns `x`, which the inverter decodes to `x`
(`NUPPT.inverter_eq_some_iff`), a preimage of `x` (`ofString_id_f`); so the event holds for
every coin string and its probability is `uprob True = 1`. -/
theorem not_worstCaseOneWay_id : ¬ FunFamily.WorstCaseOneWay (FunFamily.ofString id .var) := by
  intro h
  obtain ⟨A, hA⟩ := exists_runAt_eq_arg
  refine h.hard ⟨A, fun n x => ?_⟩
  have hp : (fun r : A.Coins n => ∃ x', A.inverter n ((FunFamily.ofString id .var).inLen.eval n)
      ((FunFamily.ofString id .var).outLen.eval n) ((FunFamily.ofString id .var).f n x) r =
        some x' ∧ (FunFamily.ofString id .var).f n x' = (FunFamily.ofString id .var).f n x) =
      fun _ => True := by
    funext r
    refine propext ⟨fun _ => trivial, fun _ => ⟨x, ?_, rfl⟩⟩
    rw [NUPPT.inverter_eq_some_iff, hA, FunFamily.ofString_id_f]
  rw [hp, uprob_true]

/-! ## One-way permutations -/

/-- A family of permutations of `{0,1}^n` (the single one-way permutation of
[PS10, Theorems 79.4 and 126.4]; the *collection* of permutations of [PS10, Definition 55.1] is
`PermCollection` in `Asymptotic/Collections.lean`). -/
structure PermFamily where
  /-- The permutation at parameter `n`. -/
  f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)

/-- The function family underlying a permutation family: `inLen = outLen = var`. -/
def PermFamily.toFunFamily (P : PermFamily) : FunFamily where
  inLen := .var
  outLen := .var
  f n := P.f n

/-- `P` is a *one-way permutation* when its underlying family is strongly one-way
[PS10, §2.10, Definition 55.1, single-function form, as used in Theorems 79.4 and 126.4]. -/
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay

/-- The function of a permutation family is the permutation. -/
@[simp] theorem PermFamily.toFunFamily_f (P : PermFamily) (n : ℕ) (x : Fin n → Bool) :
    P.toFunFamily.f n x = P.f n x := rfl

end TCSlib.Cryptography

## ===== briefs/pass-shelat/DESIGN.md =====

# FROZEN DESIGN — Pass–shelat Chapters 2–4 computational-model layer and workstream map

Run 1 synthesis (2026-10-27). Inputs: `inventory-ch{2,3,4}.md`, `design-reuse-max.md`,
`design-abstract-interface.md`, `design-faithful-tapes.md`, three judge reports. Output of
this file: (1) the frozen Lean signatures, (2) the final text of the foundation decisions,
(3) the workstream map covering every core inventory item exactly once, (4) the
consolidated list of source errors, (5) the open questions for the maintainer.

**Evidence.** Every signature in §2 is reproduced from
`briefs/pass-shelat/DESIGN-freeze-scratch.lean` (1252 lines, 205 declarations), compiled on
2026-10-27 with `lake env lean` against the worktree: **exit 0, 0 errors, 53 `declaration
uses 'sorry'` warnings**, every sorry being a theorem stub under a stated proof plan (the
inventory of the 53 stubs is in §9). The proved parts are `PolyExpr.eval_*`, `eval_subst`,
`eval_mono`, `eval_le`, `NUPPT.output_spec`, `computesFunInTime`, `polyTimeComputable_output`,
`output_eq_of_computesInTime`, `length_advInput`, `output_ofPolyTime`,
`ofPolyTimeUniform_uniform`, `NUPPT.nonempty`, `invProbOpt_le_invProb`, `invProbOpt_some`,
`hybrid_lemma`, `prfAdv_toOracleAdversary`.

**Verdict adopted.** REUSE-MAXIMAL is the base (all three judges rank it first). The panel's
mandatory repairs are applied (§3) and the recommended grafts are taken (§4): syntactic
`PolyExpr` lengths everywhere, distribution-level samplability, `∀ q` oracle budgets, a
first-mover field and a fixed-alternation execution, literal `[false]` soundness, `≤` advice
length, literal Def 26.1 / Def 69.4 forms next to the `1^n` forms with the bridging lemmas,
abort-form perfect ZK, rejection-sampled permutations and positions, non-vacuity theorems in
`Checks.lean`, and the repaired construction of the repetition lemma. ABSTRACT-INTERFACE's
bundled class and FAITHFULNESS-FIRST's coin tape, pair-form bridges, oracle machines and
`NUPPTSeq` equivalence are **not** on the critical path (the latter two survive as optional
modules with one named admission each).

---

## 1. Foundation decisions D1–D11 (final text for `PassShelatChapter2-4Plan.md`)

D1. **Base and branch.** Branch `cryptography/pass-shelat-ch2-4` from `cryptography/garg-ch1-3`;
    worktree `/Users/dehmelf/Research/tcslib-pass-shelat`. Verification by shell
    `lake build <module>` / `lake env lean <file>` (user-approved deviation from `AGENTS.md`),
    one Lean process at a time.

D2. **Two layers, as in the Garg plan.** Concrete reductions are reused verbatim from
    `TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}`; the
    asymptotic layer adds machines, negligible functions and closure. Every asymptotic theorem
    is proved as (i) instantiate the concrete reduction at each `n`, (ii) exhibit the reduction
    as a `Complexity.NUPPT` by `NUPPT.ofPolyTime` of a function obtained from the FP calculus of
    `ClassNP/PolyTimePairing.lean` with `NUPPT.polyTimeComputable_output` as a black box, plus
    the two new machine lemmas of D11, (iii) negligible-function arithmetic through
    `not_negligible_iff`. New concrete lemmas go into campaign-owned files, never into the
    frozen Garg files. *Exception* (gate 03a, ruling G3-7a, user 2026-11-05): the general
    helper `negligible_zero` moved from `Asymptotic/Ensembles.lean` into
    `Foundations/Negligible.lean`, full name `TCSlib.Cryptography.negligible_zero` unchanged; its
    copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) is left to the duplicate clean-up
    (ruling G3-5).

D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
    `TCSlib/Complexity/Randomized/PPT.lean`): a `Turing.FinTM Bool` that halts on **every** input
    `z` within `Ct * (|z| + 1) ^ ct` steps, an explicit coin polynomial `coins : PolyExpr`, an
    advice polynomial `adv : PolyExpr` and an advice function. The single semantic primitive is
    `output z` (the output tape when the budget expires); `output` is `PolyTimeComputable`
    (proved) and every `PolyTimeComputable` function gives an `NUPPT` (`ofPolyTime`, proved).
    A PPT ([PS10, Def 23.4]) is an `NUPPT` with empty advice (`Uniform`; `Complexity.PPT` is the
    subtype). The activation at security parameter `n` on argument `y` with coins `r` is
    `runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`; the
    random tape is part of the input, the time bound holds for every coin string
    ([PS10, Def 23.5], worst case), and "`A` computes `f` with probability 1" ([PS10, Def 24.6])
    is `Computes`: equality for every coin string. `Computes` does not require `Uniform`: Def
    24.6 (on the encodings `⟨1^n, y⟩`, which is all `Computes` constrains; gate 03a, round 2,
    R2-1) is the case `A.Uniform ∧ A.Computes f`; for a non-uniform `A` it is the advice
    analogue and holds for uncomputable `f` (advice `[h n]`), so `∃ A, A.Computes f` is not "a
    PPT computes `f`" (gate 03a, finding 1). Honest evaluators ("easy to compute") are
    stated as `PolyTimeComputable` string functions on `⟨1^n, x⟩`. Recorded deviations:
    totality on all inputs (behaviour class unchanged: a machine polynomial-time on well-formed
    inputs is clocked by `timed_universal`; the optional lemma `NUPPT.ofPartial` is not needed
    by any theorem); time measured in the machine-input length (a polynomial in `n + |y|`,
    so the classes coincide); advice and coins indexed by the parameter `n` read from `1^n`
    rather than by the input length (interdefinable in every experiment of the text, and what
    makes one random tape per `n` well-typed for the oracle and interactive layouts).

D4. **Non-uniform PPT** ([PS10, Def 26.8]) in the advice formulation: `advice n` of length
    `≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
    `A_{|y|}(y)` of the text is `runLit y r := runAt |y| y r` (the prefix `1^{|y|}` carries no
    information); it is the layout of the literal forms of Def 26.1 and Def 69.4 (D5, D6). The
    machine-sequence formulation (`NUPPTSeq`, with `CodeTM.serialize` size) is an **optional**
    corollary module (`Randomized/Sequence.lean`) with the equivalence
    `nuppt_seq_iff_advice` as one named, non-blocking admission; it is not formalized in the
    core (Deviation recorded in the docstring of `NUPPT`).

D5. **Domains are typed at each parameter.** A function family is
    `FunFamily := ⟨inLen outLen : PolyExpr, f n : (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)⟩`;
    the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p` (`inLen = var`; exact for
    length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding is lossy). An
    inverter's output is decoded by `decodeFin` as an `inLen n`-bit string and a wrong length is
    a failure (`invProbOpt`, bridged to the concrete `invProb` by `invProbOpt_le_invProb` and
    `invProbOpt_some`). Adversaries receive `1^n` exactly where the text gives it
    (Defs 27.3, 28.4, 75.2, 96.1, …); where the text withholds it (Def 26.1: `A(f(x))`;
    Def 69.4: `D(t)`) the frozen definition is the literal one (`WorstCaseOneWay` with
    `inverterLit`, `Ensemble.IndistLit`), and the `1^n` form (`Ensemble.Indist`) is the headline
    form of the theorems, related by `Indist.toLit` (always) and `IndistLit.toIndist`
    (injective `ℓ`, i.e. every ensemble of the text; for constant `ℓ` the two forms coincide
    as well, by point tests, which is not formalized: gate 03a, note 14). The two are never
    unified silently.

D6. **Ensembles** ([PS10, Def 69.3]) are `Ensemble ℓ := ⟨σ : ℕ → Type, Fintype, X n : σ n → (Fin (ℓ.eval n) → Bool)⟩`
    with arbitrary finite seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`, the
    random-function oracle has function tables). "Efficiently samplable" is the predicate
    `Samplable` at the **distribution level**: a polynomial-time sampler from `s.eval n` uniform
    bits whose output law equals `X n` (`StatClose … 0`). Lemma 71.5 is `Indist.push` (image
    under an `NUPPT`, padded to an explicit `ℓ' : PolyExpr`), the multicopy corollary
    `Indist.copies` takes `Samplable X`, `Samplable Y`, and the hybrid lemma is the concrete
    `exists_hybrid_gap`. Deviation: every samplable distribution is dyadic; non-dyadic
    distributions of the text (primes, `Z_q`, permutations) appear only as *ideal* distributions
    in experiments and are approximated by rejection samplers within `StatClose` error (D10).

D7. **Oracle adversaries** ([PS10, Def 96.1]) are next-query machines: an `NUPPT` activated once
    per query on the encoded history of (query, answer) pairs with one random tape per `n`, and
    an explicit query budget `q : PolyExpr` quantified universally in the definition
    (`∀ D q`); `NUPPT.toOracleAdversary n ℓ₁ ℓ₂ (q.eval n)` builds the concrete `QueryTree`
    (`OracleAdversary`), `toOracleAdversary_boundedBy` supplies `BoundedBy q` for
    `ggm_prfAdv_le`/`exists_ggmBits_dist`. No oracle tapes (the library's `OracleTM` is a
    language oracle); the bridge `exists_queryTree` from `OracleTM`-level machines is an optional
    module. Deviation recorded.

D8. **Interactive protocols** ([PS10, §4.4]). A `Strategy` is a next-message function
    `next x z r received` with an explicit random-tape polynomial `coins : PolyExpr`; its value
    on the complete history is the party's output. A `Protocol` is `⟨P, V, rounds, verifierFirst⟩`
    where `rounds : PolyExpr` is the number of messages exchanged and `verifierFirst` the first
    mover (GNI: verifier; GI, 3COL: prover). `exec` is the fixed alternation of
    `rounds.eval |x|` moves; the verifier's verdict is `V.next` on the complete history
    (`outV`), so it is always defined and the literal `out_V = 0` is `outV = [false]`.
    `Strategy.Efficient` = one activation of a uniform `NUPPT` at parameter `|x|` on
    `⟨⟨x, z⟩, messages⟩` with the whole random tape (time polynomial in the total input,
    Deviation from the text's `t(|x|)`). Soundness quantifies `∃ ε` before `∀ x ∉ L ∀ P' ∀ z`
    over arbitrary strategies `P'` (unbounded provers; polynomial coin tapes lose nothing by
    averaging). Zero knowledge: `∀ V* efficient, ∃ S uniform NUPPT, ∀ Lz D, ∃ ε, ∀ x y z`,
    `R x y → |z| ≤ Lz.eval |x| → distAdv ≤ ε |x|` — strict PPT simulators, auxiliary inputs
    bounded by an arbitrary polynomial quantified after the simulator (the class a `t(|x|)`-time
    verifier can read; required for the non-uniform reduction of Prop 128.8). Statistical ZK
    (`StatZK δ`, sup-over-test-sets `StatClose`), `PerfectZK := StatZK 0` and Goldreich's abort
    form `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated
    simulators, rejection-sampled permutations). Deviations: fixed number of moves (a halting
    party is modelled as sending `[]`; all protocols of the text are fixed-round), strict
    simulators, statistical instead of perfect ZK, `|z|` polynomially bounded.

D9. **Lengths are syntax.** Every length or budget that depends on the parameter (coins,
    advice, input/output lengths of families and ensembles, stretch, query budgets, rounds,
    auxiliary-input bounds) is a `Complexity.PolyExpr` (`const/var/add/mul/pow`, `eval`,
    `subst`, `eval_subst`, `eval_mono`, `eval_le`, `normal C c = C(n+1)^c`). Time bounds of
    machines stay in the normal form `Ct (n+1)^ct` (the shape of `PolyTimeComputable`).
    `polyTimeComputable_unaryPoly p : x ↦ 1^{p(|x|)}` is proved by induction with the new
    primitive `computesFunInTime_unaryMul`, never through the repetition lemma. Abstract
    `ℕ → ℕ` lengths appear only as hypotheses of theorems with a `PolyExpr` majorant
    (`exists_reparam_advice`), never in a definition.

D10. **Sampling device.** `TCSlib/Cryptography/Asymptotic/Sampling.lean` owns
    `StatClose` (with `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`),
    `rejectionSample m k T` (`T` trials of `k` bits; uniform on `Fin m` conditioned on `some`,
    failure `(1 - m/2^k)^T`) and `permFromCoins` (Fisher–Yates with rejection-sampled offsets).
    Experiments use ideal uniform distributions (as the text); honest parties and reductions
    sample by rejection with `2^{-n}`-close laws and the theorems carry the explicit
    statistical term. This one device serves Theorem 35.1's uniform position (`m = 2nq(n)` is
    kept literal), SamplePrime/`Z_q`/`Z_N^*`/`QR_N` (Q3), and Chapter 4's permutations, edges
    and colour permutations (DQ1 option A at the concrete level).

D11. **Admissions policy.** `Complexity.polyTimeComputable_iterateFind`
    (`Randomized/Repetition.lean`) is the single machine lemma that may remain admitted at the
    end of run 4; every theorem that repeats an adversary depends on it and on nothing else
    admitted. The two new primitives (`pairSplitAt`, `unaryMul`) are built in the `Build/`
    style in the campaign-owned `Randomized/Primitives.lean`. `NUPPTSeq`'s equivalence,
    `NUPPT.ofPartial` and `exists_queryTree` are optional modules, each with its own named
    admission, off every critical path. Number-theoretic machine facts (binary `mul`,
    `add`, `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality; run-3
    audit P7-1 added `add`/`sub`/bit length) are explicit hypotheses
    (`Candidates/Arithmetic.lean` bundle), never axioms; `#print axioms` of every headline must
    show `[propext, Classical.choice, Quot.sound]` plus, at most, the admissions named here.
    *Status* (gate 03a, note 20; decision log 2026-10-28): run 3b proved
    `polyTimeComputable_iterateFind`, so the permitted machine admission is unused.
    `NUPPT.ofPartial` was never written; the only machine-layer `sorry` is the optional bridge
    `NUPPT.decides_of_decidesWithAdviceInTime` (`Randomized/NonUniform.lean`), whose sketch does
    `ofPartial`'s clocking inline. It is the named admission of that optional module (open
    question 5, ruled outside the core on 2026-10-27).

---

## 2. Frozen Lean signatures

All code below is verbatim from `DESIGN-freeze-scratch.lean` (compiled). Namespaces:
`Complexity` for the machine layer (`open Turing`), `TCSlib.Cryptography` for everything
else (`open Complexity Turing`). Each file's `## References` lists `[PS10]`, `[Gar26]`, `[AB09]`.
Docstrings in the skeleton must begin with the natural-language statement, then the
`[PS10, …]` citation, then the Deviation notes quoted in §5.

### 2.1 `TCSlib/Complexity/Randomized/PolyExpr.lean`

```lean
namespace Complexity

inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr
def eval : PolyExpr → ℕ → ℕ                       -- structural
def subst : PolyExpr → PolyExpr → PolyExpr          -- p[q/n]
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl       -- likewise eval_var/add/mul/pow
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n)   -- proved
theorem eval_mono (p : PolyExpr) : Monotone p.eval                                       -- proved
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c               -- proved
end PolyExpr

/-- `1^{p(|x|)}` is polynomial-time computable. Proof: induction on `p`; `const` =
`polyTimeComputable_const`, `var` = `polyTimeComputable_unary`, `add` = `PolyTimeComputable.append`,
`mul` = `computesFunInTime_unaryMul` (§2.4) composed with `PolyTimeComputable.pairEncode` of the
two unary strings, `pow p c` = induction on `c` through `mul`. -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true
end Complexity
```

### 2.2 `TCSlib/Complexity/Randomized/PPT.lean` — the structure and its primitive

```lean
namespace Complexity
open Turing

/-- NUPPT [PS10, Def 26.8, advice formulation]; PPT [PS10, Def 23.4] = `Uniform`. -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ                                  -- M halts within Ct (|z|+1)^ct on EVERY input z
  coins : PolyExpr                        -- coins.eval n uniform coins at parameter n
  adv : PolyExpr                          -- |advice n| ≤ adv.eval n
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT
variable (A : NUPPT)
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.coins.eval n
def adviceLen (n : ℕ) : ℕ := A.adv.eval n
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output
theorem output_spec (z) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length)      -- proved
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound                   -- proved
theorem polyTimeComputable_output : PolyTimeComputable A.output                          -- proved
theorem output_eq_of_computesInTime {z w t} (h : A.M.ComputesInTime z w t) : A.output z = w  -- proved
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y   -- ⟨1^n, y⟩
theorem length_advInput (n y) : (advInput n y).length = 2 * n + 2 + y.length                -- proved
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
theorem runAt_eq (n y r) : A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl
/-- `A_{|y|}(y)` of [PS10, Def 26.8]: activation at the input length. -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r
def Uniform : Prop := ∀ n, A.advice n = []
/-- [PS10, Def 24.6]. -/
def Computes (f : List Bool → List Bool) : Prop := ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
noncomputable def ofPolyTime {f} (hf : PolyTimeComputable f) (coins adv : PolyExpr)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT
theorem output_ofPolyTime … : (ofPolyTime hf coins adv advice hα).output = f                -- proved
noncomputable def ofPolyTimeUniform {f} (hf : PolyTimeComputable f) (coins : PolyExpr) : NUPPT
theorem ofPolyTimeUniform_uniform … : (ofPolyTimeUniform hf coins).Uniform                  -- proved
end NUPPT

def PPT : Type 1 := {A : NUPPT // A.Uniform}
theorem NUPPT.nonempty : Nonempty NUPPT                                                       -- proved
end Complexity
```

### 2.3 `TCSlib/Complexity/Randomized/NonUniform.lean` — Def 26.8 material

Contents: the docstring of Def 26.8 (both formulations, the advice one frozen), `runLit` lemmas
(`runLit_eq_runAt`), `Uniform` lemmas (`ofPolyTime` with empty advice; `Uniform.advice_eq`),
the sanity bridge to the library's advice machines, and the optional `NUPPTSeq`:

```lean
/-- Optional sanity bridge (needs the clocking construction `NUPPT.ofPartial`; off the
critical path). -/
theorem NUPPT.decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x]
```

Optional module `Randomized/Sequence.lean` (owner: machine-core, deferred): `NUPPTSeq`
(FAITHFUL §2.1 verbatim with `CodeTM.serialize`) and `nuppt_seq_iff_advice` (⇒ conditional on
`PolyBound c.canonizerTime` as in `TMSAT_mem_NP`; ⇐ via the hard-wiring construction), one
named admission; no theorem of chapters 2–4 depends on it.

### 2.4 `TCSlib/Complexity/Randomized/Primitives.lean` — two new machines

```lean
namespace Turing.FinTM
/-- NEW: `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (coin splitting at a unary length). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length) | none => [])
      fun n => c * (n + 1)
/-- NEW: unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{a·b}`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, v) => List.replicate (u.length * v.length) true | none => [])
      fun n => c * (n + 1) ^ 2
end Turing.FinTM

theorem Complexity.polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length)
theorem Complexity.polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length)
```

Construction sketches. `pairSplitAt`: the buffered aligned parser of `computesFunInTime_pairFst`
(reads the doubled prefix `u` onto a work tape without emitting), then a copy scan of `b` that
emits the doubled bit `bb` while the work head walks across `u`, then the separator `01`, then
the remainder verbatim; linear, two work tapes (≈ 300–500 lines). `unaryMul`: copy `1^b` onto a
work tape (the parser of `pairSnd`), then for each token of `u` replay the work tape onto the
output (`emitAction`-style) and rewind; `O(ab + a + b)` steps, ≈ 300–500 lines. Fallback for
`unaryMul` only: an instance of `polyTimeComputable_iterateEmit` (state `⟨1^{rest}, 1^b⟩`,
`emit = pairSndD`, step pops one token) — acceptable only after `iterateFind` is closed.
`pairTakePoly p` = `pairFstD ∘ pairSplitAt ∘ pairEncode (unaryPoly p ∘ pairFstD) pairSndD`
by `polyTimeComputable_of_linear`, `PolyTimeComputable.pairEncode`, `.comp`.

**As-built note (2026-11-05, gate 03l; the sketch above is unchanged).** The `pairSplitAt`
machine (`Randomized/Build/PairSplit.lean`) uses one work tape, not two: the parser stores `u`,
and the copy scan of `b` doubles each bit while the work head walks across the stored `u`. Its
buffered aligned parser is public (`Turing.PairParse`) and is shared by the `unaryMul` machine
(`Randomized/Build/UnaryMul.lean`), which stores `u` and replays it once per symbol of `v`.

### 2.5 `TCSlib/Complexity/Randomized/Closure.lean` — closure catalogue

Every lemma is `NUPPT.ofPolyTime` of an FP function built from
`A.polyTimeComputable_output`, `PolyTimeComputable.comp/.pairEncode/.append`,
`polyTimeComputable_const/_prepend/_unary/_pairFstD/_pairSndD/_iterate_pairFstD/_pairConcat/_pairSwap/_ite/_and/_lenLe/_lenEq`,
`polyTimeComputable_unaryPoly` and `pairTakePoly/DropPoly`; the equation is `output_ofPolyTime`
+ `pairDecode_pairEncode` + `funext`. `Uniform` is preserved whenever the advice is `A.advice`
or `[]`.

```lean
theorem NUPPT.exists_comp (A : NUPPT) {pre post} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r)
theorem NUPPT.exists_reparam (A : NUPPT) (p : PolyExpr) :                        -- n ↦ p(n), uniform
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r
theorem NUPPT.exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr) (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n)))      -- 1^{φ n}, advice (φ n) hard-wired
theorem NUPPT.exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧ ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r
theorem NUPPT.exists_split (A : NUPPT) (p : PolyExpr) :                          -- extra coins as data
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n))
theorem NUPPT.exists_seq (A B : NUPPT) :                                          -- sunglass composition
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n))
```

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | `pairFstD`, `pairSndD`, `pairEncode`, `comp`, `A.polyTimeComputable_output` |
| `exists_reparam p` | advice `A.advice (p n)` (length `A.adv.subst p` by `eval_subst`); machine replaces `1^n` by `1^{p n}` (`unaryPoly p` on `pairFstD (pairFstD (pairFstD z))`) and re-pairs | `unaryPoly`, `pairEncode`, `comp` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩` (length `2p+2+A.adv.subst p`); coins `A.coins.subst p ≥ A.coins.eval (φ n)` (`eval_mono`); the machine cuts `1^{A.coins.eval (φ n)}` coins (`unaryPoly A.coins` on the advice's `1^{φ n}`, then `pairSplitAt`) | `pairSplitAt`, `unaryPoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`, length `2·A.adv + 2 + b`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `1^{p n}`; pass the head as data | `pairTakePoly p`, `pairDropPoly p` |
| `exists_seq` | cut at `1^{A.coinLen n}`; run `A.output` on the first part, then `B.output` on `⟨⟨⟨1^n, ⟨y, a⟩⟩, α_B⟩, r₂⟩`; advice `⟨α_A, α_B⟩` | both outputs, `pairTakePoly/DropPoly`, pairing |
| negation / `[true]` normalisation | `computesFunInTime_ifEq` via `exists_comp` | Composition.lean |
| branching | FP-level `polyTimeComputable_ite`, `computesFunInTime_cond` | PolyTimePairing, Build/Wrappers |
| length tests | `polyTimeComputable_lenEq/_lenLe` | PolyTimePairing |
| loop fuel | `computesFunInTime_polyBits` (normal form) and `unaryPoly` + `computesFunInTime_lengthBits` (general `PolyExpr`) | Build/Primitives |

### 2.6 `TCSlib/Complexity/Randomized/Repetition.lean` — the load-bearing lemma, repaired

```lean
theorem polyTimeComputable_iterateFind {g} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out} (hout : PolyTimeComputable out) (R P : PolyExpr)
    (horbit : ∀ x i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x) | none => []
theorem polyTimeComputable_iterate {g} (hg) (R P) (horbit) : PolyTimeComputable fun x => g^[R.eval x.length] x
theorem polyTimeComputable_iterateEmit {g emit} (hg) (hemit) (R P) (horbit) :
    PolyTimeComputable fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x)
theorem polyTimeComputable_majority : PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)]
theorem polyTimeComputable_pairXor : PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z)
theorem polyTimeComputable_pairEq : PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)]
theorem polyTimeComputable_blockMap (b : PolyExpr) {g} (hg) :
    PolyTimeComputable fun z => (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
      g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))
```

**Construction of `iterateFind` (instance of `exists_loopFindTM`, Loop.lean:2633), with the
three panel repairs built in.**

1. *State word carries the input.* `s0 x := pairEncode x x` (the second component is the
   current orbit point). Loop data: `stepF x w := if |pairSndD w| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`
   (**length-guarded**), `acceptF x w := acc (pairSndD w)`, `out x w := out (pairSndD w)`,
   `Inv x w := pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length`. `hInv0` is
   `pairDecode_pairEncode`; `hInvStep` holds because the guard fixes the state once the bound
   is exceeded and otherwise `|g s| ≤ …` is **not** needed: the guarded step keeps the second
   component unchanged when it is already too long, so `Inv` is closed under `stepF` for every
   `w` (refutation J1-7/J2-15/J3-5). On the orbit `i ≤ R|x|`, `horbit` shows the guard is never
   taken, so `(stepF x)^[i] (s0 x) = pairEncode x (g^[i] x)` and the `find?` of the conclusion
   is the statement's (a 40-line pure lemma `iterate_guard_eq`).
2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
   `C₁ := exists_installCallTM` for `w ↦ pairEncode [acc (pairSndD w)] w` (verdict as the first
   cell of the installed word: `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed),
   `C₂ := exists_installCallTM` for `w ↦ stepF' (pairSndD w)` where `stepF'` is the guarded step
   on the pair (FP: `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on
   `⟨pairSndD w, 1^{P|pairFstD w|}⟩` by `unaryPoly P ∘ pairFstD`), `C₃ := exists_emitCallTM` for
   `w ↦ out (pairSndD (pairSndD w))`. Each module promises first-visit-to-exit from the clean
   seam over an arbitrary native input (Loop.lean:5645/5691) and `0 < C.k`.
3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
   the tape counts are equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean).
   **The anchor is the fresh state `inl ()`** whose transition is stationary into `C₁.entry`
   (refutation J2-16/J3-6: no module-internal state is the anchor). The module tables are
   copied with every transition *targeting* `Cᵢ.exit` **redirected** to a fresh branch state
   (`inr (inr k)`), so the module's own table at `exit` is never consulted and the case
   `entry = exit` is harmless: the first positive visit of `exit` promised by the contract is
   exactly the first entry into the branch state, with the clean seam on the tapes. Branch
   states: after `C₁`, read tape-0 cell 0 — `true` → `C₃.entry`, `false` → `C₂.entry`; after
   `C₂` → anchor (one stationary step); after `C₃` → halt.
4. *`hstart`.* From `initCfg x`, install `s0 x = pairEncode x x` on tape 0: this is one more
   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
   argument word `x` itself, which must first be on tape 0: a one-state copy scan of the native
   input onto tape 0 plus `timed_rewind` (≈ 100 lines; precedent: the startup phases of
   `computesFunInTime_splitSolveWith`). No anchor visit before the seam.
5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
   clause: `C₃` to its first exit emitting `out (pairSndD w)` and halt; advancing clause: `C₂`
   to its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside
   the round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch
   state). Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
   `Q n := 2 n + 2 + P.eval n + 4` (length of the state word), a normal-form majorant by
   `eval_le`.
6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
   `unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?` range must be
   exactly `R|x| + 1`: use the exact form).
7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
   `PolyTimeComputable`. `iterate` threads a unary counter in the state
   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input);
   `iterateEmit` threads an accumulator; the derived string functions are instances
   (REUSE-MAX §7.4, unchanged).

Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
`satStopTM`, `sat_run_agree` in `ClassNP/SAT.lean` (private copies, not edits). If the lemma is
not closed in run 4 it is the single named admission of D11.

**As-built erratum (2026-11-05, gate 03l, minor 2; the frozen text above is unchanged).** The
machine of `polyTimeComputable_iterateFind` (`Randomized/Build/IterateFind.lean`, with
`Randomized/Build/IterateFindHost.lean` and the public host `TuringMachine/Build/ModuleHost.lean`)
departs from steps 1–5 and 7 as follows. The frozen signatures and decisions are unchanged.
- *Step 1: the guard and the invariant.* The guard tests the **new** point:
  `stepF x w := if |g (pairSndD w)| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`. The guard
  on the old length written above does not close `Inv`: for `x = []`, `P = var` and
  `g s = true :: s`, the word `⟨[], []⟩` satisfies `Inv`, passes the guard `0 ≤ 0`, and steps to
  `⟨[], [true]⟩`, which does not. The machine's invariant is the actual-pair invariant
  `Inv x w := ∃ s, w = pairEncode x s ∧ |s| ≤ P|x|`, which, unlike `pairFstD w = x ∧ …`, excludes
  malformed words and gives the length bound `|w| ≤ 2|x| + 2 + P|x|` that the budget needs.
  (`Repetition.lean`'s `guardedStep` is the same step; its `LoopInv` is the pure invariant above,
  not the machine's.)
- *Steps 2–3: the gluing.* No transition is redirected. A release flag halts each clean-call
  module one silent step after its first positive exit, and the run is cut at its first halt
  (the clean-module contract `Turing.ModuleHost.Clean`, `clean_install`, `clean_emit`). The
  modules are padded to a common bank of tapes and run in one finite host with states
  `Fin 3 ⊕ Σ i, (M i).State` over five modules (copier, startup install `x ↦ ⟨x, x⟩`, verdict
  install, step install, payload emit): the anchor `inl 0`, the branch `inl 1` and the halt
  `inl 2`. This host is now the public clean-module host `Turing.ModuleHost.hostTM`
  (`machine-library-design.md` §14, row H14), harvested on 2026-11-05 from `ClassNP/SAT.lean`'s
  private module layer and this machine's copy of it.
- *Step 4: the startup.* The input is copied onto tape 0 by a two-state copier (`copyTM`: copy and
  turn, then rewind both heads), not by a one-state scan and `timed_rewind`.
- *Step 5: the budget.* Every request has length at most `2n + 6 + P n`, and the common budget is
  `T n = A·(2n + 7 + P n)^D` (`IterateFind.lean`), with `A` and `D` collected from the modules'
  budgets and the fuel machine.
- *Step 7.* `iterate`'s counter test is `R|x| ≤ |cnt|` (`StateLoop.IterLoop.acc`), not `lenEq`.

### 2.7 `TCSlib/Cryptography/Asymptotic/Sampling.lean`

```lean
def StatClose {σ τ γ} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
theorem distAdv_le_of_statClose … (h : StatClose X Y δ) (D : γ → ρ → Bool) : distAdv X Y D ≤ δ
theorem StatClose.prod … (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ')
theorem StatClose.map … (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m)
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m)
theorem rejectionSample_uniform_of_some (m k T) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b => rejectionSample m k T b = some i) = uprob (fun b => rejectionSample m k T b = some j)
theorem uprob_rejectionSample_none (m k T) (hm) (hk) :
    uprob (fun b => rejectionSample m k T b = none) = (1 - (m : ℝ) / 2 ^ k) ^ T
theorem statClose_rejectionSample (m k T) (hm) (hk) (d : Fin m) :
    StatClose (fun b => (rejectionSample m k T b).getD d) (id : Fin m → Fin m) ((1 - (m : ℝ) / 2 ^ k) ^ T)
```

**Run-3 repair (audit P2-1, pack P2).** `uprob_permFromCoins_none_le` is stated with the
provable bound `n * (1 - 1/2^k)^T` (the frozen `n (1/2)^T` is false: the last position has
range `1` and fails with probability `(1 - 1/2^k)^T`). The permutation section moved to
`Asymptotic/Permutations.lean` (file-size limit), which also owns the campaign parameters and
the closed form:
```lean
def permBits (n : ℕ) : ℕ := Nat.size n            -- n ≤ 2^k ≤ 2n
def permTrials (n : ℕ) : ℕ := 2 * n * n
theorem statClose_permFromCoins (n k T) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b => (permFromCoins n k T b).getD d) id (n * (1 - 1 / 2 ^ k : ℝ) ^ T)
theorem uprob_permFromCoins_none_le_two_pow (n) :
    uprob (fun b => permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n
theorem statClose_permFromCoins_two_pow (n) (d) :
    StatClose (fun b => (permFromCoins n (permBits n) (permTrials n) b).getD d) id (n * (2 : ℝ)⁻¹ ^ n)
```
with the general `statClose_getD_of_uniform_of_some` (a sampler uniform conditioned on
success, made total by a default, is `StatClose` to uniform within its failure probability),
`StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` (`(1 - 1/m)^m ≤ 1/2`, Bernoulli)
in `Sampling.lean`; all proved except `permFromCoins_uniform_of_some` (fill).

Proof sources: `distAdv_le_of_statClose` transposes `abs_sum_sub_le_statDist`'s argument
(average over the distinguisher's coins; each coin string is one test set; `uprob_prod`);
`StatClose.prod` by `uprob_prod` (Fubini) and the triangle inequality; the rejection lemmas by
`uprob_prod` over trials, `OneWay.uprob_pi_forall` for the all-fail event, and the bijection
`bitsToNat : (Fin k → Bool) ≃ Fin (2^k)` (`finFunctionFinEquiv`) for uniformity of one trial.
This file also hosts the ch. 2 concrete lemmas C4 (`first_hit_uniform` = `rejectionSample_uniform_of_some`),
C5 (`pushesUniform_of_card_fiber`) and C10 (statistical switch = `StatClose.map` + `distAdv_le_of_statClose`).

### 2.8 `TCSlib/Cryptography/Asymptotic/Adversary.lean`

```lean
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool)       -- wrong length = failure (D5)
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool                   -- pad/truncate (samplers)
def Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)
def Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) : (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool)
def Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
def Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool
def Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
noncomputable def invProbOpt {α β ρ} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : ℝ
theorem invProbOpt_le_invProb [Inhabited α] (f) (A) : invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default)  -- proved
theorem invProbOpt_some (f) (A : β → ρ → α) : invProbOpt f (fun y r => some (A y r)) = invProb f A           -- proved
```

### 2.9 `TCSlib/Cryptography/Asymptotic/OneWay.lean`

```lean
structure FunFamily where
  inLen : PolyExpr
  outLen : PolyExpr
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily
def Easy (𝓕 : FunFamily) : Prop :=                                         -- [26.1(1), 27.3(1)]
  ∃ F, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
noncomputable def invProbAt (𝓕) (A : NUPPT) (n : ℕ) : ℝ := invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))
structure StrongOneWay (𝓕 : FunFamily) : Prop where                        -- [PS10, Def 27.3]
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n
structure WeakOneWay (𝓕 : FunFamily) : Prop where                          -- [PS10, Def 28.4]
  easy : 𝓕.Easy
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀, 𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where                     -- [PS10, Def 26.1], 1^n form (headline; run-3 audit P3-2)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where                  -- [PS10, Def 26.1], literal (A gets f(x) only)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
theorem FunFamily.WorstCaseOneWay.toLit {𝓕} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit          -- always (proved)
theorem FunFamily.WorstCaseOneWayLit.toParam {𝓕} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay                                                 -- injective outLen (proved)
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily        -- inLen = var, outLen = p
def LengthRegular (f) (p : PolyExpr) : Prop := ∀ x, (f x).length = p.eval x.length
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily                        -- inLen = q·inLen, f' = prodFun blockwise
end FunFamily

theorem weak_to_strong {𝓕} (h : FunFamily.WeakOneWay 𝓕) : ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q)   -- [35.1]
theorem strong_prod_two {𝓕} (h : FunFamily.StrongOneWay 𝓕) : FunFamily.StrongOneWay (𝓕.prod (.const 2))      -- [35.2]
theorem FunFamily.StrongOneWay.weak {𝓕} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay                                   -- sanity
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var)                           -- non-vacuity

structure PermFamily where f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)        -- the single OWP of 79.4/126.4
def PermFamily.toFunFamily (P : PermFamily) : FunFamily
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay
```

Theorem 35.1 plan (REUSE-MAX §3.3 with the sampling repair). `q := mul (const 2) (mul var q_w)`
(the text's `m = 2nq(n)`, literal). The reduction machine `A*` hard-wires in its advice
`⟨A'.advice n, 1^{m n}, 1^{T n}, 1^{inLen n}, 1^{A'.coinLen n}⟩` (all `PolyExpr`, so advice is
optional and the reduction is in fact `Uniform`-preserving) and iterates
(`polyTimeComputable_iterateFind`, `T n := 2 n m(n) n^c` rounds) the step: cut a coin segment
(`pairTakePoly`), sample the position `i` by `rejectionSample (m n) k n` with `k := clog`-free
`k n := m n` bits (`2^{m n} ≥ m n`, failure `≤ 2^{-n}` per trial), evaluate `F` blockwise
(`blockMap inLen`), plant `y` (`blockSelect`), call `A'.output` on the re-paired layout, test
`F ⟨1^n, z_i⟩ = y` (`pairEq`), emit `z_i` (or `0^{inLen n}` on exhaustion so that the machine is
`yaoInverter` *including its default*). Functional identity: `A*.inverter n _ _ y r = some (yaoInverter (𝓕.f n) (B n) (T n) y (coinsEquiv n r))`
on the event that every position trial succeeds, which has probability `≥ 1 − T n · 2^{-n}`;
`StatClose.prod`/`distAdv_le_of_statClose` move `invProb` by at most that. Then
`yao_amplification_exp` with `α' := 1/q_w(n)`, `μ₀ := 1/n^c − T n 2^{-n}`, and
`not_negligible_iff` as in REUSE-MAX steps 8–9.

### 2.10 `TCSlib/Cryptography/Asymptotic/Collections.lean`

```lean
structure Collection where                      -- [PS10, Def 41.1]; Gen(1^n) = ⟨i, t⟩, t ignored by plain collections
  D : List Bool → Type
  [fintypeD : ∀ i, Fintype (D i)]  [inhabitedD : ∀ i, Inhabited (D i)]
  encD : ∀ i, D i → List Bool
  decD : ∀ i, List Bool → Option (D i)
  decD_encD : ∀ i x, decD i (encD i x) = some x
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w                     -- canonical decoding; gate 03b, G3-1
  f : ∀ i, D i → List Bool
  gen : NUPPT     gen_uniform : gen.Uniform
  sample : NUPPT  sample_uniform : sample.Uniform
  eval : List Bool → List Bool   eval_poly : PolyTimeComputable eval
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,          -- [41.1 (2), membership]; run-3 audit P3-1
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
    eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) = f (pairFstD (gen.runAt n [] r)) x
namespace Collection
def index (F) (n) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)
def trap  (F) (n) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)
def SampleClose (F) (δ : ℕ → ℝ) : Prop := ∀ n r, StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)
noncomputable def invProbAt (F) (A : NUPPT) (n) : ℝ :=        -- i ← Gen; x ← D_i uniform (ideal); uexp over Gen's coins
  uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n =>
    ∃ x', F.decD _ (A.runAt n (pairEncode (F.index n r) (F.f _ z.1)) z.2) = some x' ∧ F.f _ x' = F.f _ z.1
structure OneWay (F : Collection) : Prop where
  sampleClose : ∃ δ, Negligible δ ∧ F.SampleClose δ
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop := …          -- Def 78.3 for collections (uexp/uprob form)
end Collection
structure PermCollection extends Collection where perm : ∀ i, D i ≃ D i; f_perm : ∀ i x, f i x = encD i (perm i x)   -- [55.1]
structure TrapdoorCollection extends PermCollection where                                                                -- [56.1]
  inv : NUPPT  inv_uniform : inv.Uniform
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)
theorem Collection.OneWay.exists_strongOneWay {F} (h : F.OneWay) : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay            -- [42.2 ⇒]
```

The dependent domain is handled by `uexp` over the generator's coins of the inner `uprob` on
`D i × ρ` (the uniform-on-`Σ` trap of the inventory is avoided). The (⇐) direction of Thm 42.2
(`StrongOneWay 𝓕 → (collection with Gen = 1^n).OneWay`) is stated alongside.

Run-3 audit (P3-1): the field `sample_spec` was added — without it Thm 42.2 (⇒) is unprovable
(nothing ties the sampler's outputs to `D_i` off the canonical encodings); `exists_strongOneWay`
is now proved from the explicit `owfFamily_strongOneWay` (sorried under its sketch), and every
instance discharges `sample_spec` (`FunFamily.toCollection`, `factoringCollection` by the
canonical default pair, `Collection.glPad m henc` — which now takes `henc` — by `F.sample_spec`,
the RSA/Rabin/Blum/exponentiation candidates by sorried `*Sampler_spec` stubs;
`expCollection H G hV` takes the validity bridge and its generator outputs `dlDefaultIndex`
below `n₀`). Run-3 audit (P3-5): the literal `Inv(1^n, ⟨⟨i, t⟩, y⟩)` form of Def 56.1 (6) was
not adopted; the Deviation is recorded on `TrapdoorCollection`, `rsaGen` and `blumGen`.

Gate 03b (finding 1, ruling G3-1): the field `encD_decD` (canonical decoding) was added. Without
it the sampler's and the trapdoor inverter's outputs were pinned only up to a possibly lenient
decoder, so `eval` and a hard-core evaluator (constrained on encodings) could misbehave on them.
Every instance discharges it by a decoder lemma (`ofFn_of_decodeFin_eq_some` for
`FunFamily.toCollection` and the padding of `Collection.glPad`; `expEnc_of_expDec`,
`encodeDistinctPrimes_of_decode`, `rsaEnc_of_rsaDec`; inline for `rabinCollection` and
`rabinBlumTrapdoor`). Derived: `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`,
`sample_eq_encD`, `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv`,
`Collection.HardCore.nonempty_predEvaluator` and the evaluator-free
`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. The helpers of Thm 42.2
(`NUPPT.withIndexParam`, `NUPPT.runLenPoly`, `splitCoins`, the marker padding) moved, names
unchanged, to `Asymptotic/CollectionsHelpers.lean`, which `Collections.lean` imports.

### 2.11 `TCSlib/Cryptography/Asymptotic/Ensembles.lean`

```lean
structure Ensemble (ℓ : PolyExpr) where                 -- [PS10, Def 69.3]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)
namespace Ensemble
def uniform (ℓ : PolyExpr) : Ensemble ℓ
def Samplable (X : Ensemble ℓ) : Prop :=                 -- distribution level, D6
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0
def Indist (X Y : Ensemble ℓ) : Prop :=                  -- [69.4], D receives 1^n (headline)
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))
def IndistLit (X Y : Ensemble ℓ) : Prop :=               -- [69.4] literal: D receives t only
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)                                  -- [74.1]
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ'                               -- {M(X_n)}
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ)
end Ensemble
theorem Ensemble.Indist.toLit (h : X.Indist Y) : X.IndistLit Y
theorem Ensemble.IndistLit.toIndist (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y
theorem Ensemble.Indist.refl (X) : X.Indist X                                                      -- non-vacuity
theorem Ensemble.Indist.symm (h : X.Indist Y) : Y.Indist X
theorem Ensemble.Indist.push {ℓ ℓ'} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) : (X.push M ℓ').Indist (Y.push M ℓ')   -- [71.5]
theorem hybrid_lemma {m} (hm : 0 < m) (X : ℕ → σ → γ) (D) : ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i+1)) D  -- [71.6], proved
theorem Ensemble.Indist.trans (h₁ : X.Indist Y) (h₂ : Y.Indist Z) : X.Indist Z
theorem Ensemble.Indist.copies (h : X.Indist Y) (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) : (X.copies t).Indist (Y.copies t)
def mixEnsemble (X₀ X₁ : Ensemble ℓ) (n) : Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool)
theorem predict_eq … : uprob (fun z => D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) = 1/2 + (acceptProb X₁ D - acceptProb X₀ D)/2   -- Claim 73.a
theorem prediction_lemma (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ) (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv …) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1/2 + μ n/2 < uprob fun z => A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1   -- [73.8]
```

**Run-3 repair (audit P2-2, pack P2).** `Ensemble` has the additional instance field
`[nonempty : ∀ n, Nonempty (σ n)]` (an empty seed type is not a distribution; without it
`NextBitUnpredictable` was vacuous for an empty-seed ensemble and `prediction_lemma`,
`NextBitUnpredictable.pseudorandom` were unprovable as frozen). Every ensemble of the
campaign fills it by instance resolution (including `ddhReal`/`ddhRandom` of
`Candidates/ElGamal.lean`, whose seeds are products of coin types since the run-3 repair
P8-1). `prediction_lemma` and
`NextBitUnpredictable.pseudorandom` have exactly the frozen shapes above (the run-2 ad hoc
hypotheses `h₀ h₁`, `hσ` were dropped); `predict_eq` carries `[Nonempty σ₀] [Nonempty σ₁]
[Nonempty ρ]`, discharged automatically for ensemble seeds and machine coins.

Proof plans: 71.5 — `D' := exists_seq M D` (coins `M.coins + D.coins`), then
`distAdv_sunglassRed` with `P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` gives equal advantages
after `acceptProb_comp_equiv` on the coin split (`Fin.appendEquiv`-style equivalence
`(Fin (a+b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)`); `ℓ' : PolyExpr` makes the padding
computable (`unaryPoly ℓ'`). `toLit`: a literal distinguisher at length `ℓ n` is a `1^n`
distinguisher via `exists_reparam_advice ℓ.eval ℓ` with the advice carrying `α(ℓ n)` and
ignoring `1^n`; `toIndist` (injective `ℓ`): a `1^n` distinguisher `D` becomes a literal one with
advice `⟨1^n, D.advice n⟩` at length `ℓ n` (`Classical.choose` of the preimage; `[]` off the
image), coins `D.coins` evaluated at `ℓ n ≥ n` (`eval_mono`) and cut to `D.coinLen n`
(`exists_reparam_advice` with `φ := ℓ⁻¹`). `copies`: for every `n` take a maximising hybrid
index `k_n` (`exists_multicopyRed_ge`, `Finset.exists_max_image`) into the advice, sample the
other coordinates with the `Samplable` evaluators (`iterateEmit` over `t n` positions,
`StatClose … 0` lifts to the product law by `StatClose.prod`), plant the challenge; then
`Negligible.mul_pow`. `prediction_lemma`: `A := D` or `D` negated (`exists_comp` with
`computesFunInTime_ifEq`), chosen by pigeonhole on the infinite set; `predict_eq` is proved
once with `uprob_bool_prod`.

### 2.12 `Asymptotic/{Pseudorandom,NextBit,HardCore}.lean` — definition shapes

(The collection form of Thm 87.3, `Collection.glPad` … `goldreich_levin_coll`, moved unchanged to
`Asymptotic/HardCoreCollection.lean`, which `HardCore.lean` imports; gate 03c, finding 11.)

```lean
structure PRG where                                           -- [PS10, Def 77.1], length-regular
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, n < stretch.eval n                           -- every n, n = 0 included: 2n, n^c excluded (§5.25; gate 03c, G3-2)
def PRG.Easy (P : PRG) : Prop := ∃ F, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
def PRG.ensemble (P : PRG) : Ensemble P.stretch               -- seeds Fin n → Bool
def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

noncomputable def nextBitProb {ℓ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i
def Ensemble.NextBitUnpredictable (X : Ensemble ℓ) : Prop :=   -- [PS10, Def 75.2], i < ℓ n, A gets 1^n and the prefix
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1/2 + ε n
theorem Ensemble.NextBitUnpredictable.pseudorandom (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]; the source's statement (hℓ : ∀ n, 0 < ℓ.eval n dropped at gate 03c, G3-7b)

def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=   -- [PS10, Def 78.3]
  (∃ H, PolyTimeComputable H ∧ ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1/2 + ε n
```

Theorem shapes of the HardCore file (statement phase): `owp_hardcore_prg (P : PermFamily) (h) : OneWayPermutation P → HardCore P.toFunFamily h → (PRG with G n s = f n s ‖ h n s).Secure`
(79.4, via `exists_owpPredictorBits`); `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (prgExtBits-based PRG of stretch ℓ).Secure`
(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator; **as shipped**
(gate 03c, finding 4): `prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
(hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure`, the one-bit input of the
text's Lemma 80.5 ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG"); a general secure `P : PRG` reaches it through
`PRG.truncate` with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` in `Asymptotic/PRF.lean`, and `hℓ`
carries the cost of §5.25);
`cor_81_7` (closed form `prgExt_succ`); `goldreich_levin (𝓕) : StrongOneWay 𝓕 → StrongOneWay (glPad 𝓕) ∧ HardCore (glPad 𝓕) glBit`
(87.3, via `invProb_guessInverter`, `k(n) := ⌈log₂(2n^{2c+1}+1)⌉` hard-wired, `iterateFind`
for the `n(2^k−1)` calls, `majority`, `pairXor`); `goldreich_levin_coll (F : Collection) …`
(87.3.coll, `half_le_uprob_threshold` over `i`).

### 2.13 Encryption shapes — `Asymptotic/Encryption.lean`, `Asymptotic/PublicKey.lean`, `ZeroKnowledge/Encryption.lean`

```lean
structure PrivateKeyScheme where                               -- [PS10, Def 24.7]
  gen enc dec : NUPPT
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_uniform : dec.Uniform
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg) (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m
def PrivateKeyScheme.encDist (S) (n) (m : Fin n → Bool) : S.gen.Coins n × S.enc.Coins n → List Bool
def PrivateKeyScheme.SingleMessageSecure (S) : Prop :=        -- [91.1]
  ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool), distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.multiEncDist (S) (n q : ℕ) (m : Fin (q+1) → Fin n → Bool) : S.gen.Coins n × (Fin (q+1) → S.enc.Coins n) → List Bool
def PrivateKeyScheme.MultiMessageSecure (S) : Prop :=         -- [93.1], q n + 1 messages
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
    distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.ZeroKnowledge (S) : Prop :=               -- [111.1]
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m : Fin n → Bool),
    distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n
theorem PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge (S) : S.SingleMessageSecure ↔ S.ZeroKnowledge   -- [112.2]

structure PublicKeyScheme where                                -- [PS10, Def 102.1]; clause (4) dropped (Deviation)
  gen enc : NUPPT   dec : List Bool → List Bool
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_poly : PolyTimeComputable dec
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg)) (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
def PublicKeyScheme.pkEncDist (S) (n) (m) : S.gen.Coins n × S.enc.Coins n → List Bool    -- ⟨pk, Enc_pk(m)⟩
def PublicKeyScheme.Secure (S) : Prop := ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n   -- [102.2]
```

`MultiMessageSecure` for PKE, `SingleBitSecure` (message space `Bool`, encoded as `[b]`), the
bitwise scheme (103.f) and Alg 104.3 (`gen := TDP gen`, `enc := ⟨f_i(r), b_i(r) ⊕ m⟩`) follow the
same shapes in `PublicKey.lean`. Alg 92.1 and Alg 99.1 are `PrivateKeyScheme` values built with
`ofPolyTimeUniform` of FP functions (`pairXor` for the one-time pad).

### 2.14 `TCSlib/Cryptography/Asymptotic/PRF.lean`

```lean
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where              -- [PS10, Def 96.1]
  σ : ℕ → Type   [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂            -- RF_n, seed = table
def OracleEnsemble.keyed {ℓ₁ ℓ₂} (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) : OracleEnsemble ℓ₁ ℓ₂
inductive OracleMove (ℓ₁ : ℕ) | query (x : Fin ℓ₁ → Bool) | ret (b : Bool)
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁                 -- ⟨[false], x⟩ query; [true, b] verdict
def encodeHist {ℓ₁ ℓ₂} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool
def buildTree {ℓ₁ ℓ₂} (next : List (…) → OracleMove ℓ₁) : ℕ → List (…) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
def Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) : OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)
theorem Complexity.NUPPT.toOracleAdversary_boundedBy (D) (n ℓ₁ ℓ₂ q) : (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q
def OracleEnsemble.Indist (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=               -- ∀ D, ∀ q
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n => distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))
theorem OracleEnsemble.Indist.refl (O) : O.Indist O                                                     -- non-vacuity
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where                 -- [PS10, Def 96.2]
  easy : ∃ E, PolyTimeComputable E ∧ ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)
theorem prfAdv_toOracleAdversary (F) (D : NUPPT) (n q : ℕ) :
    distAdv ((keyed F).O n) ((random .var .var).O n) (oracleDist (D.toOracleAdversary n n n q)) = prfAdv (F n) (D.toOracleAdversary n n n q) := rfl
```

Theorem 97.3 plan: REUSE-MAX §5 unchanged (the hybrid indices `(i_n, j_n)` from
`exists_ggmBits_dist` into the advice; the PRG distinguisher hosts `D`'s next-query function
in an `iterateFind` loop over at most `q n + 1` activations with the lazily sampled table in the
state; functional identity with `evalLazy`/`noteQuery` by induction on the tree;
`Negligible.mul_pow` for `n · q n`). Theorem 99.2's oracle adversary is a chain of `q n + 1`
`query` nodes built by `buildTree` from an FP next-query function with the messages as advice.

### 2.15 Chapter 4 — `ZeroKnowledge/{Interaction,InteractiveProofs,Defs,Commitment,GraphIsomorphism}.lean`

```lean
structure Strategy where
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool     -- x z r received ↦ message / output
  coins : PolyExpr
namespace Strategy
def coinLen (S) (n) : ℕ := S.coins.eval n
abbrev Coins (S) (n) : Type := Fin (S.coinLen n) → Bool
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []
def ofNUPPT (A : NUPPT) : Strategy :=   -- one activation at parameter |x| on ⟨⟨x, z⟩, messages⟩, whole random tape
  { next := fun x z r hist => A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r, coins := A.coins }
def Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
end Strategy

def moverIsV (vFirst : Bool) (k : ℕ) : Bool := if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)
/-- Messages received by (P, V) after k moves. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 => let e := exec P V vFirst x zP zV rP rV k
             if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2) else (e.1, e.2 ++ [P.next x zP rP e.1])
structure View where (x z r : List Bool) (received : List (List Bool))
def View.encode (v : View) : List Bool := pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))
structure Protocol where (P V : Strategy) (rounds : PolyExpr) (verifierFirst : Bool)    -- rounds = number of messages
namespace Protocol
abbrev ExecCoins (π) (P' : Strategy) (x) : Type := P'.Coins x.length × π.V.Coins x.length
def withV (π) (V' : Strategy) : Protocol := { π with V := V' }
def transcriptWith (π) (P') (x y z) (r : π.ExecCoins P' x) : List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
def outV (π) (P') (x y z) (r) : List Bool := π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
def outP (π) (x y z) (r) : List Bool
def viewV (π) (x y z) (r : π.ExecCoins π.P x) : View := ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩
def viewP (π) (x y z) (r) : View
end Protocol

structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where            -- [PS10, Def 116.1]
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y, ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) z, 1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])
structure InteractiveProofErr (π) (L) (s : ℕ → ℝ) : Prop where                        -- soundness error s
  efficientV …  complete …
  sound : ∀ x ∉ L, ∀ P' z, 1 - s x.length ≤ uprob (fun r => π.outV P' x [] z r = [false])
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where   -- Appendix B
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧ ∀ x y, T (pairEncode x y) = true ↔ R x y
structure EfficientProverProof (π) (L) (R) : Prop extends InteractiveProof π L where    -- [PS10, Def 119.5]
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z, uprob (fun r => π.outV π.P x y z r = [true]) = 1
structure EfficientProverProofErr (π) (L) (R) (s) : Prop extends InteractiveProofErr π L s where …

def Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool := S.runAt x.length (pairEncode x z) r
def HVZK (π) (R) : Prop :=                                                               -- [121.1]
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧ ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
    distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def ZK (π) (R) : Prop :=                                                                 -- [121.2]
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def StatZK (π) (R) (δ : ℕ → ℝ) : Prop :=
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
def PerfectZK (π) (R) : Prop := StatZK π R (fun _ => 0)
def PerfectZKAbort (π) (R) : Prop :=                                                     -- Goldreich Def 4.3.1, ⊥ = []
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1/2 ∧
    ∀ T : List Bool → Prop, uprob (fun r => T (view r)) * uprob (fun r => S.simulate x z r ≠ []) = uprob (fun r => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))
theorem StatZK.zk (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R
theorem StatZK.hvzk (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R

structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where          -- [PS10, Def 126.3], binding repaired
  easy : PolyTimeComputable Com
  binding : ∀ n v₀ v₁ r₀ r₁, v₀.length = n → v₁.length = n → r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
            (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r))) (D.distinguisherL n) ≤ ε n
```

Graph isomorphism (compiled expressibility check): `Graph n := Fin n → Fin n → Bool`,
`permGraph G π u v := G (π.symm u) (π.symm v)`, `encGraph`/`decGraph` (adjacency matrix, `n²`
bits, `Nat.sqrt`), `encPerm`/`decPerm` (relation matrix, `Fin.find`, `Equiv.ofBijective`),
`fisherYates n c`, `permFromCoins n k T : (Fin n → Fin T → Fin k → Bool) → Option (Equiv.Perm (Fin n))`
with `permFromCoins_uniform_of_some` and `uprob_permFromCoins_none_le (hk : n ≤ 2^k) : … ≤ n (1/2)^T`;
`giProver` (coins `normal 1 2`; `π` by `permFromCoins n n n`, identity on failure; message 1
`encGraph (π(G₀))`, message 3 `encPerm (if b then π * σ⁻¹ else π)`), `giVerifier` (coins
`const 1`; on `[H]` sends `[b]`, on `[H, γ]` outputs `[decide (encGraph (permGraph G_b (decPerm n γ)) = H)]`),
`giProtocol := ⟨giProver, giVerifier, const 3, false⟩` (three messages, prover first; the
verdict is the fourth activation), `Liso`, `Riso`, `Riso_witnessRelation`,
`gi_sim_H_dist`/`gi_sim_half` (Lemma 123.5, exact over `Equiv.Perm (Fin n)`),
`gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1/2)` (Prop 120.7,
one iteration), `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (Theorem 122.3,
`δ n = 2^{-n} + 2 n (1/2)^n` from the truncated simulator and the rejection sampler),
`giProtocolRep := ⟨giProverRep, giVerifierRep, mul (const 3) var, false⟩` with
`InteractiveProof giProtocolRep Liso` (Lemma 120.d), and the sanity
`npProtocol_interactiveProof : EfficientProverProof (npProtocol T) L R` (P sends `y`).

**Run-3 repair (audit P2-1, pack P2).** The permutation-sampler parameters above are
superseded: the honest parties sample by
`samplePerm n r := (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1`
(`permBits n = Nat.size n`, `permTrials n = 2n²`, `Asymptotic/Permutations.lean`) with
`permCoinLen n := n * permTrials n * permBits n ≤ (N + 1)²` whenever `2n² ≤ N`
(`permCoinLen_le`; every encoded instance has length `3n² + 2`, so the coin polynomials
`normal 1 2` are kept), `permFailBound n := n * (2 : ℝ)⁻¹ ^ n` (`statClose_samplePerm` and
`negligible_mul_permFailBound` proved from the shared lemmas; the run-2 `permFailBound_le_exp`
removed), and `polyTimeComputable_encPermFromCoins` (`ZeroKnowledge/Encoding.lean`) is stated
at the same parameters, GI's private `polyTimeComputable_encSamplePerm` being derived from
it. `gi_statZK`'s planned error becomes `δ n = 2^{-n} + (n + 1) · n · 2^{-n}`.

**Run-3 repair (audit P10-1/P10-2, pack P10).** The exact-probability engines of the
adaptive-prover bounds, `uprob_adaptive_guess` (Lem-119.c) and `uprob_gni_rep_cheat`
(Lem-119.b), assume the auxiliary coin type nonempty (`[Nonempty W]`, `[Nonempty ρ]`): `uprob`
on an empty type is `0`, so the run-2 statements specialised to `Empty` at `m = 0` read
`0 = 1`. Every consumer instantiates the coin type with a tape `Fin k → Bool`, so no
downstream statement changes; `uprob_gi_rep_cheat_le` (Lem-120.d, an inequality) keeps its
statement and is reproved by a case split on `ρ`. Audit P10-3 (divergent sampler copies) is
resolved by the P2-1 repair above: `polyTimeComputable_encSamplePerm` is derived from the
shared `polyTimeComputable_encPermFromCoins` at the one set of parameters.

---

## 3. Disposition of every panel refutation

| # | Refutation (judge) | Disposition |
| --- | --- | --- |
| 1 | REUSE-MAX `iterateFind`: `Inv x s := ∃ i ≤ R|x|, s = g^[i] x` not closed under `stepF` (J1-7, J2-15, J3-5) | **Fixed** (§2.6): length-guarded step on a state word carrying the input, `Inv x w := pairFstD w = x ∧ |pairSndD w| ≤ P|x|`; `horbit` shows the guard is inactive on the orbit. The statement is unchanged. |
| 2 | REUSE-MAX anchor exclusion / `entry = exit` and overriding the module table at `exit` (J2-16, J3-6) | **Fixed** (§2.6 step 3): fresh anchor state `inl ()` stepping into `C₁.entry`; transitions *into* `exit` are redirected to fresh branch states, the module table at `exit` is never overridden. |
| 3 | REUSE-MAX `Indist.push` without `hℓ'` (J1-8, J2-17, J3-7) | **Fixed**: `ℓ' : PolyExpr`; the bound is intrinsic (`eval_le`) and `1^{ℓ' n}` is computed (`unaryPoly`). |
| 4 | REUSE-MAX `Indist.copies` without `Samplable` (J1-8, J3-7) | **Fixed**: hypotheses `hX : X.Samplable`, `hY : Y.Samplable` (§2.11). |
| 5 | REUSE-MAX `Samplable` as a seed bijection is unsatisfiable for `U_n` and pushed ensembles (J2-14) | **Fixed**: distribution-level `Samplable` (`StatClose … 0` from `s.eval n` bits, `s : PolyExpr`); `U_n` has `s = var`, `S = pairSndD`. |
| 6 | REUSE-MAX GI `rounds = 3` leaves `outB = none`; `CR(n+1)^cR ≠ 3` (J1-9); FAITHFUL `rounds = 1` gives the coin bit (J1-14, J3-?) | **Fixed**: `rounds : PolyExpr := const 3` counts messages; the verdict is `V.next` on the complete history (fourth activation), always defined. |
| 7 | REUSE-MAX abstract `ℕ → ℕ` lengths (`inLen/outLen`, `Ensemble ℓ`, `push ℓ'`, `copies t`) against the brief (J1-10, J3-8) | **Fixed**: all are `PolyExpr`; `InLenPoly` and `Lin` disappear (`polyTimeComputable_unaryPoly`). |
| 8 | REUSE-MAX `1^n` given to Def 26.1 / 69.4 adversaries (J1-10, graft from FAITHFUL) | **Fixed**: `WorstCaseOneWayLit` literal (`inverterLit`), `IndistLit` literal; `WorstCaseOneWay`/`Indist` (headline, `1^n` form) related by `toLit`/`toParam`, `toLit`/`toIndist` (D5; run-3 audit P3-2 made the `1^n` form the headline of Def 26.1 as well). |
| 9 | REUSE-MAX power-of-two block count in 35.1 (J2 graft `pow2log`, J1 fallback R2) | **Rebutted/replaced**: no `pow2log` constructor; the text's `m = 2nq(n)` is literal and the uniform position is rejection-sampled with the D10 device (statistical term `T·2^{-n}` absorbed in `μ₀`). |
| 10 | REUSE-MAX `Samplable` claims and `prediction_lemma` advice (J1 critique) | `prediction_lemma` uses no advice (pigeonhole, `exists_comp`); `copies` uses advice for `k_n`. |
| 11 | ABSTRACT `WeakOWF` vacuous, `weak_to_strong` false (J1, J2, J3) | **Guarded**: `WeakOneWay.hard` carries `∀ n, 0 < q.eval n`; `weak_to_strong` stated for the guarded notion. |
| 12 | ABSTRACT `iterate`/`mem_iter` unsatisfiable without a growth bound (J1, J2, J3) | **Avoided**: every iteration lemma carries `horbit`; no interface fields. |
| 13 | ABSTRACT don't-care runs outside the declared coin length (`oracleAdv`, `coinsP/coinsV` at `z = []`, `PRF` unsatisfiable) (J1, J2, J3) | **Not applicable**: `NUPPT` is total; `runAt n` fixes one coin type per `n`; strategies use the whole tape at parameter `|x|`; oracle adversaries use `runAt n` on the growing history. |
| 14 | ABSTRACT `gi_sim_statDist` ill-typed (`FinDist` needs `Fintype`) (J2, J3) | **Avoided**: `StatClose` sup-over-test-sets form; `distAdv_le_of_statClose`. |
| 15 | ABSTRACT `exec` hardcodes verifier-first (J1) | **Fixed**: `Protocol.verifierFirst`, `moverIsV`. |
| 16 | ABSTRACT `exists_stepCallTM` extends private Loop.lean machinery (J1, J2) | **Avoided**: `iterateFind` uses only the public `exists_loopFindTM`, `exists_installCallTM`, `exists_emitCallTM`. |
| 17 | FAITHFUL `runCoins_eq_of_take` false at `t = 0` (J2) | **Not applicable** (no coin tape); the "extra coins unread" device is the `r.take` clause of `exists_reparam_advice`, a statement about FP functions. |
| 18 | FAITHFUL `Poly.eval = C(n+1)^c` cannot express `n`, `2n` (J1, J2) | **Fixed by `PolyExpr`** (`var`, `mul (const 2) var`). |
| 19 | FAITHFUL `FunFamily.str` conflates parameter and input length (J1, J2) | **Avoided**: `Easy` evaluates on `⟨1^n, x⟩`. |
| 20 | FAITHFUL `∃ N` after `∀ x y z` in `HVZK`/`ZK`/`hide` (J1, J2, J3) | **Avoided**: no coin budget variable; distinguisher at parameter `|x|`, `Lz` universally quantified before `ε`. |
| 21 | FAITHFUL `nuppt_seq_iff_advice` conditional on `PolyBound canonizerTime`; `one_work_tape_binary` not at the seam (J1, J2, J3) | **Off the critical path**: `NUPPTSeq` optional module with one named admission (D4, D11). |
| 22 | FAITHFUL `Strategy.IsPPT` run cut at the deadline; `encodeView` sorried (J3) | **Not applicable**: total machines; `View.encode` is defined. |
| 23 | FAITHFUL `exists_handlerSim` possibly prohibitive (J1) | **Not needed**: D7 next-query machines; GGM's reduction hosts the adversary's next-query function in `iterateFind`. |
| 24 | FAITHFUL `forall_of_uprob_eq_one` namespace (J1, J3) | Recorded: `TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one` (HardcoreBit/Basic.lean:107), `uprob_eq_one_of_forall` (:120). |
| 25 | FAITHFUL/J2: `distAdv_sunglassRed` is at Indistinguishability.lean:130 | Recorded. |
| 26 | J3: `1^n` vs `|x|` indexing, time in machine-input length, totality must be in the decision log | **Recorded** in D3 with the interdefinability argument. |

Issues found in this synthesis and resolved here (not raised by the panel):

* The text's "a round ends with the active machine halting — in which case the protocol ends"
  makes the literal `Pr[out_V = 0]` unsatisfiable against the immediately-halting prover
  (the verifier never outputs). The fixed-alternation model with the verdict on the complete
  history is the reading under which the literal `[false]` soundness clause is satisfiable
  (D8, Deviation recorded).
* With total machines, a verifier `V*` and a distinguisher `D` read all of an unbounded `z`,
  so the non-uniform reduction of Prop 128.8 (which hard-wires the worst `(x, y, z)`) needs
  `|z|` polynomially bounded; hence the `∀ Lz` clause (D8). The text's own model (time `t(|x|)`)
  implies the same bound implicitly.
* `exists_reparam_advice` is the one place an abstract `φ : ℕ → ℕ` appears; it is a theorem
  hypothesis with a `PolyExpr` majorant (needed by Lemma 64.3's `m(n) = n − ⌊log₂ n⌋` and by
  `IndistLit.toIndist`), consistent with the brief.

## 4. Grafts adopted (source → where)

| Graft | From | Where it lands |
| --- | --- | --- |
| Syntactic `PolyExpr` for every length/budget | ABSTRACT | `Randomized/PolyExpr.lean`; all structures |
| `∀ q : PolyExpr` oracle budget | ABSTRACT | `OracleEnsemble.Indist` |
| First-mover field; padded/explicit per-parameter coin types | ABSTRACT | `Protocol.verifierFirst`; coins at parameter `|x|` |
| Non-vacuity theorems | ABSTRACT, FAITHFUL | `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof` + `Checks.lean` prints |
| Power-of-two index discipline for exact uniformity; definable `NESubset k ≃ Fin (2^k − 1)` | ABSTRACT | GL inverter packaging (HardCore workstream) |
| Literal Def 26.1 and Def 69.4 forms, never unified silently | FAITHFUL, J1–J3 | `WorstCaseOneWay`, `IndistLit`, `toLit`/`toIndist` |
| `advice_length ≤` | FAITHFUL | `NUPPT.advice_length` |
| Literal `[false]` soundness; `∃ ε` before `∀ x P' z`; arbitrary provers | FAITHFUL | `InteractiveProof.sound` |
| Abort-form perfect ZK; non-dyadic permutation finding | FAITHFUL, J2 | `PerfectZKAbort`; `permFromCoins`; `gi_statZK` |
| "Extra coins unread" transport instead of Σ-types | FAITHFUL | `exists_reparam_advice`'s `r.take`; `StatClose.prod` |
| `NUPPTSeq`, `exists_queryTree`, `ofPartial` as optional modules with named admissions | FAITHFUL, J1 | D4, D7, D11 |
| Statistical-switch device for non-dyadic samplers (Q3), shared by Thm 35.1, candidates and ch. 4 | inventory-ch2 F4/C10, J2 | `Asymptotic/Sampling.lean` (D10) |
| Distribution-level `Samplable` | J2 | `Ensemble.Samplable` |
| Closure lemmas preserve `Uniform` | J2, ABSTRACT | `exists_reparam`, `exists_seq`, `ofPolyTimeUniform` |
| Repaired `iterateFind` construction (guarded step, carried input, fresh anchor) | J1–J3 | §2.6 |

## 5. Deviations register (docstring text, one line each)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional module).
3. `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead of a PPT
   computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`).
4. `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable by `ifEq`).
5. `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n` (literal form
   `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the constant case
   by point tests, not formalized; gate 03a, note 14).
6. `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's `m = 2nq(n)` and a
   rejection-sampled position (statistical term absorbed).
7. `OracleEnsemble.Indist`: next-query machines with an explicit universally quantified
   budget; no oracle tapes; forced verdict `false` after `q n` queries.
8. `Protocol`: fixed number of messages `rounds.eval |x|`, verdict on the complete history
   (halting = sending `[]`); `Efficient` time polynomial in the total input length. The honest
   messages are polynomially bounded in `|x|` (`Protocol.ProverBounded`, in
   `InteractiveProof(Err).complete` and the field `EfficientProverProof(Err).boundedP`): the
   source's p.p.t. prover writes at most `t(|x|)` bits. Against a cheating prover the verifier's
   work is polynomial in the message length, not in `|x|` (gate 03e, finding 1; ruling G3-3).
9. Soundness `1 − ε < Pr[out = [false]]` literal; provers have polynomial coin tapes (no loss by
   averaging); completeness `uprob = 1` (every coin pair).
10. `ZK`/`HVZK`: strict PPT simulators; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
    simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`.
11. GI/3COL: statistical ZK (truncated simulators, rejection-sampled permutations / edges /
    colour permutations); one-iteration ZK, `n`-fold protocols get soundness only (sequential
    composition is §7.2.1, out of scope). `PerfectZK` and `PerfectZKAbort` are stated, but no
    source protocol attains them under D8/D10; GI is `StatZK` with negligible δ, and
    `PerfectZKAbort.statZK` turns the abort form into statistical ZK with error `2^{-|x|}`
    (gate 03e, finding 2; ruling G3-4).
12. `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit argument,
    colours padded to `n` bits (DQ4).
13. `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the canonical message.
14. `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible statistical distance of
    uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins).
15. Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n` throughout; `p ≠ q`
    (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT with `2^{-n}` failure.
16. `WorstCaseOneWayLit` (run-3 audit P3-2; reworded at gate 03b, finding 9): when `outLen` is
    constant, so that `|f(x)|` does not determine `n`, the literal form can hold for families
    that are trivially invertible given `1^n` (e.g. the constant family, or `f n b = b ⊕ [n odd]`
    on one bit), an artefact of D5's typed inverse; the `1^n` form `WorstCaseOneWay` is the
    headline, and `toParam` applies whenever `outLen` is non-constant (for `PolyExpr`,
    injective ⇔ non-constant).
17. `TrapdoorCollection.inv_spec` (run-3 audit P3-5): the inverter receives `⟨t, y⟩` without the
    index. The classes coincide (gate 03b, finding 6): a text TDP becomes one of this shape with
    `t' := ⟨i, t⟩` (`Gen'` outputs `⟨i, ⟨i, t⟩⟩`; the trapdoor never reaches the adversary), and
    this shape is a text TDP whose `Inv` ignores `i`. RSA's trapdoor is `⟨N, d⟩` (text: `d`) and
    Rabin's inverter recomputes `N = pq`.
18. `Collection.glPad m henc`, `expCollection H G hV` (run-3 audit P3-1): the encoding-length
    hypothesis resp. the validity bridge are arguments of the definitions; `expGen` outputs the
    fixed valid instance `dlDefaultIndex` below the instance generator's threshold `n₀`. Cost of
    `henc` (gate 03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly
    increasing, so an index generated at two parameters forces `m` constant, and no candidate of
    the library satisfies `henc` as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements,
    `rabinBlumTrapdoor`: `2·max(n, 3)`, `expCollection`: `dlDefaultIndex` below `n₀`); Thm 104.4's
    reading "from trapdoor permutations" (`glPad_hardCore`, `exists_glPad_singleBitSecure`) holds
    for TDPs whose generated indices encode elements in exactly `m(n)` bits. A per-index form
    (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit the candidates; not formalized.
19. Theorem 63.1 (run-3 audit P3-4): `theorem_63_1`, `fUniversal_*` are conditional on an
    encoding scheme with `CanonizerExp c`; no instance proved (`exists_canonizerExp`).
20. `ddhReal`/`ddhRandom` (run-3 audit P8-1): the DDH exponents `a, b, z` are read from
    `n · n`-bit seed blocks by rejection (`ddhExpo`, within `2^{-n}` of uniform, D10) — product
    seeds, never a dependent sum (uniform-on-`Σ` tilts the instance law by the fibre sizes).
21. `ExpGroupGen.FullLengthExcept δ` (run-3 audit P8-2): full-length primes except on a set of
    the generator's coins of probability `δ n`; `fullDLCollection_hardCore` and `elGamal_secure`
    take `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` (full length on every coin string is not
    known to be achievable in polynomial time).
22. `uprob_adaptive_guess`, `uprob_gni_rep_cheat` (run-3 audit P10-1/P10-2): the auxiliary coin
    type (`W`, `ρ`) is assumed nonempty — `uprob` on an empty type is `0`, so the exact `2^{-m}`
    fails for `Empty`; every consumer passes a tape type `Fin k → Bool`.
23. Thms 35.1, 35.2 and Claim 38.2 (gate 03b, finding 8): the direct products are families at
    parameter `n` whose adversaries receive `1^n` (the text: `1^{n·m(n)}`, `1^{2n}`;
    interderivable, so negligibility in `n` and in `n·m(n)` coincide); Claim 38.2 runs
    `T(n) + 1 = 2n·m(n)·n^c + 1` rounds with Garg's threshold `μ₀/(2m)` (the text: `2nm²p(n)`
    rounds, threshold `1/(2m²p(n))`), with the margin `(T + 1)·2^{-n}` for the rejection-sampled
    positions.
24. `Collection.encD_decD` (gate 03b, finding 1; ruling G3-1): decoders are canonical — a string
    decodes only if it is the encoding of its value — so the outputs of the sampler and of the
    trapdoor inverter are encodings ([PS10, Defs 41.1 (2), 56.1 (6)]: "an element of `D_i`",
    "computes `f_i^{-1}(y)`"); every decoder of the library is canonical.
25. `PRG.expands` (gate 03c, finding 1; ruling G3-2): expansion at every seed length, `n = 0`
    included (Def 77.1 (2)'s `|G(x)| > |x|` read literally at `x = ε`). A `PolyExpr` stretch has
    coefficients in ℕ, so stretches with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) are not
    `PRG`s, although the text uses them (the length-doubling `G` of Alg 92.1 and Thm 97.3; Lem 80.5's
    "for any polynomial `ℓ`"); `PRG.expand`/`prg_expand` take the same `hℓ : ∀ n, n < ℓ(n)`. Thm 97.3
    uses the separate predicate `DoublingPRG`, produced from any secure `PRG` by `PRG.doubling`
    (`PRG.Secure.doubling`, `Asymptotic/PRF.lean`); elsewhere `2n + 1`, `n^c + 1` are reached by
    `prg_expand` from the one-bit truncation `PRG.truncate`, and shorter outputs by truncation
    (`PRG.Secure.truncateTo_easy`/`_negligible`). Alg 92.1 needs only `n ≤ ℓ(n)`. "PRGs exist" has the
    same meaning under every reading (truncate to `n + 1` bits, change below `n₀`), and no statement
    of ch. 2–8 is vacuous by it.

---

## 6. Workstreams, ownership, coverage, build order

Every **core** item of the three inventories appears exactly once (68 + 82 + 69 = 219 ids).
Optional/deferred items are listed in §6.2 for information. Paths are relative to the
worktree. New files not in the plan's layout are marked (new).

| WS | Name | Owned files | Inventory ids covered | Depends on |
| --- | --- | --- | --- | --- |
| M1 | machine-core | `TCSlib/Complexity/Randomized/PolyExpr.lean` (new), `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Complexity/Randomized/NonUniform.lean`, `TCSlib/Complexity/Randomized.lean` (facade), `TCSlib/Cryptography/Asymptotic/Adversary.lean` (new) | Def-23.4, Def-23.5, Def-24.6, Def-26.8 | — |
| M2 | machine-primitives-closure | `TCSlib/Complexity/Randomized/Primitives.lean` (new), `TCSlib/Complexity/Randomized/Closure.lean` | Claim-26.3 | M1 |
| M3 | machine-repetition | `TCSlib/Complexity/Randomized/Repetition.lean` | Inf-4.3 | M1, M2 |
| S | sampling | `TCSlib/Cryptography/Asymptotic/Sampling.lean` (new) | (concrete lemmas C4, C5, C10 of inventory-ch2 §4; DQ1-A) | M1 |
| C2a | onewayfunctions | `TCSlib/Cryptography/Asymptotic/OneWay.lean` | Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2 | M1, M2, M3, S |
| C2b | collections | `TCSlib/Cryptography/Asymptotic/Collections.lean` | Def-41.1, Thm-42.2, Def-55.1, Def-56.1, Def-78.3.coll | C2a, S |
| C2c | universal-owf | `TCSlib/Cryptography/Asymptotic/Universal.lean` | Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 | C2a, M2, M3 |
| NT | number-theory | `TCSlib/Cryptography/NumberTheory.lean` (facade), `TCSlib/Cryptography/NumberTheory/Chebyshev.lean`, `…/Euclid.lean`, `…/ModExp.lean`, `…/Units.lean`, `…/Primality.lean`, `…/QuadraticResidues.lean` | Def-29.3, Thm-31.3, Claim-33.1, Alg-43.2, Claim-43.3, Claim-44.5, Alg-45.5, Claim-47.2, Cor-48.12, Thm-54.3, Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a, Alg-50.16, Lem-51.17, Def-57.0, Lem-57.1, Thm-58.2, Def-59.3, Thm-59.4, Thm-60.5, Cor-60.6, Claim-60.7, Claim-62.1, Claim-63.1 | S (Lem-51.17 closeness), M3 (Lem-51.17(iii) only) |
| Cand1 | candidates-factoring | `TCSlib/Cryptography/Candidates.lean` (facade), `TCSlib/Cryptography/Candidates/Arithmetic.lean` (new), `…/Concrete.lean` (new), `…/Factoring.lean` | Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Claim-36.2, Alg-37.4, Thm-51.1 | C2a, C2b, NT, S |
| Cand2 | candidates-rsa-rabin | `TCSlib/Cryptography/Candidates/RSA.lean`, `…/Rabin.lean` | Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Claim-62.2, Thm-63.10 | Cand1, NT, C2b |
| Cand3 | candidates-dl-elgamal | `TCSlib/Cryptography/Candidates/DiscreteLog.lean`, `…/DiscreteLogHardcore.lean` (new), `…/ElGamal.lean` (new) | Asm-52.2, Thm-52.3, Lem-84.1, Lem-84.1.0, Lem-84.1.1, Alg-84.2, Alg-85.a, Lem-84.1.3, Lem-84.1.4, Lem-84.1.5, Asm-105.1, NT-105.a, Alg-106.2, Claim-107.a, Thm-107.3 | C2b, NT, C3a, C3f, M3 |
| C3a | ensembles | `TCSlib/Cryptography/Asymptotic.lean` (facade), `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def-69.3, Def-69.4, Lem-71.5, Lem-71.6, Claim-73.a, Lem-73.8, Claim-73.b, Ineq-189.a | M1, M2, M3, S |
| C3b | pseudorandom-nextbit | `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean`, `TCSlib/Cryptography/Asymptotic/NextBit.lean` (new) | Def-74.1, Def-75.2, Rem-75.3, Thm-75.4, Thm-75.4.c, Thm-75.4.1, Thm-75.4.2, Alg-76.5, Def-77.1 | C3a |
| C3c | hardcore | `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def-78.3, Thm-79.4, Lem-80.5, Cor-81.7, Thm-87.3, Thm-87.3.a, Thm-87.3.b, Thm-87.3.c, Thm-87.3.1, Thm-87.3.2, Thm-87.3.3, Fact-88.4, Alg-88.5, Alg-89.6, Thm-87.3.6, Thm-87.3.7, Thm-87.3.8, Thm-87.3.9, Thm-87.3.coll | C3b, C2a, C2b, M3 |
| C3d | encryption | `TCSlib/Cryptography/Asymptotic/Encryption.lean`, `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean` | Def-24.7, Def-91.1, Alg-92.1, Claim-92.a, Thm-92.2, Def-93.1, Thm-94.2, Def-111.1, Thm-112.2, Thm-112.2.i, Thm-112.2.ii | C3b, M2 |
| C3e | prf-multimessage | `TCSlib/Cryptography/Asymptotic/PRF.lean`, `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (new) | Def-95.a, Claim-95.b, Def-96.1, Claim-96.b, Def-96.2, Cor-97.a, Constr-97.b, Claim-97.c, Thm-97.3, Thm-97.3.1, Thm-97.3.2, Thm-97.3.3, Alg-99.1, Thm-99.2, Thm-99.2.1, Thm-99.2.2, Thm-99.2.3 | C3c, C3d, M3 |
| C3f | publickey | `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def-102.1, Def-102.2, Def-103.c, Thm-103.d, Def-103.e, Thm-103.f, Alg-104.3, Lem-104.a, Thm-104.4 | C2b, C3c, C3a |
| C4a | zk-model | `TCSlib/Cryptography/ZeroKnowledge.lean` (facade), `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean`, `…/InteractiveProofs.lean`, `…/Defs.lean`, `…/Encoding.lean` (new) | Def-114.a, Def-114.b, Def-115.a, Def-115.b, Def-115.c, Def-115.d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-119.5, Def-121.1, Def-121.2, Def-122.a, Def-191.11, Inf-4.1, Inf-4.2, Inf-4.4 | M1, M2, S |
| C4b | zk-graph-isomorphism | `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean`, `…/GraphIsomorphismZK.lean` | Def-117.e, Def-118.a, Prot-118.3, Lem-119.a, Lem-119.b, Lem-119.c, Lem-119.d, Prop-118.4, Prot-120.6, Lem-120.a, Lem-120.b, Lem-120.c, Lem-120.d, Prop-120.7, Thm-122.3, Thm-122.3.hv, Thm-122.3.trunc, Alg-123.4, Lem-123.5, Claim-123.b, Claim-123.d | C4a, M3, S |
| C4c | zk-commitment | `TCSlib/Cryptography/ZeroKnowledge/Commitment.lean` | Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d | C4a, C3c, C3a |
| C4d | zk-3col-np | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean` (split into `ThreeColoring/Protocol.lean` and `ThreeColoring/Simulator.lean` if > 600 lines), `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d, Thm-124.1, Def-124.a, Claim-124.d | C4c, C4a, M3, S |
| A | audit-integration | `audits/pass-shelat/Checks.lean` (append only), facade registration in `TCSlib.lean`/`TCSlib/ComputationalModels.lean` (integrator) | — (sanity prints: `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof`, and every headline theorem) | all |

### 6.1 Build order (run 2 statement phase)

1. **M1** (serial; everything imports it) — then **M2 and M3 statements** (serial; their fills
   are the machine agent's run-4 work and may lag).
2. **S** (small; concrete) in parallel with the statement skeletons of **C2a, C3a, C4a, NT**.
3. **C2b, C3b, C4b, Cand1, C2c**.
4. **C3c, C3d, C4c, Cand2**.
5. **C3e, C3f, Cand3, C4d**.
6. **A** after each workstream lands (append its `#print axioms` lines) and at closure.

Fill-phase critical path: `pairSplitAt` → `unaryMul` → `Closure.lean` → `iterateFind`
→ {Thm 35.1, `Indist.copies`, GL, GGM, GI/3COL simulators} in parallel.

### 6.2 Optional / deferred items (not counted; for information)

Ch. 2: Def-21.x, Rem-22.1, Def-27.2, Rem-28.1, Claim-32.4, Claim-44.4, Thm-45.6, Def-46.x,
Thm-46.8, Claim-47.1, Thm-47.10, Cor-48.11, Ex-*, Def-52.1, Rem-52.2, Claim-53.1, Claim-53.2,
Claim-58.1, Thm-58.3, Claim-59.1, App-A.*, Thm-189.9, Def-191.10, Def-191.11 (ch. 2 copy);
deferred: Rem-24.2, Rem-26.2 (optional module `Randomized/Sequence.lean`), Rem-27.1, Rem-29.2,
Rem-33.2 (hypothesis in `Candidates/Arithmetic.lean`), Rem-43.6, Rem-48.2, Lem-50.15b,
Rem-49.3, Rem-50.2, Ex-58.3, Thm-188.7, Lem-189.8, Def-192.12.
Ch. 3: optional Claim-67.a, Rem-72.7, Claim-72.a, Ex-72.b, Thm-75.4.conv, Constr-77.a,
Claim-78.a, Claim-78.b, Claim-79.a, Claim-96.a, Claim-96.c, Claim-103.a, Claim-103.b,
Constr-104.a, Claim-106.a, Claim-106.b, Def-107.b, Claim-107.c, Thm-188.7, Lem-189.8;
deferred Claim-78.c, Constr-82.a/b, Constr-83.a/b, Claim-83.c, Claim-107.d.
Ch. 4: optional Def-111.a, Def-111.b, Claim-112.a, Claim-112.b, Def-117.b, Claim-117.c,
Claim-118.b, Def-119.e, Claim-122.b, Def-191.10, Def-192.12; deferred Claim-117.d,
Claim-118.c, Claim-119.f, Def-121.a, Claim-122.c, Claim-123.a, Claim-123.c, Claim-124.b,
Claim-124.c, Claim-124.e.

---

## 7. Consolidated errors and gaps in the source text

Outright errors (to replace the plan's seeded list):

**Chapter 2.**
1. Algorithm 64.2 / Theorem 63.1: `f_universal(⟨M, x⟩) = M(x)` omits the machine description
   from the output; the proof is invalid. Corrected definition outputs `⟨M, M(x)⟩`.
2. §2.6.5, `L_N`: "`N = u2^j`" should be `N − 1 = u·2^j`; the condition stated with `i = j`
   only is vacuous; intended `∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. Claim 32.4 is false as a strict inequality (`x = 1, p = 2`); correct form
   `p^{ν_p(C(2x,x))} ≤ 2x` (`Nat.pow_factorization_choose_le`).
4. §2.6.6 (p. 50): prime probability "exceeds `1/n`"; Theorem 31.3 gives `1/(2n)`.
5. Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6 need `p ≠ q` odd primes (`Π_n` contains
   2 and allows `p = q`); `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`.
6. Theorem 61.8 (⇐) needs square roots modulo arbitrary primes; only `p ≡ 3 (mod 4)` is proved
   (Theorem 58.2); Theorem 63.10's `Gen` needs the density of primes `≡ 3 (mod 4)` (not in
   Mathlib; explicit hypothesis).
7. Theorem 59.4: "`zinQRq`" typo; the `⇒`/`⇐` labels of the proof are swapped.
8. Theorem 52.3: `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; Assumption 52.2 gives `A`
   only `g^x` (needs `q, g`); `G_q` unspecified.
9. Theorem 53.2's proof samples `e ← Z_N^*` (should be `Z*_{Φ(N)}`).
10. Definition 56.1(5): `≤ e(k)` should be `e(n)`.
11. Definition 41.1(4): "p.p.t. `A`" contradicts the nuPPT convention; `f(A(1^n, i, y)) = y`
    should read `f_i`; `R_i` unconstrained; `D_i` must be finite.
12. Theorem 42.2 proof idea: "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n`.
13. §2.4.3 proof: "for each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra
    factor `m` is garbled.
14. Algorithm 33.6 line 7: `A(1^n, z′)` should be `A(1^{2n}, z′)`; Algorithm 37.4 must output a
    verified factor.
15. Lemma 189.8 garbled ("`1 − 2??`"), proof unfinished; Theorem 188.7's threshold `ε` should be `εn`.
16. §2.3 attack `A(z) = (2, z/2)` returns a preimage of a different input length.
17. Claim 43.3 case 2: "`b > 2^n`" should be `b ≥ 2^n`; the precondition allows `b = 0`.
18. p. 61 example `N = 77`: numbers garbled.
19. Theorem 63.1 proof: "hardness amplification from §2.3" should be §2.4; budget `|y|^3`
    becomes `(|y|+1)^3`.
20. Theorem 49.14: "with probability `1 − 2^{−t}`" should be "at least". (Lemma 50.15's "`N > 2`
    composite" is right as stated: for even `N > 2` the liars also form a proper subgroup, since
    `(−1)^{N−1} = −1`; the formal lemma restricts to odd `N` only for convenience. Corrected on gate
    03f2, F01.)
21. p. 27: "NP ⊄ BPP ⟺ worst-case OWFs exist" mixes uniform BPP with non-uniform inverters.
22. Theorem 45.6 / p. 46: the remark that Euler's theorem "removes the restriction `x < N`"
    refers to a restriction Algorithm 45.5 does not have.
23. Theorem 31.3 proof: "each term is greater than 2" — the term `(x+x)/x` equals 2.
24. Theorems 61.8 / 55.2 mix `n` and `k`; Theorem 61.7 writes `Z_n^*`; Theorem 51.1's `D_i`
    uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.
25. Theorem 35.1's `m = 2nq(n)` is kept, but the uniform position of Algorithm 38.5 is not
    exactly samplable by a bit-coin PPT unless `m` is a power of two (D10).

**Chapter 3.**
26. Theorem 87.3 says `⟨x, r⟩` is hard-core "for `f`"; it is for `g(x, r) = (f(x), r)`.
27. Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma and
    Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`; "`ε = s(n)`"
    should be `1/s(n)`; the range reduction "as we will show later" is never shown; the
    good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
    `Pr[noinc | low]` by `1/2 − ε/2`, the complementary event of its own increment rule (`lo`
    counts disagreements `b_i ≠ half(r_i)`). (Run-3 audit P8-3: line 11's root selection is
    consistent with `half`'s convention, and the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant, not needed by the halving invariant.)
28. Theorem 107.3 / Algorithm 106.2: El Gamal with `m ∈ Z_p^*` is insecure under DDH on `G_q`
    (Legendre symbol of `c_2`); correct with message space `G_q`; `Gen` draws `g ∈ Z_p` (may be
    `0, ±1`); the square-vs-generator sampling term `1/q` is missing.
29. Definition 75.2 quantifies `i ∈ [0, ℓ(n)]` (bit `t_{ℓ(n)+1}` does not exist).
30. Definition 78.3 mixes `k` and `n`.
31. Definition 96.1: `{O'_n} ≈ {O'_n}` typo.
32. Theorem 104.4 omits the hard-core bit from its hypothesis; its proof writes `D` for `A`.
33. Algorithm 76.5 draws `U_{ℓ(n)−1}` (should be `U_{ℓ(n)−i}`); Theorem 75.4's proof defines
    `H̃^i` with a stray `u_{l(m)}`, mixes 0/1-indexing, and its last display has `A(t) = 1` for
    `A(t) = b`.
34. Lemma 80.5's proof: `m(n)`/`ℓ(n)` interchanged; hybrids must start at `i = 0`; `M(y)` reads
    bit-then-seed against the construction's seed-then-bit.
35. Theorem 99.2's collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`.
36. Theorem 92.2's proof: hybrid `H²` mislabelled ("`m_1`"); gap `1/(3p(n))`, not `1/(4p(n))`.
37. Theorem 87.3's final constant: text `ε^3/(32n)` (with `ε' = ε/2`) versus the concrete
    layer's stronger `ε^3/(16n)` (the plan's seeded `ε^3/(4n)` note compares `ε'` with `ε`).
38. Lemma 71.6: the proof gives `ε/(m−1)`, the statement `ε/m` (harmless); Corollary 81.7 lists
    `ℓ(n)+1` bits.

**Chapter 4.**
39. Proposition 120.7 says "for `L_niso`"; it is for `L_iso`; its proof reverses the maps
    (`π(H) = G1`, `σ(π(H))`) and renames the graphs.
40. Definition 126.3, binding: omits `v₀ ≠ v₁`; as printed unsatisfiable.
41. Proposition 127.6's proof: "repeated `|E|^2` times" vs the protocol's `n|E|`.
42. Protocol 127.5: witness listed as `c_0 … c_m` (should be `c_1 … c_n`); Simulator 128.7:
    "`k ∈ [m] \ {i', j'}`" should be `[n]`.
43. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`" without checking the openings — unsound;
    undefined for `E = ∅`; `Com` on 2-bit colours has security parameter 2 (pad to `n`).
44. Theorem 122.3 claims perfect ZK for the `n`-iteration protocol; the proof covers one
    iteration and relies on §7.2.1; with bit-coin parties perfect completeness and perfect ZK
    cannot both be literal (`n!` is not dyadic); same for Protocol 118.3's `σ` and 127.5's
    colour permutation.
45. Definitions 121.1/121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined
    (`n = |x|`); Definition 121.2 relies on expected polynomial time.
46. Proposition 128.8's proof: hybrid count `2n|E|` vs `n|E|` attempts; "`S̃_{e+1}` … `S̃_{e+1}`"
    typo; the `6|E|` sub-hybrid is unnecessary.
47. §4.7 step 2: "Cook's reduction applied to the witness" needs a Levin reduction (never
    defined); "execute `(P, V)` on `x'`" should be `(P', V')`; Theorem 126.4 needs a hard-core
    predicate (Theorem 87.3) and uses a single OWP, not Definition 55.1's collection.
48. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
49. Proposition 118.4's proof uses `G1, G2` for `G0, G1`; "the prover runs in exponential time"
    is only an upper bound; the adaptive-prover argument is hidden.
50. §4.4: a round ends when the active machine *halts* ("the protocol ends"), which makes the
    literal `Pr[out_V = 0]` of Definition 116.1 unsatisfiable against a prover that halts at
    once; time complexity `t(|x|)` "regardless of messages" leaves the simulator's call to `V*`
    on long `z` ill-defined (D8 reading).
51. Definition 121.2 read literally (`∀ z ∈ {0,1}*`, the distinguisher polynomial-time in its
    input) fails for every protocol whose hiding is only computational: with `|z| ≥ 2^n` the
    distinguisher, whose input (the view) contains `z`, may run in time `2^n`, invert the OWP on
    `n`-bit inputs and open the unopened commitments. So the bound `∀ Lz : PolyExpr` on `|z|`, and
    indexing the distinguisher's advice by `|x|` rather than by its input length, are necessary,
    not only convenient (gate 03e, finding 9; `ZeroKnowledge/Defs.lean`'s module docstring).

Gaps the formalization fills (not errors): Theorem 42.2 (⇒) and Theorem 57.2 ("exercises");
the PKE single ⇒ multi-message theorem and the bitwise theorem (p. 103); Theorem 107.3
("exercise") with the `1/q` term; Lemma 84.1's range reduction and averaging; the square-root
algorithm for `p ≡ 1 (mod 4)` (restricted to `3 (mod 4)` instead); Miller–Rabin's composite
case (proved: `two_mul_card_mrLiars_le`, `uprob_millerRabin_le`); Chernoff (replaced by Chebyshev for pairwise independence); Theorem 112.2's
message sampler (`0^n`); Theorem 124.1's string-level Levin reduction to 3COL (hypothesis).

---

## 8. Open questions for the maintainer (everything else is decided above)

1. **Conditional candidates.** Every number-theoretic candidate theorem (Thms 33.5, 36.3, 51.1,
   52.3, 53.2, 55.2, 57.2, 61.7, 61.8, 63.10, 107.3, Lem 84.1) is stated with the hypothesis
   bundle `Candidates/Arithmetic.lean` (polynomial-time machines for binary `mul`, `add`,
   `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality — the three fields
   `add`, `sub`, `size` added by the run-3 audit repair P7-1, since the generators and
   reductions of §2.9–§2.12 decrement, add, subtract modulo `N` and read bit lengths) because
   the library has no binary-arithmetic
   machines (inventory F1/F6). `#print axioms` stays clean but the theorems are conditional.
   Confirm this is acceptable as the campaign's headline form, or fund the arithmetic machines
   (research-level, ≥ 5k lines).
2. **Theorem 124.1 ("ZK for NP").** Core form (A): every `(L, R_L)` with a Levin reduction to
   3COL, the reduction being an explicit hypothesis; the "every `L ∈ NP`" form needs a
   string-level Levin reduction `SAT3 → 3COL` (the repository's is graph-level with a private
   witness map). Confirm form (A) as the headline or fund the string reduction.
3. **Rabin/RSA scope.** Rabin results restricted to Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`)
   with the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Theorem 63.10's `Gen`
   clause; RSA and factoring assumptions restricted to `p ≠ q`. Lemma 84.1's asymptotic form
   restricts `Gen_DL` to `p ≡ 3 (mod 4)` (square roots). Confirm these restrictions.
4. **Lemma 84.1 deliverable.** The concrete statement (Classical roots, `p ≡ 3 (mod 4)`) is
   core; is the asymptotic wrapper (the hardest ch. 3 fill) mandatory for closure, or may it
   remain sorried under its sketch if the fill stalls?
5. **Optional literal modules.** `NUPPTSeq` (Def 26.8 verbatim), `exists_queryTree`
   (`OracleTM` bridge) and `NUPPT.ofPartial` are specified as optional modules with one named
   admission each; confirm they are out of the mandatory core (they are not needed by any
   chapter 2–4 theorem). **Ruled** (decision log 2026-10-27): outside the mandatory core.
   The one admission in this area is the optional bridge
   `NUPPT.decides_of_decidesWithAdviceInTime` (decision log 2026-10-28; see D11).
6. **Encoding scheme for Theorem 63.1 (run-3 audit P3-4).** `theorem_63_1` and `fUniversal_*`
   are stated for schemes with an at most exponential canonizer (`CanonizerExp c`); the only
   scheme in the library (`Turing.exists_effectiveMachineCode`) has no bound on its canonizer,
   so the headlines are conditional. Ratified as an explicit hypothesis like `ArithmeticFP`
   (D11); the open problem `exists_canonizerExp` (a `Build/`-style parser-and-reserializer
   canonizer) is stated and sorried. Confirm, or fund the canonizer construction.

---

## 9. Appendix — the 53 statement stubs of the compiled scratch (owner workstream)

M1: `polyTimeComputable_unaryPoly` (needs M2's `unaryMul`), `NUPPT.decides_of_decidesWithAdviceInTime` (optional).
M2: `computesFunInTime_pairSplitAt`, `computesFunInTime_unaryMul`, `polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly`, `NUPPT.exists_comp`, `exists_reparam`, `exists_reparam_advice`,
`exists_withAdvice`, `exists_split`, `exists_seq`.
M3: `polyTimeComputable_iterateFind`, `iterate`, `iterateEmit`, `majority`, `pairXor`, `pairEq`, `blockMap`.
S: `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`, `rejectionSample_uniform_of_some`,
`uprob_rejectionSample_none`, `statClose_rejectionSample`, `permFromCoins_uniform_of_some`,
`uprob_permFromCoins_none_le` (the last two may move to C4a/Encoding).
C2a: `weak_to_strong`, `strong_prod_two`, `StrongOneWay.weak`, `not_strongOneWay_id`.
C2b: `Collection.OneWay.exists_strongOneWay`.
C3a: `Indist.toLit`, `IndistLit.toIndist`, `Indist.refl`, `Indist.symm`, `Indist.push`, `Indist.trans`,
`Indist.copies`, `predict_eq`, `prediction_lemma`.
C3b: `NextBitUnpredictable.pseudorandom`.
C3d: `singleMessageSecure_iff_zeroKnowledge`.
C3e: `toOracleAdversary_boundedBy`, `OracleEnsemble.Indist.refl`.
C4a: `StatZK.zk`, `StatZK.hvzk`, `npProtocol_interactiveProof`.
C4b: `Riso_witnessRelation`, `gi_sim_H_dist`, `gi_sim_half`, `gi_efficientProverProofErr`, `gi_statZK`.

Compile command and outcome: `lake env lean briefs/pass-shelat/DESIGN-freeze-scratch.lean`
→ exit 0, 0 errors, 53 sorry warnings (2026-10-27).

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | The `j`-th block of `c` bits of a coin string, `(r.drop (j * c)).take c`, stated three times: `coinSlice` (`ZeroKnowledge/GraphIsomorphism.lean`, ch. 2–4), `Authentication.coinBlock` (`Authentication/Lamport.lean`, prong A), `Protocol.phaseSlice` (`Composability/SequentialZK.lean`, prong C) | found by the Lamport worker and the maintainer | Before the ch. 5–8 statement gate: one copy in a shared upstream module, with its length lemma, used by all three. |
| DL-7 | `List.ofFn (padFin ℓ w) = w` for `|w| = ℓ`: `Authentication.ofFn_padFin_of_length` (`Lamport.lean`) is the equal-length case of ch. 2–4's `ofFn_padFin_of_le` (`Asymptotic/Collections.lean`); `Composability.length_eval_of_length` (`CCA2Scheme.lean`) repeats the step inline | found by the Lamport worker | Before the ch. 5–8 statement gate: use `ofFn_padFin_of_le (le_of_eq h)`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/review/gate03a-review.md =====

# Gate 03a: review of the external auditor's findings

## Summary

- **Verdicts on the 26 items:** 23 true, 3 partly true (#2, #20, #22), 0 false. Two true items are understated: #4 and #8 are wider than the auditor saw, and #12 is too (see "Missed").
- **Severity changes:** four.
  - #4 (private state-loop host) goes from minor to **major**.
  - #8 (duplication) goes from minor to **major**. Policy §1 makes accumulated duplication a major until the user ledgers it, and the copies rooted in 03a's `private` helpers number about twenty: `ptc_comp` ×6, the `blocks` bijection ×6 plus one inverse, `stateFind` ×4, and `abs_uexp_sub_le`, `negligible_zero` and `forall_of_uprob_eq_one` ×2 each.
  - #2 goes from minor to note: the cited source assumes samplability, and the lemma has no consumer.
  - #6 goes from minor to note: the cost is benign and the lemma has no consumer.
  - New tally: **0 blockers, 2 majors, 9 minors, 15 notes.**
- **Closing the gate.** The pack does not close as filed. It closes once #4 and #8 are fixed, or once the user ledgers them (ruling R2). Every other fix is a docstring edit, an import or header edit, or additive API.
- **Fixes that need a ruling:** three.
  - **R1:** the unapproved `@[simp]` attributes. One cross-pack ruling would also settle 03b #12a, 03c #11 and 03e #17.
  - **R2:** the duplication ledger, and when the cleanup happens.
  - **R3:** where `negligible_zero` lives. DESIGN D2 freezes the Garg files.
- **Downstream check for #1: clean.** The auditor asked for this check. No ch. 5–8 file uses `NUPPT.Computes` (0 hits in the five worktrees). In ch. 2–4 it appears only in an `iff` (`computes_iff_uprob`) and in two statements that also assume `Uniform`.
- **Ripple:**
  - **Statements.** No recommended fix changes the meaning of any statement, in ch. 2–4 or ch. 5–8.
  - **Ch. 5–8.** No statement uses an affected declaration: `Ensemble`, `Indist`, `Samplable`, `StatClose` and `Computes` all have 0 uses. The only ch. 5–8 text to touch is two proof sketches in `wt-s2b/.../Games/Efficiency.lean` that cite `GGMRed.stateLoopFun`, which R2-A would re-point. If R1 went the other way (drop the attributes), 62 non-`only` `simp` calls in ch. 5–8 would need a replay.
- **Dispatch:**
  - **Now:** 03f1, 03f2 and 03l are unaffected. 03g can go now with a one-line erratum.
  - **Wait, under R2-A:** 03h, 03i and 03k. Their public statements name copies that the dedup PR deletes or renames.
  - **Under R2-B:** 03h, 03i and 03k go now, with an erratum.
  - **Still held by F-1, as before:** 03d and 03j. Neither depends on 03a's fixes for its meaning.

## What was checked

- **The code.** Worktree `wt-g03` at `a3c5fa8b72e50939822f22364647dc844a3914a0`, clean. I read all eleven files of the pack in full, and parts of `EnsemblesLemmas`, `GGMReduction`, `Repetition`'s neighbours, the copies named below, and the `03b`, `03c` and `03e` findings.
- **The source.** The pdftotext extracts in `blueprint/src/references/pass-shelat-2010-{ch2,ch3,appendix}.raw.md`, plus book p. 181 from `scratchpad/srctext/p178.txt`. The PDF itself is in the repository root (`Pass–Shelat.pdf`). So the auditor's (src) rows are now checked: see #6 and #25.
- **The records.** `DESIGN.md`, the plan's decision log (`PassShelatChapter2-4Plan.md`, lines 362–374; the bundle did not carry it), `policy.md`, `duplication-ledger.md`, `run3-audit-summary.md` and the evidence under `evidence/a/`.
- **Ch. 5–8.** Five worktrees, all clean: `wt-s2b` `afe5982f`, `wt-prong-a` `2d7b5441`, `wt-prong-b` `1cf007d1`, `wt-prong-c` `aa71d0e7`, `wt-prong-d` `6ea900ae`. I grepped the five ch. 5–8 directories.
- **The ripple script.** `gate03-review/scripts/ripple03a.py` greps each pending pack's file list (`gate03/packs.json`) for the affected identifiers.
- **No Lean was run.**

Line numbers are at `a3c5fa8b`. Paths are under `TCSlib/` unless written out.

## Findings

Types of fix used below:
- **D**: docstring or design record only.
- **S**: statement change.
- **A**: new API (additive).
- **P**: proof-level or refactor; no statement changes meaning.

### #1 (minor, agree): `NUPPT.Computes` presented as Def 24.6 without `Uniform`

- **Verdict: true.**
  - `Complexity/Randomized/PPT.lean:224–229` says "`A` computes `f` with probability one [PS10, Definition 24.6]". The module docstring (:36–39) and DESIGN D3 say the same. Nothing in the definition requires `A.Uniform`.
  - The source's notion is for "a randomized algorithm", which Def 23.4 defines as a PPT, a uniform Turing machine (ch2 raw :129–132, :95–99).
  - The auditor's machine checks out: `ofPolyTime polyTimeComputable_inAdvice (.const 0) (.const 1) (fun n => [h n]) _` has `runAt n y r = [h n] = f ⟨1^n, y⟩`, for an arbitrary `h`.
  - The file's own converse needs uniformity: `Closure.lean:381`, `Computes.polyTimeComputable (hA : A.Uniform)`.
- **Downstream check (the auditor's point (c)): clean.**
  - Ch. 5–8: 0 uses of `Computes` in the five directories.
  - Ch. 2–4 statements: `Adversary.lean:208` (`computes_iff_uprob`, an equivalence with no efficiency claim), `Closure.lean:381` and `PPT.lean:314`. The last two both assume `Uniform`.
  - Prose: `OneWay.lean:103`, `Pseudorandom.lean:39,126` and `PRF.lean:328` say "equivalent by `Computes` + `ofPolyTimeUniform`". That is the uniform direction, so it is correct.
- **Fix (D).** Add one sentence to `Computes`, to the module docstring and to DESIGN D3: "[PS10, Def 24.6] proper is the case `A.Uniform`. For a non-uniform `A`, `Computes` is the advice analogue and holds for uncomputable `f` (advice `[h n]`)." The auditor's option (b), a `PPT.Computes` wrapper, has no consumer, so skip it.
- **Ripple:** none. `Computes` is on the S1 interface list, so tell Seyoon about the docstring change; nothing needs re-sync.
- **Ruling:** no.

### #2 (minor → note): `Indist.copies` requires `Samplable X`, `Samplable Y`

- **Verdict: partly true.**
- **True:**
  - Against non-uniform distinguishers the hypotheses are unnecessary. Use the advice hybrid: fix `k` and the other `t − 1` coordinates `w*` that keep the gap, and hard-wire them with `exists_withAdvice`.
  - An `Ensemble` with `σ n = Fin 3` is never `Samplable`. *[Erratum, gate 03a round 2, R2-3: wrong as stated; a constant map from `Fin 3` is a samplable point mass. The obstruction is a law with a non-dyadic atom, e.g. three seeds mapped to distinct strings.]* `Samplable` (`Ensembles.lean:149–152`) demands an exact law over `2^{s(n)}` seeds, so the law is dyadic.
- **Not true:** "stronger than the uses can meet".
  - There are no uses: 0 in ch. 2–4 statements and 0 in ch. 5–8. The one intended use, PRG outputs, gets `Samplable` from `Easy.samplable` (`Pseudorandom.lean:60,167,169`).
  - The hypothesis is faithful to the cited source. [Gar26, Lemma 3.3]'s reduction samples the other copies; `Pseudorandom/Indistinguishability.lean:193–197` says "this is where efficient samplability of X and Y is used".
  - It is also the frozen design: D6, "`Indist.copies` takes `Samplable X`, `Samplable Y`".
- **Severity:** note. No statement builds on it, and nothing in it misleads.
- **Fix (D).** Add to the docstring at `Ensembles.lean:437–440`: "The samplability hypotheses are [Gar26, Lemma 3.3]'s uniform reduction (D6). Against non-uniform distinguishers they can be dropped by hard-wiring the hybrid index and the other copies. That form is not proved, since no consumer needs copies of a non-samplable ensemble." A samplability-free `Indist.copies'` (A, with its reduction in `EnsemblesLemmas`, 03i) can go to the backlog.
- **Ripple:** none.
- **Ruling:** no. D6 stays as frozen.

### #3 (minor, agree): `exists_comp` is blind to `n`

- **Verdict: true.** In `Closure.lean:200–203`, `pre` sees only `y` and `post` sees only `A`'s output.
- **One correction.** `EnsembleLemmas.exists_pushRed` is public in `EnsemblesLemmas.lean` (03i's scope), not private, as the auditor's own note 22 says.
- **Evidence that the gap costs work.** Ch. 5–8 build their n-aware reductions from the raw layout: `NUPPT.inParam` occurs 55 times and `NUPPT.inArg` 57 times across 7 files in prongs A, B and C.
- **Fix (A).** Add to `Closure.lean`:
  ```lean
  theorem NUPPT.exists_compParam (A : NUPPT) {pre post : List Bool → List Bool}
      (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
      ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
        ∀ n y r, B.runAtL n y r =
          post (pairEncode (List.replicate n true) (A.runAtL n (pre (advInput n y)) r))
  ```
  - The raw function is `z ↦ post ⟨inParam z, A.output (layout (inParam z) (pre ⟨inParam z, inArg z⟩) (inAdvice z) (inCoins z))⟩`.
  - The proof is the same as `exists_comp`'s.
  - `exists_comp` becomes the special case.
- **Ripple:**
  - Additive.
  - Optionally, `EnsembleLemmas.exists_pushRed` (03i) could be re-derived from it.
  - Ch. 5–8: none. `ObliviousTransfer.lean:392`'s sketch cites `exists_comp` and keeps working. The closure calculus is on the S1 list, so announce the addition.
- **Ruling:** no.

### #4 (minor → major): the state-loop host is private

- **Verdict: true, and understated.**
  - `Repetition.lean:264` has `private theorem polyTimeComputable_stateFind`. It is a host in the sense of policy §1, "Hosts come first", which is binding (user, 2026-10-12): "A host is never built `private` … A private host already in the tree is harvested into the shared layer before a second consumer is briefed against it."
  - The trigger has fired three times. There are three public copies:
    - `GI.stateFind` (`ZeroKnowledge/GraphIsomorphism/Efficiency.lean:83–100`: "copy of `polyTimeComputable_stateFind` …, which is private there"), used by `EfficiencyRep.lean:206,405` (03k);
    - `EncodingMachines.polyTimeComputable_stateFind` (`ZeroKnowledge/EncodingMachines.lean:470–490`, 03k), used by `ThreeColoring/Machines.lean:126` (03g);
    - `GGMRed.stateLoopFun` with `stateLoopFun_poly` and `stateLoopFun_eval` (`Asymptotic/GGMReduction.lean:258–300`: "the function form of the private …"; 03j). Ch. 5–8 cites this one: `wt-s2b/.../Games/Efficiency.lean:124–126,214` (proof sketches).
  - There is also a fixed-round variant, `polyTimeComputable_stateIterate` (`HardCoreLoops.lean:62–70`, 03i).
- **On the auditor's two "deficiencies" of the public lemmas.** Both are correct.
  - (i) `horbit` quantifies over every word. Once the loop is pre-composed with `x ↦ ⟨x, start x⟩`, a guard is needed.
  - (ii) Rounds are counted in `|x|`.
  - Re-deriving the form takes about 20 lines from public pieces (`StateLoop.gstep_poly`, `length_gstep_iterate_le`, `gstep_iterate_eq`, `find?_range_eq_some`). That is why it was copied.
- **Severity:** major. A binding rule is broken and the debt has spread. It needs the fix, or the user's explicit acceptance (pack scale: "debt that needs explicit human acknowledgment").
- **Fix (P/A).**
  - Drop `private` and keep the full name `Complexity.polyTimeComputable_stateFind` in `Repetition.lean`. Do not move it to `Build/StateLoop`, which sits below `iterateFind`. Register it in the host registry.
  - Delete the two 03k copies and re-point their users.
  - For `GGMRed.stateLoopFun`, either derive `_poly` and `_eval` in one line each from the public lemma, or move the function form next to the lemma (for example `Complexity.StateLoop.loopFun`) and re-point `GGMReductionEval.lean:610,635` and the two wt-s2b sketches.
  - The deletion must be atomic. Inside `namespace TCSlib.Cryptography.EncodingMachines` with `open Complexity`, two `polyTimeComputable_stateFind`s would collide.
  - Update the prose that calls it private: `Repetition.lean:40–46`, `Build/StringLoops.lean:36–38` (03l) and `HardCoreLoops.lean:68`.
- **Ripple:**
  - Packs: 03g (`Machines.lean`), 03j (`GGMReduction`, `GGMReductionEval`), 03k (`Efficiency`, `EfficiencyRep`, `EncodingMachines`), 03l (prose only), 03i (prose only).
  - Ch. 5–8: the two wt-s2b sketches.
  - No statement changes meaning.
- **Ruling:** R2 (when). The fix itself is not a design choice.

### #5 (minor, agree): `polyTimeComputable_runAtL` overclaims "polynomial-size `A_n`"

- **Verdict: true.**
  - `NonUniform.lean:127–128` proves `PolyTimeComputable` at each fixed `n` only. The machine and the constants may depend on `n`, through `polyTimeComputable_const (A.advice n)` at :130–131.
  - The proof never uses `advice_length`, so the statement would hold with `2^n` bits of advice.
  - The docstrings at :118–121, :31–33 and :57–59 say "each `A_n` is a polynomial-size machine".
- **Consumers:** none (grep).
- **Fix (D).** Reword: "at each fixed `n` the activation is a polynomial-time function of `⟨y, r⟩` (the machine hard-wires `1^n` and `advice n`, so its size and constants depend on `n`). The polynomial size of `A_n` in Def 26.8 comes from `|advice n| ≤ adv(n)`, not from this lemma."
- **Ripple:** none.
- **Ruling:** no.

### #6 (minor (src) → note): `pairwise_sampling_ineq` does not state its cost

- **Verdict: true, now checked against the source.** The appendix (raw :100–108, p. 189) reads: "`E(X_i) = µ` and `|X_i| ≤ 1` … `Pr[|∑X_i/n − µ| ≥ e] ≤ (1 − µ²)/(ne²)`". For bits, `1/4 > 1 − p²` exactly when `p > √3/2`. The deviation note at `Ensembles.lean:671–673` gives the `p(1−p) ≤ 1/4` bound but not this comparison.
- **Severity:** note. The deviation is declared and benign:
  - the lemma has no consumer (grep: 0 outside `Ensembles.lean`);
  - the campaign's samplers (Goldreich–Levin) work near `p = ½`.
- **Fix (D).** Add to the deviation clause: "weaker than the text's `(1 − p²)/(mε²)` when `p > √3/2`; the variance form `p(1−p)/(mε²)` implies both."
- **Ripple:** none.
- **Ruling:** no.

### #7 (minor, agree): `Ensemble` says "every distribution is dyadic"

- **Verdict: true.** `Ensembles.lean:112` says "every distribution is dyadic (a pushforward of uniform seeds)". But `σ n` is any finite nonempty type (:125–129), so the laws are rational. Only `Samplable` laws are dyadic. The module docstring (:46), D6 and register #5 get this right.
- **Also missed:** the same deviation note does not mention the fixed length. Def 69.3 (ch3 raw :93–95) allows "a probability distribution over `{0,1}*`". The formal ensemble lives on `{0,1}^{ℓ(n)}`, which is what Def 69.4 requires.
- **Fix (D).** "Deviation: each `X_n` is the pushforward of the uniform distribution on a finite nonempty seed set (rational probabilities; samplable ensembles are dyadic, D6), on strings of the fixed length `ℓ(n)` that Def 69.4 requires (Def 69.3 allows `{0,1}*`)."
- **Ripple:** none.
- **Ruling:** no.

### #8 (minor → major): duplicated material without ledger entries

- **Verdict: true, and much wider than reported.** Policy §1, Duplication: "every instance of duplicated proved material must be human-approved … the audit template treats accumulated duplication as a major finding that a gate cannot close over without the human maintainer explicitly accepting the debt". None of the following is in `duplication-ledger.md`, which holds DL-1 to DL-8. The copies are disclosed in docstrings, so they are debt, not a freeze violation. Five of the six families are rooted in a `private` declaration in this pack's files:

  | Family | Copies (pack) |
  |---|---|
  | block bijection `{0,1}^{qℓ} ≃ ({0,1}^ℓ)^q` | `FunFamily.blocks` (`OneWay.lean:201`, 03b; 56 qualified uses in 14 files); private `Ensemble.blocks` (`Ensembles.lean:186`, 03a); `EnsembleLemmas.blocks` (`EnsemblesLemmas.lean:365`, 03i); `blocksEquiv` (`HardCoreLoops.lean:93`, 03i); `OneWay.blocksE` (`OneWayYao.lean:62`, 03h); `blocksEquivX` (`HardCoreGL.lean:767`, 03i, any codomain); the inverse `GI.blocksEquiv` (`GraphIsomorphism/SoundnessRep.lean:230`, 03k). Most copies carry their own `_apply`, `_symm_apply` and `ofFn_…_symm` lemmas. |
  | applied-form composition `ptc_comp` | private in `Closure.lean:148` (03a); private copies in `UniversalLemmas.lean:66`, `Universal.lean:337` (03h), `Collections.lean:642` (03b) and `EnsemblesLemmas.lean:174` (03i); public in `ThreeColoring/Machines.lean:87` (03g) |
  | state loop | see #4: private original plus three public copies |
  | `abs_uexp_sub_le` | private in `Sampling.lean:188` (03a); public copy `PublicKeyLemmas.lean:823` (03j: "copy of the private lemma of … Sampling") |
  | `forall_of_uprob_eq_one` | private copy in `Adversary.lean:190`. The original `HardcoreBit/Basic.lean:107` is public and importable; "lives in a frozen file" forbids editing it, not importing it. |
  | `negligible_zero` | `Ensembles.lean:231`; copy `negligible_const_zero` in `ZeroKnowledge/Defs.lean:197` (03e) |

- **Fix (P), to be done atomically per family, since the public names collide once the `private`s go:**
  - Adversary: `import TCSlib.Cryptography.HardcoreBit.Basic`, delete :188–201, use `HardcoreBit.forall_of_uprob_eq_one` at :217.
  - `blocks`: move `FunFamily.blocks` and its two lemmas (`blocks_symm_apply`, `ofFn_blocks_symm`) down into a file every user imports. `Adversary.lean`, beside `decodeFin` and `padFin`, works. Keep the full name `TCSlib.Cryptography.FunFamily.blocks`, so its 56 qualified uses don't change. Then delete the other five copies and their lemma copies, and turn the inverse into `(FunFamily.blocks m c).symm`. `blocksEquivX` may stay as the general-codomain form if 03i wants it, or become the canonical form.
  - `ptc_comp`: publish one applied-form lemma in `Closure.lean` and delete the five copies, or inline `hg.comp hf`.
  - `abs_uexp_sub_le`: make `Sampling`'s public and delete the 03j copy.
  - `negligible_zero`: see R3.
  - `stateFind`: see #4.
- **Ripple:**
  - Pack files touched: 03a; 03b (`OneWay.lean` loses `blocks` to a lower file, `Collections.lean`); 03e (`ZK/Defs`); 03g; 03h (`OneWayYao`, `Universal*`); 03i (`HardCoreLoops`, `HardCoreGL`, `EnsemblesLemmas`); 03j (`PublicKeyLemmas`, `GGMReduction`); 03k (`SoundnessRep`, `Efficiency`, `EncodingMachines`).
  - No statement changes meaning, but public statements in 03h, 03i and 03k name `blocksE`, `blocksEquiv` and `GI.stateFind`, so their text changes.
  - Ch. 5–8: none. The `blocks` hits there are prose.
- **Ruling:** R2 (ledger, and when to clean up) and R3 (`negligible_zero`).

### #9 (minor, agree): the `Claim-26.3` tags read as [PS10] item numbers

- **Verdict: true.** The bare tags are at `Closure.lean:211` (`[Claim-26.3, implicit]`), :275 (`(d)`), :305 (`(c)`) and :328 (`(b), (c), (e)`). :191 has `[PS10, §2.1, implicit; Claim-26.3 …]` without the word "inventory".
  - The book has no item 26.3. §2.1 has 23.4, 23.5, 24.6, 24.7 and 26.8; §2.2 has 26.1, 27.2, 27.3 and 28.4.
  - `Claim-26.3` is an inventory id (`inventory-ch2.md:104,269`), and it breaks ch3's own synthetic-id convention, `<Kind>-<page>.<letter>`.
- **Also missed:** `exists_reparam_advice` (:236) has no tag at all.
- **Fix (D).** Use "[PS10, §2.1, implicit; inventory Claim-26.3(x)]" throughout and add it to `exists_reparam_advice`. Do not rename the inventory id: it is cited elsewhere.
- **Ripple:** none.
- **Ruling:** no.

### #10 (minor, agree): `StatClose` lacks its defining tag

- **Verdict: true.** `Sampling.lean:103–108` cites §2.4.2 and §4.3, where the notion is used. [PS10] defines it only at Def 181.1 (book p. 181): "Two distributions X and Y are ε-close … if for every (deterministic) distinguisher D (with no time bound), `|Pr[D(x)=1] − Pr[D(y)=1]| ≤ ε`". The ch. 2–4 and appendix extracts contain no definition. `EpsClose` (`InformationTheory/Extractors.lean:65–69`) and `SamplingFinDist.lean:30–32` already cite Def 181.1.
- **Fix (D).** Add "[PS10, Definition 181.1], in its sup-over-test-sets form" to the docstring, and Def 181.1 to the module `## References` (:90–92).
- **Ripple:** none.
- **Ruling:** no.

### #11 (minor, agree): eleven `@[simp]` attributes without recorded approval

- **Verdict: true.** The eleven are at:
  - `PPT.lean:261, 266, 271, 298`;
  - `Closure.lean:104, 108, 112, 116, 161, 169`;
  - `Sampling.lean:354`.

  DESIGN §2.1 (:190) shows `@[simp]` only on `eval_*`. Policy §1 (user, 2026-10-16): "None carries `@[simp]` unless a gate approves it."
- **Same question in other packs:** 03b #12a (15 lemmas), 03c #11 (1) and 03e #17 (15).
- **Fix:**
  - Approve, with no change (recommended); or
  - drop the attributes (P). That is a replay of everything downstream. Ch. 5–8 has 62 non-`only` `simp` calls, and 10 of its files use `layout` or `ofPolyTime*`. Prong A's `Lamport.lean:429–430` names the lemmas explicitly and is unaffected either way.
- **Ruling:** R1.

### #12 (minor, agree; understated): facade import, and `negligible_zero` out of place

- **Verdict: true.**
  - **The facade.** `Ensembles.lean:6` imports `TCSlib.Complexity.Randomized`, a facade of 71 modules, 65 of them unrelated to the campaign (`Randomized.lean`). It puts 77 `Complexity/Randomized/*` modules into the replay closure (`evidence/a/replay.log`); the auditor's count of 65 is right.
  - **Missed: two more files import the facade.** `EnsemblesLemmas.lean:6` (03i) and `Candidates/DiscreteLog.lean:6` (03f1).
  - **Missed: `negligible_zero` (`Ensembles.lean:231`) has a second copy:** `negligible_const_zero` (`ZeroKnowledge/Defs.lean:197`, 03e).
  - **The auditor's fix conflicts with D2.** Moving the lemma into `Foundations/Negligible.lean` runs against "never into the frozen Garg files".
- **Fix (P).**
  - Use precise imports, `Randomized.{Closure, Repetition}` or whatever the file actually uses, in all three files.
  - Move `negligible_zero` per R3. `Negligible.lean` is in `namespace TCSlib.Cryptography` (:51), so the full name, and its four users (`Ensembles:308`, `PRF:270`, `NextBit:740`, `ZK/Encryption:102`), stay unchanged.
- **Ripple:**
  - Elaboration only: anything that relied on the facade transitively must be found by a replay.
  - Ch. 5–8 prong D uses `Randomized.InBPP`. It reaches `Randomized/Classes` through `BPPBridge` independently (checked), so the cleanup does not break it.
  - Packs: 03f1 and 03i (an import line each); 03e (under R3-A).
- **Ruling:** R3, for the `negligible_zero` part only.

### #13 (minor, agree): the `SamplingFinDist.lean` header

- **Verdict: true.** Lines 1–9 have no `Authors:` line and no `set_option maxHeartbeats 0`, and the module docstring has no `## Main definitions` section. Lint found the last two.
- **Fix:** the header (D).
- **Ripple:** none.
- **Ruling:** no.

### Notes #14–#26

| # | Verdict | Severity | Evidence / correction | Fix · ripple · ruling |
|---|---|---|---|---|
| 14 | true | note | Checked. `PolyExpr` has ℕ coefficients and no subtraction, so `eval` is either constant or strictly increasing, and `hℓ` fails only for constant `ℓ ≡ L`. In that case `IndistLit` makes each of the `2^L` point tests negligible. Then `TV(X_n, Y_n) ≤ ½Σ_{t₀}|X_n(t₀) − Y_n(t₀)|` is negligible and bounds every distinguisher (`distAdv_le_of_statClose`). | D: one sentence on `IndistLit.toIndist` (`Ensembles.lean:340–342`), and in D5 and register #5 change "injective" to "every `PolyExpr ℓ` (the constant case by point tests, not formalized)". Dropping `hℓ` would be an S change; there is no consumer. No ruling. |
| 15 | true | note | Checked. Under [PS10]'s experiment, `f(0^{|y|}‖y) = y` succeeds with probability 1. Under the typed one a special preimage has the wrong length, so success is at most `Adv_g + 2^{-L/2}`. This is the same daylight as 03b #2 (`ofString` without `LengthRegular`). | D, routed to 03b #2's resolution: state the proviso at `FunFamily.ofString`, and add a pointer from `inverter` (`Adversary.lean:99–100`). No ruling. |
| 16 | true | note | `hybrid_lemma` (`Ensembles.lean:415–417`) takes `X : ℕ → σ → γ`, one seed type. Harmless. | D (optional). No ripple. |
| 17 | true | note | The `PolyExpr` docstrings (`PolyExpr.lean:12–24, 63–68`) do not say that `n − 1`, `⌊n/2⌋` and `⌈log n⌉` are not expressible. `exists_reparam_advice` is the escape hatch (D9). | D, one sentence. No ripple. |
| 18 | true | note | `push` (`Ensembles.lean:176–182`) pads with `padFin`, which loses information for variable-length `M`. It is lossless when `M` has the fixed output length `ℓ'(n)`, the only case Def 69.4 can type. Ch. 5–8 uses no `Ensemble` (0 hits); it works over the games framework and `OracleEnsemble`. | D: one sentence in `push`. Do not build `EnsembleL` now, since no consumer asks for it. No ruling. |
| 19 | true | note | `axioms.log` has 41 entries, and the eleven named lemmas are not among them. The replay shows 22 `sorry` warnings: TimeConstructible 2, NonUniform 1, Build/Loop 5, Build/Primitives 3, RecordTable 4, Wrappers 2, Composition 3, Encoding 1, Simulation 1. | Add the prints to `audits/pass-shelat/Checks.lean` and re-run with the repair. Not Lean statements. |
| 20 | **partly true** | note | **(i) True.** D11 (`DESIGN.md:155–157`) names `NUPPT.ofPartial`, which does not exist. The `sorry` is in `decides_of_decidesWithAdviceInTime` (`NonUniform.lean:153–158`), whose sketch does `ofPartial`'s clocking inline. **(ii) False.** The Q5 ruling exists: `PassShelatChapter2-4Plan.md:366` (2026-10-27, "Open question 5 … outside the mandatory core"), and :371 (2026-10-28) names this bridge as "the only remaining machine-layer sorry". The bundle did not carry the plan. I agree that the statement is true: clock `M`, use `α` as advice at `|x|`, no coins. | D: annotate D11 and §8 Q5 with the decision-log entries and the actual admission. No ruling: it is already ruled. |
| 21 | true | note | Only "nonempty" checks exist (`PPT.lean:329–335`, `Indist.refl`, `uniform_samplable`). | Add a `Checks.lean` entry with a constant-zero ensemble and `¬ (uniform .var).Indist zeros` (first-bit distinguisher). It needs a small `def` in `Checks.lean` or in `Ensembles`. No ripple. |
| 22 | **partly true** | note | `EnsemblesLemmas.lean` is not in 03a, but it **is** audited: it is in 03i's scope (`PLAN.md` 03i row; `03i-pack.md:34`). Ch. 5–8 cites none of its declarations (0 hits for `EnsembleLemmas`, `exists_pushRed`, `coinsEquiv` and `acceptProb_*`). | Pack erratum: list it as context for 03a, audited in 03i. No ruling. |
| 23 | true | note | `inventory-ch2.md:265` (Def-26.8 "run on `pairEncode (pairEncode x (α \|x\|)) r`", `Ca·(n+1)^ca`) and the pack's Q1 are stale against D3 and D4. | Add "superseded by DESIGN D3–D6" banners to the inventory rows, and an erratum to the pack. Not Lean. |
| 24 | true | note | (a) `PPT.lean:62–66`, "with `φ := length`": `φ : ℕ → ℕ`, and (i) holds by `runLit`'s definition. (b) `Ensembles.lean:390` cites "run-3 audit note P2-4". `run3-audit-summary.md` has only P2-1 and P2-2 (:91–101), and nothing under `briefs/` or `audits/` mentions P2-4. | D: fix (a); for (b), cite "`exists_comp` sees only `y` (gate 03a #3)" instead. No ruling. |
| 25 | true then; **resolved** | note | The source is in the tree. I checked #6 against p. 189 (confirmed), and read Defs 23.4, 23.5, 24.6, 26.8, 69.3, 69.4 and Lemmas 71.5, 71.6, 73.8 (ch2 raw :95–216, ch3 raw :93–300). No new daylight: `Distinguishes` is strict, like p. 70's "> e" (`Ensembles.lean:218–222`), and `prediction_lemma`'s strict conclusion is stronger than the text's `≥`. | Close the note. |
| 26 | true | note | `uprob` on an empty type is 0 (Def at `Sampling.lean:109`). Every use has nonempty seeds (`Ensemble.nonempty`, `SamplingFinDist`'s `[Nonempty σ]`). | D, optional. No ripple. |

## Rulings for the user

**R1. Unapproved `@[simp]` attributes.** This covers 03a #11, and the same question in 03b #12a, 03c #11 and 03e #17.
- **(A) Recommended.** Approve, in one gate-03 ruling, every `@[simp]` that the four findings list, and record the list in the resolutions. 03a's eleven are simp-normal forms: the field equations of `ofPolyTime` and `ofPolyTimeUniform`, the projections of `layout`, the decoding of `combineAdvice`, and `bitsEquiv_val`. **Cost:** none; no file changes.
- **(B)** Approve 03a's eleven now, and decide the other packs' lists one by one. **Cost:** a replay for each pack whose attributes are dropped.
- **(C)** Drop every unapproved attribute. **Cost:** a full replay of ch. 2–4 (about 93 files) and of the five ch. 5–8 worktrees, with unknown breakage. Ch. 5–8 alone has 62 non-`only` `simp` calls, and the ch. 2–4 proofs were written against these simp sets.

**R2. Duplication rooted in 03a's `private` helpers** (#4, #8 and the copies listed there).
- **(A) Recommended.** Ledger the six families as DL-9 to DL-14 under "Inherited with ch. 2–4", and clean them up in the gate-03 repair PR:
  - make `polyTimeComputable_stateFind`, `ptc_comp` and `abs_uexp_sub_le` public;
  - import `HardcoreBit.Basic` in `Adversary.lean`;
  - keep one `FunFamily.blocks` in a low file;
  - delete the copies;
  - re-point the wt-s2b sketches.

  **Cost:** one proof-level PR over about 15 files in 03a, 03b, 03e, 03g, 03h, 03i, 03j, 03k and 03l, plus a replay. 03h, 03i and 03k wait for it, because their public statements name copies that it renames.
- **(B)** Ledger now, with "paid back at the `main` landing". Fix only the parts inside 03a's files now (drop the three `private`s, delete `Adversary`'s copy), keeping the downstream copies under different names. **Cost:** the gate closes on recorded debt; the copies stay on the trusted surface; 03g to 03k audit them as they are, with an erratum; ch. 5–8 keeps citing `GGMRed.stateLoopFun`.
- **(C)** Accept the copies permanently ("accepted, no payback"). **Cost:** it leaves a standing breach of the binding "Hosts come first" rule. Not recommended.

**R3. Where `negligible_zero` lives** (#12; its copy `negligible_const_zero` is in `ZK/Defs`, 03e).
- **(A) Recommended.** Move it to `Foundations/Negligible.lean`, as policy §1 "Helpers" asks. Its full name stays the same, so its four users don't change. Delete `negligible_const_zero` (2 uses). **Cost:** one 5-line lemma added to a Garg-audited file, overriding D2's "never into the frozen Garg files" for this one case.
- **(B)** Keep it in `Ensembles.lean`, and have `ZK/Defs` import `Ensembles`. **Cost:** `ZK/Defs` pulls in Ensembles' heavy closure (`EnsemblesLemmas`, `Indistinguishability`, `GeneratorFromPermutation`, `PairwiseIndependence`) for 5 lines.
- **(C)** Put it in a new campaign-owned helper file (for example `Asymptotic/NegligibleLemmas.lean`) that both import. **Cost:** one more small file; respects D2.

## What the auditor missed

1. **Duplication is wider than reported** (folded into #4 and #8).
   - The `blocks` bijection has 6 copies plus an inverse, most with their own lemma copies.
   - `ptc_comp` has 6 copies.
   - The state loop has 4, plus the variant `stateIterate`.
   - `abs_uexp_sub_le` and `negligible_zero` have 2 each.
   - The root cause is the same throughout: helpers that are `private` in this pack's files.
2. **The facade import also sits in** `EnsemblesLemmas.lean:6` (03i) and `Candidates/DiscreteLog.lean:6` (03f1) (#12).
3. **`exists_reparam_advice` has no source tag** (`Closure.lean:236`) (#9).
4. **`Ensemble.Samplable` misattributes** (`Ensembles.lean:147–148`). It cites "[PS10, … Lemma 71.6's multicopy corollary]", and [PS10] has no such corollary: the multicopy lemma is [Gar26, Lemma 3.3]. p. 72's Example ("efficiently sample") is the right tag. Minor, docstring only.
5. **`Ensemble`'s deviation note omits the fixed-length restriction** relative to Def 69.3 (#7).
6. **Prose calls `stateFind` private** in `Build/StringLoops.lean:36–38` (03l) and `HardCoreLoops.lean:68` (03i). Update it with #4.
7. **Cross-pack:** 03b #12b proposes moving `NUPPT.withIndexParam`, `length_runAt_le` and `runLenPoly` from `Collections.lean` into `Complexity/Randomized/`, which is 03a's directory. Ch. 5–8 cites `NUPPT.runLenPoly` and `length_runAt_le_runLenPoly` (`ObliviousTransfer.lean:417`, `Composability/PublicKey.lean:276–293`). Keep the full names `Complexity.NUPPT.*` when moving them; 03a's closing diff should then include them.
8. **The auditor's downstream check for #1 is clean** (see #1). Nothing in ch. 5–8 is a blocker on that account.

## Pending packs: which can go now

The criterion: does an 03a fix change a statement a pack audits or cites, or rename or delete a declaration on its surface? With the recommended options, **no fix changes any statement's meaning**. Only the dedup renames or deletes copies.

| Pack | Touched by 03a's fixes | Dispatch |
|---|---|---|
| 03d | No. It uses `negligible_zero` and `FunFamily.blocks` under unchanged names. | Unaffected by 03a; still held by F-1 (`PLAN.md`) |
| 03f1 | Only `DiscreteLog.lean:6`'s import line, if the facade cleanup is extended to it | **Now** |
| 03f2 | No | **Now** |
| 03g | `Machines.lean`: its public `ptc_comp` copy (:87) is deleted, and `stateFind` at :126 is re-pointed (proof) | **Now**, with a one-line erratum |
| 03h | `OneWayYao.blocksE` and its lemmas (public statements) are replaced by `FunFamily.blocks`; private `ptc_comp` in `Universal*` | Under R2-A, after the dedup PR; under R2-B, now with an erratum |
| 03i | `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks` and `ptc_comp` (public statements), the facade import, the `stateFind` prose | Under R2-A, after the dedup PR; under R2-B, now with an erratum |
| 03j | `GGMRed.stateLoopFun*`, `PublicKeyLemmas.abs_uexp_sub_le` | Held by F-1 anyway; under R2-A, re-pin after both land |
| 03k | `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `SoundnessRep.blocksEquiv` (public) | Under R2-A, after the dedup PR; under R2-B, now with an erratum |
| 03l | Only `StringLoops.lean:36–38` prose ("private") | **Now** |

Under R1-C, every pack's *proofs* would change, but no statement would. That would add a replay, not a reason to hold any statement pack.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03a-r1.md =====

# Gate 03a (machines and probability): round 1 resolutions

- **Round 1:** findings `findings/gate03a-findings.md`, verbatim, SHA-256
  `9dd9195111dfc8aca6748405f2730ca98c8f61f3ae51b2858b2fe87e8cfa5f92`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 0 majors, 13 minors, 13 notes.**
- **Review:** `review/gate03a-review.md`: 23 true, 3 partly true (#2, #20, #22), none false. Four
  severity changes: #4 and #8 minor → **major**; #2 and #6 minor → note. New tally **0 blockers,
  2 majors, 9 minors, 15 notes**. Eight items missed by the auditor (M1–M8 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`, decision log rows "Gate 03 rulings G3-5 to
  G3-8"**):** G3-5 (A), ledger the duplicates as DL-9 onward and clean them up in the gate 03
  clean-up PR (#4, #8); G3-6 (A), approve every listed `@[simp]` (#11); G3-7 (a), move
  `negligible_zero` to `Foundations/Negligible.lean`, overriding D2 for one lemma (#12). R-03l-1
  (gate 03l) widens the same clean-up PR; its part 1 also carries DL-11's first half (#4).
- **Repair:** commit `e8f45ca3ca7246d1379c4b66ce5a7a72d0b2d820` (on #198's head
  `c10ed6ace0b991146c0be769313fbbe52d36e25a`), merged with the ch. 2–4 head as
  `956c595f2584532899aac1fb6fbe3d0aab9fa370`, in PR #201 with 03c's
  `bc2aab59333e27729c9fbac3052cd650bf62c3aa`. #201's head is
  `0c348ff94cacf24d96d99078c9dd9e328530c8d2`, merged by `02951926d9c9cea1d3596afa71c252176ca9de1d`.
  Gate 03 clean-up part 1 is PR #203 (head `f29be161cd86cfc3a9c38bd203bfa095b4974086`, merged by
  `8ec28f130eaca5f7d7dc756953bde0807d41b7df`; evidence `evidence-repairs/03l-cleanup1/`). Evidence `evidence-repairs/03ac/` (replay of the 97 downstream modules
  plus `Checks`, the full `Checks` axiom print at #201's head, lint 0). Line numbers are at #201's
  head unless a row says otherwise; Lean paths are under `TCSlib/`.
- **Scheduled work** goes to the gate 03 clean-up: part 1 is merged (#203);
  part 2 follows #195 (`duplication-ledger.md` DL-9 to DL-15; `QUEUE.md:147`).

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | minor | **Fixed.** `NUPPT.Computes` (`Complexity/Randomized/PPT.lean:229–241`), the module docstring (:40–48, :89–90) and DESIGN D3 (`briefs/pass-shelat/DESIGN.md:64–67`) say that Def 24.6 proper is `A.Uniform ∧ A.Computes f` and that the non-uniform form holds for uncomputable `f`. No `PPT.Computes` wrapper (no consumer); the downstream check is clean (review: 0 uses in ch. 5–8). |
| 2 | note (was minor) | **Fixed** (docstring). `Ensemble.Indist.copies` (`Cryptography/Asymptotic/Ensembles.lean:456–460`) says the samplability hypotheses are [Gar26, Lemma 3.3]'s uniform reduction and can be dropped against non-uniform distinguishers (not proved, no consumer). D6 unchanged; the optional `Indist.copies'` is not added. |
| 3 | minor | **Fixed** (#203, item H; found missing while drafting these resolutions). `NUPPT.exists_compParam` (`Complexity/Randomized/Closure.lean:209`, at #203's head): closure under polynomial-time pre- and post-processing that see `1^n`, with the review's statement. `exists_comp` is re-derived as its special case (statement unchanged), and its Scope paragraph points to the new theorem; `Checks.lean` prints it (standard axioms). Its proof, like `exists_comp`'s, reads `PPT.lean`'s `runAtL` and `advInput` by `simp`; the equation lemmas `runAtL_eq` and `advInput_eq` are **scheduled** for part 2. |
| 4 | major (was minor) | **Fixed** in its first half (#203, item D): `Complexity.polyTimeComputable_stateFind` is public (`Complexity/Randomized/Repetition.lean:241`, at #203's head), with its statement unchanged, and the prose calling it private is fixed (`Repetition.lean`, `Build/StringLoops.lean`, `Asymptotic/HardCoreLoops.lean:68`). **Scheduled:** part 2 re-points the copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun` and the variant `stateIterate`, and their "private" docstrings (DL-11). Meanwhile `ThreeColoring/Machines.lean:126` names the `EncodingMachines` copy explicitly, since the public name made the call ambiguous. |
| 5 | minor | **Fixed.** `polyTimeComputable_runAtL` (`Complexity/Randomized/NonUniform.lean:122–128`), the module docstring (:33–37) and its main-results line (:61–62) say the machine's size and constants depend on `n`, and that Def 26.8's polynomial size comes from `advice_length`. |
| 6 | note (was minor, src) | **Fixed.** `pairwise_sampling_ineq`'s deviation (`Ensembles.lean:691–696`) states that `1/4 > 1 − p²` exactly when `p > √3/2`, and that the variance form implies both bounds. The review checked the source (p. 189). |
| 7 | minor | **Fixed.** `Ensemble`'s deviation (`Ensembles.lean:119–125`): rational laws (seeds `Fin 3` give mass `1/3`; the samplable ensembles are the dyadic ones, D6) on strings of the fixed length `ℓ(n)` (missed item M5). |
| 8 | major (was minor) | **Scheduled** (G3-5). Ledgered as DL-9 (`blocks`), DL-10 (`ptc_comp`), DL-11 (state loop), DL-12 (`abs_uexp_sub_le`), DL-13 (`negligible_const_zero`), DL-14 (`forall_of_uprob_eq_one`), all "accepted; scheduled"; clean-up part 2, except DL-11's first half (part 1). The copies are still in the tree, e.g. `Asymptotic/Adversary.lean:198`, `Ensembles.lean:199`, `Closure.lean:149`, `Asymptotic/Sampling.lean:198`, `ZeroKnowledge/Defs.lean:248`. |
| 9 | minor | **Fixed.** The catalogue tags read "[PS10, §2.1, implicit; inventory Claim-26.3(x)]" (`Closure.lean:192, 219, 245, 283, 313, 338`); `exists_reparam_advice` gains its tag (:245, missed item M3); the inventory id is not renamed. |
| 10 | minor | **Fixed.** `StatClose` (`Asymptotic/Sampling.lean:104–114`) cites [PS10, Definition 181.1] in its sup-over-test-sets form; the module References list it (:91). |
| 11 | minor | **Recorded** (G3-6, `QUEUE.md:125`): the eleven attributes are approved and unchanged: `coins_ofPolyTime`, `adv_ofPolyTime`, `advice_ofPolyTime`, `coins_ofPolyTimeUniform` (`PPT.lean:275, 280, 285, 312`); `inParam_layout`, `inArg_layout`, `inAdvice_layout`, `inCoins_layout`, `pairFstD_combineAdvice`, `pairSndD_combineAdvice` (`Closure.lean:105, 109, 113, 117, 162, 170`); `bitsEquiv_val` (`Sampling.lean:364`). |
| 12 | minor | **Fixed**, with two items **Scheduled.** Precise imports replace the facade in `Ensembles.lean:6–11`, `Asymptotic/EnsemblesLemmas.lean:6–7` and `Candidates/DiscreteLog.lean:6–8` (missed item M2); `negligible_zero` is in `Cryptography/Foundations/Negligible.lean:164` under its full name (G3-7 (a); D2's exception at `DESIGN.md:47–51`). Scheduled: `ThreeColoring/SimulatorMachine` is to import `NonUniform` itself so that `Ensembles` can drop it (`QUEUE.md:147`), and the copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean:248`) goes as DL-13 (part 2). |
| 13 | minor | **Fixed.** `Asymptotic/SamplingFinDist.lean:4` (`Authors:`), :9 (`maxHeartbeats 0`), :23–25 (`## Main definitions`: None). |
| 14 | note | **Fixed** (docstring). `IndistLit.toIndist` (`Ensembles.lean:349–354`), the module docstring (:41–42, :52–54), DESIGN D5 (`DESIGN.md:96–98`) and register item 5 (:1003–1004) say the two forms coincide for every `PolyExpr ℓ` (constant case by point tests, not formalized). `hℓ` is kept (no consumer). |
| 15 | note | **Fixed.** The wrong-length cost is stated on `NUPPT.inverter` (`Asymptotic/Adversary.lean:102–108`) and on `FunFamily.ofString` (`Asymptotic/OneWay.lean:198–206`), as routed with 03b #2. |
| 16 | note | **Fixed.** `hybrid_lemma` (`Ensembles.lean:426–428`): one seed type; other shapes embed into a product seed. |
| 17 | note | **Fixed.** `PolyExpr` (`Complexity/Randomized/PolyExpr.lean:68–72`): `n − 1`, `⌊n/2⌋`, `n(n−1)/2`, `⌈log₂ n⌉` not expressible; pad or use `exists_reparam_advice`. |
| 18 | note | **Fixed.** `Ensemble.push` (`Ensembles.lean:189–192`): padding is lossless only for exact `ℓ'(n)`-bit outputs. No `EnsembleL` (no consumer). |
| 19 | note | **Fixed.** The eleven prints and `negligible_zero`'s are in `audits/pass-shelat/Checks.lean:454–467`; all twelve print `[propext, Classical.choice, Quot.sound]` at #201's head (`evidence-repairs/03ac/checks-axioms.log:471–482`). |
| 20 | note (partly true) | **Fixed.** DESIGN D11 (`DESIGN.md:172–177`) names the real admission, `NUPPT.decides_of_decidesWithAdviceInTime`, and says `ofPartial` was never written; §8 Q5 (:1283–1285) cites the ruling of 2026-10-27. |
| 21 | note | **Fixed.** `PassShelatChecks.zeros` and `not_indist_uniform_zeros` (first-bit distinguisher) in `audits/pass-shelat/Checks.lean:475, 507`; its print is standard (`checks-axioms.log:483`). |
| 22 | note (partly true) | **Fixed in the closing-round pack** (pack erratum): `EnsemblesLemmas.lean` is context for 03a and audited in 03i. |
| 23 | note | **Fixed.** Banners "superseded by DESIGN D3–D6" on `inventory-ch2.md:255, 265` (Def-23.4, Def-26.8) and `inventory-ch3.md:38, 195, 204` (Machine-NUPPT, Def-69.3, Def-69.4); the erratum to the pack's stale Q1 is in the closing-round pack. |
| 24 | note | **Fixed.** (a) `PPT.lean:68–70`: (i) holds by `runLit`'s definition, no ill-typed `φ := length`. (b) `Indist.push`'s sketch cites gate 03a finding 3, not "P2-4" (`Ensembles.lean:402`). |
| 25 | note | **No change.** Resolved by the review: the source is in the tree; #6 checked against p. 189; Defs 23.4, 23.5, 24.6, 26.8, 69.3, 69.4 and Lemmas 71.5, 71.6, 73.8 read, no new daylight. |
| 26 | note | **Fixed.** `StatClose` (`Sampling.lean:115–118`): on an empty seed type the law is the zero measure; every use has nonempty seeds. |
| M1 | (review) duplication wider | **Scheduled** with #4 and #8 (DL-9 to DL-14). |
| M2 | (review) facade imports elsewhere | **Fixed** with #12 (`EnsemblesLemmas.lean:6–7`, `DiscreteLog.lean:6–8`). |
| M3 | (review) `exists_reparam_advice` untagged | **Fixed** (`Closure.lean:245`). |
| M4 | (review) `Samplable` misattributed | **Fixed.** `Ensemble.Samplable` (`Ensembles.lean:157–158`) cites [PS10, p. 72, Example] and [Gar26, Lemma 3.3] for the multicopy lemma. |
| M5 | (review) fixed length not declared | **Fixed** with #7 (`Ensembles.lean:122–123`). |
| M6 | (review) prose calls `stateFind` private | **Fixed** (#203, item D); see #4. |
| M7 | (review) 03b #12b's `NUPPT` helpers | **Fixed** in #198: moved to `Cryptography/Asymptotic/CollectionsHelpers.lean:58–115` (not 03a's directory) with the full names `Complexity.NUPPT.*` unchanged, so 03a's closing diff does not include them. |
| M8 | (review) downstream check for #1 | **No change:** clean (no ch. 5–8 use of `NUPPT.Computes`). |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack-r2.md =====

# Gate 03a ([PS10] ch. 2–4, probabilistic machines, closure, ensembles: the interface), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e28773ef3bda6f7b4b112ec1657427bfef01e374` (the branch after #201 and #203 merged; its Lean files are #203's head `f29be161`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 0 majors, 13 minors and 13 notes**; after the review, 2 majors (#4 and #8 raised: duplication rooted in private helpers) (`gate03a-findings.md`, in the bundle,
  verbatim).
- **The repair:** the 03a repair commit (G3-7 (a): `negligible_zero` moved; precise imports; minors and notes), merged in #201; gate 03 clean-up part 1, #203 (item H: `NUPPT.exists_compParam`, the fix for #3 that #201 missed; item D: `polyTimeComputable_stateFind` public; item G: `Repetition.lean`'s construction prose). The full delta is `evidence-r2/03a/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03a-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03a-review.md` (in the bundle).
- **The deliverable:** **`gate03a-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Errata to the round 1 pack (review of round 1)

- **Context** (#22): `Asymptotic/EnsemblesLemmas.lean` is context for this pack; pack 03i audits it.
- **Q1** (#23): the stale question is answered by the inventory banners ("superseded by DESIGN
  D3–D6", `inventory-ch2.md`, `inventory-ch3.md`).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03a-r1.md` (the
   findings, grouped as the review grouped them, and the review's missed items `M1`, …) say
   whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR (clean-up part 2,
     after #195), and the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03a/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement, rename and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** No public statement of this pack changes (statement-text comparison against round 1). `negligible_zero` moved from `Ensembles.lean` to `Negligible.lean` (both in this pack), name and statement unchanged. `Repetition.lean`'s proofs were re-pointed to `Build/`'s new reading lemmas (#203); its 03l-related prose is re-audited in gate 03l round 2 as well.
- **New public declarations:**
- `NUPPT.exists_compParam` (`Closure.lean`): closure under polynomial-time pre- and
  post-processing that see `1^n`; `exists_comp` is re-derived as its special case;
- `polyTimeComputable_stateFind` (`Repetition.lean`): made public (statement unchanged).

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03a-findings.md`, `review/gate03a-review.md`, `resolutions-03a-r1.md`, `evidence-r2/03a/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles, SamplingFinDist}.lean`, `TCSlib/Cryptography/Foundations/Negligible.lean` |
| Context | `03a-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; clean-up part 2 (after #195) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/a2/` in the bundle)

### Attestation results at `e28773ef3bda6f7b4b112ec1657427bfef01e374` (evidence under `evidence/a2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 64 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   18 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 164 prints of every public theorem and lemma in this pack's files:
   163 use only the standard axioms, and 1 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 11 files.

The one `sorryAx` print and the one admission are the same declaration,
`NUPPT.decides_of_decidesWithAdviceInTime` (`NonUniform.lean:160`): the optional admission recorded
in DESIGN D11 (round 1, note 20).

The replay is the 416-module replay at `af91d53a`, overlaid by the re-check at #201's head
(`evidence-repairs/03ac/replay.log`) and by #203's builds and re-check
(`evidence-repairs/03l-cleanup1/`); each line of `replay.log` is the newest check of its module,
and the Lean files at the pin equal #203's head.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row (or row group): `<row>: fixed / recorded / scheduled / not resolved —
<reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.
