# Pass–shelat Gate 38 — derand

**Verdict: CLEAR under the supplied rulings.** No new findings.

| Blockers | Majors | Minors | Notes |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |

| Pin | Audited value |
|---|---|
| Repository / PR | [Shilun-Allan-Li/tcslib #326](https://github.com/Shilun-Allan-Li/tcslib/pull/326) |
| Lean head | `c27005d67298f79c785a4e8ac1648da0a67d3614` |
| Comparison base | `6ce4658db08a1dc2a03a149987197660db078011` |
| Campaign records | `24f4405205542f810157cbaf29a36ab99a52cbe8` |
| Exchange | `4b6ee799d15bac4042288fcb165d5c4d2d8f6a31` |

The three targets establish their frozen statements. The 20 disclosed Rule-10 failures remain approved debt under F-01 / DW-5; they are not counted again. E1's disclosed repetition remains covered by F-03. SR-01 and its 1415-line exception are accepted as instructed. LE-doc resolves F-04.

**Audit method and limit.** I read the delivered proofs and relevant interfaces, checked the book, and independently reran checks of Git blobs, declarations, probe construction, raw diagnostics, controls, census output, duplication candidates, and integration source identity. Lean/lake were unavailable in this audit session, so I did **not** perform a new Lean build or kernel replay. Build and axiom conclusions use the supplied, hash-verified Lean evidence, with the independent checks described below. No repository changes, dispatch, readiness change, or merge was made.

## Integrity and scope

All **25** entries of the pack's `SHA256SUMS` verify, including `README.md`, `pack.md`, `bundle.md`, and every supplied ZIP. The bundle SHA-256 is:

`1a268dccad2b66a300e25c3bcfae84135e98bc728c33884d0ff7cb8175d4ccb5`

The nested archives have exactly the files named by their manifests, plus the manifest itself; all hashes verify:

| Archive | Files | Verified manifest entries |
|---|---:|---:|
| `verification.zip` | 153 | 152 |
| Its `review-evidence.zip` | 1318 | 1317 |
| `integration/int-all-open-evidence.zip` | 1249 | 1248 |
| `landing-ledoc/ledoc-derand-seqzk-evidence.zip` | 59 | 58 |

All **207** source-closure files match their Git blob IDs at the audited Lean head. The supplied diff reproduces byte-for-byte from the base and head, using nine-character Git index abbreviations: **15 paths, +1741/−36**. The records pin identifies this gate, and its changes after `c2f6adeb` are records only.

The five existing files retain all **93** pre-existing declaration headers, in order, and their definition bodies. The public declaration delta is **53 ADDED / 0 CHANGED / 0 REMOVED**. There is also the disclosed private theorem `short_poly`; it does not alter that public count. The two owned files retain their seven original declarations and frozen target statements. Their proof, allowed sketch/status, module-documentation, and import changes are in scope.

The shared-file additions are exactly:

| File under `TCSlib/Complexity/` | Additions | Delta |
|---|---|---:|
| `ClassP/DTIME.lean` | E2 `mem_DTIME_iff`; E3 `FinTM.decidesInTime_iff` | +18/−0 |
| `Randomized/Build/IterateFind.lean` | E1 `IterateFind.computesFunInTime_find`, plus its allowed module-docstring bullet | +245/−0 |
| `Randomized/Classes.lean` | SR-01 `Randomized.inBPP_iff` | +12/−0 |

E2 and E3 match the approved signatures and `Iff.rfl` bodies. SR-01's code matches its approved patch. The old `polyTimeComputable_find` and `final_bound` proofs remain unchanged. `Classes.lean` has **1415 lines**, maximum width **97**. No additional shared-file edit was found.

## Proof audit

The book comparator is [Pass–shelat, third edition, §8.2, Theorem 180.1, p. 180](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf). Its route stretches a shorter seed, substitutes generated coins, and enumerates seeds to obtain deterministic subexponential time. The delivered proof supplies the integer schedule, non-uniform bad-input argument, and finite-length treatment required by the frozen formulation.

### H17 and its corollary

1. From polynomial-time computation of the unary width, the proof obtains a polynomial bound on `w(n)`. For every prefix rank,

   \[
   0\le a_i=\#\{j<i:\operatorname{pairEncode}(x,\operatorname{word}(w(n),j))\in V\}
   \le i\le R=2^{w(n)}.
   \]

   `length_state_le` consequently bounds the retained-input state by `2n + 3w(n) + 7`. Both counters, including the terminal value `R`, fit in `w(n)+1` bits.

2. E1 retains the size guard and uses `inv_step` for the **total** step. `exists_countingTM` proves that the guard never fires along the genuine prefix through rank `R`. It does not assume that unbounded post-termination increments preserve a fixed size bound.

3. Fuel is **`Nat.bits (2 ^ w(n))`**, computed through the existing binary power-of-two evaluator. The search is over `List.range (R+1)`. Its test is false before `R` and true at `R`, so the terminal rank is included. `count_all` identifies the terminal count with the frozen count over Boolean tuples. The payload is `[decide (R < 2a_R)]`; ties reject.

4. The time estimate uses the generic-fuel contract directly:

   \[
   R\ge1,\qquad R+2\le3R,\qquad
   c_0(T(n)+1)(R+2)\le3c_0A\,R(n+1)^e.
   \]

   **`final_bound` is not applied to exponential fuel.** No admitted loop-host or timed-conditional specification is used.

5. `exists_seedMajorityTM` takes **one** machine from `exists_countingTM`. Its decision clause and envelope both use that machine's `ComputesFunInTime` evidence and the same budget `B(n)`. For a work-head position `p`, the interval/run readers give

   \[
   p(0)=0,\qquad |p(u)|\le u,\qquad
   p(v)=p(\min(v,B(n))),\qquad |p(v)|\le B(n).
   \]

   The equality uses halting by `B(n)` and constancy thereafter. `seedMajority_mem_DTIME` then transports the decision witness through `mem_DTIME_iff`, without unfolding `DTIME` or either decision predicate.

At `w(n)=0`, `R=1`: one empty seed is tested, and the same strict comparison is correct. Initialization at `n=0` is covered by the polynomial factor `(n+1)^e`. A zero time coefficient cannot satisfy the supplied computation contract; no positive-time claim is derived by assuming such a witness valid.

### Theorem 180.1

1. `exists_root_degree` supplies an integer `d≥2` with `1/d<min(ε,1)`. `ceilRoot` uses the existing natural floor root, handles zero separately, and proves

   \[
   \ell(0)=0,\quad n\le\ell(n)^d,\quad
   \ell(n)\le n^{1/d}+1.
   \]

   Its unary evaluator uses integer search. No machine computes an arbitrary real power. The case `ε≥1` poses no restriction; `d=2` is admissible.

2. The expanded output polynomial is `P(s)=a(s^d+1)^k+s+1`. Thus `P(s)>s` for **every** `s`, including zero, and

   \[
   m(n)=a(n+1)^k\le P(\ell(n)).
   \]

   The proof reuses truncation, `prg_expand`, the security reader, and the existing FP-evaluator interface.

3. At each bad seed length `s`, the advice argument chooses one offending input, of length at most `s^d`. It builds **one** non-uniform distinguisher for these choices. Beyond `max(N,12)`, security gives advantage at most `1/s≤1/12`, contradicting a selected bad gap. This is a uniform bound over all inputs at those seed parameters, not a separate negligible bound for each fixed input. Since `n≥S^d+1` implies `ℓ(n)>S`, it gives an input-length threshold. Multiple input lengths sharing a seed length are handled by the same existential bad-input selection.

4. Both the test and the width change at that threshold: true coins below it, generated prefixes above it. They are polynomial-time, with the threshold hard-coded; no exceptional-input table is used. The existing uniform-prefix and rational/real probability bridges apply also when the coin width is zero.

5. If `p` is true-coin acceptance and `q` is generated acceptance, the checked inequalities are

   \[
   |q-p|\le\frac1{12},\qquad
   x\in L\Rightarrow q\ge\frac23-\frac1{12}=\frac7{12}>\frac12,
   \]
   \[
   x\notin L\Rightarrow q\le\frac13+\frac1{12}=\frac5{12}<\frac12.
   \]

   Below the threshold the original bounds apply. `half_lt_randProb_iff` therefore identifies exactly the frozen strict-majority language.

6. The host corollary supplies time `2^{w(n)}(n+1)^e`. The root and logarithmic terms divided by `n^ε` tend to zero, so this time is eventually at most `2^{n^ε}`. The proof explicitly absorbs earlier lengths with `C=1+Σ_{i<K} 2^{w(i)}(i+1)^e`, using positivity of the rounded bound at every length. `DTIME.mono` and `DTIME_const_mul_subset` finish the transport. No monotonicity of the arbitrary exceptional widths is assumed.

## Rule 10, duplication, documentation, and axioms

I reconstructed all **80** strict/coe A/B probe cases from their insertion records. Their original sources agree with the pinned sources, except for the documented, code-identical pre-LE-doc version of `Classes.lean`. The **28** reused coe probes are byte-identical to their executed strict counterparts. The recorded chunked probes retain installation and EOF checks.

Both diagnostic forms, `error:` and `error(…)`, were counted from the raw logs. The only failing owner is `IterateFind`:

| Declaration | Head source lines, with multiplicity | Errors in each variant |
|---|---|---:|
| unchanged `polyTimeComputable_find` | 362×2, 380, 382, 389, 390, 433, 434, 539, 555, 556 | 11 |
| E1 `computesFunInTime_find` | 602×2, 622, 624, 631, 632, 676, 677, 799 | 9 |

The base has precisely the same 11 old failures after accounting for the three inserted documentation lines. The first eight E1 failures repeat the corresponding host field/state conversion failures; the ninth is the generalized final transport. **There is no additional failing declaration.** This is exactly F-01's attribution.

The canonical controls have **16 probes / 22 sealed negatives**, each negative failing exactly once and each positive passing. Strict controls have **20 / 33**, with exactly the two disclosed `ctlCoeReader` harness failures in sealed AdviceGap probes. The explicit-unfold scan's sole apparent foreign reference is the local polynomial `P`, misresolved to `Complexity.P`; the source confirms the shadowing.

The duplication review covered all 54 additions and their proof bodies, the worker's overlap table, the maintainer's added disclosures, the full pinned TCSlib source, the changed comparator files, and the relevant pinned Mathlib root lemmas. The independent statement screen finds **zero** exact normalized signature matches for the 46 new theorems, including the private one. The eight-line copy screen finds only the disclosed E1 repetition. These screens support, and do not replace, semantic review. The envelope and rank-count lemmas have the different contracts described in the pack; the root family uses Mathlib's root interface; the coin-map wrapper composes the existing efficiency/preimage interface; `short_poly` is the disclosed specialization. I found **no additional undisclosed re-proof or private copy**.

LE-doc is exactly one file, **+4/−4**, changing one `inBPP_iff` docstring while preserving code and line count. Its formula follows the reader's argument and conjunct order. The seven post-edit `NO-FORMULA` rows state FP/efficiency propositions adequately; the detector's missing relation symbol is not a documentation defect. The new public formulas and the **12** sketches for proofs of at least 15 lines agree with the delivered proof route. The eight new public definitions have readers. No new simp attribute or instance was found.

The independently parsed census has **202→320** stored constants, no removals or changed type hashes, and exactly three changed axiom sets: the three targets drop `sorryAx`. The head's axiom union is exactly `{propext, Classical.choice, Quot.sound}`. The targets, E1–E3, SR-01, and helper endpoints have only these standard axioms; the downstream `polyTimeComputable_iterateFind` evidence is unchanged. The admissions reduction is the expected **26→23**.

## Integration and disposition

The pinned current tip plus #324, #326, and #327 have pairwise disjoint code-path deltas. Independent code-tree overlays in all six orders agree. I matched **all 694** final build source hashes to the resulting Git blobs, verified their raw log hashes, and recounted diagnostics: **694/694 rc 0; zero errors**. Later records correctly override the 21 rebuilt #324 modules. The fifteen Gate 38 files, including post-LE-doc `Classes.lean`, are covered. The Mathlib overlay/retry is the disclosed F-05 environment repair.

The merge order with #324 last, and any rebuild required when the second PR merges, remain maintainer merge conditions. No additional intermediate-state build is requested by this audit. No concrete merged-code name, instance, or build interaction was found.

**Gate 38 closes at zero blockers and zero majors.** DW-5 remains recorded deferred work; dispatch and merge remain with the user.

## Evidence and notation

The accompanying ZIP contains this report, independent check scripts/results, the input manifests, source closure, and integration evidence. The original complete pack remains at the pinned exchange path `outbox/gates/38-derand-gate/`.

Notation used above: `n=|x|` is input length; `V` is the paired polynomial-time test; `w` is seed width; `R=2^{w(n)}` is the number of seeds; `a_i` is the number accepted before rank `i`; `B` is H17's common time/envelope budget; `m(n)=a(n+1)^k` is the verifier's original coin width; `d` is the fixed positive root degree; `ℓ(n)=ceilRoot d n`; `P` is the expanded output-length polynomial; `S,N,K` are the respective fixed thresholds in the cited arguments; `p,q` are the true/generated acceptance probabilities; other capital/lowercase coefficients in bounds are fixed natural constants.
