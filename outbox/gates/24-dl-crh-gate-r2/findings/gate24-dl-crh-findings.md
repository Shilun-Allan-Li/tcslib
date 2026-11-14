# Pass–shelat Gate 24 — dl-crh findings

**Verdict: HOLD.** One major duplication finding remains outside the supplied dispositions. No mathematical, frozen-statement, or Rule-10 defect was found. Two additional findings concern audit-record prose.

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 1 | 2 | 0 |

Audited [draft PR #307](https://github.com/Shilun-Allan-Li/tcslib/pull/307):

- Lean head: `649c4888f23fbb9df71d555e952d1149a0aaa00b`.
- PR base: `a757b6a18785377c158312ed051b1789cf45badf`.
- Records: `b01c150512fe6668ee6dddb1c6b429d1b9c822bf`.
- Exchange: `e7b9e53e4a41ffa84b52deb17d34d144877d31f3`, `outbox/gates/24-dl-crh-gate/`.

## Findings

Paths in this table are relative to the repository, except `pack.md` and `review.md`, which are relative to the gate pack.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G24-01 | **major** | `TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean:73` · `inputWord_take` | An additional public result is re-proved without a disposition covering the overlap. | It specializes public `TCSlib.Cryptography.take_ofFn_castLE`, `Asymptotic/ReductionSupport.lean:288`; the finite-index embeddings agree pointwise. See comparison below. DL-41 enumerates other restatements and omits this one. | Reuse the existing public proof, directly or through a thin reader, and recheck the affected imports/seals; alternatively obtain an explicit disposition covering this overlap. |
| G24-02 | minor | `review.md:92` · Content, step 2 | The review reverses the selector argument: it says equal images under **different** selectors are impossible. | With `p=3`, `m=2`, `g=2`, `z=0`, the distinct inputs `(0,false)` and `(0,true)` both hash to `1`. The Lean lemma and frozen target sketch correctly rule out collisions with **equal** selectors. | Append an erratum to the gate record, preserving the frozen review. |
| G24-03 | minor | `pack.md:99–100` · ruling 3 | The claim that FAIL and WARN lines are identical, with an empty r3 diff, contradicts the archived evidence. | `ledoc-evidence.zip/logs/lint-crypto-tip-vs-head-r3.diff` is **674 bytes**. Two `DiscreteLog` WARN lines change: size `1192 → 1212`, and the missing-reader count `6 → 5` after adding `expSampleRaw_eq`. FAIL lines are identical; counts remain `92 FAIL / 102 WARN`. | Correct the description to distinguish unchanged FAIL lines from these two accepted WARN changes. |

### G24-01: exact overlap and its disposition

The existing public lemma states

```lean
theorem take_ofFn_castLE {ℓ m : ℕ} (h : m ≤ ℓ) (f : Fin ℓ → Bool) :
    (List.ofFn f).take m = List.ofFn fun i : Fin m => f (Fin.castLE h i)
```

Specialize its bounds to `n+1` and `n`, with proof `Nat.le_succ n`. For every `j : Fin n`,

\[
\bigl(\mathrm{Fin.castLE}\;(\mathrm{Nat.le\_succ}\;n)\;j\bigr).\mathrm{val}
=j.\mathrm{val}
=(j.\mathrm{castSucc}).\mathrm{val}.
\]

`Fin.ext` identifies the embeddings, so this specialization gives exactly

```lean
(List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc)
```

The new reader instead derives this again from `inputWord_split` and `List.take_left'`. The existing result is present at the pinned head and is unchanged by this PR. Its file has Git blob `a314f02fe231ef4a64f02a7b68f53fd520760469` and SHA-256 `e79e05e05d01a6fff4e9d65970aa9e73ad457c9455b1ff987971c4eab7210934`.

The issued brief forbids copying public lemmas, and policy §1 requires explicit approval for duplicated proved material. The worker lists `inputWord_take` as a promotion candidate, but does not disclose this public overlap. Neither the pinned DL-41 row nor `evidence/PROMOTION.md` identifies `take_ofFn_castLE`. Listing a promotion destination does not record acceptance of this additional re-proof. The major concerns that missing disposition; the lemma itself is true.

## Proof and integrity checks

The proof matches [PS10, Protocol 142.2 and Theorem 142.3, pp. 142–143](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf), with the frozen, documented restriction on exponent inputs.

1. **Compression.** At generated indices above `G.n₀`, validity and well-formedness give `m>0`, exact output width `n`, and
   \[
   |D|=2m,\qquad |R|=p-1=m<2m.
   \]
   The evaluator writes a unit residue, so it lands in the specified range.
2. **Extraction.** Equal selectors permit cancellation; injectivity on bounded exponents then contradicts distinctness. For different selectors,
   \[
   z=\begin{cases}
   (x'+m-x)\bmod m,&b=1,\\
   (x+m-x')\bmod m,&b=0.
   \end{cases}
   \]
   The formal formulas use `x' + (m - x)` or `x + (m - x')`; the domain guards justify these subtractions. Equal exponent prefixes and the zero challenge are included.
3. **Reduction.** `collisionPost_split` covers arbitrary raw outputs using the collision game's padding/truncation. Exact hash-output lengths justify removing output padding. The polynomial-time reduction retains the finder's coins and advice and decodes the recovered exponent exactly.
4. **Probability.** Coin equivalences preserve independence. The published sampler law, including fallback zero and auxiliary finder coins, gives, for `n ≥ G.n₀`,
   \[
   \Pr[A\text{ collides}]\le G.\mathrm{dlProb}(B,n)+2^{-n}.
   \]
   Applying `hDL` to this concrete reduction and eventual domination proves negligible acceptance. Choosing actual acceptance as the negligible upper bound covers every parameter. Compression is eventual by its frozen definition; no arbitrary invalid-index claim is required.

| Check | Result |
|---|---|
| Pack integrity | **15/15** top-level SHA-256 entries verified. `verification.zip` has exactly its 44 manifested payloads plus its manifest. Nested review and LE-doc archives verify **478/478** and **128/128** entries, with exact member sets. |
| Pinned content | All **126** source-closure files match Git blobs in head tree `1d9f6d52d136f8bc8229bfaffe3c714aadb5eebd`. The six-patch series applies to independently retrieved base bytes and reproduces all **9** changed files exactly. |
| Freeze and exceptions | All **128** pre-existing declaration headers are byte-identical; pre-existing bodies other than the target are unchanged. The target docstring is unchanged. `DiscreteLog` gains exactly the two approved `rfl` readers and their documentation. The facade adds exactly six imports; its import graph is acyclic. |
| LE-doc | Removing doc comments leaves identical bytes in all **8** edited files. All **59** new formulas were compared with their declarations; no formula error found. The archived docaudit records **68/68 OK**. |
| Rule 10 | Independently reconstructed **48** head/base, strict/coercion, A/B and facade probe inputs. Requested sets equal the conservative closure inventories and cover elaborated-term references and matchers. Their source/log hashes and successful runs agree. All **12** controls match expectations: **21** sealed negatives fail once each, reader controls pass, and no stray errors occur. The archived explicit scan has 595 items and zero foreign-definition reads. |
| Axioms and admissions | Census **172 → 265**, with pre-existing types and attributes retained, no new simp attributes, instances or abbreviations, and only standard axioms. The target loses `sorryAx`; the issued-module admission census is **22 → 21**, solely the target. |
| Build evidence | All **22** final build rows have pinned source bytes, matching raw-log hashes, rc 0, zero errors and zero sorries. The archived **1207-module** object snapshot agrees with its latest successful run records. |
| Existing dispositions | DL-41's listed overlaps, the accepted `DiscreteLog` size/split follow-up, the projection-coercion ruling and the two disclosed review slips were not re-raised. |

**Verification limit:** no fresh Lean compilation was performed; this environment has no Lean executable. Compilation and seal execution conclusions use the authenticated archived runs, supplemented by independent source, patch, closure, census, control-log and hash checks. The archived object snapshot was checked for internal consistency; its oleans were not re-executed locally.

**Gate action:** hold for G24-01 until the public proof is reused or the additional overlap receives an explicit disposition. G24-02 and G24-03 are nonblocking record corrections. The user dispatches and merges; no repository changes or GitHub messages were made.

**Notation:** `n` is the security parameter; `i` a group index; `p=dlP i`, `m=dlM i=p−1`, and `g=dlG i`; `z` is the canonical challenge exponent; `x,x'` are bounded exponents and `b` the first selector; `D,R` are domain and range; `A` is the collision finder and `B=collisionReduction H A`; `G` is the instance generator and `H` the arithmetic bundle; `j` is a finite index. In the quoted existing lemma, `ℓ,m` are generic vector bounds, `h` their comparison proof, `f` a bit vector, and `i` its finite index.
