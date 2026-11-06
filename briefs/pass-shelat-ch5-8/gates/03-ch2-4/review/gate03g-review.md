# Gate 03g: review of the auditor's findings (3-colouring zero knowledge)

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03g-findings.md` (SHA-256
  `09f34930…f7f1f2`, filed in `e6ffd681`). It has 110 rows: 6 findings (2 majors, 4 minors) and 104
  notes. The notes cover the admission verdicts, adversarial tests and declaration coverage.
- **Pack:** `03g-pack.md` (SHA-256 `945f565e…297066`), with the common brief `03a-pack.md`.
- **Code:** worktree `wt-g03c-fix` at `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (checked with
  `git rev-parse`). Line numbers are at that commit unless marked "HEAD".
- **Since the pin:** the branch head is `559c3624`. #203 changed one proof line in this pack's files,
  `ThreeColoring/Machines.lean:126`: `polyTimeComputable_stateFind` became
  `EncodingMachines.polyTimeComputable_stateFind`, so lines after 126 move down by one.
  - It affects no finding. Only the line numbers of the auditor's Machines.lean notes (rows 33–45)
    are one too low at HEAD.
  - `Simulator.lean` and `Language.lean` are identical at the pin and at HEAD.
  - #203 also adds `NUPPT.exists_compParam` (Closure.lean). The fixes below may use it, but do not
    need it.
  - The records changed after the pin (`e79397ea`: DESIGN §5 items 8 and 11, §7 item 51;
    `559c3624`: D3). Row 6's complaints still hold at HEAD (see #6).
- **Source:** `pass-shelat-2010-ch4.raw.md`. I also looked at PDF pp. 140–141 (book pp. 128–129),
  rendered from `Pass–Shelat.pdf`, to check Algorithm 128.7 steps 4–5 and the S′/S″ wording.
- **Downstream:** `wt-prong-{a,b,c,d,d2}` and `wt-s2b` were grepped for `col_zk`, `colProtocol`,
  `R3COL` and `ThreeColoring`. Only facade imports were found. Prong C's `ZK.seqRep`
  (`SequentialZK.lean:376`) is the planned consumer: the gate-06 corollary in the decision log,
  2026-11-05.
- **Arithmetic:** `scratchpad/g03rev2/tools/arith.py`, run with `python3 -I`. It enumerated every
  3-colourable symmetric loopless graph on 0–5 vertices, the complete tripartite family, the
  `comp_sqrt` thresholds for c ≤ 5 and n₀ ≤ 5, `Nat.size` at powers of two, and the sampler failure
  rates.
- **Not done:** no Lean was built or run. The Lean-level fix sketches below are unchecked.

## Summary

- **Verdicts:** 6 true and 0 false; 0 partly true. Two of the true findings are understated:
  - #2 is worse than stated. The sketch's machine cannot match the ideal reduction even in law (see #2).
  - #5's misattribution also appears at three more sites.
- **The key question: is `col_zk` provable as stated in its declared D8 scope? Yes.** I found no
  counterexample, and I can give a complete corrected argument (§#1–#2). Both majors are defects of
  the **proof sketch only**. No statement, interface or signature changes.
  - The other two admissions, `R3COL_witnessRelation` and `colRep_efficientProverProof`, are true
    as stated. I agree with the auditor's verdict (a) for both.
  - On `col_zk` the auditor gives (b): "weaker than the source's literal all-z wording". The
    literal reading is **false** for this protocol, so no stronger true statement exists. I record
    `col_zk` as **(a) in its declared D8 scope**. The (b) only means "weaker than an unprovable
    literal reading", and it should not be read as debt. Note 9 below has the triangle
    counterexample.
- **Severity:** I agree with all six (2 majors, 4 minors).
  - #1 and #2 stay majors. Policy §3 says "the sketch *is* the plan" for a sorry-stub, and this
    pack gates the fills. The sketch of the chapter's hardest theorem contains a false inequality
    (#1) and an impossible identification (#2). Pack question 3 asks exactly whether the bound
    reduces to hiding "as the sketch claims", and the answer is no. Precedent: 03a r2 R2-2 and
    03f1 #1 were docstring and sketch claims rated major.
  - Both majors have one-paragraph fixes, using lemmas the library already has.
- **Fixes, in order of importance:**
  1. Rewrite `col_zk`'s proof sketch (`Simulator.lean:727–763`). Use the text in §#2.3 (it covers
     #1, #2, the m = 0 and N = 0 cases, and M1). The leading term becomes `N² · ε_B(⌊√N⌋)`. The
     hiding reduction fixes the ideal attempt table by `CommitmentLemmas.exists_fixCoins`, so the
     machine `B` is deterministic in the challenge, apart from `D`'s coins: one call of `V'`, one
     call of `D`.
  2. Fix the truncation attribution: `colSim` (#5), and also `Simulator.lean:34–36`, `:722`, and
     `inventory-ch4.md:30–31`.
  3. Fix the records (#6): DESIGN D8, §5 item 11, an as-built note under §2.15, and inventory
     Thm-124.1 (A), Claim-124.d and Def-124.a.
  4. Fix the docstrings of `Negligible.comp_sqrt` (#3) and `sampleEdgeIdx` (#4).
  5. Quote the S′/S″ typo faithfully (M2).
  6. For the fill brief: give the sorry ladder in M3.
- **Rulings needed: none.** No fix changes a statement or an interface, and none accepts new debt.
  - The bounded-auxiliary-input scope of `ZK` was already ruled and recorded: D8, Q-1, the
    `Defs.lean` module docstring, and DESIGN §7 item 51.
  - The choice between the two bridges for #2 is a proof strategy, so it is the maintainer's call.
    I recommend the fixed-coin bridge.
- **Ripple:** none to statements.
  - `Checks.lean` keeps its prints. `col_zk` prints `sorryAx` until the fill lands.
  - `NP.lean`'s form (A) and its tied and untied variants (pack 03e) are unchanged.
  - Prong C's planned `ZK.seqRep` corollary is unchanged.
  - The 03g fill brief must carry the corrected sketch and the ladder of M3.

## Overview

| # | Auditor | Verdict | Severity | Fix kind | Packs / prongs touched | Ruling? |
|---|---|---|---|---|---|---|
| 1 | major | true | **major** (agree) | sketch rewrite (`Simulator.lean:739–759`) | 03g only; fill brief | no |
| 2 | major | true, **understated** | **major** (agree) | sketch rewrite (`Simulator.lean:727–738, 756–759`) | 03g only; fill brief | no |
| 3 | minor | true | minor | docstring (`Simulator.lean:679–681`) | none | no |
| 4 | minor | true | minor | docstring (`Language.lean:303–305`) | none | no |
| 5 | minor | true, **understated** (3 more sites) | minor | docstrings + inventory | 03g; inventory ch. 4 | no |
| 6 | minor | true (still true at HEAD) | minor | records | 03e's §2.15 record; 03k reads D8 | no |
| M1 | — | missed | (folded into #1) | sketch | 03g | no |
| M2 | — | missed | minor | docstring + DESIGN §7 item 46 | 03g | no |
| M3 | — | missed | note | fill brief (sorry ladder) | 03g fill | no |
| M4 | — | missed | note | optional move | 03g / clean-up | no |

---

## #1 (major): the attempt-count loss in `col_zk`'s sketch

### Verdict: **true**

- The sketch (`Simulator.lean:756–759`) concludes step (4) with
  "`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`". On a yes-instance `|x| = n²`, so this asserts `n·m ≤ n²`,
  i.e. `m ≤ n`. But `m = edgeCount G` counts **ordered** adjacencies (run-3 P11-3).
- The auditor's triangle checks: `n = 3`, `m = 6`, `N = 9`, `K = n m = 18`.
- So does `K_{t,t,t}`: `n = 3t`, `m = 6t²`, `N = 9t²`, `K = 18t³`, `K/N = 2t` (computed for
  t = 1…4). The ratio is unbounded, so no constant repairs the bound.
- The failure is the rule, not an edge case. Among 3-colourable graphs, `nm > N` holds for 4 of 8
  graphs on 3 vertices, 41 of 63 on 4, and 902 of 958 on 5 (enumeration).
- The sketch is also internally inconsistent: for the sampler term it already uses `N²`
  (`2 N² (1/4)^N + N² (1/2)^N`, :739), which is the right majorant.
- The loss is genuinely `K`. `exists_colSimRed_ge` (:551) divides by the attempt count, and
  `exists_hybRed_ge` cannot avoid that factor.
- **The statement is unaffected.** `ZK` has `∃ ε`, so only the named `ε` changes.

### Recomputed bound

`K = n m ≤ n · n² = n³ ≤ n⁴ = N²` for `n ≥ 1` (and `K = 0` at `n = 0`). This was checked on every
enumerated graph. Two further points matter for the fill:

- **ε_B is nonnegative.** The step `K ε_B(n) ≤ N² ε_B(n)` needs `ε_B(n) ≥ 0` at every `n`.
  - `hC.multiHiding var B` bounds a `distAdv` (an absolute value) for all `n`-vectors, and vectors
    exist at every `n`. So `0 ≤ ε_B n` follows from the conclusion at `v = v'`.
  - The sketch should say so.
- **Under a "worst instance" choice, the factor must be the uniform majorant `n³`.**
  - If `B` hard-wires the instance that maximizes the hybrid advantage, a different instance `x'`
    at the same vertex count is bounded through the hard-wired instance's `K`, not its own.
  - So the multiplier must be the uniform `n³` (or `N²`), not "the instance's `n m`". With the
    choice of §#2.3, which maximizes the reduction's gap, either works.

The corrected error function is:

```
ε N := N² · ε_B (Nat.sqrt N) + Real.exp (-(Nat.sqrt N : ℝ)) + N² · ((1/2)^N + (1/4)^N) + (1/4)^N
```

Its terms are:
- step (4) and the `m = 0` case: `≤ K ε_B(n) ≤ N² ε_B(√N)` for `n ≥ 1`;
- step (5): `(1 − 1/m)^K ≤ e^{−n}`;
- step (2): `K(2^{−N} + 4^{−N}) ≤ N²(…)`. The edge sampler accepts with probability at least 1/2
  (minimum 1/2 at powers of two); the colour-pair sampler fails with probability 2/8 = 1/4;
- step (1): `4^{−N}`, the same rate for `samplePerm3`.

The sketch's `2 N² (1/4)^N` was slack; one `N²(1/4)^N` suffices.

- **Negligible** by `Negligible.mul_pow (Negligible.comp_sqrt hε_B) 2`,
  `negligible_exp_neg_sqrt_div` (C = 1), `Negligible.mul_pow negligible_two_pow_neg 2`,
  `(1/4)^N ≤ (1/2)^N` with `Negligible.mono`, and `Negligible.add`.
- **At N = 0** the exponential term is 1, which bounds every advantage. This matters (M1).

A tighter alternative is `N · Nat.sqrt N · ε_B(Nat.sqrt N)`, i.e. `n³ ε_B(n)`. It is optional.

### Severity: **major** (agree)

The step is load-bearing in the plan of a sorried theorem, it is false for most inputs, and the
pack's question 3 asks exactly this. Fixing it takes one line, but as it stands it misleads.

### Fix

`Simulator.lean:739` and `:759`: replace the leading `N · ε_B (Nat.sqrt N)` by
`N² · ε_B (Nat.sqrt N)`, and the chain "`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`" by
"`≤ n m ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` (`n ≥ 1`, `0 ≤ ε_B`)". The full replacement
paragraph is in §#2.3.

### Ripple

None outside the sketch.
- The pack's question 3 quotes the old bound. The closing pack should quote the new one.
- The inventory's Prop-128.8 and Claim-129.d already state the correct `(n·m) · ε_Com`
  (`inventory-ch4.md:693, :729`). Nothing else repeats `|x| ε_B(√|x|)`: grep over briefs, TCSlib
  and audits.

---

## #2 (major): the bridge from the ideal reduction to a machine

### Verdict: **true, and understated**

- **What the auditor says, which checks.**
  - `colSimRed`'s coin type (`Simulator.lean:404–413`) is
    `(Fin K → ((Fin m × Perm (Fin 3)) × (Fin n → Fin ℓ(n) → Bool)) × ρ) × ρ'`.
  - Its cardinality `(6 m 2^{nℓ(n)} |ρ|)^K |ρ'|` is divisible by 3 for `K ≥ 1`, while a fair-bit
    tape has `2^b` elements.
  - So no `Equiv` exists, and `acceptProb_comp_equiv` cannot give
    "`colSimRed … = B.distinguisherL n` up to the coin bijection" (:758).
- **What is worse.** The identification is impossible even as an equality of acceptance
  probabilities, not just as a coin bijection.
  - A fair-coin machine's acceptance probability is dyadic.
  - The ideal reduction's probabilities are generally not. A `D'` that accepts when the colour opened
    at the first endpoint of a later `S′` attempt is 0 gives terms of `Pr_π[π(a) = 0] = 1/3`, mixed
    with weights in `1/m`.
  - So no "same law" argument of any form can bridge. The bridge must be an **inequality** (fix the
    coins) or an **approximation** (re-sample the coins, with an error term).
- **The sketch's machine is the lossy variant without its error term.**
  - The sketch builds `B` with "coins … the other attempts' blocks and `D`'s coins
    (`NUPPT.exists_split`)", runs the attempts with `polyTimeComputable_iterateFind`, and samples
    them from fair bits (:733–735).
  - That machine's acceptance differs from `colSimRed`'s by up to `(K − 1)·(edge-sampler error +
    permutation-sampler error)` on each challenge distribution. After multiplication by `K` this
    becomes a `~K²δ` term, and the ε of :739 has no such term.
  - The simulator's own sampler error (step 2) is a different term, as the auditor says.
- **The admitted statement is unaffected.** The repair below is lossless and uses only existing
  lemmas and closure facts. No new cryptographic hypothesis is needed.

### 2.1 Recommended repair: fix the ideal coins (lossless; the library's own idiom)

1. **Average out the attempt table.** Apply `CommitmentLemmas.exists_fixCoins`
   (`CommitmentLemmas.lean:108`), with `κ :=` the attempt table and `ρ :=` `D`'s coins, to
   `colSimRed … k e₀ π₀ D'`.
   - Some table `w₀` satisfies `distAdv X Y colSimRed ≤ distAdv X Y (colSimRed with w₀ fixed)`.
   - `Commitment.multiHiding` itself is proved this way (its sketch, `Commitment.lean:385–388`).
2. **With `w₀` fixed, only attempt `k` reads the challenge.**
   - Attempts `t < k` (`colSimAttemptH`) and `t > k` (`colSimAttemptW`) depend only on `w₀ t`.
   - So the fixed reduction is `cv ↦ D'(pre <|> colSimAttemptPlanted … cv (w₀ k) <|> post, ·)`,
     where `pre` and `post` are the first successes among attempts `< k` and `> k`. Both are
     constants.
   - The machine needs no loop over attempts and no `K`-entry table: one call of `V'` on the spliced
     commitment vector and one call of `D`.
   - The auditor's version (hard-wire the whole table, `≤ n³` entries) is also correct, but it is
     needlessly heavy.
3. **Choose the worst data, at each `n`.** The data are: a graph on `n` vertices, a proper `c`,
   `z` with `|z| ≤ Lz(n²)`, `k`, `e₀`, `π₀` and `w₀` (or the `m = 0` data below). Choose those that
   maximize the fixed reduction's gap on its own vectors `X`, `Y`.
   - **The set is finite only because `|z|` is bounded.** This is where `Lz` is used (the `Defs.lean`
     module docstring), and the sketch should say so.
4. **Build `B` at parameter `n`.**
   - Advice: `x`, `z`, a case flag, `ρ_k`, `e₀`, the two endpoint commitments with their openings,
     `pre`, `post`, and `D.advice (n²)`.
     - The length is polynomial in `n`. Every view is polynomially bounded:
       `hC.easy.output_length_le`, `colProtocol_proverBounded`, `|z| ≤ Lz(n²)`.
     - The advice polynomial printed at :731 omits the pairing overhead and every component after
       the instance, so it must be redone.
   - Coins: `D`'s at parameter `n²`, by `NUPPT.exists_reparam_advice` with `φ n = n²`,
     `p = mul var var`; then `B.coinLen n = D.coinLen (n²)` exactly.
   - Computation: `B` splices `cv` with `msgAt`. It evaluates `V'.next x z ρ_k [com]` through the
     uniform machine of `Strategy.Efficient` (`A.polyTimeComputable_output` on the
     `⟨⟨x, z⟩, encodeMsgs [com]⟩` layout), compares `edgeIdxOfMsg m` with `e₀`, and runs `D`.
   - It is packaged by `NUPPT.ofPolyTime` and `exists_withAdvice`, or by `exists_compParam` at HEAD.
5. **Transport the coins.** `B`'s acceptance on `multiCom` samples equals the fixed reduction's.
   - Use `acceptProb_distinguisherL_of_runAtL` (`CommitmentLemmas.lean:143`) in a two-parameter
     form (`B` at `n`, `D` at `n²`, `B.coinLen n = D.coinLen (n²)`).
   - That is a small new glue lemma, or `EnsembleLemmas.acceptProb_coins_equiv` along `finCongr`.
     The coin types here are bits on both sides, so this equivalence exists.
6. `hC.multiHiding var B` gives `ε_B`. The hybrid term is at most `K ε_B(n)`, as in #1.

### 2.2 Alternative: re-sample inside `B` (lossy)

`B` samples the other attempts with fair-bit rejection samplers (`T` trials each). Then
`|gap_B − gap_ideal| ≤ 2(K − 1)(2^{−T} + 4^{−T})`, and step (4) gains `2K(K−1)(2^{−T} + 4^{−T})`.
This is negligible for `T = n²`. It is correct, but it needs the `iterateFind` loop and an extra
term. I do not recommend it.

### 2.3 The corrected sketch (replacement for `Simulator.lean:727–763`)

> **Proof sketch.** Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy`, and fix `Lz`
> and `D`. For `x = encGraph G`, `y = encColoring c` with `c` proper and `|z| ≤ Lz |x|`, let `n` be
> the vertex count, `m = |E|`, `K = n m ≤ n³`, and `D'` the distinguisher `D.distinguisherL |x|`
> on the encoded optional view (`⊥ ↦ []`).
>
> (1) The real view, with `π = samplePerm3 |x| …`, is within `(1/4)^{|x|}` of the view with a
> uniform `π`: `statClose_samplePerm3`, `StatClose.prod`/`StatClose.refl` for the prover's
> randomness and `V'`'s tape, and `StatClose.map`. `exec_succ` three times, `decGraph_encGraph`,
> `decColoring_encColoring`, and `colProver` with `V com r_V := V'.next x z r_V [com]` unfold it to
> `some ∘ colRealView`.
>
> If `m > 0`:
> (2) `colSim` is within `K((1/2)^{|x|} + (1/4)^{|x|})` of `colSimTrunc … K`, with uniform
> `(e'_t, (a_t, b_t))` read from disjoint fields of the `t`-th block (`statClose_sampleEdgeIdx`,
> `statClose_sampleColorPair`, `StatClose.prod` over the blocks).
> (3) `uprob_colSimTruncW_eq`.
> (4) `exists_colSimRed_ge` with `N := K` gives `k, e₀, π₀` with
> `distAdv truncW truncH D' ≤ K · distAdv X Y (colSimRed … k e₀ π₀ D')`.
> `CommitmentLemmas.exists_fixCoins` fixes the reduction's attempt table `w₀` without loss.
> With `w₀` fixed, only attempt `k` reads the challenge `cv`, so the fixed reduction is
> `cv ↦ D'(pre <|> planted cv <|> post)` for two constant optional views.
> (5) `statClose_colSimTruncH` and `one_sub_inv_pow_mul_le_exp` give
> `distAdv truncH (some ∘ colRealView) D' ≤ e^{−n}`.
>
> If `m = 0` and `n ≥ 1`, the two views differ only in the commitment vector (`π ∘ c` against
> `0`). For each fixed `π`, `D`'s advantage is the hiding gap of `cv ↦ D(encode ⟨x, z, r_V, [cv, []]⟩)`,
> with `r_V` fixed by `exists_fixCoins`. Average over `π`.
> If `n = 0`, bound the advantage by `1`: the simulator's tape is empty, so its `r_V = []` differs
> from the real tape when `V'.coinLen 0 > 0`.
>
> The machine `B` at parameter `n`: among the finitely many data at vertex count `n` (finite
> because `|z| ≤ Lz(n²)`), take those whose fixed reduction (either case) has the largest gap on
> its own vectors. Hard-wire `x`, `z`, the case, `ρ_k`, `e₀`, the two endpoint commitments and
> openings, `pre`, `post` and `D.advice (n²)` as advice (`NUPPT.exists_withAdvice`; polynomially
> bounded by `hC.easy.output_length_le` and `colProtocol_proverBounded`). Call `V'`'s uniform
> machine once (`Strategy.Efficient`) and `D` at parameter `n²` on `B`'s coins
> (`NUPPT.exists_reparam_advice`, `φ n = n²`). Its acceptance probabilities on `multiCom` samples
> are the fixed reduction's (coin transport along `finCongr`).
> `hC.multiHiding var B` gives a negligible `ε_B ≥ 0` (it bounds a `distAdv` at every `n`), so the
> hiding terms are at most `K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`.
>
> Put `ε N := N² ε_B (Nat.sqrt N) + exp (−Nat.sqrt N) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`. It is
> negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div` (`C = 1`),
> `negligible_two_pow_neg` and `Negligible.add`. At `N = 0` its exponential term is `1`. Use the
> triangle inequality for `distAdv` (`abs_sub_le`), and `Nat.sqrt |x| = n`
> (`length_encGraph`, `Nat.sqrt_eq`).

### Severity: **major** (agree)

As written, the sketch specifies a machine whose analysis cannot be completed, and the error
budget is missing a term. The repair is standard, but the fill would otherwise have to discover it.

### Ripple

- None to statements.
- The fill needs two or three new lemmas (M3). `ColSimLemmas` and `CommitmentLemmas` keep their
  statements.
- If a two-parameter coin-transport lemma is added, ledger it next to
  `acceptProb_distinguisherL_of_runAtL` (duplication ledger), and do not keep a private copy.

---

## #3 (minor): `Negligible.comp_sqrt`'s printed threshold

### Verdict: **true**

- The sketch (`Simulator.lean:679–681`) takes `N ≥ max((n₀+1)², 4^c·4)`, then needs
  `⌊√N⌋ ≥ 4^c`.
- From `N ≥ 4^{c+1}` one only gets `√N ≥ 2^{c+1}`, which is `≥ 4^c` only for `c ≤ 1`.
- The auditor's `c = 3`, `n₀ = 1` (`N = 256`, `√N = 16 < 64`) checks. The enumeration shows the
  first failure at `c = 2` (`N = 64`, `√N = 8 < 16`).
- The code (:686–687) uses `K := max (max n₀ (4^c)) 1` and threshold `K * K`, which is correct
  (checked on samples).

### Severity: minor (agree)

The sketch of a proved lemma disagrees with its proof; this is the 03b #4 precedent.

### Fix

`Simulator.lean:679–681`:

> "Given `c`, take `n₀` from `hμ (2c + 1)`, `K := max (n₀, 4^c, 1)` and `N ≥ K²`:
> `n := Nat.sqrt N ≥ K` (`Nat.le_sqrt`), so `n ≥ n₀`, `n ≥ 4^c`, `n ≥ 1`, and
> `N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`); hence `N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` and
> `|μ n| < 1/n^{2c+1} ≤ 1/N^c`."

### Ripple

None.

---

## #4 (minor): `sampleEdgeIdx`'s bit-width bound

### Verdict: **true**

- `Language.lean:303–305` says "(so that `m ≤ 2^k < 2m`, success probability `≥ 1/2`)" with
  `k = Nat.size m`.
- For `m = 2^j`, `2^{size m} = 2m` (`m = 1, 2, 4, 8` checked), so the strict bound fails.
- For `m = 0`, it reads `0 ≤ 1 < 0`.
- The correct bound, `m < 2^k ≤ 2m` for `m ≥ 1`, holds for `m ≤ 5000`. It is what
  `statClose_sampleEdgeIdx` proves and uses (`h2 : 2 ^ Nat.size m ≤ 2 * m`, :397–401).

### Severity: minor (agree)

### Fix

`Language.lean:304`: "(for `m > 0`, `m < 2^k ≤ 2m`, so each trial succeeds with probability
`≥ 1/2`; for `m = 0` the sampler returns the default)".

### Ripple

None.

---

## #5 (minor): truncation attributed as a deviation from Algorithm 128.7

### Verdict: **true, and understated**

- PDF p. 140 (book p. 128), Algorithm 128.7:
  - step 4: "Otherwise, restart the process from the first step, but at most n|E| times";
  - step 5: "If, after n|E| repetitions the simulation has not been successful, output fail."
- The same misattribution as `colSim`'s docstring (`Simulator.lean:636–637`) appears at:
  - `Simulator.lean:34–36` (module docstring): "the simulator is strict PPT, truncated at `n|E|`
    attempts … which costs the statistical term";
  - `Simulator.lean:722`, `col_zk`'s deviation: "strict PPT simulator truncated at `n|E|`
    attempts";
  - `inventory-ch4.md:30–31` (HEAD): "The two rewinding simulators (123.4, 128.7) are truncated at
    `n` resp. `n·|E|` attempts".
- GI's Algorithm 123.4 does restart until success (PDF raw text lines 603–604, "expected
  polynomial time"), so there the truncation **is** a deviation. Keep it.
- For 3COL, the `(1−1/|E|)^{n|E|}` cost is the text's own `O(e^{−n})` term.
- The real deviations are the rejection-sampled `e'`, colour pair and `π` (D10), and `ZK`'s strict
  simulators, which are a property of the definition (Def 121.2 allows expected time).

### Severity: minor (agree)

This is an attribution defect.

### Fix

- **`Simulator.lean:636–637`**: "As in [PS10, Algorithm 128.7, steps 4–5], at most `n|E|`
  attempts, then `fail` (`⊥ = []`). **Deviation (D10):** `e'` and the colour pair are
  rejection-sampled from the tape (defaults `0` and `(0, 1)`)."
- **`:34–36`**: "the simulator makes at most `n|E|` attempts and outputs `⊥ = []` on failure, as the
  text does (Algorithm 128.7, steps 4–5); the failure costs the text's own term
  `(1 − 1/|E|)^{n|E|} ≤ e^{−n}`."
- **`:722`**: delete "truncated at `n|E|` attempts". Keep "strict PPT simulator", attributed to D8's
  definition of `ZK`.
- **`inventory-ch4.md:30–31`**: "The GI simulator (123.4) is truncated at `n` attempts (D8); the
  3COL simulator (128.7) already stops after `n·|E|` attempts in the text."

### Ripple

- 03k is unaffected: GI's truncation stays declared.
- The inventory's Alg-128.7 row (:205) is already right.

---

## #6 (minor): records out of sync

### Verdict: **true, and still true at HEAD**

- **D8** (DESIGN.md:136–140 HEAD): "GI and 3COL are proved statistically (truncated simulators,
  rejection-sampled permutations) … statistical instead of perfect ZK". `col_zk` is computational
  `ZK` from `Commitment.multiHiding`.
- **§5 item 11** (:1055 HEAD) still opens "GI/3COL: statistical ZK". `e79397ea` added the
  PerfectZK text but kept this.
- **§2.15** (:879–892 HEAD) prints `InteractiveProof.complete` without the message bound and
  `EfficientProverProof` without `boundedP`. The code has both (`InteractiveProofs.lean:126–128`,
  and the `boundedP` field).
  - §5 item 8 was synced after the pin; §2.15 was not.
- **Inventory:**
  - Thm-124.1 (A) (`inventory-ch4.md:535–539`) says "the composed protocol … is a ZK proof with
    efficient prover", with no `hLR`. `zk_proof_of_levinReduction` (`NP.lean:584–592`) gives two
    protocols (the repeated one, a proof; the single one, ZK) and needs `hLR`.
  - Claim-124.d (:563ff) omits `hLR` for the completeness transfer.
  - Def-124.a (:548–551) omits `length_eq` and `le_eval` (`NP.lean:145–147`).

### Severity: minor (agree)

These are records only. The Lean statements are right.

### Fix

- **D8:** "GI is proved statistically (`gi_statZK`: truncated simulator, rejection-sampled
  permutations); 3COL is computational ZK from the commitment's hiding (`col_zk`), its simulator
  stopping after `n|E|` attempts as in the text".
- **§5 item 11:** "GI: statistical ZK (…); 3COL: computational ZK (`col_zk`, via
  `Commitment.multiHiding`; rejection-sampled edges, colour pairs and colour permutations)".
- **§2.15:** do not edit the frozen block. Append an "As-built note (gate 03g, #6)", as §2.4 and §2.6
  do, giving the G3-3 signatures of `complete` and `boundedP`.
- **Inventory:**
  - Thm-124.1 (A): add `hLR`, and say "the pulled-back repeated protocol is an interactive proof
    with efficient prover and the pulled-back single iteration is ZK (DQ5)".
  - Claim-124.d: add `hLR`.
  - Def-124.a: add `length_eq` and `le_eval`.

### Ripple

- §2.15 is 03e's interface record. Note the as-built line in 03e's closing record.
- D8's GI sentence is unchanged, so 03k is unaffected.

---

## The notes (rows 7–110): checked, with one disagreement

- **Row 7, `R3COL_witnessRelation`: (a), agree.** Only `decidable` is sorried (`Protocol.lean:838`).
  The re-encoding decider is polynomial in `|⟨x, y⟩|`, including long `y`, since it reads only `2n`
  bits.
- **Row 8, `colRep_efficientProverProof`: (a), agree.**
  - I re-traced the layout (`Protocol.lean:458–504`): four moves per iteration; challenges on odd
    history counts from block `t` of `(|x|+1)²` bits; the verdict at `2|x|²`.
  - The sketch's soundness error checks: `ε N = exp(−√N) + N²(1/2)^N + 2^{−N}`.
    `(1−1/m)^{nm} ≤ e^{−n}`, and `K·2^{−N} ≤ N²2^{−N}` with `T = N` trials per block.
  - The extra `2^{−N}` makes the strict inequality hold, including the always-reject cases.
- **Row 9, `col_zk`: verdict (b) is technically right, but should read (a) in the declared
  scope.** The literal source reading (all `z`, `D` polynomial in its input) is false here.
  - Take the triangle and `|z| ≥ 2^{ℓ(n)}·poly`. `D` brute-forces every commitment in the view,
    which binding makes uniquely openable, and accepts iff all three committed colours are distinct.
  - The real view gives probability 1. The simulated view gives `Pr[{a, b} = {1, 2}] = 1/3`.
  - The `Lz` bound is therefore necessary (`Defs.lean` module docstring at the pin; DESIGN §7 item 51
    at HEAD). The source's `V*` is "p.p.t." (Def 121.2), i.e. uniform, as `V'.Efficient` is.
- **Rows 10–12** (adversarial instances): agree.
  - The total challenge decoding is checked (`Language.lean:321`).
  - The `N = 0` tape mismatch is real: `colSimCoins` is 0 at `N = 0`, so
    `colCoinSlice B 0 [] = []` and `r_V = []`. It is covered only by the `exp(0) = 1` term (M1).
  - The attempt count is advice-independent (`colIterations` depends on `x` alone; `K ≤ N²`).
- **Rows 13–14** (`hLR`, headline dependencies): agree.
  - `NP.lean:584–592` consumes `colRep_efficientProverProof`, `col_zk` and
    `col_efficientProverProofErr`.
  - `R3COL_witnessRelation` reaches no form (A) body; its only other use is `Checks.lean:312`.
- **Row 15** (evidence): reconciled.
  - `replay.log`: 115 lines with `rc=0`.
  - `axioms.log`: 6 `sorryAx` lines (258 prints).
  - `admissions.txt`: 3 entries, at `Protocol.lean:838`, `:914` and `Simulator.lean:764`.
- **Rows 16–110:** I spot-checked rows 63, 67, 76–82, 84, 88 and 90 against the code and found no
  disagreement. I did not re-derive the coverage count (row 110).

---

## Missed by the auditor

- **M1 (folded into #1): the `m = 0` sentence is false at `n = 0`.**
  - `Simulator.lean:744–746` claims the advantage is at most `ε_B n` whenever `m = 0`.
  - At `x = []` (`R3COL [] []` holds), the simulator's tape is empty, so its `r_V = []`, while the
    real `r_V` has `V'.coinLen 0` bits. `D` can then tell them apart with advantage 1.
  - The auditor notes the mismatch (row 11) but not that the sketch's sentence is false.
  - §#2.3 restricts the case to `n ≥ 1` and bounds `n = 0` by 1.
- **M2 (minor): a silent source correction in a quotation.**
  - `uprob_colSimTruncH_none` (`Simulator.lean:320–321`) quotes the text as "`S''` fails with
    probability `(1 - 1/|E|)^{n|E|}`".
  - The PDF (p. 141, book p. 129) prints "S′ fails with probability …", and before it "If we assume
    that S′ never outputs fail". Both are typos for S″.
  - **Fix:** quote "`S'` [sic: `S''`] fails …", and add the two typos to DESIGN §7 item 46
    (:1279 HEAD).
- **M3 (note; for the fill brief): the single `sorry` has no ladder.**
  - Policy §3 says each `sorry` of a skeleton should correspond to a named step. `col_zk` is one
    `sorry` for the chapter's hardest theorem, and its sketch names steps that have no lemma: "the
    colour-pair analogue of `statClose_samplePerm3`", and the machine `B`.
  - The 03g fill brief should fix the ladder:
    1. `statClose_sampleColorPair` (within `(1/4)^T` of uniform on `ColorPair`);
    2. step (1), the real view to `some ∘ colRealView`;
    3. step (2), `colSim` to `colSimTrunc`;
    4. `exists_colSimRed_fixCoins` (§2.1, items 1–2);
    5. the reduction machine `exists_colHidingRed` (§2.1, items 3–5);
    6. the `m = 0` reduction;
    7. the assembly.
  - It should also carry the 20 lint findings, which by the 2026-11-05 decision are swept with these
    fills.
- **M4 (note): placement.** `Negligible.comp_sqrt` is a general negligibility fact (Inf-4.4).
  `inventory-ch4.md` puts Inf-4.4 in `Defs.lean`, next to `negligible_exp_neg_sqrt_div`. Moving it
  there in clean-up part 2 is optional. It has no duplicate in the library (grep).

## Proposed closing condition

Gate 03g closes at **0 blockers and 0 majors** when:

1. **The `col_zk` sketch is rewritten.** `Simulator.lean:727–763` is replaced by the text of §#2.3,
   with:
   - the leading term `N² ε_B(⌊√N⌋)`;
   - the fixed-coin bridge;
   - the `m = 0`/`n ≥ 1` and `N = 0` cases;
   - the corrected advice bound;
   - the use of `Lz` stated.
2. **The minors are fixed:**
   - #3 (`Simulator.lean:679–681`) and #4 (`Language.lean:304`);
   - #5 at all four sites;
   - #6's records (D8, §5 item 11, an as-built note under §2.15, inventory Thm-124.1 (A),
     Claim-124.d, Def-124.a);
   - M2 (`Simulator.lean:321` and DESIGN §7 item 46).
3. **Checks pass and a delta audit is run.**
   - The repair touches only docstrings, so a re-check of `Language.lean`, `Simulator.lean` and their
     downstream closure suffices.
   - The admissions stay at 3 and `axioms.log` stays at 6 `sorryAx`.
   - A delta round-2 audit reads the new sketch and the changed docstrings. It is needed because both
     majors are about the sketch, and the sketch gates the fill.
4. **The fill brief for the three admissions carries the corrected sketch and the ladder of M3.**

No user ruling is needed.
