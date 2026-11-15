# Pass–shelat Gate 28 — derandomization host statement audit

**Verdict: HOLD.** **0 blockers, 2 majors, 1 minor, 1 note.**

The mathematical contract and probability reader pass this statement audit. The contract is
sufficient for the paper proof of Theorem 180.1. Closure is held on the host-policy issues below;
the intended `sorry` is not a finding. No dispatch, repository write, or merge was performed.

| Item | Audited revision |
|---|---|
| Draft PR | [#312](https://github.com/Shilun-Allan-Li/tcslib/pull/312) |
| Lean head | `8972fb4ef15fa3d4e3df37d6aa8674408835593d` |
| Lean merge base | `013119f006af40d03b88b0fc2d9b453cf0a9b348` |
| Campaign records | `1ea6503c82b12fd7e49c2e621fcae4cd29d9d08c` |
| Exchange | `2776272b61fcc7a1adf3f743c735c7e45be5045c` |

## Findings

Paths in this table are repository paths. Line numbers refer to the pinned files.

| ID | Severity | File / declaration | Finding and evidence | Proposed fix |
|---|---|---|---|---|
| G28-01 | **major** | `machine-library-design.md` §14; `seedMajority_mem_DTIME` | H17 is absent from the actual host registry. The only row is a draft in `briefs/pass-shelat-ch5-8/maintainer/stmt-derand-2026-11-15/pr-body.md:182`. Policy §1's review checklist requires a registered public host. The same campaign treated missing H15 registration as G08-01, a major (`PassShelatChapter5-8Plan.md:413–421`). Disclosure of this omission does not discharge it. | Enter H17 in the canonical registry before or with the statement landing, before briefing the consumer against it. Record the contract, home, reader, Gate 28 status, proof owner, consumers, route, and disposition of G28-02. A registry-only repair can accompany this statement gate; it need not await the host proof. |
| G28-02 | **major** | `TCSlib/Complexity/Randomized/SeedMajority.lean:71–72,149–154`; policy §1 | The proposed host deliberately has no space/head-envelope clause. Policy §1:113–117 expressly requires such a clause; the two recorded derand pre-approvals concern the generic-fuel harvest and `mem_DTIME_iff`, not an exception to that requirement (`PassShelatChapter5-8Plan.md:698`). Calling the contract a decision-layer membership does not itself record an exception. | Retain the useful `DTIME` corollary, and expose a shared host contract tying correctness, time, and a stated head envelope to the **same machine**; alternatively obtain and record Seyoon's explicit approval of this time-only decision-layer interface. A coarse envelope derived from the time bound suffices for the literal policy; no polynomial-space strengthening is required by this finding. Do not use the admitted `loopHostTM_*` space specifications as if proved. |
| G28-03 | **minor** | `TCSlib/Complexity/Randomized/SeedMajority.lean:54–56` | The displayed consumer test always applies `G`, while the next clause says true coins below a threshold are handled by changing the width. Changing the width alone does not remove the generator. The correct paper proof changes **both** the test and width (`pr-body.md:113–121`). PRG security imposes no correctness guarantee on finitely many exceptional seed lengths. | Give the piecewise test and width from the paper proof in this consumer paragraph: use the original seed below the threshold and the generator output from the threshold on. |
| N28-01 | note | `SeedMajority.lean:26`; PR description; issued derand brief | “The proof is a separate fill” can mean separate from the statement phase; the PR description assigns both proofs to derand. This is ambiguous ownership prose, not a mathematical contradiction. The issued brief still has its old host scope-request checkpoint; its post-gate update is already recorded. | Name the proof owner consistently and update the issued brief/order/roots before dispatch, including the two pre-approved shared-file changes. |

**G28-02 precedent considered.** H15 was accepted as a high-level polynomial-time interface without
a separate machine envelope; the registry records that choice explicitly. This is relevant
precedent for requesting the same treatment here. It is not a blanket change to policy §1 or a
recorded ruling for H17. Conversely, Gate 03l round 2 treated H14's missing envelope as a major
and repaired it. I do not silently choose a new exception between those precedents. The shared
`Complexity/Randomized/` location is appropriate for the decision corollary; its pathname is not
an additional finding.

## Integrity and evidence

- The outer `SHA256SUMS` verifies **10/10** files. In particular, `bundle.md` is
  `b07f60050d951bb5cf9e90f4dea56a1263636b891fb5c6e79473021b8e36cb60`.
- `verification.zip`: **44/44** manifest entries verify; its 45 file entries are exactly those
  entries plus `SHA256SUMS`. The nested maintainer archive verifies **106/106** entries and has
  exactly 107 files. Its manifest equals `evidence-SHA256SUMS`; all **27** evidence extracts are
  byte-identical to their originals.
- All **308** source files in `sources.zip` match their Git blob IDs in the independently
  retrieved, nontruncated tree at the Lean head. All **11** bundle sections match the specified
  Lean/records blobs after removing only the bundle's separator newline where present.
- The independently retrieved base/head comparison has one commit and exactly two changed
  paths: the new 163-line module and four facade lines, **167 additions / 0 deletions**. No
  frozen Lean file changed. Both head source SHA-256 values match `source-head.json`.
  GitHub’s target pin is `b12a12f2`; the two base-to-records-tip commits through `41e3cd2a`
  change only campaign records and the two statement-evidence folders, as disclosed.
- The archived plan is explicitly from records `41e3cd2a`, as its provenance says. Compared
  with the requested records pin, it lacks only the final Gates 27–28 staging row. I read that
  newer row too; it adds no space-clause exception. Policy, registry, duplication ledger, brief,
  and full paper-proof text were checked against the requested records pin.
- The 63 recorded module builds all report return code 0 and zero errors. I recomputed every
  archived build-log hash and both diagnostic forms. The sole reported sorry warning is the
  authorized contract at `SeedMajority.lean:154:8`. The before/after object-tree snapshots match.
  Independent width checks give 163/97 and 210/100 for lines/maximum width.

**Limit:** Lean and its compiled dependencies are absent from this audit environment. I did not
rerun Lean or independently reproduce the 63 builds, seals, or axiom prints. Their authenticated
source/log pairs were inspected and checked for internal consistency. The attached verifier
reproduces the byte, archive, width, and log checks; it does not prove the sorried host.

## Truth and boundary cases

For the reader, let `count` be the displayed filter cardinality. In the rationals,

\[
  2^m>0,\qquad
  \frac12<\operatorname{randProb}(m,A)
  \iff \frac12<\frac{\mathrm{count}}{2^m}
  \iff 2^m<2\,\mathrm{count}.
\]

This is exactly `randProb_eq` followed by positive-denominator multiplication and natural-to-
rational casts. The new proof performs those operations through the published reader. A tie
has `2 count = 2^m`, so both strict inequalities are false. For `m=0`, there is exactly one
function `Fin 0 → Bool`, whose list is `[]`; `count` is 0 or 1. Thus the reader and the host
reduce to the single empty-seed test, with no division by zero or tie convention change.

For the host, fix an input of length `n` and put `R = 2^{w(n)}`. The width hypothesis gives

\[
  w(n)\le C(n+1)^c
\]

by applying `PolyTimeComputable.output_length_le` to any word of length `n`. Enumerate ranks
`0,…,R−1`, and maintain

\[
  \mathrm{count}_i
   =\#\{j<i:\operatorname{pairEncode}(x,\mathrm{word}_{w(n)}(j))\in V\},
  \qquad 0\le\mathrm{count}_i\le i\le R.
\]

Initialize `i=count=0`; each nonterminal step tests rank `i`, adds its Boolean verdict, and
increments `i`. Induction on `i` proves the invariant. At `i=R`, fixed-width binary expansion
is a bijection from the ranks onto `Fin (w n) → Bool`, so `count_R` is precisely the theorem's
cardinality. Emit the one-bit strict comparison. This establishes the mathematical correctness
argument, including rejection on ties.

The binary rank and count each need at most `w(n)+1` bits, including the terminal value `R`.
The paired state consequently has length at most `2n+3w(n)+7`. Computing the unary width,
padding a seed, running the `P` test, updating the counters, and the final comparison all have
a common polynomial budget `T(n)`. For suitable constants `A,e`, take

\[
  T(n)+1\le A(n+1)^e,\qquad
  R+2\le3R,\qquad
  c_0(T(n)+1)(R+2)\le3c_0A\,2^{w(n)}(n+1)^e.
\]

The constant is absorbed in `DTIME`. At `n=0`, the bound is positive (`2^{w(0)}`), and the
constant covers initialization and the fixed width-computation cost. At lengths with `w(n)=0`,
there is one test and polynomial time. No lower bound on `w`, monotonicity, or time-
constructibility of an arbitrary numerical time function is needed.

This is a mathematical proof plan, not a completed Lean proof. The fill must supply the
enumeration bijection, invariant, polynomial-time components, and machine composition.

## Sufficiency for Theorem 180.1

The full `pr-body.md` route is sound. It also matches the frozen theorem's intended proof:

1. From `InBPP polyTimeModel L`, use its Boolean verifier and `polyTimeModel_eff_iff` to obtain
   the accepting paired language `V₁ ∈ P`. Set `m(n)=a(n+1)^k`. Choose fixed `d≥2` with
   `1/d<min(ε,1)` and `ℓ(n)=min{t:n≤t^d}`. Here `ℓ(0)=0`; for `n≥1`, searching `t≤n`
   computes its unary word in polynomial time. No real exponent is computed by a machine.
2. Expand to the syntactic polynomial `P(s)=a(s^d+1)^k+s+1`, using one-bit truncation and
   `prg_expand`; obtain evaluator `F'` through `PRG.easy_iff`. The inequalities
   `P(s)>s` and `m(n)≤P(ℓ(n))` hold at every length, including zero.
3. If the probability gap exceeds `1/12` at infinitely many input lengths, it does so at
   infinitely many seed lengths: `ℓ(n)=s` implies `n≤s^d`, so each fiber is finite. Choose one
   bad input `x_s` for each such `s`, with empty advice otherwise. Its length is at most `s^d`.
   The deterministic test `y ↦ M(x_s; y.take(m(|x_s|)))` is polynomial-time with this advice.
   `verifier_toNUPPT` applies to the efficient prefix-truncated verifier. Uniform prefix
   projection and `randProb_eq_uprob` identify its advantage with the bad gap. By
   `PRG.secure_iff` this advantage is negligible, contradicting infinitely many values above
   `1/12` (already the inverse-linear bound contradicts this for sufficiently large `s`).
4. Therefore a fixed threshold `n₀` exists. Define the paired test and width **together**:

   \[
   w(n)=\begin{cases}m(n)&n<n_0,\\\ell(n)&n\ge n_0,\end{cases}
   \qquad
   V''(\langle x,u\rangle)=
   \begin{cases}
     V_1(\langle x,u\rangle)&|x|<n_0,\\
     V_1(\langle x,(F'(u)).\mathrm{take}(m(|x|))\rangle)&|x|\ge n_0.
   \end{cases}
   \]

   Both are polynomial-time: hard-code the single natural `n₀`, use integer-root search,
   pairing, prefix truncation, and `P` closure. A threshold obtained by classical existence is
   harmless: the theorem asks for an existential decider, not a uniform procedure extracting
   that decider from a security proof. Extend the test on raw words using the total pairing
   projections; behavior on malformed words is irrelevant to its paired-input specification.
5. Below the threshold, true-coin acceptance is at least `2/3` on members and at most `1/3`
   on nonmembers. From the threshold on, the respective bounds are
   `2/3−1/12=7/12>1/2` and `1/3+1/12=5/12<1/2`. The reader therefore identifies `L` exactly
   with the host's strict-majority language. This handles all finite exceptions without a
   separate finite-table machine.
6. The host gives some `e`. Eventually `w(n)=ℓ(n)≤n^{1/d}+1`, and

   \[
   \log_2\!\left(2^{w(n)}(n+1)^e\right)
     \le n^{1/d}+1+e\log_2(n+1)\le n^\varepsilon.
   \]

   The last inequality is eventual because `1/d<ε`. Rounding up preserves the upper bound.
   Since `subexpBound ε n≥1` at every length, one natural constant absorbs the finitely many
   exceptions. `DTIME.mono` and `DTIME_const_mul_subset` finish exactly as in `ConsumerProbe`.

The compiled consumer probe checks only the final transport from a supplied pointwise bound.
It does not establish steps 1–5 or the asymptotic inequality; those remain the derand fill's
proof obligations. Polynomial prefix truncation is available directly as
`Complexity.polyTimeComputable_pairTakePoly`; the fill need not unfold the older
`takePrefixByLen` definition to implement this step.

## Generality, route, and Rule 10

- A `P` test on `pairEncode x u` is sufficient for both named consumers and matches
  `polyTimeModel`. Neither presently needs an arbitrary-time leaf, a variable threshold, or
  the numerical count as output. The unary computability hypothesis is useful: a merely
  polynomially bounded width could be uncomputable. It also permits the required piecewise
  integer-root schedule. These design restrictions are not mathematical defects.
- A `DTIME` membership is enough for the theorem's decision-class conclusion. A consumer
  needing a clean submodule or a head bound would require a machine-level interface; that is
  the policy issue in G28-02, not a failure of Theorem 180.1's reduction.
- `exists_loopFindTM` quantifies over arbitrary `R,T : ℕ→ℕ`; it does not require polynomial
  fuel. Its fuel machine outputs **binary** `Nat.bits (2^{w(n)})`, of length `w(n)+1`, not an
  exponential-length unary word. The conclusion searches `List.range (R(n)+1)`, so it includes
  the terminal index `R(n)` and allows `R(n)` seed tests followed by the payload round.
- The invariant must be closed under the total step function, as required by `hInvStep`.
  Make terminal states fixed, or use the existing size guard; never assume an unbounded
  increment preserves a fixed state bound after termination. The approved generic-fuel
  harvest can retain `Inv` and the word adapters in their original shared file. The existing
  polynomial-fuel `final_bound` cannot be applied to exponential `R`; use the direct bound
  displayed above instead. These are feasible fill obligations, not a need to change the
  statement. The 900–1,600-line estimate is plausible but is not a verified size guarantee.
- The 26 route-lemma axiom records contain only the standard axioms. In particular, the
  proved `exists_loopFindTM` uses private `loopHost_contracts`, rather than the admitted
  `loopHostTM_*`/`timedCondTM_*` specification theorems. The approved `mem_DTIME_iff` addition
  supplies the missing introduction reader for the later proof.
- The new reader uses `randProb_eq` and arithmetic lemmas; no forbidden definition read was
  found. The host introduces no definition. The whole-file seal succeeds; its body-reading
  control fails once and passes unsealed. The consumer's `DTIME` constructor control likewise
  fails once sealed and passes unsealed. Classical decidability causes no mismatch: the
  decisions for a fixed proposition are subsingleton, and both counts describe the same event.
- The existential projection decider computes an any-verdict at fixed polynomial width;
  block-majority counts polynomially many supplied blocks; H16 performs one round per
  **counter letter**. None supplies this exponential seed-majority contract at polynomial
  state size. The approved shared harvest avoids copying the private `IterateFind` machinery.
  No duplicate public result or new copied proof was found in this statement change.
- The theorem docstrings state their formulas and source locations; the host has a deviation
  note and proof sketch. The proof reader is short enough not to require an additional sketch.
  The facade imports the new module, and the pinned root imports the Randomized facade.

## Sources and reproducibility

Primary source checked: Pass–shelat, *A Course in Cryptography*, third edition, §8.2,
[Theorem 180.1, printed p. 180](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf).
The source's exhaustive-seed argument supports the contract; the integer-root schedule,
nonuniform-advice argument, and all-length repair are explicit elaborations checked above.
The repository's [AB09] enumeration attribution is consistent with that standard argument.

The evidence ZIP contains this report, `verification-results.json`, the offline verifier,
Git-blob maps, repository comparison metadata, and focused source/policy excerpts. To rerun
the byte checks, place the verifier and both Git-blob maps together and run:

```sh
python3 verify_gate28.py /path/to/outbox/gates/28-derand-host-gate
```

**Glossary.** `count` is an accepting-seed cardinality; `count_i` is the tally before rank `i`;
`word_w(i)` is the width-`w` binary expansion of `i`; `R=2^{w(n)}` is the seed count; `T` is a
common per-round polynomial budget; `C,c,A,c₀,e` are fixed natural bounds/constants. In the
consumer argument, `M` is the BPP verifier, `V₁` its accepting paired language, `m(n)=a(n+1)^k`
its coin width, `d` the fixed root degree, `ℓ(n)` its ceiling-root schedule, `s` a seed length,
`P(s)` the polynomial PRG stretch envelope, `F'` its evaluator, `x_s` an advised bad input,
`n₀` the finite-exception threshold, and `V''` the piecewise paired test. `ε>0` is the requested
subexponential exponent; `x,n,u,i,A` otherwise have the input/length/seed/rank/event meanings
in the audited statements (`A` in the probability reader is an event, not the budget constant).
