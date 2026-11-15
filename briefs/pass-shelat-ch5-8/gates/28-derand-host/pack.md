# Gate 28 · The seed-majority enumeration host for derandomization (derand host, statement)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #312](https://github.com/Shilun-Allan-Li/tcslib/pull/312) at
  `8972fb4ef15fa3d4e3df37d6aa8674408835593d` (branch `stmt/pass-shelat-derand-host`, tree
  `ba544f9ca0d80ff12644128a2cc32a94d6b5f709`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `013119f006af40d03b88b0fc2d9b453cf0a9b348` (the merge base; GitHub shows the branch tip at opening, `b12a12f2`, a
  records commit). The two commits from the base to the records tip `41e3cd2a6b637ed10c6782b5f3c68212f9f77b65`
  (`b12a12f2`, `41e3cd2a`) touch records only: `PassShelatChapter5-8Plan.md` and the two evidence folders
  `maintainer/stmt-b1-2026-11-15/` and `maintainer/stmt-derand-2026-11-15/`. The diff
  `origin/cryptography/pass-shelat-ch2-4...8972fb4e` equals `013119f0..8972fb4e` byte for byte (`pr.diff.txt`).
- **Commits:** 1, by the maintainer (author Claude): `8972fb4e` "Statement: the seed-majority enumeration host
  (derand, PS10 Thm 180.1)".
- **Scope:** a **statement audit** of a *host contract*. Seyoon ruled on 2026-11-14 that `derand`
  (`Randomness.bpp_subset_dtime_subexp`, [PS10, §8.2, Theorem 180.1]) is **held**: the deterministic counting/majority
  enumeration host it needs is first stated, sorried, by the maintainer in a statement PR with its own gate, and only
  then is `derand` dispatched. This PR is that statement. It adds no `def`.
- **Sources:** [PS10] §8.2, Theorem 180.1 (book p. 180), step 4 of its proof; [AB09] S. Arora and B. Barak,
  *Computational Complexity*, 2009, §7.1, p. 126 (`BPP ⊆ EXP` by enumerating the random strings) and Claim 2.4.

## What changed

The PR touches 2 Lean files (167 insertions, 0 deletions). Paths are under `TCSlib/Complexity/`.

| File | Status | Lines | SHA-256 at head |
|---|---|---:|---|
| `Randomized/SeedMajority.lean` | new | 163 | `3f6758b1…` |
| `Randomized.lean` (facade) | modified: one import and one `## Contents` entry (3 lines) | 206 → 210 | `bfefe641…` |

The new module imports `ClassP/P`, `ClassNP/PolyTime`, `TuringMachine/Encoding` and `Randomized/Classes`. It has two
public theorems and nothing else:

```lean
open Classical in
theorem Complexity.seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry   -- the contract; the only sorry

theorem Randomized.half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card   -- proved
```

`DTIME T = {L | ∃ c M, M.DecidesInTime L (fun n => c * T n)}` (`ClassP/DTIME.lean`), so the one membership carries
correctness (some machine decides exactly the strict-majority language; ties reject) and the time bound
`c · 2^{w(n)} · (n+1)^e`.

The maintainer's design choices, disclosed for this gate (PR description; `pr-body.md` § Design and § Decisions):
1. **Existential machine.** The contract is a class membership. No `def`, so no sorried definition and no reader owed;
   consumers read it through `DTIME.mono`, `Randomized.DTIME_const_mul_subset` and `half_lt_randProb_iff`.
2. **Generality.** The test is any `V ∈ P` read on `pairEncode x u` (the convention of `Randomized.polyTimeModel`), not
   a decider of arbitrary time on `x ++ u`; the width is any `w` whose unary word is polynomial-time; majority is
   strict, with no general threshold; only the `DTIME` form, with no machine-level `DecidesInTime` contract.
3. **No head-envelope (space) clause:** a decision-layer host, as `exists_proj_decider` is.
4. **Placement:** the shared `Complexity/Randomized` layer, not `derand`'s helper directory (policy §1, a second
   prospective consumer `BPP ⊆ EXP` [AB09, p. 126], and Complexity does not import Cryptography).
5. **Relatives not reused:** `Complexity.exists_proj_decider` (any-verdict, fixed width `C(n+1)^c`, test on `x ++ u`,
   private engine) and the polynomial block-majority tests.
6. **Registry row H17** for `machine-library-design.md` §14 is drafted in `pr-body.md` and not yet entered.

## Rulings and records in force

- **derand held; host contract first (Seyoon, 2026-11-14,** decision-log row "Rulings (Seyoon) on the staged
  fills"**):** the deterministic counting/majority enumeration host's contract is first stated (sorried) by the
  maintainer in a statement PR with its own gate; then `derand` is dispatched.
- **Derand fill pre-approvals (Seyoon, 2026-11-15,** row "derand host statement PR"**), for the later fill, not for
  this PR:**
  1. harvest one public generic-fuel `computesFunInTime_find` (with its contract) into the frozen
     `Complexity/Randomized/Build/IterateFind.lean`, reusing its private helpers in place;
  2. add `mem_DTIME_iff` (by `Iff.rfl`, with a formula docstring) beside `DTIME` in the frozen shared
     `ClassP/DTIME.lean`, its downstream rebuilt at review.

  The same row says the derand brief is updated after this gate: step 4 and checkpoint 1 consume the contract, and the
  order and roots are regenerated.
- **The derand brief** `fills/derand/issued-r1/brief.md` (in `verification.zip`, `records/`) is the consumer's issued
  brief. Its checkpoint 1 asked for a scope request for "a deterministic machine that runs a decider on `x ++ u` for
  every seed `u` of width `w` and accepts iff more than half accept, within `b · 2^w · (T(n + w) + poly)`". The stated
  contract specializes this to a `P` test on `pairEncode x u`; see question 3.
- **Policy §1, *Hosts come first*:** a host is never built `private` inside the proof that first needs it; its public
  contract is designed, statement-gated and placed in the shared construction layer first, generic in the parts its
  consumers vary, with time and space (head-envelope) clauses. The host registry is `machine-library-design.md` §14
  (rows H14 clean-module host, H16 counted word loop at the FP layer, in `verification.zip`).
- **Standing rules:** Rule 10; formula docstrings with `[PS10 …]`/`[AB09 …]` tags and a `**Proof sketch.**` (policy
  §§2–3); the #305 facade rule; lint baseline **92 FAIL / 101 WARN** on `TCSlib/Cryptography` with no new line (the
  PR also reports `TCSlib/Complexity`, 25 / 391); lines of at most 100 characters.

## What is frozen

Every file other than the new module and the facade's import and `## Contents` lines, in particular
`Cryptography/Randomness/Derandomization.lean` (`bpp_subset_dtime_subexp`, `subexpBound`), `ClassP/DTIME.lean`,
`Randomized/Classes.lean` (`randProb`, `randProb_eq`), `Randomized/QuasiPolyHierarchy.lean`
(`DTIME_const_mul_subset`), `Randomized/Build/IterateFind.lean` and `ClassNP/EXP.lean`: byte-identical to the base
(check with `pr.diff.txt`). The two derand pre-approvals above are not exercised here.

## Questions for the audit

1. **Is the contract true?** Including:
   - **ties:** `2^w = 2 · count` rejects; is that the intended strict majority, and is it what Theorem 180.1 needs (its
     `1/12` margin keeps acceptance probabilities away from `1/2`)?
   - **`w = 0`** (and `w x.length = 0` at some lengths): one seed, the empty word; the language is
     `{x | pairEncode x [] ∈ V}` at those lengths and the bound is `(n+1)^e`;
   - **small `n`:** `n = 0`, where the bound is `2^{w 0}`; and `DTIME_eq_empty_of_exists_zero` (the bound is never 0
     here);
   - **the time:** `2^{w(n)}` rounds, each a polynomial-time step on a state of length `O(n + w(n))`, with
     `w(n) ≤ C(n+1)^c` from `hw` (`PolyTimeComputable.output_length_le`); is `c · 2^{w(n)} · (n+1)^e` attainable on
     every input, including the cost of computing `1^{w(|x|)}` and of the final comparison?
   - the decision layer: `DecidesInTime` requires output exactly `[decide (x ∈ L)]` within `c · T(|x|)` steps on every
     `x : List Bool`.
2. **Is it sufficient for Theorem 180.1?** The PR description (`pr-body.md` § "Theorem 180.1 from the contract and the
   PRG hypothesis") gives a six-step paper proof; the module docstring's § Consumers gives the instantiation. Check:
   - the test `V'' = {⟨x, u⟩ | if |x| < n₀ then ⟨x, u⟩ ∈ V₁ else ⟨x, F'(u)↾m(|x|)⟩ ∈ V₁}` is in `P`
     (`preimage_mem_P`, Boolean closure, `PolyTimeComputable.pairEncode`, prefix truncation), with `V₁` the
     `some true`-set of the `polyTimeModel` verifier;
   - the width `w(n) = if n < n₀ then m(n) else ℓ(n)` (`ℓ(n)` the least `t` with `n ≤ t^d`) has a polynomial-time unary
     word; `n₀` is obtained non-constructively from PRG security, which is harmless for a fixed function `w` — is it?
   - `L` equals the majority language: below `n₀` with the true coins (acceptance `≥ 2/3` or `≤ 1/3`), from `n₀` on with
     gap at most `1/12` (`≥ 7/12` or `≤ 5/12`); `half_lt_randProb_iff` converts;
   - the bound `2^{w n}(n+1)^e ≤ c · subexpBound ε n` for all `n`, the finite exceptions absorbed into `c`
     (`subexpBound_pos`), then `DTIME.mono` and `DTIME_const_mul_subset`;
   - whether step 2 (bad input lengths to bad seed lengths, advice `|x| ≤ s^d`, `verifier_toNUPPT`,
     `NUPPT.exists_withAdvice(On)`, `randProb_eq_uprob`, `PRG.secure_iff`) is consistent with the frozen sketch of
     `bpp_subset_dtime_subexp`.

   `probes/ConsumerProbe.lean` checks only the last step (from a pointwise bound to `DTIME T`), sealed.
3. **Is the generality appropriate?**
   - A `P` test on `pairEncode x u`, versus the brief's decider of arbitrary time on `x ++ u`: is `P` enough for both
     consumers (derand's `V''` and `BPP ⊆ EXP` by coin enumeration with `w = polyLen a k`), and is `pairEncode` the
     right convention (it is `polyTimeModel`'s)?
   - Strict majority only, with no general threshold: does any foreseeable consumer need `t · 2^w < count`, or the
     count itself?
   - The `DTIME` form only, with no machine-level contract: does any consumer need to compose the host's machine (e.g.
     as a clean module inside a larger machine), which a `DTIME` membership cannot provide?
   - Is the width hypothesis `hw` the right one (input-length dependence only; the unary word rather than a binary
     one)?
4. **Is it placed in the shared layer, and is it Rule-10 clean?**
   - Policy §1 asks for the shared *construction* layer and for time and space (head-envelope) clauses. Is
     `Complexity/Randomized/` the right home (rather than `TuringMachine/Build/` or beside `ClassNP/EXP.lean`), and is
     the missing space clause acceptable for a decision-layer contract (precedent `exists_proj_decider`)?
   - Must the registry row H17 be entered in `machine-library-design.md` §14 before this PR merges, or with it?
   - Rule 10: `half_lt_randProb_iff` reads `randProb` only through `randProb_eq`; the statement uses `DTIME`, `P`,
     `PolyTimeComputable`, `pairEncode` and the `Finset` count as atoms. The evidence has a whole-file seal of the new
     module and a consumer probe, each with a paired control.
   - Nearest relatives: `exists_proj_decider` (`ClassNP/EXP.lean`), the block-majority tests
     (`ClassNP/PolyTimeBlockMajority.lean`), H16 `BinArith.forLoop` (`ClassP/BinaryArith/Loops.lean`, a counted loop
     with one round per counter letter) and `IterateFind.polyTimeComputable_find`. Is any of them, or a published
     generalization of one, the contract that should be stated instead?
5. **Is it provable on the stated route?** The module docstring's § Route: a state loop `⟨x, ⟨i, a⟩⟩`; the
   result-bearing combinator `Turing.FinTM.exists_loopFindTM` over the clean-module host with fuel
   `Nat.bits (2^{w(|x|)})`, bound `c (T(n) + 1)(R(n) + 2)`; the count through `i ↦ word_w(i)`; the normal form.
   - `evidence/probes/RouteAxioms.log`: 26 route lemmas, standard axioms only; the route avoids the admitted
     `loopHostTM_*` and `timedCondTM_*` specs.
   - Is the exponential fuel compatible with `exists_loopFindTM`'s contract (its fuel and time parameters, and the
     polynomial `T` of each round), and with the private `IterateFind` helpers (`Inv`, `verdictWord`, `stepWord`,
     `outWord`, `final_bound`), given the pre-approved harvest of a generic-fuel `computesFunInTime_find`?
   - Is introducing a `DTIME` membership possible without reading `DTIME`'s body, given the pre-approved
     `mem_DTIME_iff`?
   - The size estimate is 0.9–1.6k lines for the host; is it plausible?
6. **Docstrings and attribution.** Module docstring (formal reading, `## Main results`, consumers, design, route,
   `## References`) and the two theorem docstrings: formulas, `[PS10 …]`/`[AB09 …]` tags, the `**Deviation.**` and the
   contract's `**Proof sketch.**`.

## Known dispositions (not findings)

- **The facade edit** (one import, one `## Contents` entry) is the #305 facade rule, not a frozen-file change.
- **The host's proof is out of scope.** The gate asks whether the contract is true, sufficient, appropriately general,
  well placed and provable on the stated route.
- **Not exercised here:** the two derand pre-approvals (the `IterateFind` harvest and `mem_DTIME_iff`); the H17
  registry row (drafted only); the derand brief update.
- **Two PR texts.** The GitHub description of #312 is a shortened rewrite of the evidence's `pr-body.md` (in
  `verification.zip`, `records/…/stmt-derand-2026-11-15/pr-body.md`, byte-identical to the ZIP entry). The paper proof,
  the eight decisions for Seyoon and the draft H17 row are in full only in `pr-body.md`.
- **The evidence build** checked 63 modules in an olean tree whose base is source `eff2dcd0`: the new module, its
  facade, the 51 Cryptography modules changed between `eff2dcd0` and the PR base and their downstream, root `TCSlib`
  and `audits/pass-shelat/Checks`. `build/results.jsonl` has 64 lines: 63 module rows and a final `done` marker.

### Wording noted by the staging (please rate)

- The module docstring says "the proof is a separate fill"; the PR description says "The `derand` fill will then
  prove both the host and the theorem", and the 2026-11-15 pre-approvals are given to the derand fill. Which unit
  proves the contract is not stated the same way in the three places.

## Also check

- The `sorry` is the only one in the PR, at `SeedMajority.lean:154` (`seedMajority_mem_DTIME`); `half_lt_randProb_iff`
  uses the three standard axioms (`evidence/probes/ConsumerProbe.log`).
- Every line of the two files is at most 100 characters (`source-head.json`; `evidence/lint/widths.txt`).
- `open Classical in` on the contract: is the decidability instance of the `Finset.filter` the one a consumer obtains
  (the consumer probe rewrites with `half_lt_randProb_iff`, whose `[DecidablePred A]` is explicit)?
- Namespaces: the contract is in `Complexity`, the reader in `Randomized`, matching `DTIME` and `randProb`.

## Evidence

`verification.zip` (45 entries; its `SHA256SUMS` lists every other entry, `PROVENANCE.txt` maps each to its source)
holds byte-identical originals from records `41e3cd2a`:
- `stmt-derand-evidence.zip` (SHA-256 `aace4d2a…`, 107 file entries = the 106 manifest paths under `stmt-derand/` plus
  that folder's `SHA256SUMS`, byte-identical to the manifest) and its manifest `evidence-SHA256SUMS`;
- `records/`: the evidence's `PROVENANCE.txt` and `pr-body.md` (as beside the ZIP), the decision log, the duplication
  ledger, `machine-library-design.md` (§14, host registry) and the derand issue package `fills/derand/issued-r1/`;
- `evidence/`: byte copies of the ZIP entries cited here:
  - `build/order.txt`, `build/results.jsonl`, `build/mods/*.log` (4 of the 63): 63/63 rc 0, 0 errors (both
    `error:` and `error(` forms counted, G26-N1); the only `sorry` warning is `SeedMajority.lean:154:8`;
  - `probes/RouteAxioms.lean`/`.log` (route lemmas' axioms); `probes/SealSeedMajority.lean`/`.log` (whole-file seal:
    `randProb`, `DTIME`, `P`, `PolyTimeComputable`, `pairEncode` local irreducible; rc 0);
    `SealSeedMajorityControl` / `UnsealedSeedMajorityControl` (a control reading `randProb` through its body fails
    sealed exactly once, line 172, and passes unsealed); `ConsumerProbe` / `ConsumerProbeUnsealed` (the last step of
    derand through readers only, sealed; its control builds `DTIME` membership through the body and fails exactly
    once sealed; all pass unsealed);
  - `lint/linediff.txt` (Cryptography 92/101 and Complexity 25/391 at base and head, 0 new and 0 gone lines),
    `lint/widths.txt` (max widths 100 and 97);
  - `patches/COMMITS.tsv`, `patches/am-check.txt` (the tree reproduced from the patch; the commit is SSH-signed),
    `restore/restore-log.txt`, `tree/snapshot-pre.txt`, `restore/snapshot-post.txt` (the olean tree restored,
    SHA-256 `457ba704…` before and after), `PROVENANCE.txt`, `pr-body.md`.

Also: `pr.diff.txt` (2 paths, 167/0), `source-head.json` (hashes, line counts and over-width counts of the 2 files) and
`sources.zip` (the import closure at the head of both changed modules, 308 files). The consumer
`Cryptography/Randomness/Derandomization.lean` is not in that closure; it is in the bundle.

## Findings delivery

Return `gate28-derand-host-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable contract, or a scope violation (a frozen file changed).
- **major:** a missing or wrong hypothesis, a contract too weak for Theorem 180.1 or not provable on any reasonable
  route, a misplaced host under policy §1, a forbidden read, a duplicate public result, or necessary evidence that
  cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, route or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
