# Claude fill · pseudorandom generators derandomize `BPP` in subexponential time (`bpp_subset_dtime_subexp`, Theorem 180.1)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `derand`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `bpp_subset_dtime_subexp` of [PS10, §8.2, Theorem 180.1] in
`TCSlib/Cryptography/Randomness/Derandomization.lean`. The statement passed the prong D statement phase (ruling D-6: stated against `main`'s `InBPP` and `DTIME`) and Gate 06,
and is frozen. Its docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

**Not dispatchable as a pure fill yet.** The statement looks true, but step 4 needs a counting enumeration host that the library lacks, and the hosts-first rule requires its contract to be statement-gated in the shared layer first. The machine construction must also avoid the admitted `Build/Loop` (`loopHostTM_*`) and `Build/Wrappers` (`timedCondTM_*`) specs in `base-sorries.txt`.

**Estimated size:** 4,000–8,000 lines: the counting host 1,500–3,000 (cf. the enumerator behind `NP_subset_EXP`), the PRG step 1,000–2,000, majority and time analysis 1,000–2,000, the seed schedule and table 500–1,000. The plan's prong D estimate was 2–4k lines and called this theorem machine-level.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/derand` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/derand/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/derand/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill derand: checkpoint N` and `fill derand: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `seq-zk`, `canonizer`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Target (frozen; quoted from the issue base)

```lean
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Randomness`. There are no section variables. The theorem takes `hPRG : ∃ G : PRG, G.Secure`, `ε : ℝ` and `hε : 0 < ε`.

- **`BPP`** is `Randomized.InBPP Randomized.polyTimeModel` (`Complexity/Randomized/PolyTimeModel.lean`): a
  polynomial-time verifier with randomness `polyLen a k |x|` and error `1/3`.
- **`DTIME T`** (`Complexity/ClassP/DTIME.lean`, `DTIME.mono`): decided by a finite binary multi-tape machine within
  `c · T(n)` for some `c`.
- **`subexpBound ε n = ⌈2^{n^ε}⌉₊`** (`subexpBound_eq`, `subexpBound_pos`, owned).
- **PRGs** (`Pseudorandom/Generators/Asymptotic/Defs.lean`, `…/Stretch.lean`): `PRG.secure_iff`, `PRG.easy_iff`,
  `prg_expand`, `PRG.Secure.truncate`, `PRG.Secure.truncateTo_easy`, `PRG.Secure.truncateTo_negligible`.
- **The bridge** (`Randomness/BPPBridge.lean`): `polyLenExpr_eq`, `verifier_toNUPPT`, `randProb_eq_uprob`.

Read the module docstring's *formal reading* and the target's six-step sketch: step 4 states that the machine
construction is "the substantive remaining fill obligation, not supplied by the sketch".

## Published interfaces

| Interface | Provider |
|---|---|
| `subexpBound_eq`, `subexpBound_pos` | owned file |
| `polyLenExpr_eq`, `verifier_toNUPPT`, `randProb_eq_uprob` | `Randomness/BPPBridge.lean` |
| `PRG`, `PRG.secure_iff`, `PRG.easy_iff`, `prg_expand`, `PRG.Secure.truncate`, `truncateTo_easy`, `truncateTo_negligible` | `Pseudorandom/Generators/Asymptotic/{Defs,Stretch}.lean` |
| `Randomized.InBPP`, `polyTimeModel` and its readers | `Complexity/Randomized/*` |
| `DTIME`, `DTIME.mono`, `FinTM.DecidesInTime` | `Complexity/ClassP/DTIME.lean` |
| `exists_proj_decider` (existential enumeration, the nearest host), `counterLoopTM` and the `Build/` catalog (`machine-library-design.md` §14 is the host registry) | `Complexity/ClassNP/EXP.lean`, `Complexity/TuringMachine/Build/*` |
| `polyTimeComputable_blockMajorityTest` (majority over polynomially many blocks) | `Complexity/ClassNP/PolyTimeBlockMajority.lean` |
| `NUPPT.exists_withAdvice(On)` (advice: one bad input per seed length), `Negligible` readers | `Complexity/Randomized/Closure.lean`, `Foundations/Negligible.lean` |

## Proof route and checkpoints

1. **Checkpoint 1 · the counting enumerator host (scope request first).** Step 4 needs a deterministic machine that runs a decider on `x ++ u` for every seed `u` of width `w` and accepts iff more than half accept, within `b · 2^w · (T(n + w) + poly)`. No such host exists: `exists_proj_decider` is existential, its engine `enumMachine_contracts` is private, and the majority tests are polynomial-time over polynomially many blocks. Policy §1 (*Hosts come first*) forbids building it privately. Write its contract (statement and proof sketch, generic in the decider) and send it as a scope request to Seyoon before proving anything that depends on it. Send this checkpoint.
2. **Checkpoint 2 · the PRG step (sketch steps 1–2).** The integer seed schedule `ℓ(n)` (least `t` with `n ≤ t^d`), the envelope `P`, the expanded and truncated generator, and the contradiction: infinitely many bad input lengths give a non-uniform distinguisher at infinitely many seed lengths (advice: one bad input each, length at most `s^d`; `verifier_toNUPPT`, `randProb_eq_uprob`). Send this checkpoint.
3. **Checkpoint 3 · majority correctness (sketch step 3).** Eventually every input has gap at most `1/12`, so `M'` is correct with probability at least `7/12` and the majority over all seeds is correct. Send this checkpoint.
4. **Final · the machine and the time bound (sketch step 4).** The host applied to `M'` (with `G` run by its evaluator), the time `2^{ℓ(n)} · poly(n) ≤ c · 2^{n^ε}` eventually, and a finite table for the remaining lengths, giving `DTIME (subexpBound ε)`.

Check the edge cases: small `n` (the finite table); `ε ≥ 1`; `d` with `1/d < min(ε, 1)`; seed lengths shared by many input lengths; the expanded generator's output envelope at `s = ℓ(n)`; ties in the majority (the `1/12` margin excludes them).

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Randomness/Derandomization.lean` (97 lines at the issue base):
  - replace the target's proof body and edit its sketch to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Randomness/Derandomization/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - Helpers may import the machine library and the complexity classes already in the closure (for example `Complexity/ClassNP/EXP`, `Complexity/TuringMachine/Build/*`).
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines. Do not add to it.
  - **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
    import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff
    and the reason, and go ahead only on his approval. Record the request and his answer verbatim under
    `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. The Codex fills obtained their facade
    imports, and dl-crh its two `DiscreteLog` readers, this way. Seyoon prefers a route with no frozen-file edit
    where one exists.
  - A lemma that belongs in an existing file goes in your helper module, with a promotion request.
- **Parallel fills.** The seven fills `prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot` and
  `sc-compose` are issued from the same base. Edit only your owned file and helper directory.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:** `Complexity.NP_subset_EXP` and its enumerator `exists_proj_decider` (`ClassNP/EXP.lean`), `Randomized.mem_EXP_of_inBPP_polyTimeModel` (`Randomized/Inclusions.lean`, via Sipser–Gács), the block-majority tests (`ClassNP/PolyTimeBlock*.lean`) and `BPPAmplify`.
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file. The owned file's definitions
    are foreign to your helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (203 modules) and the narrow `roots.txt` (80), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (20 declarations in 10 modules). The only change
    must be the removal of `bpp_subset_dtime_subexp`.
- **Axioms.**
  - Print the axioms of `bpp_subset_dtime_subexp`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (after #305).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base and the status of each target;
  - the changed files and the sketch edits;
  - the new declarations;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**
