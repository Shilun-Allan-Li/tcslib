# Fill brief: the discrete-log candidates (`Candidates/{DiscreteLog, Concrete, DiscreteLogHardcore, ElGamal}`)

**Status: Issued @ISSUED@.** Issue commit `@ANCESTOR@` on `cryptography/pass-shelat-ch2-4`.

- **Ruled 2026-11-05:** fill all 57 `Candidates` `sorry`s, discrete log first, because ch. 5–8
  cites the DL candidate in Thm 142.3. Each group is filled after its statement pack of gate 03
  closes; for these files that is pack **03f1**.
- **Gate 03f1 is closed** (round 2: 0 blockers, 0 majors). Its repairs landed in PR #206 (merge
  `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`). They changed docstrings only, plus two new
  equations, `sampleBelowL_eq_rejectBlocksL` and `rejectBlocksL_eq`. The four files are unchanged
  from that merge to the pre-ship tree. `hbig` stays in both headline statements (ruling
  R-03f1-1 (A)).
- **Ruled 2026-11-06:** the three units may run in parallel on separate hosts.
- **Before issue:** the rule-10 prerequisites below land in `@ANCESTOR@`.

The targets were written by Frederick Dehmel's campaign in run 2. Each is a `sorry` under a
detailed proof sketch, and the statements had the run-3a internal audit and gate 03f1. This
campaign has owned them since 2026-11-05.

## Repository, branch and delivery (read this before anything else)

The exchange protocol is the `README.md` of the exchange branch `exchange/pass-shelat-ch5-8`.

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out `cryptography/pass-shelat-ch2-4`
  at the issue commit `@ANCESTOR@`.
- Work on a local branch `fill/<unit>` (`fill/dl-a`, `fill/dl-b`, `fill/dl-c`) created from
  `@ANCESTOR@`. **Never push it.** Record the base hash in `REPORT.md`, and never rebase.
- **Deliver by pushing `inbox/fills/<unit>/`** on the exchange branch `exchange/pass-shelat-ch5-8`,
  from a separate checkout or worktree of that branch. The folder holds:
  - `REPORT.md`;
  - `patches/`: the whole series from `git format-patch @ANCESTOR@..fill/<unit>`;
  - `src/`: the owned file(s) at your head, under their repository paths;
  - `evidence/`: the logs this brief and the addendum require (preflight, cache, bootstrap,
    sweep, axiom prints, lint, seal).
- Push that folder at each checkpoint, with the commit message `fill <unit>: checkpoint <n>`. The
  final push is `fill <unit>: final`. If your session ends early, your last checkpoint is the
  delivery.
- Write only `inbox/fills/<unit>/`. Run `git pull --rebase origin exchange/pass-shelat-ch5-8`
  before each push; if a push is rejected, pull with rebase again and retry. Never force-push. No
  PRs. Never merge the exchange branch anywhere.
- The source is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of
  `cryptography/pass-shelat-ch2-4` (SHA-256
  `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`; book page = PDF page − 12).


**Mathlib first (user direction 2026-11-06).** Before proving any number-theory fact, search the
pinned Mathlib. The names to cite for this fill are in `briefs/pass-shelat-ch5-8/mathlib-overlap-nt.md`,
section "Advice for the fill briefs" (all reachable from the owned files' current imports). Proving
a fact Mathlib already has is a reuse finding at delivery review.

## Units (disjoint file ownership; they may run in parallel, on separate hosts)

Cross-file dependencies are on **statements** only: a target may use another unit's sorried
theorem, and the integration replay closes the chain. In particular, dl-b's headline uses
`statClose_sampleBelowL` (a dl-a target) as stated.

| Unit | Owned file(s) | Targets (`sorry`s), in fill order |
|---|---|---|
| **dl-a** | `TCSlib/Cryptography/Candidates/Concrete.lean`, `TCSlib/Cryptography/Candidates/DiscreteLog.lean` | `statClose_rejectBlocksL` (Concrete); then `statClose_sampleBelowL`, `polyTimeComputable_expSampleRaw`, `expSampler_spec`, `expCollection_sampleClose`, `expCollection_invProbAt_le`, `expCollection_oneWay` (DiscreteLog) (7) |
| **dl-b** | `TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean` | `dlBits_pow`, `uprob_trial_ge`, `uprob_majOracle_ne_le`, `invProb_shiftInverter_ge`, `invProb_dlInverter_ge`, `polyTimeComputable_halfStr`, `fullDLCollection_hardCore` (7) |
| **dl-c** | `TCSlib/Cryptography/Candidates/ElGamal.lean` | `statClose_sq_generator`, `polyTimeComputable_egGenRaw`, `polyTimeComputable_egEncRaw`, `egDecStr_apply`, `elGamal_correct`, `polyTimeComputable_egGroupGenRaw`, `elGamal_secure` (7) |

**Build inputs** (records paths under `briefs/pass-shelat-ch5-8/fills/dl-candidates/`; computed by
`fillinputs.py` at the pre-ship tree):

| Unit | Order list (bootstrap) | Mathlib roots | Base sorries |
|---|---|---|---|
| dl-a | `inputs/dl-a/order.txt`, 94 modules | `inputs/dl-a/roots.txt`, 75 | `inputs/dl-a/base-sorries.txt`: 75 in 15 modules; the unit's 7 are the `Candidates/Concrete` (1) and `Candidates/DiscreteLog` (6) rows |
| dl-b | `inputs/dl-b/order.txt`, 94 modules | `inputs/dl-b/roots.txt`, 75 | `inputs/dl-b/base-sorries.txt`: 75 in 15 modules; the unit's 7 are the `Candidates/DiscreteLogHardcore` row |
| dl-c | `inputs/dl-c/order.txt`, 94 modules | `inputs/dl-c/roots.txt`, 75 | `inputs/dl-c/base-sorries.txt`: 75 in 15 modules; the unit's 7 are the `Candidates/ElGamal` row |

The three lists are identical: each owned module is upstream of the facade
`TCSlib/Cryptography/Candidates.lean`, so each closure contains all eight candidate files. Your
final sweep checks the whole list. A sorry outside your rows is not yours. Its count must not change.

Each target's docstring carries its proof sketch. **Follow it, or report why it fails.** The
sketches name the lemmas to use; read them with the corrections below.

### dl-a: fill order

1. `statClose_rejectBlocksL` first (Concrete), following its sketch (`firstHit` on `Fin (2^k)`,
   `statClose_firstHit`, `StatClose.comp_pushesUniform`, `StatClose.map Fin.val`).
2. `statClose_sampleBelowL` is then **a corollary, not a second copy** (gate 03f1 review M2,
   confirmed in round 2): rewrite with `sampleBelowL_eq_rejectBlocksL`, apply
   `statClose_rejectBlocksL (· < m) (Nat.size m) n n` with `d = 0`, transport the target along
   `Fin m ≃ {v : Fin (2^k) // v < m}` (`StatClose.comp_equiv_right`), and weaken
   `(1 − m/2^k)^n ≤ (1/2)^n` (`StatClose.mono`; the acceptance probability by `uprob_comp_equiv`
   with `bitsEquiv`, `bitsEquiv_val` and `uprob_bitsToNat_lt`). The pre-ship route probe proved
   exactly this under a seal (Pre-ship record).
3. Then `polyTimeComputable_expSampleRaw`, `expSampler_spec`, `expCollection_sampleClose`,
   `expCollection_invProbAt_le`, `expCollection_oneWay`. `expCollection_sampleClose` uses
   `statClose_sampleBelowL` directly on the sampler's `n · n` coins. Its sketch's mention of
   `NumberTheory.chunk` and `statClose_firstHit` describes what `statClose_sampleBelowL` already
   contains.

### dl-b: the headline route (`fullDLCollection_hardCore`)

Follow the docstring sketch: it is the gate 03f1 review §1.4 text, landed in #206. Gate 03f1
round 2 checked its constants. In short, for a predictor `A` with advantage at least `n^{−c}` on
infinitely many `n`:
- **Parameters:** `ε = 1/(2n^c)`, `s = ⌊(p−1)/(8n^c)⌋`, `T = ⌈(p−1)/s⌉`, `k = n` and
  `ℓ = 16n^{2c+1}`, so `k/(ε²ℓ) = 1/4`.
- **Large `n`:** take `n ≥ G.n₀`, `δ(n) ≤ ε/2`, `2^{n−1} − 1 ≥ 16n^c` and `16n^c < 2^n`. Then
  `(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16n^c) ≥ 1`, `4s ≤ ε(p−1)`, `Ts ≥ p − 1`, and
  **`T ≤ K(n) := 16n^c < 2^n`**. The ceiling adds no `+1`.
- **Good set:** `good_instances` gives mass `≥ ε`. Removing the short-prime coins (`hbig`, at most
  `δ(n) ≤ ε/2`) leaves mass `≥ ε/2`. The ideal success on each good instance is
  `≥ 3/(4T) ≥ 3/(4K(n))`. The `δ` loss is paid here once; do not subtract it again.
- **Predictor input:** the encoded group element,
  `A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ` (not `encD y`).
- **The machine `B`** is a non-uniform PPT:
  - **advice** `⟨A.advice n, ⟦8n^c⟧_n⟩`, the `n`-bit numeral of `8n^c`, exact once `8n^c < 2^n`.
    The bundle has no unary-to-binary conversion. No bundle field is added;
  - **coins** `n·n + n·ℓ·(n·n + A.coins)`, that is `n² + 16n^{2c+4} + 16n^{2c+2}·A.coinLen(n)`:
    one full `n²`-bit sampler tape for `t`, and for each of the `nℓ` trials one `n²`-bit tape for
    `r_{j,i}` plus fresh coins for `A`. This is a fixed `PolyExpr` (`c` is fixed);
  - **guard:** output `0^n` unless `1 ≤ s` and `T < 2^n`. The loops have fixed polynomial
    lengths, and the machine never iterates `T` times.
- **Sampling loss:** each of the `1 + nℓ` sampled coordinates is within `2^{−n}` of uniform
  (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`). With `StatClose.prod`
  and `StatClose.abs_uprob_sub_le_prod`, the loss is at most `(1 + 16n^{2c+2})·2^{−n}` at every
  instance.
- **Conclusion:** `G.dlProb B n ≥ 3/(256n^{2c}) − (1 + 16n^{2c+2})·2^{−n}`, which is eventually
  `≥ 3/(512n^{2c})`, for infinitely many `n`. This contradicts `hDL B` (`not_negligible_iff`).
- **`hbig` is retained** (ruling R-03f1-1 (A)). Do not try to drop it.

## Imports you may add

Only these:
- **dl-a:** none. Every cited name is reachable from the owned files' imports.
- **dl-b:** none. (`Ensemble.indist_iff_exists_negligible` in the headline's sketch is an analogy
  only, "`…`-style". Its module `Asymptotic/Ensembles` is not imported by
  `DiscreteLogHardcore`, and it is not authorized. Read `HardCore` through its prerequisite
  equation below.)
- **dl-c:** optionally `import TCSlib.Cryptography.Candidates.DiscreteLogHardcore`, and only if
  you take the `dlog` alternative in Hybrid 3 of `elGamal_secure` (`HardcoreBit.pushesUniform_add_right`
  on the exponent `z + dlog m'_b`). It creates no cycle and adds one module, which is already in
  your order list. The route the sketch names first, `Equiv.mulRight`, needs no import; prefer it.

## Name corrections (the sketches as they stand at the issue tree)

The docstrings are frozen. Where a sketch names a lemma that does not resolve under the owned
file's `open`s, use the full name:

| Sketch | Written | Use |
|---|---|---|
| `invProb_shiftInverter_ge` | `pushesUniform_fst` | `HardcoreBit.pushesUniform_fst` |
| `invProb_shiftInverter_ge` | `uprob_eq_one_div_card` | `OneWay.uprob_eq_one_div_card` |
| `uprob_majOracle_ne_le`, `invProb_dlInverter_ge` | `pushesUniform_eval` | `HardcoreBit.pushesUniform_eval` |
| `uprob_majOracle_ne_le` | `PairwiseUniform.pairwiseIndep` | `HardcoreBit.PairwiseUniform.pairwiseIndep` |
| `uprob_majOracle_ne_le` | `two_mul_card_le_of_majority_ne` | `HardcoreBit.two_mul_card_le_of_majority_ne` |
| `statClose_sq_generator` | `PushesUniform.uprob_eq` | `HardcoreBit.PushesUniform.uprob_eq` |
| `elGamal_secure` | `dlog` | `dlog` of `DiscreteLogHardcore` (not imported; see Imports) |

Every other name cited by this brief or by the 21 target sketches resolves in the owned file's
scope at the pre-ship tree. `statClose_sampleBelowL`'s docstring also names its downstream consumers
`ddhExpo`, `egUnit`, `egGenParts` and `egEncParts` (in `ElGamal`); dl-a does not need them.

## Templates (cite; do not copy)

These are read as models. The template modules marked † are not in your order list. Do not
import them.
- **Samplers close to uniform:**
  - `statClose_rejectionSample` (`Asymptotic/Sampling.lean`) is the model for
    `statClose_rejectBlocksL`. `statClose_sampleBelowL` follows from it as above;
  - also `statClose_firstHit`, `StatClose.comp_pushesUniform`, `StatClose.comp_equiv_right` and
    `StatClose.map` (all in `Asymptotic/Sampling.lean`);
  - `TCSlib.Cryptography.statClose_permFromCoins` (`Asymptotic/Permutations.lean` †) for a full
    worked instance;
  - `statClose_sampleEdgeIdx` (`ZeroKnowledge/ThreeColoring/Language.lean` †): the same
    `2^{Nat.size m} ≤ 2m` bound, for a sampler with stride `Nat.size m`. It is related, not a
    duplicate.
- **Polynomial-time samplers and evaluators:**
  - the closure calculus (`Complexity/Randomized/Closure.lean`) and the pairing calculus
    (`Complexity/ClassNP/PolyTimePairing.lean`);
  - `Complexity.polyTimeComputable_iterateFind` for trial loops;
  - the proved instances `TCSlib.Cryptography.polyTimeComputable_prgPadFun`
    (`Asymptotic/Encryption.lean` †) and `TCSlib.Cryptography.MultiMsg.polyTimeComputable_preFun`,
    `…_postFun`, `…_blockMapFun` (`Asymptotic/MultiMessageLemmas.lean` †);
  - the arithmetic is the hypothesis bundle `Candidates.ArithmeticFP` (decision D11). Never prove
    an arithmetic operation polynomial-time yourself: use the bundle's field (`H.mul`, `H.add`,
    `H.sub`, `H.divMod`, `H.xgcd`, `H.modExp`, `H.le`, `H.size`, `H.prime`). **If a needed
    operation is missing from the bundle, report it** (pack 03b audits the bundle).
- **The DL hard-core bit (dl-b):** the Goldreich–Levin inverter in `Asymptotic/HardCoreGL*.lean` †,
  with its majority over polynomially many fresh-coin calls (`Complexity/Randomized/Repetition.lean`),
  is the machine-level model for `invProb_shiftInverter_ge`/`invProb_dlInverter_ge`.
- **Reductions to an assumption (dl-a, dl-c):**
  - `expCollection_invProbAt_le` is "the same machine, no reduction";
  - `elGamal_secure` reduces to DDH through the ensemble lemmas of `Asymptotic/Ensembles.lean`
    and the run-3a repair P8-1 (product seeds for `ddhReal`/`ddhRandom`).

## Prerequisites (rule 10): equations that land before issue

Rule 10 forbids reading another file's TCSlib definition except through a published lemma. At the
pre-ship tree the sketches need the definitions below, and these have no such lemma. A
prerequisite PR lands them in `@ANCESTOR@`. The issued brief gives their exact names; the forms
below are what that PR is asked for (each with a docstring stating its formula, no `@[simp]`).

| Prerequisite | Beside | Form | Used by |
|---|---|---|---|
| `firstHit_eq` | `firstHit` (`Asymptotic/Sampling.lean`) | `firstHit E xs = (List.finRange T).findSome? fun t => if E (xs t) then some (xs t) else none` | dl-a `statClose_rejectBlocksL` |
| `statClose_iff` | `StatClose` (`Asymptotic/Sampling.lean`) | `StatClose X Y δ ↔ ∀ T, |uprob (T ∘ X) − uprob (T ∘ Y)| ≤ δ` | dl-c `statClose_sq_generator` |
| `NUPPT.coinLen_eq` | `coinLen` (`Complexity/Randomized/PPT.lean`) | `A.coinLen n = A.coins.eval n` (also a prerequisite of the efficiency brief) | dl-a `expCollection_sampleClose`; dl-b headline; dl-c `elGamal_correct`, `elGamal_secure` |
| `NUPPT.distinguisherL_eq` | `distinguisherL` (`Asymptotic/Adversary.lean`) | `A.distinguisherL n w r = decide (A.runAt n w r = [true])` | dl-b headline; dl-c `elGamal_secure` |
| `predProb_eq`, `invProb_eq`, `distAdv_eq` | `Foundations/Experiments.lean` | the bodies (`uprob fun z : α × ρ => …`; `|acceptProb X D − acceptProb Y D|`) | dl-b `uprob_trial_ge`, `uprob_majOracle_ne_le`, `invProb_shiftInverter_ge`; dl-c `elGamal_secure` |
| `Collection.sampleClose_iff`, `Collection.invProbAt_eq`, `Collection.hardCore_iff` | `Asymptotic/Collections.lean` | the bodies of `SampleClose`, `invProbAt`, `HardCore` | dl-a `expCollection_sampleClose`, `expCollection_invProbAt_le`; dl-b headline |
| `divModStr_pairEncode`, `xgcdStr_pairEncode`, `sizeStr_eq`, `natToList_eq` | `Candidates/Arithmetic.lean` | `divModStr ⟨a, b⟩ = ⟨⟦a / b⟧_{|a|}, ⟦a mod b⟧_{|b|}⟩`; `xgcdStr ⟨a, b⟩ = ⟨⟦gcd⟧_{|b|}, ⟦(a : Z_b)⁻¹.val⟧_{|b|}⟩`; `sizeStr w = 1^{Nat.size ⟦w⟧}`; `natToList k N = List.ofFn (natToBits k N)` | dl-b `polyTimeComputable_halfStr`, headline; dl-c `polyTimeComputable_egEncRaw`, `egDecStr_apply`, `elGamal_correct`; `sizeStr_eq` for dl-a/dl-c's samplers if a step needs more than `length_sizeStr` |
| `dlP_eq`, `dlM_eq`, `dlG_eq` (or their `pairEncode` forms) | `Candidates/DiscreteLog.lean` | `dlP i = listToNat (pairFstD i)`, `dlM i = listToNat (pairFstD (pairSndD i))`, `dlG i = listToNat (pairSndD (pairSndD i))` | dl-b headline; dl-c `polyTimeComputable_egEncRaw`, `elGamal_correct`, `elGamal_secure` |
| `expValid_iff`, `wellFormedIndex_iff`, `safePrimeValid_iff`, `ExpGroupGen.fullLengthExcept_iff`, `ExpGroupGen.dlHard_iff`, `ExpGroupGen.dlProb_eq`, `expF_eq` | `Candidates/DiscreteLog.lean` | the bodies | dl-b headline; dl-c `elGamal_correct`, `elGamal_secure` |
| `expCollection`'s field equations (`f`, `encD`, `decD`, `gen`, `sample`; `expCollection_D` exists) | `Candidates/DiscreteLog.lean` | `simps` with `(config := { isSimp := false })`, or `rfl` lemmas | dl-b headline |

The `DiscreteLog.lean` rows are dl-a's file. dl-a may not add public lemmas (ground rule 1), so
they belong to the prerequisite PR as well. In your own file you may unfold its definitions, but
prefer their equation lemmas.

Already published and sufficient (read through these): `rejectBlocksL_eq`, `rejectBlocksL_spec`,
`sampleBelowL_eq_rejectBlocksL`, `sampleBelowL_lt`, `bitsEquiv_val`, `bitsToNat_eq_listToNat`,
`uprob_bitsToNat_lt`, `mem_QR_iff`, `coe_sqTo`, `leStr_pairEncode`, `modExpStr_pairEncode`,
`mulStr_pairEncode`, `subStr_pairEncode`, `addStr_pairEncode`, `length_sizeStr`,
`listToNat_natToList`, `natToList_length_listToNat`, `decodeFin_ofFn`, `ofFn_of_decodeFin_eq_some`,
`padFin_ofFn`, `NUPPT.inParam_layout`/`inArg_layout`/`inAdvice_layout`/`inCoins_layout`,
`NUPPT.runAt_eq`, `NUPPT.runAtL_ofPolyTime(Uniform)`, `NUPPT.coins_ofPolyTime(Uniform)`,
`NUPPT.distinguisher_eq`, `expCollection_D`, `expCollection_index(_of_lt)`, `expOrd_of_valid`,
`WellFormedIndex.dlW_eq`, `dlP_lt_two_pow`, `Ensemble.indist_iff_exists_negligible`,
`not_negligible_iff`, the `HardcoreBit.majority` lemmas and the `uprob`/`uexp`/`acceptProb`
calculus. A definition you need that is in neither list is reported in `REPORT.md`: do not read it
another way.

## Ground rules (binding)

1. **Statement freeze.** Every definition and target statement is byte-identical in your delivery.
   Only the bodies of the listed `sorry`s change, plus new private helpers under your unit's
   prefix.
2. **Rule 10.** Read other files' definitions only through their published equations (the
   prerequisites and the list above). Never pass another file's TCSlib definition to `unfold`,
   `simp`, `rw`, `delta` or `dsimp`, and never read it through `rfl`, `show`, `decide` or
   term-mode defeq. Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step,
   but are never passed to `simp`, `rw` or `unfold`. Reducible abbreviations are notation.
3. **Reuse, not copy.** If a lemma you need is private elsewhere, request it in `REPORT.md` and
   reprove a generic version under your prefix.
4. **Escalation.** A target that looks false or unprovable as stated is reported with the missing
   hypothesis or a counterexample, never patched. Pack 03f1 has screened them, so a report here is
   a finding against that pack.
5. **Budget:** complete targets beat partial ones. Order within a unit: the sampler and closeness
   lemmas first, then polynomial time, then the headline (dl-a: the fill order above).

## Environment and verification

Use the environment addendum attached at dispatch (`fill-environment-addendum.md`, v1), and
**never `lake build`**. Fetch the Mathlib cache for your order list's roots only
(`inputs/<unit>/roots.txt`, 75 modules, unless you add the one authorized import). One Lean process
at a time on your host. Final checks:
- each owned file with zero errors and no `sorry` warning for a filled target, then the sweep of
  the whole order list;
- axiom prints for every filled target: at most the standard triple
  `[propext, Classical.choice, Quot.sound]`;
- **rule 10 seal:** a sealed copy of each owned file, with `attribute [local irreducible]` on every
  other-file TCSlib definition your proofs mention (and `attribute [-simp]` on those that are
  `@[simp]`), compiles, and one control closes unsealed and fails sealed. List the sealed names
  in `REPORT.md`;
- lint 0 FAIL on the owned files (`python3 scripts/campaign_style_lint.py TCSlib/Cryptography/Candidates`).

## REPORT.md checklist

- [ ] Each target: filled, partial (with its frontier), or escalated (with the reason).
- [ ] Every new `private`, with its role.
- [ ] The reuse-not-copy screen.
- [ ] Any prerequisite or definition you found missing, and any name correction you needed beyond
      the table above.
- [ ] The final sweep tail, the axiom prints, the seal (sealed names and control) and the lint line.
- [ ] The diff touches only the owned file(s); the base hash (`@ANCESTOR@`) and the head hash of
      `fill/<unit>`.
- [ ] Delivered as `inbox/fills/<unit>/` on the exchange branch (`REPORT.md`, `patches/`, `src/`,
      `evidence/`); the commit of the final push is `fill <unit>: final`.

## Pre-ship record

Run on 2026-11-06 at the records commit `5f2771631fe853dae9c2aa44791ae5b0e09c95eb` (gates 03f1, 03g
and 03l closed). The four owned files there are identical to the #206 merge. Lean was run one
process at a time with `scripts/lean_check_tree.sh` against a full olean tree of that commit, and
never `lake build`. Logs are under `briefs/pass-shelat-ch5-8/fills/dl-candidates/preship/`. If the
prerequisite PR changes any import, re-run `fillinputs.py` at `@ANCESTOR@` before issue.

- **Build inputs** (`inputs/<unit>/`, by `fillinputs.py` at that commit; for dl-a the union of the
  two owned modules, whose lists coincide): order 94 modules and roots 75 for each unit. The base
  sorry set is 75 in 15 modules. Each unit's rows are exactly its 7 targets, matching the draft's
  list.
- **Import probe** (`preship/import-probe-dl-{a,b,c}.log`): a `#check` of every name cited by the
  draft and by the 21 target sketches, in each owned file's scope.
  - All are present, except the qualified-name cases in **Name corrections** (each verified under
    its full name) and `dlog` (dl-c, optional import, no cycle).
  - The templates resolve under their full names in modules no owned file imports. The draft's
    bare `polyTimeComputable_preFun`/`postFun`/`blockMapFun` do not resolve; the full names are
    given above.
  - The "already published" list above was probed too: 46 names, all present.
- **Duplication probe** (`preship/dup-probe-dl-{a,b,c}.log`): each target's `sorry` was replaced by
  `exact?` in a copy of its file, so the target cannot match itself.
  - Pass 1 ran at `maxHeartbeats 400000`; the targets that timed out were rerun at 2000000.
  - Not found: 12 targets (`polyTimeComputable_expSampleRaw`, `expCollection_sampleClose`,
    `dlBits_pow`, `uprob_trial_ge`, `uprob_majOracle_ne_le`, `invProb_dlInverter_ge`,
    `polyTimeComputable_halfStr`, `fullDLCollection_hardCore`, `polyTimeComputable_egGenRaw`,
    `polyTimeComputable_egEncRaw`, `polyTimeComputable_egGroupGenRaw`, `elGamal_secure`).
  - Timed out at both budgets: the other 9.
  - A library grep finds no declaration of any target's name outside `Candidates/`, and no
    equivalent statement. The nearest relatives (`statClose_rejectionSample`, `statClose_firstHit`,
    `statClose_sampleEdgeIdx`, `HardcoreBit.uprob_majority_fails_le`) are listed there.
- **Route probe** (`preship/route-probe-dla.log`): with `statClose_rejectBlocksL` as given, the
  statement of `statClose_sampleBelowL` is proved through `sampleBelowL_eq_rejectBlocksL` under
  the seal `rejectBlocksL sampleBelowL StatClose uprob listToNat firstHit bitsToNat bitsEquiv
  HardcoreBit.PushesUniform Nat.size`.
  - It compiles with 0 errors and 0 warnings.
  - The controls show the seal is active (sealed `rfl` on `rejectBlocksL` and a lambda for
    `StatClose` fail).
  - Its axioms are the standard triple plus `sorryAx` from `statClose_rejectBlocksL` only. Nothing
    is missing.
- **Rule 10 note** (`preship/rule10-note.log`): the foreign definitions each sketch reads, with
  their published lemmas (check 8 of `campaign_style_lint.py` and a lemma-name survey). The
  missing ones are the **Prerequisites** table. This is a reading-based screen: no fill proofs
  exist yet, so only the route probe is a sealed compile.
- **Not checked here:** the fills themselves, the 9 targets whose `exact?` timed out (no
  duplicate found, but not excluded by `exact?`), and the brief review by a review sub-agent, which
  is still to do.
