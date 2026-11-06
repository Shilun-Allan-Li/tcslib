# Fill brief (DRAFT, not issued): the discrete-log candidates (`Candidates/{DiscreteLog, Concrete, DiscreteLogHardcore, ElGamal}`)

**Status: draft, 2026-11-05.**
- **Ruled 2026-11-05:** fill all 57 `Candidates` `sorry`s, discrete log first, because ch. 5–8
  cites the DL candidate in Thm 142.3. Each group is filled after its statement pack of gate 03
  closes; for these files, that is pack **03f1**.
- **Before issue:**
  - 03f1 closes, and any statement repairs it forces are applied, which re-freezes the targets
    below. Its round 1 review (`gates/03-ch2-4/review/gate03f1-review.md`) rewrites
    `fullDLCollection_hardCore`'s sketch (§1.4): `n²` coins for `t`, `n² +` A's coins per trial,
    `T ≤ 16n^c`, success `≥ 3/(256 n^{2c}) − (1 + 16n^{2c+2})·2⁻ⁿ`, and the binary numeral of
    `8n^c` in the inverter's advice. dl-b follows the corrected sketch. `hbig` stays in the
    statements (ruling R-03f1-1 (A));
  - the order lists and Mathlib roots of each unit;
  - an import probe of every cited name at the issue commit;
  - a review of this brief by a review sub-agent;
  - the issue commit (`@ANCESTOR@`).

The targets were written by Frederick Dehmel's campaign in run 2. Each is a `sorry` under a
detailed proof sketch, and the statements had the run-3a internal audit. This campaign has owned
them since 2026-11-05.

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out `cryptography/pass-shelat-ch2-4`
  at the issue commit `@ANCESTOR@`.
- Create your working branch from it (suggested `fill/dl-<unit>`). Record the base hash in
  `REPORT.md`, and never rebase.
- **Delivery is by zip**, `fill-dl-<unit>.zip`, with the standard contents:
  - `REPORT.md`;
  - the owned file;
  - a `git format-patch` series and a git bundle;
  - the sweep log and the axiom prints;
  - `SHA256SUMS`.

## Units (disjoint file ownership; they may run in parallel)

Cross-file dependencies are on **statements** only: a target may use another unit's sorried
theorem, and the integration replay closes the chain.

| Unit | Owned file(s) | Targets (`sorry`s) |
|---|---|---|
| **dl-a** | `Candidates/DiscreteLog.lean`, `Candidates/Concrete.lean` | `statClose_sampleBelowL`, `polyTimeComputable_expSampleRaw`, `expSampler_spec`, `expCollection_sampleClose`, `expCollection_invProbAt_le`, `expCollection_oneWay`; `statClose_rejectBlocksL` (7) |
| **dl-b** | `Candidates/DiscreteLogHardcore.lean` | `dlBits_pow`, `uprob_trial_ge`, `uprob_majOracle_ne_le`, `invProb_shiftInverter_ge`, `invProb_dlInverter_ge`, `polyTimeComputable_halfStr`, `fullDLCollection_hardCore` (7) |
| **dl-c** | `Candidates/ElGamal.lean` | `statClose_sq_generator`, `polyTimeComputable_egGenRaw`, `polyTimeComputable_egEncRaw`, `egDecStr_apply`, `elGamal_correct`, `polyTimeComputable_egGroupGenRaw`, `elGamal_secure` (7) |

Each target's docstring carries its proof sketch. **Follow it, or report why it fails.** The
sketches name the lemmas to use.

## Templates (cite; do not copy)

- **Samplers close to uniform:**
  - `statClose_rejectionSample` (`Asymptotic/Sampling.lean`) is the model for
    `statClose_rejectBlocksL`. `statClose_sampleBelowL` then follows from it through
    `sampleBelowL_eq_rejectBlocksL` (added by the gate 03 repair batch; gate 03f1 review, M2):
    fill it as a corollary, not a second copy;
  - also `statClose_firstHit`, `StatClose.comp_pushesUniform`, `StatClose.comp_equiv_right` and
    `StatClose.map`;
  - `statClose_permFromCoins` (`Asymptotic/Permutations.lean`) for a full worked instance.
- **Polynomial-time samplers and evaluators:**
  - the closure calculus (`Complexity/Randomized/Closure.lean`) and the pairing calculus
    (`Complexity/ClassNP/PolyTimePairing.lean`);
  - `Complexity.polyTimeComputable_iterateFind` for trial loops;
  - the proved instances `polyTimeComputable_prgPadFun` (`Asymptotic/Encryption.lean`), and
    `polyTimeComputable_preFun`/`postFun`/`blockMapFun` (`Asymptotic/MultiMessageLemmas.lean`);
  - the arithmetic is the hypothesis bundle `Candidates.ArithmeticFP` (decision D11). Never prove
    an arithmetic operation polynomial-time yourself: use the bundle's field. **If a needed
    operation is missing from the bundle, report it** (pack 03b audits the bundle).
- **The DL hard-core bit (dl-b):** the Goldreich–Levin inverter in `Asymptotic/HardCoreGL*.lean`,
  with its majority over polynomially many fresh-coin calls (`Complexity/Randomized/Repetition.lean`),
  is the machine-level model for `invProb_shiftInverter_ge`/`invProb_dlInverter_ge`.
- **Reductions to an assumption (dl-a, dl-c):**
  - `expCollection_invProbAt_le` is "the same machine, no reduction";
  - `elGamal_secure` reduces to DDH through the ensemble lemmas of `Asymptotic/Ensembles.lean`
    and the run-3a repair P8-1 (product seeds for `ddhReal`/`ddhRandom`).

## Ground rules (binding)

1. **Statement freeze.** Every definition and target statement is byte-identical in your delivery.
   Only the bodies of the listed `sorry`s change, plus new private helpers under your unit's
   prefix.
2. **Rule 10.** Read other files' definitions only through their published equations.
3. **Reuse, not copy.** If a lemma you need is private elsewhere, request it in `REPORT.md` and
   reprove a generic version under your prefix.
4. **Escalation.** A target that looks false or unprovable as stated is reported with the missing
   hypothesis or a counterexample, never patched. Pack 03f1 will already have screened them, so a
   report here is a finding against that pack.
5. **Budget:** complete targets beat partial ones. Order within a unit: the sampler and closeness
   lemmas first, then polynomial time, then the headline.

## Environment and verification

Use the environment addendum attached at dispatch, and **never `lake build`**. Fetch the Mathlib
cache for the order list's roots only. Final checks:
- each owned file with zero errors and no `sorry` warning for a filled target;
- axiom prints for every filled target: at most the standard triple;
- lint 0 FAIL on the owned files.

## REPORT.md checklist

- [ ] Each target: filled, partial (with its frontier), or escalated (with the reason).
- [ ] Every new `private`, with its role.
- [ ] The reuse-not-copy screen.
- [ ] The final sweep tail, the axiom prints and the lint line.
- [ ] The diff touches only the owned file(s).
