# Pass–shelat Chapters 2–4 campaign: agent briefing

Read this whole file before touching Lean. It is the only context you are guaranteed to share
with the other agents of this campaign.

## 0. Where you are

* Worktree: `/Users/dehmelf/Research/tcslib-pass-shelat` (git branch `cryptography/pass-shelat-ch2-4`,
  based on `cryptography/garg-ch1-3`). **Run every command from this directory.** Do not touch
  any other worktree (`tcslib`, `tcslib-garg`, …).
* Source text (pdftotext of R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., Jan 2010):
  `blueprint/src/references/pass-shelat-2010-ch2.raw.md`, `…-ch3.raw.md`, `…-ch4.raw.md`,
  `…-appendix.raw.md`. Results are numbered `<page>.<counter>` in the book, e.g. "Definition 27.3
  (Strong One-Way Function)" is on page 27. Cite them as `[PS10, Definition 27.3]`,
  `[PS10, Theorem 35.1]`, `[PS10, §2.4.3]`, `[PS10, Algorithm 64.2]`.
* Campaign plan: `PassShelatChapter2-4Plan.md` (scope, foundation decisions, module layout,
  decision log). Repository standards: `policy.md` (binding), `workflow.md`, `lean-glossary.md`.
  The sorry-ladder technique in `AGENTS.md` applies, **except** its ban on shell builds: on this
  campaign the verification path is the shell (`lake build <module>`, see §3).

## 1. Repository rules that bind every Lean file you write (digest of `policy.md`)

1. File header, verbatim shape:
   ```
   /-
   Copyright (c) 2026 TCSlib contributors. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: TCSlib contributors
   -/
   import …            -- precise imports only; a bare `import Mathlib` is forbidden
   set_option maxHeartbeats 0
   set_option relaxedAutoImplicit false
   set_option autoImplicit false
   /-! # Title … ## Main definitions … ## Main results … ## References … -/
   ```
   `## References` must contain the full citation
   `* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.`
   plus any other source you cite (`[Gar26]`, `[AB09]`, `[GL89]`, …; copy the existing entries from
   the files you build on).
2. Every public declaration has a docstring that **begins with a natural-language statement** of
   what it asserts (for a definition: what it is), then the `[PS10, …]` citation, then any
   **Deviation:** note (different constants, typed domain instead of `{0,1}*`, strict instead of
   expected polynomial time, …) with a one-line reason, then for nontrivial proofs a
   `**Proof sketch.**` paragraph in mathematical English naming the intermediate steps. Sorried
   theorems MUST carry the sketch (the sketch is the plan for the fill). Private helpers should
   have docstrings too.
3. Layout `TCSlib/<Area>/<Topic>/<Piece>.lean` + facade `TCSlib/<Area>/<Topic>.lean` with a
   `## Contents` list; 150–600 lines per file, never above 1000. Namespaces are topic-local
   (`TCSlib.Cryptography.…`, `Turing.…`, `Complexity.…`); helpers `private` or in an inner
   namespace. Facades must be imported from `TCSlib.lean` (the integrator does this; tell the
   integrator in your report which facade you created).
4. **Statement freeze / file ownership.** You own exactly the files named in your task. Never
   edit, rename, or re-state a declaration in a file you do not own (in particular nothing under
   `TCSlib/Complexity/` or `TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}`
   that predates this campaign). If you need a lemma in a shared file, put a `private` copy in
   your own file and list it in your report under "requested shared lemmas".
5. No new axioms. `sorry` is allowed only where your task says so, always under a proof sketch.
   Headline theorems are later checked with `#print axioms`: closed results must show exactly
   `[propext, Classical.choice, Quot.sound]`.
6. Lint: `python3 scripts/style_lint.py <file>` must report nothing for every file you touch.

## 2. Mathematical conventions fixed for this campaign (see the plan for rationale)

* **Security parameter `n`; bit strings of length `n` are `Fin n → Bool`** in experiments (the
  concrete layer's convention) and `List Bool` on machine tapes. Bridge: `List.ofFn`,
  `fun i => l.getD i false`. The string `1^n` is `List.replicate n true`.
* **Probability** is the uniform distribution on a finite type: `TCSlib.Cryptography.uprob`,
  `uexp` (`TCSlib/Cryptography/Foundations/Probability.lean`). Non-uniform distributions are
  pushforwards of uniform seeds (samplers `σ → γ`). Experiments: `invProb f A`, `predProb f B A`,
  `acceptProb X D`, `distAdv X Y D` (`Foundations/Experiments.lean`).
* **Negligible**: `TCSlib.Cryptography.Negligible (μ : ℕ → ℝ)` (`Foundations/Negligible.lean`),
  with `Noticeable`, closure lemmas, `not_negligible_iff` (infinitely-often form).
* **Polynomials are explicit formulas `C * (n + 1) ^ c`** (coefficient and degree quantified),
  never abstract `ℕ → ℕ` functions with a bound (audit lesson recorded in
  `TCSlib/Complexity/ClassNP/NP.lean`). `Complexity.PolyTimeComputable f` means some `FinTM Bool`
  computes `f : List Bool → List Bool` within `C * (n+1)^c`.
* **Pairing of strings** is `Turing.pairEncode x y` (self-delimiting; `pairDecode`,
  `Complexity.pairFstD`, `pairSndD`, closure lemmas in `TCSlib/Complexity/ClassNP/PolyTimePairing.lean`).
  Never use plain concatenation for a pair.
* **Machines**: `Turing.FinTM Bool` (bundled finite multi-tape TM, `TCSlib/Complexity/TuringMachine/Finite.lean`);
  `M.ComputesInTime x y t`, `M.ComputesFunInTime f T`, `M.DecidesInTime L T`; `Complexity.P`,
  `Complexity.NP` (verifier language + certificate length `C(|x|+1)^c`); advice machines
  `Turing.FinTM.DecidesWithAdviceInTime M L α T` (`CircuitComplexity/Advice.lean`, pairs
  `pairEncode x (α |x|)`, time measured in `|x|`).
* **Randomized machines** (new in this campaign, `TCSlib/Complexity/Randomized/`): a PPT is a
  `FinTM Bool` run on `pairEncode x r` with `r` a uniform coin string of explicit polynomial
  length; running time is bounded for **every** coin string (worst case, [PS10, Definition 23.5]);
  non-uniform PPT = PPT + polynomial-length advice string per input length
  ([PS10, Definition 26.8], advice formulation). The exact signatures are in the plan once
  frozen; before that, do not invent your own.
* **Inverses are sought in the domain at the current parameter** (an inverter's output is decoded
  as an `n`-bit string; a wrong-length output counts as failure). This is the concrete layer's
  convention; record it as a Deviation where [PS10] writes `f(A(1^n, y)) = y` over all strings.
* **Ensembles** are families of samplers from uniform bit seeds of explicit polynomial length
  (dyadic distributions); this covers every ensemble in [PS10]. Record as Deviation.
* **Interactive machines** (Chapter 4) are next-message functions computed by PPTs; simulators
  are strict PPT (expected polynomial time is not formalized; the GI simulator is truncated with
  failure probability `2^{-n}`, giving statistical rather than perfect zero-knowledge). Record as
  Deviation.

## 3. Verification protocol (the shell IS the verification path on this campaign)

* Compile one module: `lake build TCSlib.Cryptography.Asymptotic.OneWay` (module name = path
  with `/` → `.`, no extension). Lake only rebuilds what changed; all pre-existing modules are
  already built. Expect ~10 s for a small file plus elaboration time.
* Quick check without producing oleans (e.g. while iterating): `lake env lean <path>.lean`.
* **Run at most one Lean process at a time** (16 GB machine shared by several agents). Never run
  a bare `lake build` of the whole library, never `lake clean`, never `lake update`.
* Pass = exit code 0, no `error:` lines. `declaration uses 'sorry'` warnings are expected where
  your task permits sorries; count them in your report.
* Lint: `python3 scripts/style_lint.py <file.lean> …`.
* Axioms: put `#print axioms <decl>` lines in `audits/pass-shelat/Checks.lean` (shared; append
  only) or check ad hoc with a scratch file under `/tmp` compiled via `lake env lean`.

## 4. Existing API you must build on (do not re-prove these)

Concrete-layer cryptography (namespace `TCSlib.Cryptography`, source tag `[Gar26]`):
* `Foundations/Probability.lean`: `uprob`, `uexp`, `uprob_eq_card_filter`, `uprob_nonneg`,
  `uprob_le_one`, `uprob_not`, `uprob_mono`, `uprob_or_le`, `uprob_exists_le`, `uprob_prod`
  (Fubini), `uprob_comp_equiv`, `uprob_fst`, `half_le_uprob_good` (averaging),
  `abs_sub_le_sum_hybrids`, `exists_hybrid_gap` (hybrid lemma).
* `Foundations/Experiments.lean`: `invProb`, `predProb`, `acceptProb`, `distAdv`,
  `acceptProb_comp_equiv`, `distAdv_le_statDist`.
* `Foundations/Negligible.lean`: `Negligible`, `Noticeable`, `.add`, `.mul`, `.mul_pow`,
  `.const_mul`, `.mono`, `negligible_two_pow_neg`, `not_negligible_iff`, `not_negligible_sub`.
* `OneWayFunctions/Basic.lean` (namespace `…OneWay`): `uexp_*`, `uprob_and_le_mul`,
  `sum_uprob_eq_card_mul`, `uprob_pi_forall`, `uprob_update`, `uprob_eq_one_div_card`.
* `OneWayFunctions/Amplification.lean` (namespace `…OneWay`): `prodFun f q`, `yaoInverter`,
  `yao_amplification`, `yao_amplification_exp` — Yao's weak→strong amplification, concrete.
* `HardcoreBit/`: `ip` (inner product), `glPad`, `glBit`, `guessInverter`, `invProb_guessInverter`,
  `invProb_guessInverter_cubic` (Goldreich–Levin, concrete: `ε^3/(16n)`), `chebyshev_pairwise`,
  `PushesUniform`.
* `Pseudorandom/Indistinguishability.lean`: `sunglassRed`, `distAdv_sunglassRed` (closure under
  post-processing), `distAdv_comp`, `mixDist`, `copies`, `multicopyRed`, `exists_multicopyRed_ge`.
* `Pseudorandom/Generators.lean`: `prgAdv`, `prgExt`, `prgExtRed`, `exists_prgExtRed_ge`,
  `prgExtBits`, `exists_prgExtBitsRed_ge` (PRG expansion by hybrids).
* `Pseudorandom/GeneratorFromPermutation.lean`: `owpGen f B` = `(f x, B x)`, `owpPredictor`,
  `exists_owpPredictor`, `exists_owpPredictorBits` (PRG from OWP + hard-core bit).
* `Pseudorandom/Functions/`: `QueryTree`, `OracleAdversary`, `oracleDist`, `randomFunction`,
  `prfAdv`, `ggm`, `ggmBits`, `ggm_prfAdv_le`, `exists_ggmBits_dist` (GGM).
* Headline list and axiom prints: `audits/garg-ch1-3/Checks.lean`.

Complexity (namespaces `Turing`, `Complexity`, source tag `[AB09]`):
* `TuringMachine/Finite.lean`, `ClassP/{DTIME,P}.lean`, `ClassNP/{PolyTime,PolyTimePairing,NP,
  PClosure,Reductions}.lean` (`PolyTimeComputable`, `.comp`, `.pairEncode`, `polyTimeComputable_ite`,
  `polyTimeComputable_unary`, `polyTimeComputable_polyUnary`, `pairFstD/pairSndD`, `NP`,
  `PolyTimeReducible`, `NPHard`, `NPComplete`).
* `TuringMachine/Composition.lean`: `computesFunInTime_id/const/comp`, `exists_cond`;
  `Build/Wrappers.lean`: `computesFunInTime_cond` (timed branch);
  `Build/Loop.lean`: `exists_loopTM`, `exists_loopFindTM` (first accepting round's payload),
  `exists_emitLoopTM` (concatenate per-round chunks), `exists_installCallTM`,
  `exists_emitCallTM` (callable modules with clean seams); `Build/Primitives.lean`:
  `computesFunInTime_{prepend,lengthBits,polyUnary,polyBits,pairEncodeFixed,pairFst,pairSnd,
  pairValid,pairConcat,pairDup,pairMapSnd,pairLenCheck,stripLast,splitSolve,incFixed,unaryToken,appendBit}`.
* `TuringMachine/Universal.lean`: `timed_universal`, `timed_universal_concrete` (clocked universal
  simulation on `pairEncode (pairEncode (Nat.bits t) α) x`, quadratic in `t`); `Encoding.lean`:
  `CodeTM`, `MachineCode`, `EffectiveMachineCode`, `exists_codeTM`.
* `CircuitComplexity/Advice.lean`: `DecidesWithAdviceInTime`, `DTIMEAdvice`, `PAdvicePoly`.
* `CookLevin/Hardness.lean`: `SAT_NPComplete`, `SAT3_NPComplete`; `NPReductions/ThreeSATToColoring.lean`:
  `SATtoColorReduction` (graph-level, `SimpleGraph`, not a string reduction).
* `Cryptography/RSA.lean` (legacy, `TimeM` cost monad + `rsa_correctness` via CRT),
  `Cryptography/SchnorrProtocol.lean` (completeness, special soundness, HVZK by reindexing).

Mathlib (pinned revision `029db123ddaa`): `Nat.gcdA/gcdB/gcd_eq_gcd_ab` (extended Euclid),
`Nat.exists_mul_emod_eq_one_of_coprime`, `ZMod`, `ZMod.unitOfCoprime`, `ZMod.pow_totient` (Euler),
`ZMod.pow_card_sub_one_eq_one` (Fermat), `ZMod.chineseRemainder` (CRT, ring equiv),
`Nat.totient_prime`, `Nat.totient_mul`, `ZMod.euler_criterion`, `ZMod.exists_sq_eq_neg_one_iff`,
`Nat.primeCounting`, `Nat.primesBelow`, `Nat.exists_prime_lt_and_le_two_mul` (Bertrand),
`Nat.centralBinom` lemmas (`Nat.four_pow_lt_mul_centralBinom`, `Nat.centralBinom_le_of_no_bertrand_prime`,
factorization bounds in `Mathlib/NumberTheory/Bertrand.lean` and `Mathlib/Data/Nat/Choose/Factorization.lean`).
There is no Miller–Rabin and no Chebyshev `π(x) > x/(2 log x)` in Mathlib. Use
`grep -rn "theorem name" .lake/packages/mathlib/Mathlib` to locate lemmas; `exact?`/`apply?` work
inside `lake env lean`.

## 5. Reporting

Your final message is data for the orchestrator, not prose for a human. Report: files created or
changed (full paths), module names compiled and the exact outcome (exit code, error count, sorry
count per file), lint outcome, declarations added (name → one-line statement), deviations from
[PS10] you introduced, requested shared lemmas, open problems / blockers with the exact Lean goal
you were stuck on.
