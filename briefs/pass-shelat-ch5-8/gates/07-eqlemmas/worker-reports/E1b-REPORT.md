## E1b report (equation-lemma PR, gate 07)

**Commit:** `55988d16c5cd154838074b835d8e681b2945b74c` on `wip/eqlemmas-e1b`. Its parent is the base `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`. Not pushed. Only six owned files change, and only by additions: `Candidates/{Arithmetic, Concrete, DiscreteLog, Factoring, RSA}.lean` and `NumberTheory/Primality.lean`.

### Added lemmas
All are public and none is `@[simp]`. Each has a docstring that states its formula and is proved by `rfl` or `Iff.rfl`, except where the table gives a short proof.

| Name | File:line | Statement | Source |
|---|---|---|---|
| `natToList_eq` | Arithmetic:92 | `natToList k N = List.ofFn (natToBits k N)` | DL prereq |
| `sizeStr_eq` | Arithmetic:297 | `sizeStr w = List.replicate (Nat.size (listToNat w)) true` | DL prereq |
| `divModStr_pairEncode` | Arithmetic:346 | `divModStr ⟨a,b⟩ = ⟨⟦a/b⟧_{\|a\|}, ⟦a%b⟧_{\|b\|}⟩` (`simp [divModStr]`) | DL prereq, fac P9 |
| `xgcdStr_pairEncode` | Arithmetic:353 | `xgcdStr ⟨a,b⟩ = ⟨⟦gcd⟧_{\|b\|}, ⟦((a:Z_b)⁻¹).val⟧_{\|b\|}⟩` (unfold + rw) | DL prereq, fac P9 |
| `NumberTheory.chunk_apply` | Primality:688 | `chunk T n r t i = r (finProdFinEquiv (t, i))` (4-line proof from the draft) | fac P7 |
| `DistinctPrimes.p_eq` / `q_eq` | Concrete:371 / 378 | `z.p = ((z.1.1 : Fin (2^n)) : ℕ)` / `z.q = ((z.1.2 : Fin (2^n)) : ℕ)` | fac P6 |
| `DistinctPrimes.default_p` / `default_q` | Concrete:459 / 462 | `(default hn).p = 2` / `(default hn).q = 3` | fac P6 |
| `encodeDistinctPrimes_eq` | Concrete:484 | `encodeDistinctPrimes m z = ⟨⟦p⟧_m, ⟦q⟧_m⟩` | fac P6 |
| `dlP_eq` / `dlM_eq` / `dlG_eq` | DiscreteLog:122 / 130 / 137 | `dlP i = listToNat (pairFstD i)`, and the same for the middle and last components | DL prereq |
| `wellFormedIndex_iff` | DiscreteLog:150 | the body of `WellFormedIndex` | DL prereq |
| `expValid_iff` | DiscreteLog:180 | the body of `ExpValid` | DL prereq |
| `expEnc_eq` | DiscreteLog:238 | `expEnc i x = natToList (dlW i) x.val` | not requested: see finding 2 |
| `expF_eq` | DiscreteLog:268 | `expF i x = natToList (dlW i) (dlG i ^ x.val % dlP i)` | DL prereq |
| `ExpGroupGen.fullLengthExcept_iff` | DiscreteLog:375 | the body of `FullLengthExcept` | DL prereq |
| `ExpGroupGen.dlProb_eq` | DiscreteLog:397 | the body of `dlProb` | DL prereq |
| `ExpGroupGen.dlHard_iff` | DiscreteLog:413 | `G.DLHard ↔ ∀ A, Negligible fun n => G.dlProb A n` | DL prereq |
| `expCollection_f` / `_encD` / `_decD` | DiscreteLog:651 / 657 / 663 | `(expCollection H G hV).f i x = expF i x`, and the same with `expEnc` and `expDec` (fully applied, the `simps` form) | DL prereq |
| `expCollection_gen` / `_sample` | DiscreteLog:668 / 672 | `… .gen = expGen G` / `… .sample = expSampler H` | DL prereq |
| `safePrimeValid_iff` | DiscreteLog:754 | the body of `SafePrimeValid` | DL prereq |
| `modulusBits_eq` | Factoring:208 | `modulusBits n z = natToBits (2n) (z.p * z.q)` | fac P10 |
| `factorProb_eq` | Factoring:233 | the body of `factorProb` | fac P10 |
| `polyTimeComputable_samplePrimeL` (S1, sorry) | Factoring:495 | as drafted | D1 (A), fac item 3 |
| `statClose_samplePrimeL_pair` (S2, sorry) | Factoring:523 | as drafted | D1 (A), fac item 1 |
| `eval_rsaBlock` / `eval_rsaTrials` / `eval_rsaSampleCoins` | RSA:339 / 347 / 353 | `= 2(n+2)` / `= (4n+8)n` / `= rsaTrials.eval n * rsaBlock.eval n` | fac P12 |
| `sampleUnitL_eq` | RSA:372 | `sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r` | fac P12 |
| `statClose_sampleUnitL` (S3, sorry) | RSA:404 | as drafted | D1 (A), rsa item 2 |
| `unitSampleStr_eq` | RSA:423 | the body of `unitSampleStr` | fac P12 |

**S1–S3:**
- After normalising whitespace, all three statements are identical to `preship/probes/Prereqs.lean`. The only edit is that S3's statement is re-wrapped to stay within 100 columns.
- Placement:
  - S1 and S2 come right after `samplePrimeL`, before their first users (`polyTimeComputable_samplePairRaw` and `factoringCollection_sampleClose`).
  - S3 comes after `sampleUnitL_spec`, before `rsaCollection_sampleClose`.
- Each has a [PS10] citation and a full proof sketch:
  - S1: Algorithm 50.16 and Lemma 51.17.
  - S2: Lemma 51.17 and Theorem 51.1.
  - S3: Theorem 53.2.
- Every lemma named in the sketches resolves; the probe is `probes/Names.lean`.
- **Truth check (my own reading): no doubts.**
  - **S1:** a pad, at most `2n²` prime tests on `n`-bit blocks, and a branch to the `n`-bit fallback. This is polynomial in `n ≤ |z|` given `hP`. At `n = 0` both sides are `[]`.
  - **S2:** each half is within `(1−1/(2n))^{2n²} ≤ e^{−n} ≤ 2^{−n}` of a uniform prime of `Π_n`, because the fallback `2` is prime and below `2^n` when `n ≥ 2`. The product of the two halves is within `2·2^{−n}`. The uniform pair and the uniform *distinct* pair differ by exactly the diagonal mass `1/|Π_n| ≤ 2n/2^n`.
  - **S3:**
    - The default `1 % N` passes the test (it is `0` when `N = 1`, and `0` is coprime to `1`).
    - The target is in value-preserving bijection with `(ZMod N)ˣ`, since `N < 2^k`.
    - The acceptance rate is `φ(N)/2^k ≥ 1/(2k) ≥ 1/(4n+8)`, using `2^k ≤ 2N` and `N ≤ φ(N)(log₂N+1) ≤ φ(N)·k`.
    - Then `(1−1/(4n+8))^{(4n+8)n} ≤ e^{−n}`.
    - At `n = 0` it holds trivially (`T = 0`, bound `1`).
    - Its proof relies on dl-a's sorried target `statClose_rejectBlocksL`, which is the route the brief gives.

**Reused, not re-added:** `dlAssumption_iff`, `expCollection_D`, `expCollection_index`, `rejectBlocksL_eq`, `primeStr_eq`, `eval_samplePrimeCoins`. A grep found no existing lemma, under any name, with the content of any lemma I added. None of the additions is a number-theory fact, so the Mathlib-first rule does not apply; `mathlib-overlap-nt.md` has no row for any of them.

**Not added:** `samplePrimeL_eq` (P11). The brief needs it only under D1 (B).

### For E1a (requested lemmas outside my files)
- `firstHit_eq` and `statClose_iff` (fac P3), in `Asymptotic/Sampling.lean`.
- `NUPPT.coinLen_eq` and `NUPPT.advInput_eq` (P5), in `Complexity/Randomized/PPT.lean`.
- `NUPPT.inParam_eq`, `inArg_eq`, `inAdvice_eq`, `inCoins_eq` (P5), in `Randomized/Closure.lean`.
- `NUPPT.distinguisherL_eq`, in `Asymptotic/Adversary.lean`.
- `predProb_eq`, `invProb_eq`, `distAdv_eq`, in `Foundations/Experiments.lean`.
- In `Asymptotic/Collections.lean`:
  - `Collection.sampleClose_iff`, `Collection.invProbAt_eq`, `Collection.index_eq` (P1);
  - `Collection.hardCore_iff` (DL);
  - `TrapdoorCollection.oneWay_iff` (P2).
- `FunFamily.easy_iff` (P4), in `Asymptotic/OneWay.lean`.
- `OneWay.yaoTry_eq` and `OneWay.prodFun_apply` (P8), in `OneWayFunctions/Amplification.lean`.

### Findings and questions for the maintainer
1. **`@[simp]` convention.** In `Arithmetic.lean` the sibling `mulStr_pairEncode`, `addStr_pairEncode`, `subStr_pairEncode`, `leStr_pairEncode` and `modExpStr_pairEncode` are all `@[simp]`. I added `divModStr_pairEncode` and `xgcdStr_pairEncode` without it, as the brief says. Should they get `@[simp]` to match?
2. **Existing cross-file read, and the extra lemma.** `DiscreteLogHardcore.lean:516` already unfolds `expEnc` and `dlP` from `DiscreteLog` with `simp only [halfStr, halfPred, expEnc, dlP, …]`. That is why I added `expEnc_eq`, which no source list asked for. I did not re-point that proof, because this PR changes no existing proofs.
3. **Seal limit for `expCollection`.**
   - The field equations cover value-level readings.
   - The domain type `(expCollection H G hV).D i` is `ZMod (expOrd i)` only by definition, and `expCollection_D` is an equality of types.
   - Under `attribute [local irreducible] expCollection`, a term `x : D i` cannot be passed to lemmas typed on `ZMod (expOrd i)` without a cast. The probe showed `expDec_expEnc i x` fails sealed.
   - dl-b's seal (and the gate) need a policy here: either keep `expCollection` reducible at the type level, or transport with `cast`/`expCollection_D`.
4. **Lint heuristic.** Check 8 still lists `rsaBlock`, `rsaTrials` and `rsaSampleCoins`, because their lemmas follow the file's `eval_samplePrimeCoins` naming. It still lists `DLHard`, because `dlHard_iff` does not match its case rule. Both are cosmetic.
5. **File size.** `RSA.lean` grows from 926 to 981 lines, so the fill will pass 1000. The brief already expects this.
6. **03f2 delta round.** D1 (A) says S1–S3 need a short 03f2 delta round. That round is still outstanding.

### Checks (logs in `$SP/e1/e1b/`)
1. **Replay** of all 11 downstream modules and `audits/pass-shelat/Checks`: 0 errors (`replay-final.log`, full logs in `full-final/`, counts in `sorry-counts.txt`).
   - `sorry` counts match the base (`replay-base.log`) in every module except Factoring (8→10) and RSA (9→10). The three new warnings are exactly S1, S2 and S3.
   - The `Checks` output is identical to the base (`checks-base.out` vs `checks-final.out`).
   - The only other warnings are ElGamal's three section-variable warnings, which ElGamal already has (the file is unchanged).
2. **Axioms** (`axioms.log`):
   - 28 of the 36 new declarations print the standard axioms only (some depend on no axioms at all).
   - S1–S3 print `sorryAx`, as intended.
   - The five `expCollection_*` field lemmas print `sorryAx`, inherited from the definition `expCollection`, which is built on sorried targets. The existing `expCollection_D` prints the same (`axioms-ref.log`).
3. **Lint:**
   - `style_lint.py` reports 0 findings on each of the six files.
   - `campaign_style_lint.py --check8b`, base vs head (`lint8b-{base,new}-*.log`), shows no new FAIL or WARN. The 8 FAILs are already in the base. WARNs drop 8→6 in Candidates (Arithmetic and Concrete clear), and `chunk` leaves Primality's check-8 list.
4. **Statement diff** (`decls-diff.tsv`): 36 rows, all ADDED.
5. **Seal probes** (`probes/`), one per consumer route, each a pass file plus a control:

| Route | Lemma groups | Pass (sealed) | Control: unsealed closes, sealed fails |
|---|---|---|---|
| DL (imports of `DiscreteLogHardcore`) | DiscreteLog, Arithmetic | `seal-dl-pass.log`, rc 0 | 17/17 fail sealed (`seal-dl-control.log`) |
| Factoring | Concrete, Primality | `seal-fac-pass.log`, rc 0 | 6/6 (`seal-fac-control.log`) |
| RSA | Factoring incl. S1/S2, Arithmetic | `seal-rsa-pass.log`, rc 0 | 5/5 (`seal-rsa-control.log`) |
| Rabin | RSA incl. S3 | `seal-rabin-pass.log`, rc 0 | 5/5 (`seal-rabin-control.log`) |

`$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

---

## E1b follow-up report: published domain equivalences

**Commits on `wip/eqlemmas-e1b`, not pushed:**
- `55988d16c5cd154838074b835d8e681b2945b74c`: the first commit, unchanged.
- `22b96745b6338af040f5e8f0d8f969f530f9b000`: the domain equivalences (HEAD).

Against the base `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`, the diff is 99 added public declarations and nothing else.

Your answers (1), (2) and (6) are applied: no `@[simp]`, `expEnc_eq` kept, DiscreteLogHardcore:516 not re-pointed.

**Two things need your decision:**
- **File size (new lint finding).** `RSA.lean` is now 1076 lines and `Rabin.lean` 1104. Rabin was already 999 at base, so any addition crosses 1000. `style_lint.py` reports "must split" on both, and `--check8b` adds a size WARN for each. I did not split.
  - (a) Approve the size, as the fill brief already expects for RSA and Rabin (D2).
  - (b) Split Rabin's Blum half into `RabinBlum.lean`, as D2 sketched.
  - (c) Move the interface lemmas to sibling files, which breaks "beside its definition".
- **Four existing statements need a sealed instance to reduce** (list below). I restated none of them, as you asked.

### 1. Probe first: existing statements that need the instance to reduce
Method: a copy of each base file with `attribute [local irreducible]` placed right after each instance's definition, and in downstream files on the imported instances. Heartbeats were capped at 400000, because `maxHeartbeats 0` hung a sealed run. Each error was then classified as falling in a statement or in a proof body (`$SP/e1/e1b/stmtprobe/classify.py`).

| Statement | File | What it reads |
|---|---|---|
| `expCollection_index` | DiscreteLog | takes `r : G.gen.Coins n` where `(expCollection H G hV).gen.Coins n` is expected; reads the `gen` field, not `D` |
| `expCollection_index_of_lt` | DiscreteLog | the same |
| `dlCollection_index` | DiscreteLog | the same, through `dlCollection` |
| `fullDLCollection_hardCore` (dl-b's sorried headline) | DiscreteLogHardcore | **a `D`-level read**: `HardCore halfPred` passes `halfPred : ∀ i, ZMod (expOrd i) → Bool` as a predicate on `(fullDLCollection H G).D i` |

- A restated form for the fourth would be `HardCore fun i x => halfPred i (fullDLCollection_domEquiv H G i x)`.
- Of the gen-coins reads, `dlCollection_index` and `expCollection_index` feed fill routes.
- No other statement in any file fails. The `factoring`/`rsa`/`rabin`/`rabinBlumTrapdoor` `_index` lemmas take `r : C.gen.Coins n`, so they are fine. The other failures are proof bodies in the instance's own file, which is allowed:
  - `expCollection_D` (`rfl`);
  - `dlCollection_oneWay`, `fullDLCollection_oneWay`, `rsaTrapdoor_oneWay` (definitional equality of the instance);
  - the `show`/`simp` reads in the `_index` proofs.
- Logs: `stmtprobe/Seal*.{lean,log}`.
- The same probe on HEAD (`stmtprobe/head/`) finds the same four statements and nothing new. Every added statement elaborates with the instance sealed; only their own-file `rfl` bodies fail, as expected.

### 2. Added in commit 2 (file:line at HEAD)
Each `<C>_domEquiv` is a public `def` equal to `Equiv.refl _`, with a docstring that names it as the interface to the domain. For each collection `C`:
- `C_domEquiv i : C.D i ≃ T`;
- `C_domEquiv_uprob`: `uprob (fun x : C.D i => P (φ x)) = uprob P`, proved by `uprob_comp_equiv`. This is the uniformity transport the routes need for `SampleClose`/`invProbAt`, and it is also what clears check 8 for the `def`;
- `C_f`: `C.f i x = F i (φ x)`;
- `C_encD`: `C.encD i x = Enc i (φ x)`;
- `C_decD`: `C.decD i w = (Dec i w).map φ.symm`;
- `C_gen`, `C_sample`, `C_eval`;
- for the trapdoor collections also `C_perm`, `C.perm i x = φ.symm (perm₀ i (φ x))`, and `C_inv`.

| Collection | `T` | `F` / `Enc` / `Dec` / perm₀ | Lines |
|---|---|---|---|
| `expCollection` | `ZMod (expOrd i)` | `expF` / `expEnc` / `expDec` | DiscreteLog:655 (`domEquiv`), 663 (`uprob`), 671/677/684 (`f`/`encD`/`decD`, restated from commit 1), 699 (`eval`) |
| `dlCollection` | `ZMod (expOrd i)` | as above | DiscreteLog:820–863 |
| `fullDLCollection` | `ZMod (expOrd i)` | as above | DiscreteLogHardcore:491–535 |
| `factoringCollection` | `DistinctPrimes (max i.length 2)` | `f = ⟦φx.p · φx.q⟧_{2·max}` / `encodeDistinctPrimes` / `decodeDistinctPrimes`; `eval z = mulStr (pairSndD z)` | Factoring:682–730 |
| `rsaTrapdoor` | `(ZMod (rsaMod i))ˣ` | `rsaF` / `rsaEnc` / `rsaDec` / `rsaPermAt`; `inv = rsaInv H` | RSA:725–771 |
| `rsaCollection` | `(ZMod (rsaMod i))ˣ` | through `rsaTrapdoor_domEquiv` | RSA:780–815 |
| `rabinCollection` | `(ZMod (rabinMod i))ˣ` | `rabinF` / `rabinEnc` / `rabinDec` | Rabin:499–537 |
| `rabinBlumTrapdoor` | `QR (blumMod i)` | `blumF` / `blumEnc` / `blumDec` / `blumPermAt`; `inv = blumInv H` | Rabin:931–982 |

- `dlCollection` and `fullDLCollection` are built from `expCollection`'s declarations (`_domEquiv := expCollection_domEquiv …`, and their equations are the `expCollection_*` lemmas). So `DiscreteLogHardcore` unfolds only its own `fullDLCollection`.
- `rsaCollection` is built from `rsaTrapdoor`'s declarations the same way.
- `expCollection_f`/`_encD`/`_decD` from commit 1 needed the type to reduce, so they are restated through `expCollection_domEquiv`. These are the only CHANGED rows against commit 1, and none of them was in the base. `expCollection_gen`/`_sample` were already well typed and stay.
- The existing `expCollection_D` (a type equality) is kept. Its docstring is unchanged, because the common brief forbids editing existing docstrings. If you want it to point to `expCollection_domEquiv`, that edit needs approval.
- **Nothing needed from E1a.** Under a seal, `(T).toCollection.D i` is the same term as `T.D i`. The Blum probe reads `x : (rabinBlumTrapdoor H).toCollection.D i` through `rabinBlumTrapdoor_domEquiv`, and `rsaCollection_domEquiv` is defined from `rsaTrapdoor_domEquiv`, so the generic equivalence is not needed. A `default`/`inhabitedD` equation is not added; no route reads it.

### 3. Checks (logs in `$SP/e1/e1b/`)
1. **Replay** (`replay-final2.log`, `full-final2/`): all 11 downstream modules and `audits/pass-shelat/Checks` give 0 errors.
   - `sorry` counts are the base's except Factoring 8→10 and RSA 9→10, which are S1–S3 only.
   - The `Checks` output is identical to the base (`checks-final2.out`).
   - The only other warnings are ElGamal's three section-variable warnings, which ElGamal already had.
2. **Axioms** (`axioms-final2.log`, 99 declarations): none outside the standard set plus `sorryAx`.
   - 28 print the standard set only.
   - 68 print `sorryAx` only because they mention an instance. All 8 instances print `sorryAx` themselves (`axioms-instances.log`), because they are built on sorried targets.
   - The other 3 are S1–S3.
3. **Lint:**
   - `style_lint.py` reports 0 findings on Arithmetic, Concrete, DiscreteLog, DiscreteLogHardcore, Factoring and Primality. RSA and Rabin each have the size finding described at the top.
   - `campaign_style_lint.py --check8b` gives the same 8 FAILs as the base (Rabin's five FAILs only moved lines). Its only new WARNs are the two size WARNs; the check-8 lists are otherwise shorter than the base's (`lint8b-final2-*.log`).
4. **Statement diff:** `decls-diff-final2.tsv` has 99 rows against the base, all ADDED. `decls-diff-commit2.tsv` has 63 ADDED and 3 CHANGED (the restated `expCollection_f`/`encD`/`decD`).
5. **Seal probes:**
   - `probes/SealDomPass.lean` (rc 0) seals all 8 instances and works through each `domEquiv`: `decD ∘ encD = some` for every collection, `f` injective at a valid `expCollection` index, the `uprob` transports (including through `toCollection`), the `perm` readings, and `fullDLCollection_f`'s width.
   - `probes/SealDomControl.lean` reads `x : C.D i` definitionally, one example per collection. All pass unsealed and all 8 fail sealed (`seal-dom-control.log`).
   - The four probes from commit 1 were re-run on HEAD and still pass (`r2-Seal*Pass.log`).

`$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.