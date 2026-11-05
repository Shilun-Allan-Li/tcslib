# Gate 03c: review of the external auditor's findings (hard-core bits and PRGs)

**Summary.**
- **Verdicts.** Of the 11 findings, 9 are **true** and 2 are **partly true**. None is false.
  - #1 is partly true. The limit on what `PRG` can express is real and exactly as stated. But its cost is already declared, with a proved workaround, in `PRF.lean` (pack 03d), which the auditor did not see. And no downstream statement is vacuous because of it.
  - #4 is partly true. The truncation lemma the auditor asks for already exists in `PRF.lean`.
- **Severity.**
  - **#1 stays major, not blocker.** No statement in ch. 2–4 or ch. 5–8 is about a `PRG` of stretch `2n` or `n^c`. It remains a major because the frozen interface needs an explicit ruling (Q1).
  - **I propose raising #3 from minor to major.** The auditor's example was hypothetical. The library's own trapdoor collections fail `henc`: RSA encodes elements in `2·max(n,2)` bits, Rabin/Blum in `2·max(n,3)` bits, and neither is a polynomial in `n`. Yet the docstring claiming "satisfiable from trapdoor permutations alone" is the stated justification of Thm 104.4's declared deviation in `PublicKey.lean`.
  - All other severities are unchanged.
- **Rulings needed: Q1 (#1), Q2 (#2), Q3 (#3).** My recommendations:
  - Q1-A: keep `∀ n, n < ℓ n` and declare the cost.
  - Q2-A: drop the extra hypothesis of Thm 75.4. The change stays inside `NextBit.lean`.
  - Q3-A: state the cost of `henc` now, and weaken it as a follow-up.
- **Impact if the recommendations are adopted.**
  - No pending pack has to wait for a 03c statement change.
  - 03d picks up docstring edits only.
  - 03f1, 03f2, 03g, 03h, 03i, 03j, 03k and 03l are unaffected.
  - No ch. 5–8 statement changes under any option. Prong D's Thm 180.1 takes `∃ G : PRG, G.Secure`, which has the same truth value under all three Q1 options.
  - 03c's collection section (`Collection.glPad`) must be re-checked after 03b's major #1 is repaired.

**How this was checked.**
- I read every Lean reference at `a3c5fa8b` in `wt-g03`.
- Source passages come from `blueprint/src/references/pass-shelat-2010-ch3.raw.md`. This settles both of the auditor's *PDF check* items (see #1 and #7).
- Downstream use was found by grepping, in each sibling worktree, only the files changed relative to `a3c5fa8b`:
  - `wt-s2b` at `afe5982f`;
  - `wt-prong-a` at `2d7b5441`;
  - `wt-prong-b` at `1cf007d1`;
  - `wt-prong-c` at `aa71d0e7`;
  - `wt-prong-d` at `6ea900ae`.
- The pack-to-file map is `gate03/packs.json`. The ripple script is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/gate03-review/scripts/ripple03c.py`.
- No Lean was built.

| # | Auditor | Verdict | Proposed severity | Fix type | Ruling |
|---|---|---|---|---|---|
| 1 | major | partly true | **major** (ruling item; not blocker) | Q1-A: docstrings + DESIGN §5/§2.12 | **Q1** |
| 2 | minor | true | minor | Q2-A: statement change (strengthening) | **Q2** |
| 3 | minor | true (understated) | **major** (as it stands) | Q3-A: docstrings + DESIGN §5.18 | **Q3** |
| 4 | minor | partly true | minor | DESIGN record + optional corollary | no |
| 5 | minor | true | minor | docstring + records | no |
| 6 | minor | true | minor | `Checks.lean` prints, re-attest | no |
| 7 | note | true | note | docstrings | no |
| 8 | note | true (answered) | note | none here; follows 03b | no |
| 9 | note | true (answered) | note | none | no |
| 10 | note | true | note | module docstring | no |
| 11 | note | true | note | hygiene | no |

---

## #1 (major): `PRG.expands` at every `n`, including `n = 0`

**Check: partly true.**

*True: the expressivity claim.*
- `Pseudorandom.lean:118` has `expands : ∀ n, n < stretch.eval n`.
- `HardCore.lean:332` (`PRG.expand`) and `:411` (`prg_expand`) take the same `hℓ : ∀ n, n < ℓ.eval n`.
- A `PolyExpr` (`PolyExpr.lean:67–83`) evaluates to a polynomial with coefficients in ℕ, with `pow p 0 = 1`. So:
  - `2·var` fails at `0 < 0`;
  - `var^2` fails at `1 < 1`;
  - no stretch equals `2n` exactly.
- The source shows `n = 0` is not intended:
  - Def 77.1 (raw l. 452–458) literally says "|G(x)| > |x|". The formal field is that literal reading at `x = ε`.
  - Lemma 80.5 does say "For any polynomial ℓ" (raw l. 565–566). This settles the auditor's *PDF check*.
  - Alg 92.1 (l. 1083) and Thm 97.3 (l. 1293) use a "length-doubling" generator.
- Inventory §4.4 (`inventory-ch3.md:995`) planned both "`n < ℓ n`" and "GGM … use `2n`", as the auditor says.

*False: "neither the PRG notes nor DESIGN §5 record this cost".* This is literally true of `Pseudorandom.lean` and of DESIGN §5, but the cost is recorded where it bites.
- `PRF.lean:43–48` (module docstring): "a length-doubling generator is not a `PRG` of this library (the stretch `2n` does not exceed `n` at `n = 0`), so it is the separate predicate `DoublingPRG`".
- `PRF.lean:370–372` repeats this as a declared deviation on `DoublingPRG`.
- The workaround is proved:
  - `PRG.truncate` (`:390`) and `PRG.Secure.truncate` (`:429`);
  - `two_mul_add_one_expands` (`:395`), the stretch `2n + 1`;
  - `PRG.doubling` (`:404`) and `PRG.Secure.doubling` (`:449`, printed in `Checks.lean:224`).
- Alg 92.1 avoids the issue: `prgScheme` uses `(P.expands n).le : n ≤ ℓ(n)` and the first `n` pad bits, declared at `Encryption.lean:55–60`.

*False: the risk "any downstream statement over `P : PRG` with `P.stretch = 2n` is vacuously true".* No such statement exists. I grepped every `PRG`-quantified statement in `wt-g03` and in the ch. 5–8 worktrees:
- `prgScheme*` (Encryption);
- `PRG.Secure.truncate`, `.doubling`, `exists_prf_of_exists_prg` (PRF);
- `truncateTo_*` (PRFLemmas);
- `exists_securePRG_of_owp` (HardCorePermutation);
- `exists_multiMessageSecure_of_exists_prg` (MultiMessage, also in S2b and the prongs);
- `bpp_subset_dtime_subexp` (prong D).

None constrains the stretch to `2n` or `n^c`. GGM is stated over `DoublingPRG G` (`PRF.lean:694`). **So the escalation condition fails; this is not a blocker.**

**Severity: agree major.** It is not misleading as code. It is a choice about a frozen interface (DESIGN §2.12, line 681) that differs from the source's use and is missing from the register. That is "debt that needs explicit human acknowledgment". QUEUE.md already lists it among the four gate 03 majors. It closes once Q1 is ruled and the register line lands.

**Facts the ruling should weigh.**
1. **"PRGs exist" is the same under every option.** A secure generator that expands only for `n ≥ n₀` gives one that expands everywhere: truncate to `n + 1` bits and output anything below `n₀`; security is asymptotic. So every `∃ P : PRG, P.Secure` statement has the same truth value under A, B and C. This covers MultiMessage, PRF, HardCorePermutation and prong D. This is a mathematical remark; it is not formalized.
2. **"Eventually" equals "from 2 on" for these polynomials.** A stretch that eventually exceeds `n` is non-constant, so `n ≤ ℓ(n)` holds for all `n`. Moreover `n < ℓ(n)` holds for all `n ≥ 2`, by cases on the polynomial:
   - degree ≥ 2: `ℓ(n) ≥ n² > n`;
   - linear coefficient ≥ 2: `ℓ(n) ≥ 2n > n`;
   - `n + c` with `c ≥ 1`: `n < n + c` everywhere.

   So option C's "eventually" can be written with the fixed threshold 2, and 2 is the least threshold that admits `n^c`.
3. **The security half of `prg_expand` needs only `0 < ℓ(n)`.** It uses `hℓ` only through `Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n)`, for the hybrid index (`HardCore.lean:422, 435`). The everywhere clause is needed only to build the `PRG` value.

**Fix: Q1-A (recommended). Docstrings and DESIGN only.**
- Add to `PRG`'s docstring (`Pseudorandom.lean:103–111`), as a second Deviation:
  > **Deviation:** the expansion clause holds at every seed length, `n = 0` included, as the text's
  > `|G(x)| > |x|` says literally for `x = ε`. A `PolyExpr` stretch is a polynomial with coefficients
  > in ℕ, so a stretch with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) is not a `PRG`, although
  > the text uses such generators (Algorithm 92.1, Theorem 97.3). They are reached up to one bit
  > (`2n + 1`, `n^c + 1`, by `prg_expand`) or by truncation (`PRG.Secure.truncateTo_easy`/`_negligible`);
  > the length-doubling generator of Theorem 97.3 is the separate predicate `DoublingPRG`
  > (`Asymptotic/PRF.lean`), produced from any `PRG` by `PRG.Secure.doubling`.
- In `HardCore.lean:61–62` (module Deviation), `:327` (`PRG.expand`) and `:384` (`prg_expand`), change "`ℓ(n) > n`" to "`ℓ(n) > n` at every `n`, see `PRG`".
- Add DESIGN §5 entry 23: "`PRG.expands` (gate 03c #1): expansion at every `n`, `n = 0` included; stretches `2n`, `n^c` excluded; `DoublingPRG` for Thm 97.3, `2n + 1` or truncation elsewhere." Add a line comment at §2.12:681.
- Optional, prong D: in `Derandomization.lean:68`, name a stretch that expands everywhere, e.g. `a(s^c + 1)^k + s + 1`.

**Fix: Q1-B (`expands : ∀ n, 0 < n → n < stretch.eval n`).** This admits `2n`, but not `n^c`.

```lean
structure PRG where
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, 0 < n → n < stretch.eval n
theorem PRG.le_stretch (P : PRG) (n : ℕ) : n ≤ P.stretch.eval n          -- replaces `(P.expands n).le`
theorem PRG.stretch_pos (P : PRG) {n : ℕ} (hn : 0 < n) : 0 < P.stretch.eval n
def PRG.expand (G) (ℓ : PolyExpr) (hℓ : ∀ n, 0 < n → n < ℓ.eval n) : PRG
theorem prg_expand (G) (ℓ) (hℓ : ∀ n, 0 < n → n < ℓ.eval n) (h : (PRG.oneBit G).Secure) :
    (PRG.expand G ℓ hℓ).Secure      -- proof: default hybrid index where ℓ n = 0, `Negligible.mono ⟨1, _⟩`
def PRG.truncate (P : PRG) : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool) :=
  fun n s i => if h : n + 1 ≤ P.stretch.eval n then P.G n s (Fin.castLE h i) else false
```

What changes under B:
- `PRG.oneBit`, `iterPRG` and `iterPRG_eq_expand` need proof-term edits only.
- `cor_81_7` and `owp_hardcore_prg` keep their statements.
- `PRG.Secure.truncate`, `PRG.doubling` and `PRG.Secure.doubling` change (`PRF.lean`, 03d, which S2b's F-1 restatement is editing now).
- The 8 uses of `(P.expands n).le` in `Encryption.lean` (03d) change.
- The callers of `truncateTo_*` must supply `hm` at `n = 0` (`PRFLemmas.lean`, 03j).
- `expandRedMachine`'s `hk : ∀ n, k n < ℓ.eval n` (`HardCoreLemmas.lean:533`, 03i) must be weakened.
- Thm 75.4's `hℓ` must go: Q2-A becomes mandatory.
- `DoublingPRG` could be retired, but that is optional.

**Fix: Q1-C (`expands : ∀ n, 2 ≤ n → n < stretch.eval n`, equivalent to "eventually").** This admits every non-trivial polynomial stretch, `n^c` included. It costs everything in B, plus:
- a private `PolyExpr` lemma (`eval p 1 = 0 → ∀ n, eval p n = 0`, by structural induction) to recover `PRG.le_stretch` for Alg 92.1;
- defaults below 2 in `truncate` and `prg_expand`.

**Ripple.**
- Q1-A: only 03c's files and DESIGN.
- Q1-B and Q1-C: 03c, then 03d (PRF.lean, Encryption.lean), 03i (HardCoreLemmas), 03j (PRFLemmas); also 03e's `Commitment.lean:445` (`simp [PRG.oneBit]`, proof-level only).
- ch. 5–8, under every option: no statement text changes. In particular, prong D's `bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure)` keeps its text and its meaning (fact 1). Its sketch already routes through `PRG.Secure.truncate` and `prg_expand`, which works under A with a stretch such as `a(s^c+1)^k + s + 1`.
- Under B or C, S2b's in-flight `PRF.lean`/`PRFLemmas.lean` would conflict.

**Ruling: yes, Q1.**

---

## #2 (minor): the extra `hℓ : ∀ n, 0 < ℓ.eval n` of Thm 75.4

**Check: true.**
- `NextBit.lean:643–644` has `(hℓ : ∀ n, 0 < ℓ.eval n)`. The source's Thm 75.4 (raw l. 351–353) has no such hypothesis.
- The docstring (`:618`) says "(with `ℓ(n) > 0`)" without a Deviation line. The module docstring's two Deviations (`:34`, `:39`) do not mention it.
- `stretch_pos` (`Pseudorandom.lean:150–152`) wrongly calls it "the hypothesis `0 < ℓ(n)` of [PS10, Theorem 75.4]".
- The hypothesis is removable. Where `ℓ(n) = 0`, both `X_n` and `U_0` are the point mass on the empty string, and seeds are nonempty (`Ensemble.nonempty`). So `prgAdv = 0`, and the contradiction set of the proof lies where `ℓ(n) > 0`.
- The machine in `exists_nextBitPredMachine` (`:540`) does not depend on `i`: its advice is `⟨D.advice n, [flip n]⟩`, and the position is read off `|t|`. So its identity generalizes to every `i : Fin (ℓ.eval n)`.
- The hypothesis is part of the frozen shape (DESIGN §2.12, line 690). It has no Lean consumer: `Ensembles.lean:57, 120` (03a) mention the theorem's name only.

**Severity: agree minor.** One interaction with #1: under Q1-B or Q1-C, PRG output ensembles with `ℓ(0) = 0` fall outside the theorem, and `stretch_pos` becomes false. So Q2-A is then required.

**Fix: Q2-A (recommended; a strengthening).**

```lean
private theorem exists_nextBitPredMachine {ℓ : PolyExpr} (D : NUPPT) (flip : ℕ → Bool) :
    ∃ (A : NUPPT) (e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n),
      ∀ n (i : Fin (ℓ.eval n)) (t : Fin i → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
        A.predictor n i t (e n (u, c)) = nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n) t (u, c)
theorem prgAdv_eq_zero_of_eval_eq_zero … : ℓ.eval n = 0 → prgAdv (X.X n) D = 0
theorem Ensemble.NextBitUnpredictable.pseudorandom {ℓ : PolyExpr} {X : Ensemble ℓ}
    (h : X.NextBitUnpredictable) : X.Pseudorandom
```

- In the proof, choose `(i n, flip n)` only where `0 < ℓ n`; take `flip n := false` elsewhere.
- Use the positive polynomial `mul p (add ℓ (const 1))`, with `1/(p(ℓ+1)) ≤ 1/(pℓ)` on the infinite set.
- Rewrite `stretch_pos`'s docstring to read "positive at every seed length (from the expansion clause)".
- Update DESIGN §2.12:690.

**Fix: Q2-B.** Keep `hℓ`, add "**Deviation:** `hℓ : ∀ n, 0 < ℓ(n)` (not in the source; removable, …)" plus a DESIGN §5 line, and fix the attribution in `stretch_pos`. Docstrings only. This is consistent only with Q1-A.

**Ripple.** `NextBit.lean` and DESIGN only. No pending pack and no ch. 5–8 file is affected.

**Ruling: yes, Q2.** It changes a frozen signature, though only to strengthen it.

---

## #3 (minor, proposed major): `henc` in `Collection.glPad`

**Check: true, and understated.**
- `HardCore.lean:731–732` requires `henc : ∀ n r x, (F.encD (F.index n r) x).length = m.eval n`.
- A non-constant polynomial with coefficients in ℕ is strictly increasing. So an index generated at two parameters forces `m` to be constant, as the auditor says.
- **The library's own instances fail it:**
  - `rsaTrapdoor` (`RSA.lean:631`). The index at `n` is `rsaIndexOf (max n 2) _` (`:406, :431`), and `rsaEnc i x = natToList (pairFstD i).length _` (`:230`), with `length_natToList` (`Arithmetic.lean:88`). So the encoding has `2·max(n,2)` bits: 4, 4, 4, 6, 8, … `henc` would need `m(0) = m(1) = 4` and `m(3) = 6`. That is impossible.
  - `rabinBlumTrapdoor` (`Rabin.lean:846`) has `2·max(n,3)` bits: `rabinIndexOf` at `:311–312`, `blumEnc` at `:682`. It fails the same way.
  - `expCollection` fails as the auditor describes.
- So `TrapdoorCollection.OneWay.glPad_hardCore` cannot be instantiated with any candidate in the library.
- Its docstring (`:973–975`) says Thm 104.4's hypothesis "is satisfiable from trapdoor permutations alone".
- That docstring is the justification of Thm 104.4's declared deviation in `PublicKey.lean:797–800` (03d): "`TrapdoorCollection.OneWay.glPad_hardCore` supplies one from trapdoor permutations alone".
- `glPad_tdpBitScheme_singleBitSecure` (`PublicKey.lean:944–949`) inherits `henc`.
- The per-index form that the auditor proposes does hold for RSA, Rabin and DL. Their encoding widths depend only on the index (`|pairFstD i|`, `|i|`, `dlW i`), and are bounded by `2n + 4` (RSA) and `2n + 6` (Rabin/Blum).

**Severity: propose major** (materially misleading as it stands). The theorems are true. But a trusted-surface claim that underwrites a declared deviation of Thm 104.4 is supported by no instance in the library. It is not a blocker:
- no ch. 5–8 statement uses `glPad`;
- OT (`ObliviousTransfer.lean:395, 427`, prong B) and padded CPA (`Composability/PublicKey.lean:432`, prong C) take `hHC : T.toCollection.HardCore h` as a hypothesis.

**Fix: Q3-A (recommended now). Docstrings only.**
- Extend the Deviation at `HardCore.lean:728–730`:
  > … `henc` ties the encoding length at every generated index to `m(n)`; a non-constant `PolyExpr`
  > is strictly increasing, so an index generated at two parameters forces `m` constant. The
  > library's candidates do not satisfy it as parametrized (`rsaTrapdoor`: `2·max(n,2)`-bit elements;
  > `rabinBlumTrapdoor`: `2·max(n,3)`; `expCollection`: `dlDefaultIndex` below `n₀`). A per-index
  > form (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit them; not formalized.
- Replace "satisfiable from trapdoor permutations alone" at `:973–975` and at `PublicKey.lean:797–800` with "satisfiable from trapdoor permutations whose generated indices encode elements in exactly `m(n)` bits (`henc`)".
- Append the cost to DESIGN §5.18.

**Fix: Q3-B (the real repair; can follow later).**

```lean
noncomputable def Collection.glPad (m : PolyExpr)
    (hreg : ∀ i (x : F.D i), (F.encD i x).length = (F.encD i default).length)
    (hbd : ∀ n (r : F.gen.Coins n), (F.encD (F.index n r) default).length ≤ m.eval n) : Collection
-- Sample'(1^n, i; s ‖ ρ) = ⟨w, ρ.take |w|⟩ with w = Sample(1^n, i; s), ρ of m(n) bits
```

- `OneWay.glPad`, `OneWay.glPad_hardCore`, `goldreich_levin_coll`, and the Perm/Trapdoor variants change their hypotheses accordingly.
- `HardCoreGLColl.lean:229, 293` (03i) carries `henc` per index and globally, and needs reworking. The GL-domain lemma `invProb_guessInverter_enc_pad` is already per-length (`GoldreichLevinDomain.lean:153`) and needs no change.
- `glPad_tdpBitScheme_singleBitSecure` (03d) changes its statement.
- Sequencing: "`|w| = L_i`" needs canonical sampler outputs. That is 03b's major #1 (`decD_canonical`). So Q3-B must follow 03b's repair.

**Fix: Q3-C.** Keep `henc` and add reparametrized candidates (RSA at `n + 2`, Blum at `n + 3`) with `henc` proofs (`m = 2·var + 4`, `2·var + 6`) and one-wayness transfer. This is new API in 03f2.

**Ripple.**
- Q3-A: 03c and 03d (docstrings).
- Q3-B: 03c, 03i (HardCoreGLColl, HardCoreLemmas), 03d (statement); after 03b.
- Q3-C: 03f2.
- ch. 5–8: none under any option.

**Ruling: yes, Q3.**

---

## #4 (minor): `prg_expand` takes a one-bit `G`, not a `P : PRG`

**Check: partly true.**
- True:
  - The code is `prg_expand (G : ∀ n, … → (Fin (n + 1) → Bool)) (ℓ) (hℓ) (h : (PRG.oneBit G).Secure)` (`HardCore.lean:410–411`).
  - DESIGN §2.12:698 records `prg_expand (P : PRG) (ℓ) : P.Secure → …`, and §5 has no entry for the difference.
  - No truncation lemma is *in this pack*.
- False in effect:
  - The truncation exists: `PRG.truncate` and `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` (`PRF.lean:390, 429`, pack 03d), on top of `PRG.Secure.truncateTo_easy`/`_negligible` (`PRFLemmas.lean:225, 248`, pack 03j).
  - Prong D's docstring already cites this route (`Derandomization.lean:31`).
  - The auditor's proposed `PRG.truncSucc` would duplicate `PRG.truncate`.

**Severity: agree minor.**

**Fix.**
- Record the shipped signature in DESIGN §2.12:698. The one-bit input is faithful to Lem 80.5.
- Optionally add the `PRG`-level corollary next to the truncation, in 03d after S2b lands:

```lean
/-- **Any PRG expands to any stretch `ℓ(n) > n`** [PS10, Lemma 80.5, with the truncation of the
proof of Theorem 97.3]. -/
theorem PRG.Secure.expand {P : PRG} (hP : P.Secure) (ℓ : PolyExpr) (hℓ : ∀ n, n < ℓ.eval n) :
    (PRG.expand P.truncate ℓ hℓ).Secure :=
  prg_expand P.truncate ℓ hℓ hP.truncate
```

**Ripple.** DESIGN only. The optional corollary goes in 03d's `PRF.lean`. Prong D could cite it.

**Ruling: no.**

---

## #5 (minor): stale sketch of `nextBitProb_nextBitPred_false`; "P2-3" unrecorded

**Check: true.**
- `NextBit.lean:360–361` still describes "the bijection `(b, (s, u), c) ↦ (s, (update u i (xor b (X s i)), c))`". The proof rewrites with `uprob_split_bit` (`:375`), whose docstring (`:232–233`) calls that very map "2-to-1, not a bijection — run-3 audit P2-3".
- "P2-3" appears nowhere in `audits/pass-shelat/`; the run-3 summary has P2-1 and P2-2 only. It appears only at `NextBit.lean:233`.
- `inventory-ch3.md:317` has the same "bijection".

**Severity: agree minor** (policy §3, Synchronization).

**Fix.**
- Rewrite the sketch: "`uprob_split_bit` at position `i` with the bit `x_i` (an adjoined uniform bit and the involution `ψ`): the success event averages the same event with `x_i` and with `x̄_i` planted at bit `i` of `u`; planting `x_i` gives `nextBitHybrid X (i+1)` and the predictor is right iff `D` accepts, planting `x̄_i` gives `nextBitHybridFlip X i` and it is right iff `D` rejects."
- Record P2-3 in gate 03's resolution log, since the run-3 summary is a closed record, and annotate inventory row 317.

**Ripple.** None outside 03c. **Ruling: no.**

---

## #6 (minor): axiom evidence omits `HardCoreClaims` and the non-vacuity theorems

**Check: true.**
- `Checks.lean:186–210` and `evidence/c/axioms.log` (22 lines) do not cover:
  - `fact_88_4`, `thm_87_3_1/2/3/6/7/8/9`;
  - `not_hardCore_const`, `Ensemble.uniform_nextBitUnpredictable`;
  - `PermCollection.OneWay.glPad_hardCore`.
- `HardCoreClaims.lean` has no `sorry`, but its declarations re-export `HardcoreBit/*` lemmas, so only a print rules out a transitive `sorryAx`.
- DESIGN §4:943 asks for non-vacuity theorems to be printed in `Checks.lean`. The two named above are not in its list, but the rule plainly covers them.

**Severity: agree minor.**

**Fix.** Append 11 `#print axioms` lines to `Checks.lean` and re-run 03c's axiom attestation. **Ripple:** none. **Ruling: no.**

---

## #7 (note): `HardCoreClaims` docstrings

**Check: true.**
- The module docstring (`HardCoreClaims.lean:16–19`) says "each the family-level instance". But `fact_88_4` and `thm_87_3_6/7/8` (`:62, 108, 119, 129`) are stated for an arbitrary `f`.
- *PDF check settled.* The text reads "each `x_i` is wrong with probability at most `1/(4mε'²) ≤ 1/(mε'²)`" (raw l. 994–998). With `ε' = ε/2`, the formal `1/(ε²(2^k − 1))` is the text's tighter `1/(4mε'²)`, where `m` counts the samples. The docstring cites the looser constant.
- The text draws `r_1 … r_{m−1}` from `log m` seeds (l. 1009). So the text's `m` is `2^k` (as `thm_87_3_8` has it), while `thm_87_3_6` uses `m = 2^k − 1`, the number of samples.

**Fix.** Docstrings only:
- "the text's `1/(4mε'²)` (`≤ 1/(mε'²)`), `m` read as the `2^k − 1` samples (the text has `m − 1` samples and writes `m`)";
- qualify "family-level instance" in the module docstring.

**Ripple:** none.

---

## #8 (note): `Collection.HardCore` not auditable from the bundle

**Check: true as a scope note, and answered.** Pack 03b audited Def-78.3.coll: `gate03b-findings.md` #1 (major), #3, #7, and its inventory row at line 186. Its major #1 changes what `Collection`'s fields guarantee (canonical decoding, or `H` on every decodable string). `Collection.glPad`'s `decD`/`sample_spec` (`HardCore.lean:734–770`) and the evaluator that `glPad_hardCore` must supply are built on those fields.

**Fix.** None in 03c. **Ripple:** in the reverse direction. 03c's collection section (`HardCore.lean:712–981`) must be re-verified after 03b's repair, together with Q3-B if that is chosen.

---

## #9 (note): the OWP route through `HardCorePermutation` (pack 03i)

**Check: true as a scope note, and answered.** At `a3c5fa8b`, 03i's evidence settles it:
- `evidence/i/replay.log:316` shows `HardCorePermutation rc=0 … sorry=0`;
- `evidence/i/axioms.log:13–15` shows `OneWayPermutation.glHalf`, `exists_owp_hardCore` and `exists_securePRG_of_owp` with the standard axioms only.

**Fix:** none.

---

## #10 (note): unformalized items not recorded as remarks

**Check: true.** `inventory-ch3.md:363` asks for Constr-77.a, Claim-78.a and Claim-78.b to be recorded "as remarks in `HardCore.lean`'s module docstring if not formalized". `HardCore.lean:22–123` has none of them.

**Fix.** Add three remark lines:
- Shamir's `f^n(s)‖…‖s`;
- Claim-78.a via `uprob_comp_equiv` on `f^[k]`;
- Claim-78.b via Garg's `predProb_fixedBitPredictor`.

Claim-107.c (a PRG is a OWF) is optional (DESIGN §6.2). **Ripple:** none.

---

## #11 (note): policy hygiene

**Check: true.**
- `@[simp]` at `Pseudorandom.lean:145`.
- There are no `_iff` lemmas for `PRG.Easy` or `HardCore`, and no `_eq` lemmas for `PRG.oneBit`, `oneBitStep`, `expandRed`, `owpPredictorSnoc` or `Collection.glBit` (policy §1, the 2026-10-16 rule).
- Lines: `NextBit.lean` has 914, `HardCore.lean` 981.

**Fix.**
- Drop the `@[simp]`. `ensemble_X` has no consumer outside `Pseudorandom.lean`; pass it explicitly in `Easy.samplable`'s `simp` (`:176`).
- Add the `rfl` lemmas.
- Split `HardCore.lean`'s collection section (`:710–981`) into a child file that `HardCore.lean` re-imports, so consumers' imports are unchanged. Do this after #3 is settled, which grows that section under Q3-B.

**Ripple:** none. **Ruling: no.**

---

## Questions for the user

**Q1 (#1). How should `PRG`'s expansion clause treat small seed lengths?**
- **A (recommended).** Keep `∀ n, n < ℓ(n)`, the literal Def 77.1(2) at `x = ε`. Declare the cost at `PRG`, at `PRG.expand`/`prg_expand`, in DESIGN §5 (new entry 23) and at §2.12. Exact `2n` stays the separate `DoublingPRG`.
  - *Cost:* docstrings in 03c's files and DESIGN.
  - No pending pack waits. No ch. 5–8 change. `∃ PRG` statements keep their meaning.
- **B.** `∀ n, 0 < n → n < ℓ(n)`. Admits `2n` (so `DoublingPRG` could be retired), but not `n^c`.
  - *Cost:* statement changes in Pseudorandom/HardCore (03c), PRF/Encryption (03d, colliding with S2b's in-flight F-1), PRFLemmas (03j) and `expandRedMachine` (03i).
  - Forces Q2-A.
  - 03d, 03i and 03j wait.
- **C.** `∀ n, 2 ≤ n → n < ℓ(n)`, which equals "eventually" for these polynomials. Admits every polynomial stretch, `n^c` included.
  - *Cost:* everything in B, plus a `PolyExpr` lemma to keep `n ≤ ℓ(n)` for Alg 92.1, and defaults below 2 in `truncate` and `prg_expand`.

**Q2 (#2). Thm 75.4's extra `hℓ : ∀ n, 0 < ℓ(n)`.**
- **A (recommended).** Drop it. This strengthens the theorem to the source's statement.
  - *Cost:* restate the private machine lemma for all positions, plus about 50 lines of proof, in `NextBit.lean` only.
  - Change DESIGN §2.12:690. No consumers.
  - Required if Q1 is B or C.
- **B.** Keep it and declare it as a Deviation (docstring and DESIGN §5), fixing `stretch_pos`'s attribution.
  - *Cost:* docstrings only. Valid only with Q1-A.

**Q3 (#3). `Collection.glPad`'s `henc`, which no library candidate satisfies.**
- **A (recommended now).** State the cost: the RSA, Rabin/Blum and DL widths fail `henc`. Correct the "satisfiable from trapdoor permutations alone" claims in `HardCore.lean:973–975` and `PublicKey.lean:797–800`, and DESIGN §5.18.
  - *Cost:* docstrings in 03c and 03d. No statement change.
- **B.** Weaken `henc` to per-index regularity plus a polynomial bound. This admits RSA, Rabin and DL as they are.
  - *Cost:* statement changes in 03c (7 declarations), 03i (HardCoreGLColl) and 03d (`glPad_tdpBitScheme_singleBitSecure`).
  - A new sampler.
  - Must follow 03b's major #1. 03d and 03i wait.
- **C.** Keep `henc` and add reparametrized RSA/Blum instances with `henc` proofs.
  - *Cost:* new API and proofs in 03f2 (RSA.lean, Rabin.lean). DL is still excluded.

---

## What the auditor missed

1. **The length-doubling cost is already declared, with a proved workaround,** in `PRF.lean:43–48, 370–372`: `DoublingPRG`, `PRG.truncate`, `PRG.Secure.truncate`, `two_mul_add_one_expands`, `PRG.doubling`, `PRG.Secure.doubling`. This weakens #1's "not recorded" and #4's "no truncation lemma".
2. **No downstream statement is vacuous** (#1's escalation test). I checked every statement quantifying over `PRG` in ch. 2–4 and ch. 5–8.
3. **`henc` fails for the library's own trapdoor collections.** RSA has `2·max(n,2)`-bit elements and Rabin/Blum `2·max(n,3)`. Thm 104.4's declared deviation (`PublicKey.lean:797–800`, 03d) rests on the overstated docstring.
4. **#1 and #2 interact.** Under Q1-B or Q1-C, `stretch_pos` is false and Thm 75.4's `hℓ` excludes PRG output ensembles.
5. **Both *PDF checks* can be settled from the branch's raw text.** Lem 80.5 does say "for any polynomial ℓ". The per-bit bound reads "`1/(4mε'²) ≤ 1/(mε'²)`", and the formal bound equals the tighter one.
6. **For `PolyExpr` stretches, "eventually expanding" is equivalent to "expanding for all `n ≥ 2`",** and every such stretch satisfies `n ≤ ℓ(n)`. Also, "PRGs exist" has the same meaning under every Q1 option.
7. **Note #8 is answered by 03b's findings** (#1, #3, #7), and 03b's repair ripples back into 03c's `Collection.glPad`.
8. **Note #9 is answered by 03i's evidence:** the three declarations are free of `sorryAx` at `a3c5fa8b`.

---

## Pending packs

| Pack | With the recommended rulings (Q1-A, Q2-A, Q3-A) | Under the alternatives |
|---|---|---|
| 03d | **Touched, docstrings only:** `PublicKey.lean:797–800` and `:938–943` (#3); optional `PRG.Secure.expand` (#4). Fold these in when 03d pins after S2b; no wait. | Waits under Q1-B/C (PRF.lean `truncate`/`doubling`, Encryption.lean `(P.expands n).le` ×8) and under Q3-B (`glPad_tdpBitScheme_singleBitSecure`). |
| 03i | Unaffected. | Waits under Q3-B (HardCoreGLColl `:229, :293`; HardCoreLemmas' `glPad` machinery) and under Q1-B/C (`expandRedMachine` `hk`, `HardCoreLemmas.lean:533`). |
| 03j | Unaffected. | Waits under Q1-B/C (callers of `truncateTo_*`). |
| 03f2 | Unaffected. | Touched under Q3-C (new instances in RSA.lean, Rabin.lean). |
| 03f1, 03g, 03h, 03k, 03l | **Unaffected under every option.** 03f1's `DiscreteLogHardcore` uses `Collection.HardCore` (03b's), not `glPad`; 03k's `CommitmentLemmas` only imports `HardCore`. | Same. |

- Packs outside the pending list: 03e's `Commitment.lean:445` (`simp [… PRG.oneBit]`) is proof-level only under Q1-B/C. 03a's `Ensembles.lean` mentions Thm 75.4 by name only.
- **03c itself:** its collection section must be re-verified after 03b's major #1 is repaired.

**After the fixes, run** (in the infoview or the gate's replay):
- the four 03c files;
- the new `#print axioms` lines (#6);
- `PRG.Easy.samplable` after dropping the `@[simp]`;
- under Q2-A, `Ensemble.NextBitUnpredictable.pseudorandom`'s axioms.
