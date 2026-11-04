# Gate 01 / prong zero: review of the external audit findings

**Summary.** Of the 10 findings, 8 are **true**, 2 are **partly true** (#5, #10) and none is false.
One severity should change: #5 goes from minor to **note**. Its factual claim holds, but the
"policy requirement" it cites does not exist in `policy.md`. The nearest basis is campaign Rule 10
in `briefs/pass-shelat-ch5-8/WORKFLOW.md`. #10 is out of date: erratum E1 and the ledger entry
DL-1, which the user accepted, supersede its "no copy established" conclusion. The severity stays
at note because the debt has been acknowledged. Every proposed edit to `SecretSharing/Defs.lean`
and `Shamir.lean` is docstring-only. The only code changes proposed anywhere are six `rfl`/`Iff.rfl`
interface lemmas for #5, and those are optional. The auditor missed 3 real items, all minor: two
missing deviation notes in `Extractors.lean` (M1, M2) and a silent correction of a source
inconsistency in `Defs.lean` (M3). There is also one cosmetic item (M4).

Audited head: `789cf450527ff6b8c779161e555f04093080b88d`. All file:line references below are from
the checkout at that head. Source text was extracted with `pdftotext -layout` from PDF pp. 163–166
and 193–198 into `gate01-review/pdftext/`.

**Vadhan [Vad12] verification limit.** The author's PDF host (`people.seas.harvard.edu`) is
blocked from this session for both curl (proxy 403) and WebFetch (outside the allowed domains), and
so is the secondary host I tried (`weikailin.github.io`). Web search could only corroborate two
things. First, [Vad12] §6.1 is "Motivation and Definition", starting at printed p. 167. Second, a
course's notes cite [Vad12] Def 6.13 for the plain `(k, ε)`-extractor and Thm 6.18 (p. 179) for
the leftover hash lemma. I could not verify that Lemma 6.3 is the statistical-difference lemma,
what Proposition/Lemma 6.4 says, or that Def 6.16 is the strong-extractor definition. Wherever
those numbers matter, I give wording that does not depend on them.

---

## Finding 1 (minor): wrong source pointers in `Extractors.lean`

**Claim.** The [Vad12] numbers are wrong: "Lemma 6.4" should be Lemma 6.3(7), and the strong
extractor is Def 6.16, not Def 6.13. Also, the `IsStrongExtractor` docstring says [PS10] §8.3.3
"states" the leftover hash lemma, but that section is an empty heading.

**Verdict: true.** The [PS10] part is verified against the PDF. The [Vad12] part is corroborated
only in part; the rest is unverified.

**Evidence.**
- PDF p. 196 (book p. 184) ends with the heading `8.3.3 Left-over hash lemma`. PDF p. 197 is
  `Bibliography`. So §8.3.3 states nothing.
- `Extractors.lean:170–171` reads "[PS10, §8.3.3] states the leftover hash lemma under this heading
  without a definition". That is false as written. It also contradicts the file's own module
  reference at `:45`, which says "(the leftover hash lemma, heading only)".
- `Extractors.lean:193` cites `[PS10, §8.3.3]` first as a source of the theorem's statement. The
  auditor's line list leaves this out, but the auditor's own fix covers it.
- Def 6.13: a secondary source cites [Vad12] Def 6.13 for the *ordinary* seeded `(k, ε)`-extractor.
  That corroborates the claim that 6.13 is not the strong definition. Note that the pack itself
  also says "follows [Vad12, Def 6.13]" in its Known deviations.
- "Lemma 6.4" (`:81`, `:102`, `:135`) and the proposed "Lemma 6.3(7)" / "Def 6.16" are unverified.
  For what it is worth, they agree with my recollection that 6.4 is the proposition about running
  randomized algorithms on extractor output.

**Severity.** Minor is correct: this is an attribution defect, and no statement is wrong.

**Disposition: fix in the closing commit.** The wording below does not depend on a [Vad12] number.
`StatisticalDistance.lean:45` on `main` already cites `statDist` as `[Vad12, §6.1]`, so the
section-level pointer matches existing practice. If the maintainer checks printed pp. 169 and 176
of the published PDF, `§6.1` can become `Lemma 6.3` and `Ch. 6, strong extractors` can become
`Def 6.16`. If Def 6.13 is confirmed wrong, also add an erratum E2 to `pack-errata.md` for the
pack's Known-deviations line.

`Extractors.lean:46–47`
```lean
-- old
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1–6.2 (Lemma 6.4, Def 6.13,
  Thm 6.18).
-- new
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1–6.2 (statistical difference,
  strong extractors, Thm 6.18).
```
`Extractors.lean:81`, `:102` and `:135`: replace `[Vad12, Lemma 6.4]` with `[Vad12, §6.1]` in
all three places. Nothing else on those lines changes.

`Extractors.lean:168–171`. This edit also carries the deviation note from M1.
```lean
-- old
/-- The seeded family `f : S → α → β` is a **strong `ε`-extractor for `C`**: for every source `X`
in `C`, the pair `(s, f s x)` with a uniform seed `s` and `x ← X` is `ε`-close to uniform on
`S × β`. [Vad12, Def 6.13]; [PS10, §8.3.3] states the leftover hash lemma under this heading
without a definition. -/
-- new
/-- The seeded family `f : S → α → β` is a **strong `ε`-extractor for `C`**: for every source `X`
in `C`, the pair `(s, f s x)` with a uniform seed `s` and `x ← X` is `ε`-close to uniform on
`S × β`. [Vad12, Ch. 6, strong extractors]. [PS10] has no such definition: its §8.3.3 (the
leftover hash lemma) contains only a heading.

**Deviation:** [Vad12] defines strong `(k, ε)`-extractors on bit strings, for the class of
`k`-sources; here the class `C` and the finite seed, input and output types are arbitrary. -/
```
`Extractors.lean:192–194`. This edit also carries the deviation note from M2.
```lean
-- old
/-- **The leftover hash lemma as an extractor.** A universal hash family `f : S → α → β` is a
strong `½ √(|β| · 2^(-k))`-extractor for the `k`-sources on `α`. [PS10, §8.3.3],
[HILL99, Lemma 4.8], [Vad12, Thm 6.18]
-- new
/-- **The leftover hash lemma as an extractor.** A universal hash family `f : S → α → β` is a
strong `½ √(|β| · 2^(-k))`-extractor for the `k`-sources on `α`. [HILL99, Lemma 4.8],
[Vad12, Thm 6.18]; [PS10, §8.3.3] carries this title but no text.

**Deviation:** stated over arbitrary finite types, for min-entropy `k` and for `f` universal in
the collision-count sense of `IsUniversal`, with the error in closed form (for `|β| = 2^m` it is
`2^((m - k)/2 - 1)`); the cited statements are over bit strings and are not phrased in exactly
these terms.
```

---

## Finding 2 (minor): `IsFlatSource` restricts `k` to ℕ without saying so

**Claim.** The deviation paragraph for `IsFlatSource` does not mention that `k : ℕ`. This excludes
flat sources whose support size is not a power of two, such as uniform on 3 points, which is
`log₂ 3`-flat in a real-parameter reading.

**Verdict: true.**

**Evidence.** `Entropy.lean:153–156`: the deviation paragraph covers only the omitted
"additionally" conjunct, and the signature has `(k : ℕ)`. [PS10] Def 183.5 (PDF p. 195): "If
additionally X is the uniform distribution on 2^k distinct elements, we say X is a k-flat source".
`k` is never typed there, and the companion `k`-source notion uses an arbitrary real threshold. The
counterexample works. Take masses `(1/3, 1/3, 1/3, 0)`. Any witness `s` must equal the positive
support, because the mass is `(2^k)⁻¹ > 0` exactly on `s`. That forces `2^k = 3`, which no natural
`k` satisfies. The pack disclosed `k : ℕ` to the auditor, but the docstring, which is the trusted
surface, does not.

**Severity.** Minor is correct: this is an undeclared restriction affecting edge cases.

**Disposition: fix in the closing commit** (docstring only).

`Entropy.lean:153–154`
```lean
-- old
**Deviation:** [PS10] requires a flat source to be a `k`-source as well; that is automatic
(`IsFlatSource.isSource`), so it is a theorem here rather than part of the definition. -/
-- new
**Deviations:** [PS10] requires a flat source to be a `k`-source as well; that is automatic
(`IsFlatSource.isSource`), so it is a theorem here rather than part of the definition. Here `k`
is a natural number, so only supports whose size is a power of two are covered; [PS10] leaves `k`
untyped, and in a real reading the uniform distribution on `N` points is `log₂ N`-flat. Those
distributions are still available as `flat s`. -/
```
Add a real-parameter predicate only if a later phase needs one.

---

## Finding 3 (minor): `Scheme.Correct` is identified with Def 152.1(2) without locality

**Claim.** The new sentence identifying threshold `Correct` with [PS10, Def 152.1, item 2] leaves
out `LocalReconstruct`. Without it, `Correct` can hold while a coalition cannot actually
reconstruct.

**Verdict: true.**

**Evidence.** `Defs.lean:97`: "For the threshold structure this is [PS10, Def 152.1, item 2]: any
`k` shares reconstruct." `Correct` (`:98–99`) constrains `reconstruct A (share sec r)`, where
`reconstruct` sees the full assignment. I checked the auditor's §5.7 counterexample:
- the setup is `P = Fin 2`, threshold 1, `share s () 0 = false`, `share s () 1 = s`,
  `reconstruct A f = f 1`;
- `Correct` holds, including for `A = {0}`;
- `LocalReconstruct` fails on `{0}`, with `f = (false, false)` and `g = (false, true)`.

[PS10]'s `Recon` (PDF p. 165) receives only the `k` shares, so "this is item 2" is false without
locality. The issue is disclosed nearby, in the `Scheme` deviation (`:82–85`) and the
`LocalReconstruct` docstring (`:101–103`), and Shamir proves `localReconstruct`. That is why the
finding is only minor.

**Severity.** Minor is correct.

**Disposition: fix in the closing commit.** The edit is docstring-only, as the ruling requires.

`Defs.lean:96–97`
```lean
-- old
/-- Every authorized set recovers the secret, whatever the dealer's coins were. [Bei11, §1]
For the threshold structure this is [PS10, Def 152.1, item 2]: any `k` shares reconstruct. -/
-- new
/-- Every authorized set recovers the secret, whatever the dealer's coins were. [Bei11, §1]
For the threshold structure, together with `LocalReconstruct`, this gives
[PS10, Def 152.1, item 2]: any `k` shares reconstruct. -/
```

---

## Finding 4 (minor): the `Shamir.scheme` source comparison needs `k ≥ 1`, and silently corrects Lem 153.2

**Claim.** The new restriction claim needs a positive threshold, and the "degree" wording should
say "at most". Also, citing [PS10, Lem 153.2] silently corrects that lemma's "unique degree-`n`
polynomial".

**Verdict: true.** One refinement: only `1 ≤ k` is actually needed. `n < p` is already stated, and
`k ≤ n` is not needed for the special-case claim, because for `k > n` the [PS10] correctness claim
is vacuous and `perfectPrivacy` covers privacy.

**Evidence.**
- `Shamir.lean:94–96` says [PS10]'s correctness and privacy claims "are special cases of `correct`
  and `perfectPrivacy`". However, `correct` (`:121`) requires `0 < k`. At `k = 0`, coins are
  `degreeLT F 0 = {0}`, `poly sec 0 = C sec`, and empty-set interpolation returns 0, so the claim
  fails at `k = 0`.
- `:97` (new text): "threshold `k` needs degree `k − 1`". It should say *at most* `k − 1`, since
  the random coefficients can be 0.
- [PS10] Lem 153.2 (PDF p. 165): "the unique degree-n polynomial that interpolates these points".
  Its own proof says "Q … is also a polynomial of degree at most n". The data `(0,0), (1,0)`
  admit no polynomial of exact degree 1, because `a + bt` with `a = 0` and `a + b = 0` forces
  `b = 0`. `Shamir.lean:89` cites the lemma for "the interpolation step" with no note.
- The "degree-`< k`" wording on `:87` predates this PR. It belongs to the other author, so I put
  the qualification in the PR's own new paragraph rather than rewriting that sentence.

**Severity.** Minor is correct.

**Disposition: fix in the closing commit** (docstring-only).

`Shamir.lean:92–98`
```lean
-- old
**Deviations from [PS10, Prot 154.4].** [PS10] works over `ℤ_p` for a prime `p > n` and gives
shares only to the parties `1, …, n`; here the field is arbitrary and every nonzero element is a
party. [PS10]'s `n`-party scheme is this one with the other parties' shares discarded, and its
correctness and privacy claims, which concern sets of those parties, are special cases of
`correct` and `perfectPrivacy`. [PS10] draws `n − 1` random coefficients and writes the
polynomial up to `a_n tⁿ`, a typo: threshold `k` needs degree `k − 1` and the `k − 1` random
coefficients that the coins `q` carry here. -/
-- new
**Deviations from [PS10, Prot 154.4].** [PS10] works over `ℤ_p` for a prime `p > n` and gives
shares only to the parties `1, …, n`; here the field is arbitrary and every nonzero element is a
party. For `F = ℤ_p` and `1 ≤ k`, [PS10]'s `n`-party scheme is this one with the other parties'
shares discarded, and its correctness and privacy claims, which concern sets of those parties,
are special cases of `correct` (which needs `0 < k`), `localReconstruct` and `perfectPrivacy`.
[PS10] draws `n − 1` random coefficients and writes the polynomial up to `a_n tⁿ`, a typo:
threshold `k` needs degree at most `k − 1`, that is, the `k − 1` random coefficients that the
coins `q` carry here. [PS10, Lem 153.2] says "the unique degree-`n` polynomial"; the interpolant
is the unique one of degree *at most* `n`, as its proof uses. -/
```

---

## Finding 5 (minor → note): no public equations or iff lemmas for the new definitions

**Claim.** Zero style-lint findings do not establish the policy's "definitions land with their
lemmas" requirement. Six definitions have no public equation or iff lemma: `shannonEntropy`,
`probTrue`, `IsFlatSource`, `IsExtractor`, `IsStrongExtractor` and `seededSources` membership.

**Verdict: partly true.** The factual part is true. The normative part is false.

**Evidence.**
- *Factual part.* None of those six declarations has an `_eq`, `_iff` or `mem_` lemma in either
  file. The existing interfaces are `maxProb_le_iff`, `le_minEntropy_iff`, `flat_apply`, and the
  one-directional `IsExtractor.mono` and `isExtractor_seeded`.
- *Normative part.* `policy.md` contains no requirement that definitions land with their lemmas.
  I grepped `policy.md`, `workflow.md` and the campaign briefs. The closest rule is campaign Rule
  10 (`briefs/pass-shelat-ch5-8/WORKFLOW.md:124–132`): "proofs read another file's TCSlib
  definitions only through published equations". It adds: "an API that must look inside an
  author's definitions goes beside them, in their file". The pack (`:102–103`) already says `main`
  has no such rule. The pack also never claimed that lint establishes this.

**Severity: note**, not minor. Under `main`'s policy no change is required. The real consequence
is a campaign one: later phases that consume these definitions from other files will need the
equations, and under Rule 10 the equations must go in these files.

**Disposition: fix in the closing commit (optional, recommended).** The lemmas are cheap,
`rfl`-proved, and would otherwise force a later PR into the same files. If the maintainer prefers
not to re-elaborate now, record the six lemmas as owed API for the first downstream consumer.
**This needs Lean:** elaborate both files and confirm each `rfl`/`Iff.rfl` closes. I have not run
them. The style lint will also want each lemma's docstring.

Insert in `Entropy.lean` after `shannonEntropy` (after `:71`) and after `IsFlatSource`
(after `:156`):
```lean
/-- Shannon entropy is the sum of `negMulLog (p a) / log 2` over the outcomes `a`. -/
theorem shannonEntropy_eq (p : FinDist α) :
    shannonEntropy p = ∑ a, negMulLog (p a) / log 2 :=
  rfl

/-- The defining condition of a `k`-flat source: some set of exactly `2^k` points has
probability `2^(-k)` at each of its points, and every other point has probability zero. -/
theorem isFlatSource_iff [DecidableEq α] {k : ℕ} {p : FinDist α} :
    IsFlatSource k p ↔
      ∃ s : Finset α, #s = 2 ^ k ∧ ∀ a, p a = if a ∈ s then ((2 : ℝ) ^ k)⁻¹ else 0 :=
  Iff.rfl
```
Insert in `Extractors.lean` after each corresponding definition:
```lean
/-- `probTrue p D` is the total probability of the points that `D` accepts. -/
theorem FinDist.probTrue_eq (p : FinDist α) (D : α → Bool) :
    p.probTrue D = ∑ a ∈ univ.filter (fun a => D a = true), p a :=
  rfl

/-- `Ext` is an `ε`-extractor for `C` exactly when `Ext(X)` is `ε`-close to uniform for every
`X ∈ C`. -/
theorem isExtractor_iff [DecidableEq β] [Nonempty β] {C : Set (FinDist α)} {ε : ℝ}
    {Ext : α → β} : IsExtractor C ε Ext ↔ ∀ X ∈ C, EpsClose ε (X.map Ext) (uniform β) :=
  Iff.rfl

/-- `f` is a strong `ε`-extractor for `C` exactly when `(s, f s x)` is `ε`-close to uniform on
`S × β` for every `X ∈ C`. -/
theorem isStrongExtractor_iff [DecidableEq S] [DecidableEq α] [DecidableEq β] [Nonempty S]
    [Nonempty β] {C : Set (FinDist α)} {ε : ℝ} {f : S → α → β} :
    IsStrongExtractor C ε f ↔ ∀ X ∈ C, EpsClose ε (hashPair f X) (uniform (S × β)) :=
  Iff.rfl

/-- The seeded sources over `C` are exactly the products of the uniform seed with a source in
`C`. -/
theorem mem_seededSources [Nonempty S] {C : Set (FinDist α)} {Y : FinDist (S × α)} :
    Y ∈ seededSources (S := S) C ↔ ∃ X ∈ C, Y = FinDist.prod (uniform S) X :=
  Iff.rfl
```
These lemmas expose only what is already in the bodies, so they add no trusted-surface claim.
`isStrongExtractor_iff_isExtractor_seeded` (audit §6 item 6) would be a new two-direction theorem
and should wait for a consumer.

---

## Finding 6 (minor): three recognizable results lack `[Tag, location]`

**Claim.** `shannonEntropy_nonneg`, `IsFlatSource.isSource` and `isSource_uniform` have no
declaration-level source tag.

**Verdict: true.**

**Evidence.** `Entropy.lean:73`, `:158` and `:187` have no tag.
- `IsFlatSource.isSource` is literally the "additionally" clause of [PS10, Def 183.5]: the
  `IsFlatSource` docstring at `:153–154` says so, but the theorem itself does not.
- The other two do not appear in [PS10]. However, policy §2 says "anything a reader would
  recognize as 'a result' may not" omit the tag, and nonnegativity of entropy is such a result.
- The auditor's selection is not exhaustive. `EpsClose.symm` and `EpsClose.trans`
  (`Extractors.lean:140`, `:145`) are of the same kind. If the convention below is adopted, apply
  it to them too, with "an elementary consequence of [PS10, Def 181.1]".

**Severity.** Minor is correct: this is an attribution defect.

**Disposition: fix in the closing commit** (docstring only).
```lean
-- Entropy.lean:73, old
/-- Shannon entropy is nonnegative: each term `-p log₂ p` is nonnegative for `0 ≤ p ≤ 1`. -/
-- new
/-- Shannon entropy is nonnegative: each term `-p log₂ p` is nonnegative for `0 ≤ p ≤ 1`. An
elementary consequence of [PS10, Def 182.3], not stated there. -/

-- Entropy.lean:158, old
/-- A `k`-flat source is a `k`-source: every point has probability `2^(-k)` or `0`. -/
-- new
/-- A `k`-flat source is a `k`-source: every point has probability `2^(-k)` or `0`. This is the
"additionally" clause of [PS10, Def 183.5], proved here rather than assumed. -/

-- Entropy.lean:187, old
/-- The uniform distribution on `α` is a `log₂ |α|`-source; on `n`-bit strings, an `n`-source. -/
-- new
/-- The uniform distribution on `α` is a `log₂ |α|`-source; on `n`-bit strings, an `n`-source.
An elementary consequence of [PS10, Defs 183.4 and 183.5]. -/
```

---

## Finding 7 (minor): `probTrue_sub_probTrue` calls a signed difference an "advantage"

**Claim.** The docstring calls the signed difference an "advantage", while `EpsClose` uses the
word for the absolute value.

**Verdict: true.**

**Evidence.** `Extractors.lean:71` says "A distinguisher's advantage is a sum …", and the statement
(`:73`) is the signed `p.probTrue D - q.probTrue D`. `EpsClose` (`:65–67`) calls `|…|` the
advantage. Counterexample: point masses `p = δ_a` and `q = δ_b` with `D` accepting only `b` give a
signed value of `−1` and an absolute advantage of `1`.

**Severity.** Minor holds. It is a naming defect in trusted-surface prose, at the boundary with
note.

**Disposition: fix in the closing commit.**
```lean
-- Extractors.lean:71, old
/-- A distinguisher's advantage is a sum of probability differences over the points it accepts. -/
-- new
/-- The signed difference of two acceptance probabilities, `Pr_p[D = 1] - Pr_q[D = 1]`, is the
sum of the probability differences `p a - q a` over the points `D` accepts. -/
```

---

## Finding 8 (note): coin bijections mean "same distribution" only for finite, uniform coins

**Claim.** The coin-bijection form of privacy implies equal view distributions only for finite,
nonempty, uniformly sampled coins.

**Verdict: true.**

**Evidence.**
- `Defs.lean:113–115` (new): "For the threshold structure this gives [PS10, Def 152.1, item 3]:
  the shares of fewer than `k` parties have the same distribution …". The uniform-coins
  qualification appears only in the pre-existing sentence before it (`:110`).
- With `Rand = Empty`, both `Correct` and `PerfectPrivacy` hold vacuously (`Equiv.refl`).
- For an infinite field there is no uniform law.
- With biased coins, for example `q = 0` with probability one over `ZMod 3` at threshold 2, a
  single party sees the secret.

Shamir over `ZMod p` with uniform `q` is unaffected.

**Severity.** Note is correct.

**Disposition: fix in the closing commit.** This is a five-word, docstring-only insertion into the
PR's own sentence, merged with M3 below. The auditor's §6 item 8 proposals (a finite-uniform coin
theorem, and a party-restriction transport theorem) would be **code changes in `Defs.lean` /
`Shamir.lean`**. They are outside this PR under the docstring-only ruling, so record them as future
API only.

`Defs.lean:113–115`
```lean
-- old
For the threshold structure this gives [PS10, Def 152.1, item 3]: the shares of fewer than `k`
parties have the same distribution for any two secrets, so they are statistically close at
distance zero. **Deviation:** stated as a bijection of the coins rather than as closeness of
-- new
For the threshold structure and finite, uniformly sampled coins, this gives
[PS10, Def 152.1, item 3]: the shares of fewer than `k` parties have the same distribution for
any two secrets, so they are statistically close at distance zero. ([PS10] writes both "at most
`k`" and "`|S′| < k`"; the latter is meant, since `k` shares reconstruct.) **Deviation:** stated
as a bijection of the coins rather than as closeness of
```
The next line, `distributions; this is the stronger, perfect form, …`, is unchanged and follows
on directly.

---

## Finding 9 (note): `minEntropy`'s informal minimum needs the infinite-surprise convention

**Claim.** The definition is correct, but its informal formula `minₓ log₂(1/p(x))` needs the
convention that zero-mass points have infinite surprise.

**Verdict: true.**

**Evidence.** `Entropy.lean:117–120`. For `(1/2, 1/2, 0)`, `maxProb = 1/2` and `minEntropy = 1`.
Under Lean's totalized arithmetic (`(0:ℝ)⁻¹ = 0`, `log 0 = 0`), a literal minimum would contain a
spurious `0`. The docstring quotes [PS10]'s formula (PDF p. 195), where the convention is standard.

**Severity.** Note is correct.

**Disposition: record only.** The following one-phrase edit is optional:
```lean
-- Entropy.lean:117–118, old
/-- The **min-entropy** of `p` in bits: `H∞(p) = minₓ log₂ (1 / p(x)) = -log₂ (maxₓ p(x))`.
[PS10, Def 183.4] -/
-- new
/-- The **min-entropy** of `p` in bits: `H∞(p) = minₓ log₂ (1 / p(x)) = -log₂ (maxₓ p(x))`, the
minimum taken over the points of positive probability (a point of probability zero has infinite
surprise). [PS10, Def 183.4] -/
```

---

## Finding 10 (note): overlap between `EpsClose` and the sampler-based `StatClose`

**Claim.** The overlap with `StatClose` on the ch. 2–4 branch is real but involves a different
carrier, and "no copied proof requiring a duplication major was established".

**Verdict: partly true.**

**Evidence.**
- *The `StatClose` part is true.* `Sampling.lean:109` on `cryptography/pass-shelat-ch2-4` defines
  `StatClose` over samplers `σ → γ` with Prop-valued tests and a possibly infinite `γ`. That is a
  different carrier from `FinDist`.
- *The conclusion is out of date.* Erratum E1, which I verified on both branches, shows that
  `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean:128`, on
  `cryptography/pass-shelat-ch2-4` and `origin/cryptography/garg-ch1-3`) duplicates
  `abs_probTrue_sub_le_statDist`:
  - it states `|∑ g ∈ T, (p g - q g)| ≤ statDist p q`, over the same `FinDist` and the same
    `InformationTheory.statDist`;
  - its proof has the same structure: the sum is zero, a complement split, and the triangle
    inequality on each part;
  - its `h0` duplicates the PR's private `sum_sub_eq_zero`.

  The auditor checked only `Sampling.lean` and so missed it.

**Severity.** Note stands. Unacknowledged debt would be major, but ledger entry DL-1
(`duplication-ledger.md:7`) records it as "accepted 2026-11-04 (user)", together with the
integration plan: the branch lemma becomes a corollary through `D := (· ∈ T)` or is removed.

**Disposition: record only.** Cite E1 and DL-1 in the resolution. Also correct the auditor's
conclusion: a copy *was* found after dispatch, and it is not on `main`. Keep the auditor's two
obligations: the sampler-to-`FinDist` bridge, and not presenting name searches as exhaustive.

---

## Missed by the auditor

**M1 (minor): `IsStrongExtractor` has no deviation note.**
- `Extractors.lean:168–171` generalizes the strong `(k, ε)`-extractor in two ways. It is defined
  for an arbitrary class `C`, not for the `k`-sources. It also allows arbitrary finite seed, input
  and output types instead of `{0,1}^d`, `{0,1}^n` and `{0,1}^m`.
- `IsExtractor` (`:157–158`) declares its finite-type generalization, but `IsStrongExtractor`
  declares nothing.
- The auditor noted "generalized to a class `C`" in §3.1 but did not report it.
- Fix: the `**Deviation:**` paragraph in the Finding 1 snippet for `:168–171`.

**M2 (minor): `isStrongExtractor_of_isUniversal` has no deviation note.**
- `Extractors.lean:192–199` cites [HILL99] and [Vad12] for a statement that differs from both.
  It uses min-entropy rather than an output length chosen from `ε`, Carter–Wegman collision-count
  universality (`UniversalHashing.lean:46`), arbitrary finite types, and a closed-form error.
- The auditor raised this in prose below the findings table ("should not be advertised as a
  literal transcription of HILL's hypotheses") but did not report it.
- The same omission exists on `main` in `leftover_hash`. That is out of scope, but worth a backlog
  line.
- Fix: the `**Deviation:**` paragraph in the Finding 1 snippet for `:192–194`. It deliberately
  makes no claim about HILL's exact hypotheses, which I could not verify.

**M3 (minor): the new `PerfectPrivacy` text silently resolves an inconsistency in [PS10].**
- [PS10] Def 152.1 item 3 (PDF p. 165) reads "for any subset of at most k indicies S′ ⊂ [1, n],
  |S′| < k". That is self-contradictory: with "at most k", privacy for `k` parties would
  contradict item 2.
- `Defs.lean:113–114` silently takes "fewer than `k`". This is the same kind of silent source
  correction as Finding 4's Lem 153.2 point, which the auditor did catch.
- Fix: the parenthetical in the Finding 8 snippet. It is docstring-only.

**M4 (cosmetic): `shannonEntropy_uniform` is called "declared" when it is not.**
- `Entropy.lean:78–79` cites the {0,1}^n example on [PS10] p. 182 for a statement about any
  finite `α`. The auditor's §7.1 calls this "the declared finite-alphabet extension", but no
  deviation is declared.
- Optional fix: append ", generalized from `{0,1}^n` to any nonempty finite type (the source's
  case is `shannonEntropy_uniform_bits`)" after "example after Def 182.3".

I found no other wrong statements, wrong [PS10] item numbers or vacuity problems. I checked:
- §6.1.1, §6.1.2–6.1.3 and Def 152.1 / Lem 153.2 / Fact 153.3 / Prot 154.4 / Prop 154.5;
- Defs 181.1, 181.2, 182.3, 183.4 and 183.5, and the p. 182 example;
- "The proof is given as an exercise";
- the typo `n − 1` coefficients up to `a_n tⁿ`.

All of these match the PDF.

## Checks for the maintainer after applying fixes (needs Lean, one process)

1. Elaborate `Entropy.lean` and `Extractors.lean`. This is needed for #5's lemmas. Every other edit
   is in a docstring, but docstrings are parsed, so also re-elaborate `Defs.lean` and
   `Shamir.lean`.
2. Re-run the comment-stripped byte comparison for `Defs.lean` and `Shamir.lean` against `main`
   (attestation 3), to show they are still docstring-only.
3. Run `scripts/style_lint.py`, which catches docstrings missing on the new lemmas, and the
   100-column check. I checked every snippet line above at 100 characters or fewer.
4. Optionally, check printed pp. 169 and 176 of the published [Vad12] PDF to restore exact numbers
   (Lemma 6.3 / Def 6.16) in place of the section-level pointers.

## Sources consulted for [Vad12] (search results only; the PDFs could not be fetched)

- [Vadhan, *Pseudorandomness*, front matter](https://people.seas.harvard.edu/%7Esalil/pseudorandomness/frontmatter.pdf):
  the search snippet "6.1 Motivation and Definition 167".
- [W. Lin, CS6222 notes, PRG from any OWF](https://weikailin.github.io/cs6222-fa23/3-1-prg-const):
  the search summary says the notes cite [Vad12] Def 6.13 for `(k, ε)`-extractors and Thm 6.18
  (p. 179) for the leftover hash lemma.
- [M. Bun, BU CS599 lecture notes](https://cs-people.bu.edu/mbun/courses/599_S22/notes/lec12.pdf):
  strong `(k, ε)`-extractor on bit strings, `(U_d, Ext(X, U_d)) ≈_ε (U_d, U_m)`.
