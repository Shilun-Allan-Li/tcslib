# Gate 07 — equation-lemma audit findings

**Verdict: remains open — 0 blockers, 2 majors, 1 minor.**

Audited PR #210 at `fff0430c7c9db136e60ed14b069e972c2ea56fc8`, against
`05fe903fc736ac8036c161ad159dc8bdddcd6ee2`; records at
`9e888f3fb85badba8724aec472150b3ed3a6cac4`. Exchange checkout started at
`0543e73e0bb7982abc1170c7d28ac43ed8cec272`. Audit date: 2026-11-06.

Verified the bundle SHA-256
`b5a4201b72e8996c869cc9ecbd6aac6d36046c55faf45d4941d7bf2e6e1bef4c`
and source PDF SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.
All 50 bundle sections match the corresponding pinned Git objects, disregarding
terminal newlines. The supplied repair diff matches the actual base-to-head diff.

This is an independent source and evidence audit, **not an independent Lean replay**:
no Lean executable/toolchain was available. I inspected the complete repair diff,
definition bodies, relevant consumers, probe sources/logs, and the textbook source.
An independent declaration-header comparison confirmed 183 additions, exactly the
three advertised changed statements, and no removals across 33 changed Lean files.
Compiler outcomes below are identified as supplied evidence. The new reproducer
below has not been executed here.

Lean paths below are relative to `TCSlib/Cryptography/`, unless stated otherwise;
record paths are relative to `briefs/pass-shelat-ch5-8/gates/07-eqlemmas/`.
Line numbers refer to the audited head.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F01 | major | `Asymptotic/HardCorePermutation.lean:177` · `PermFamily.glHalf_f_even`; `Asymptotic/HardCoreClaims.lean:75` · `thm_87_3_1` and related statements | The statement scan missed cross-file reductions of `FunFamily.glPad`. The three restatements do not exhaust the statement-level reads covered by the pack's zero-exclusions requirement. | `glHalf_f_even` passes `z : Fin (m + m) → Bool` to `P.toFunFamily.glPad.f m`, whose argument type is `Fin (P.toFunFamily.glPad.inLen.eval m) → Bool`. Identifying these types requires the body of `FunFamily.glPad`, defined in another file at `Asymptotic/HardCore.lean:564`. Its result type needs the corresponding output-length reduction. `thm_87_3_1` similarly passes `Fin.appendEquiv … y`, of length `𝓕.outLen.eval n + 𝓕.inLen.eval n`, to an adversary expecting length `𝓕.glPad.outLen.eval n`. No explicit transport or published equivalence appears in either signature. See the type analysis and reproducer below. | Extend the repair scope to these consumers. Publish input/output transports or equivalences beside `FunFamily.glPad`, restate the affected signatures through them, and re-elaborate the consumer closure with that definition sealed. Retain paired unsealed/sealed controls. |
| F02 | major | `pack.md`, Seal attestation; `worker-reports/E1a-REPORT.md`, padded permutation group; `evidence/e1a/Seal.lean.txt:232` | The evidence does not establish the claim that every lemma group is exercised sealed with controls. In particular, the padded permutation domain/field group is missing. | E1a lists `PermCollection.glPad_domEquiv`, its `_apply`, and `PermCollection.glPad_perm` as a separate group. Its `DomainGlPad` pass section seals only `Collection.glPad` and `TrapdoorCollection.glPad`, and tests the collection function/generator/sampler and trapdoor inverse. It never uses the padded permutation domain equivalence or permutation equation. The final restatement probe additionally seals `PermCollection.glPad`, but tests only the three restatements and PublicKey proofs. Across the supplied probe sources, `PermCollection.glPad_perm` occurs in axiom/direct-sorry inspection scripts, not in a sealed consumer proof. Axiom inspection does not test that interface. | Add a successful consumer of the padded permutation domain and conjugated permutation equation with `PermCollection.glPad` and `Collection.glPad` sealed, plus a matching direct-definition control that passes unsealed and fails sealed. Map each claimed group to its actual pass/control examples and logs. |
| F03 | minor | `Candidates/Factoring.lean:492` · proof sketch of `polyTimeComputable_samplePrimeL` | The stated formula for the fallback numeral omits its small-length cases. | The sketch writes `natToList n 2 = 0^(n−2)10` without restricting `n`. At `n = 0` the actual list is `[]`; at `n = 1` it is `[false]`. The displayed construction has length two in both cases when subtraction is natural subtraction. The theorem quantifies over all input lengths. This is a sketch defect, not a counterexample to polynomial-time computability. | Restrict that formula to `n ≥ 2` and give the constant branches `[]` and `[false]` at lengths zero and one. |

**F01: why this is a statement-level dependency.** The defining fields are

```lean
-- Asymptotic/HardCore.lean, FunFamily.glPad
inLen  := .add 𝓕.inLen 𝓕.inLen
outLen := .add 𝓕.outLen 𝓕.inLen
```

Consequently, the signature of `PermFamily.glHalf_f_even` uses both conversions

- `P.toFunFamily.glPad.inLen.eval m ≡ m + m`;
- `P.toFunFamily.glPad.outLen.eval m ≡ m + m`.

Both conversions require reducing that foreign definition. The equality sign in its conclusion is
homogeneous, so the second conversion is required as well as the first. This is
the same kind of implicit domain conversion repaired in PublicKey, with finite
bit-string lengths in place of a collection's `D` field. The theorem is
mathematically valid; the finding concerns its interface under rule 10.

Here is a minimal paired reproducer to run at the audited head. The first example
is the existing theorem; in the second, the signature needs the sealed length
fields before its proof can be checked. The predicted sealed failure is based on
the displayed types, not a compiler log produced in this audit.

```lean
import TCSlib.Cryptography.Asymptotic.HardCorePermutation

set_option autoImplicit false
open TCSlib.Cryptography

section Unsealed
example (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    P.glHalf.f (m + m) z = P.toFunFamily.glPad.f m z :=
  PermFamily.glHalf_f_even P m z
end Unsealed

section Sealed
attribute [local irreducible] FunFamily.glPad
example (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    P.glHalf.f (m + m) z = P.toFunFamily.glPad.f m z :=
  PermFamily.glHalf_f_even P m z
end Sealed
```

Other concrete occurrences include `glHalfBit_even` (line 197),
`predProb_glHalf_even` (211), `invProb_glHalf_even` (222), and
`PermFamily.glHalf_f_odd` (241), plus `thm_87_3_2` and `thm_87_3_3` in
`HardCoreClaims.lean` (88 and 101). They should be included in the repair sweep;
this list is not a completeness certificate. Both consumer modules are already
in the supplied downstream replay.

The probe method explains the omission: E1b's `stmtprobe/mkseal.py.txt` seals a
caller-supplied list of candidate collection definitions; `classify.py.txt`
classifies the resulting errors. Classification cannot discover a definition
that was never sealed. E1a's domain scan and the final restatement probes likewise
do not seal `FunFamily.glPad`. Thus the existing pass logs do not contradict F01.

**Shared statements S1–S3.** I found no mathematical counterexample to these
statements or mismatch with their intended factoring/RSA/Rabin interfaces. They
remain sorried statements, not completed Lean proofs.

- **S1 (`Factoring.lean:495`).** The assertion covers arbitrary coin lists.
  `padFin (2 * n^2 * n)` truncates or zero-pads them before the sampler is run.
  `exists_samplePrime_nuppt` supplies the bounded machine on that exact coin
  domain; its empty failure output can be replaced in polynomial time by the
  numeral of two. An accepted block has length `n`, so emptiness distinguishes
  failure when `n > 0`. At `n = 0`, both outputs are empty. The additional
  length-one fallback branch is constant. Thus short coins do not invalidate
  S1, and F03 requires only a sketch correction.
- **S2 (`Factoring.lean:523`).** Its hypothesis is `2 ≤ n`, and its finite coin
  domain supplies exactly two independent blocks of `2n³` bits. Splitting and
  chunking are bijections, so each run receives `2n²` independent uniform
  `n`-bit candidates. Prime density gives failure probability at most
  `(1 − 1/(2n))^(2n²) ≤ exp(−n) ≤ 2^(−n)`. The fallback two is a prime below
  `2^n`, so each run is within that bound of the uniform prime distribution.
  Product distance is at most `2 · 2^(−n)`. Conditioning the uniform independent
  pair on being distinct costs exactly the diagonal probability
  `1 / |Primes n| ≤ 2n / 2^n`. The triangle inequality gives precisely the
  advertised bound. The target is ordered distinct pairs; there is no extra
  factor of two. Lengths zero and one are excluded by hypothesis. The bound at
  length two may exceed one, which is harmless.
- **S3 (`RSA.lean:404`).** Put `k = Nat.size N`, `B = 2(n + 2)` and
  `T = (4n + 8)n`, as in the existing parameters. `NeZero N` gives `N ≥ 1`
  and `k ≥ 1`. The premise gives `k ≤ B`; the coin domain has exactly `TB`
  bits. Each trial therefore reads an independent uniform `k`-bit number.
  The cited totient estimate and bit-length bounds give

  $$
  2^k \le 2N,\qquad
  N \le \varphi(N)(\lfloor\log_2 N\rfloor+1) \le \varphi(N)k,
  $$
  $$
  \frac{\varphi(N)}{2^k} \ge \frac1{2k} \ge \frac1{4n+8}.
  $$

  The first accepted number is uniform among the residues below `N` coprime
  to `N`. These correspond bijectively to `(ZMod N)ˣ`. The fallback `1 % N`
  is also such a residue. Hence distance is at most
  `(1 − 1/(4n + 8))^((4n + 8)n) ≤ exp(−n)`. For `N = 1`, the target and
  output are both the constant residue zero, including on failure. For `n = 0`,
  there are zero trials and the bound is one. `N = 0` is excluded. Neither S2
  nor S3 promises statistical closeness for an arbitrary short coin list;
  their types supply the required budget. S3 also makes no claim when `k > B`.

These routes agree with the cited formal interfaces in `NumberTheory/Primality`
(`statClose_samplePrime`, the prime failure bound, and the uniform machine),
`Candidates/Concrete` (`statClose_rejectBlocksL`), and `NumberTheory/Units`
(`le_totient_mul_log_succ`). They supply the shared interfaces requested by
`fills/factoring-candidates/brief.md`: S1 for both raw generators, S2 for the prime
pair comparison, and S3 for units at the modulus and at its totient. Subsequent
transport, invalid-pair handling, and small-parameter branches still belong to
the fills.

I checked [PS10] Algorithm 50.16 and Lemma 51.17 (book pages 50–51), Theorem
51.1 (page 51), and Theorem 53.2 and its construction (pages 53–54; PDF pages
65–66). These support the prime/unit sampling roles. The explicit truncation,
defaults, distinct-pair conditioning and numerical statistical-distance bounds
are formalization details justified by the cited lemmas, rather than bounds
stated verbatim in the textbook.

**Other audit results and limits.**

- The added equations and predicate unfoldings agree with their definition
  bodies on source inspection. The conditional interfaces include the empty,
  malformed-input, and edgeless cases relevant to their consumers. The domain
  equivalences are identities, or aliases of the appropriate identity; encoder,
  decoder (`Option.map` of the inverse), function, permutation and probability
  transport directions are consistent. The declarations are public, beside
  their definitions, with docstrings and without newly added `@[simp]` tags.
  I found no duplicate public interface in the spot-checks; private helper
  re-exports such as the three-colouring tape lemmas are intentional. The new
  project-specific equations do not introduce an independent number-theory
  theorem requiring a Mathlib replacement.
- All three advertised restatements preserve their original propositions:
  their predicates are composed with identity domain equivalences. Hypotheses
  and conclusions otherwise agree. The PublicKey proofs use the new
  `glPad_hardCore_domEquiv` bridge. Non-additive changes in the actual diff are
  confined to those restatements/proofs, the authorized Closure proof
  re-pointing, and the authorized docstring/sketch repairs. F01 is an existing
  dependency missed by the required audit sweep, not an extra changed theorem.
- The supplied final replay records 117 successful modules. The base repair
  log records rebuilding the missing dependency caches. The axiom evidence
  covers 186 declarations with no nonstandard axiom other than `sorryAx`:
  72 mention it, comprising 68 inherited cases and the three shared statements
  plus the already-sorried hard-core headline. The direct-sorry inspection and
  warning-count delta are consistent with those three authorized new holes.
  These are checks of supplied evidence, not independently reproduced builds.
- The paired E1a/E1b controls inspected are genuine for their tested examples:
  their unsealed counterparts pass and sealed counterparts fail in the supplied
  logs. The final old-statement controls exhibit the expected predicate-type
  mismatches; the new statements and both PublicKey proof forms pass sealed.
  Those results substantiate the three particular repairs. F01 and F02 prevent
  extending them to a complete rule-10 coverage claim.

Notation used above: `≡` denotes definitional equality; `k` is `Nat.size N`;
`B` and `T` are the RSA block width and trial count; `φ(N)` is Euler's totient;
`|Primes n|` is the number of primes below `2^n`. Other identifiers retain their
repository meanings.
