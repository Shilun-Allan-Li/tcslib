# Public-key implications pilot — proposed contents

**Draft, 2026-11-07 PST.** Names below are proposals, not declarations claimed to exist.
Proof snippets are source-level drafts and have not been elaborated as a new module.

## Target predicates

| Predicate | Meaning and source |
|---|---|
| `BitPublicKeyScheme.SingleBitSecure` | Indistinguishability of encryptions of bits; `Asymptotic/PublicKey.lean:250`. |
| `PublicKeyScheme.Secure` | Indistinguishability for every equal-length pair of messages, with the public key included; `Asymptotic/PublicKey.lean:142`. |
| `PublicKeyScheme.MultiMessageSecure` | The corresponding polynomially many-message experiment; `Asymptotic/PublicKey.lean:166`. |
| `Composability.FixedLengthPKScheme.INDSecure .cpa` | Gate 06's two-stage, key-visible CPA oracle game; `Composability/PublicKey.lean` on the integration branch only. |
| `Candidates.GroupPKScheme.Secure` | ElGamal's key-dependent group-message selector model; `Candidates/ElGamal.lean:458`. Retain its separate admissible-message correctness theorem. |

The index must distinguish these conclusions. A proof for one does not acquire another label.

## Closed generic routes: implement first

All these wrappers belong above `Asymptotic/PublicKey` and use existing public theorems.

### PK-1: hard-core trapdoor permutations give single-bit PKE

Proposed name: `exists_singleBitSecure_of_hardCoreTDP`.

```lean
(T : TrapdoorCollection) {h : ∀ i, T.D i → Bool}
(hT : T.OneWay) (hHC : T.toCollection.HardCore h) :
  ∃ S : BitPublicKeyScheme, S.SingleBitSecure
```

Draft proof: obtain `E` from `hHC.nonempty_predEvaluator`, then return
`⟨T.tdpBitScheme E, T.tdpBitScheme_singleBitSecure E hT hHC⟩`.
The construction's record includes uniform key generation/encryption, polynomial-time
decryption and correctness. Source: `Asymptotic/PublicKey.lean:749` and `:911`;
[PS10, Algorithm 104.3 and Theorem 104.4].

### PK-2: the same assumption gives message encryption

Proposed name: `exists_securePublicKey_of_hardCoreTDP`, with the same premises as PK-1 and
conclusion `∃ S : PublicKeyScheme, S.Secure`.

Draft proof: obtain `⟨S, hS⟩` from PK-1; return `⟨S.bitwise, hS.bitwise⟩`.
Source: `Asymptotic/PublicKey.lean:353` and `:471`; [PS10, p. 103].

### PK-3: the same assumption gives multi-message encryption

Proposed name: `exists_multiMessageSecurePublicKey_of_hardCoreTDP`, conclusion
`∃ S : PublicKeyScheme, S.MultiMessageSecure`.

Draft proof: obtain `⟨S, hS⟩` from PK-2; return `⟨S, hS.multiMessageSecure⟩`.
Source: `Asymptotic/PublicKey.lean:529`; [PS10, p. 103].

### PK-4: fixed-width trapdoor permutations supply the hard-core bit

Proposed names: `exists_singleBitSecure_of_fixedWidthTDP` and
`exists_securePublicKey_of_fixedWidthTDP`.

Retain explicitly `m : PolyExpr`, `hT : T.OneWay`, and

```lean
henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)),
  (T.encD (T.index n r) x).length = m.eval n
```

Use `hT.exists_glPad_singleBitSecure m henc`, then bitwise encryption for the second form.
Source: `Asymptotic/HardCoreCollection.lean:92`, `:489`, `:498` and
`Asymptotic/PublicKey.lean:1059`; [PS10, Theorems 87.3 and 104.4].
This generic fixed-width result is useful on its stated domain. It is not an RSA instantiation.

## Exact CPA route: waiting on Gate 06C

Proposed name: `exists_cpaSecurePublicKey_of_hardCoreTDP`.

Start with PK-1. `BitPublicKeyScheme.exists_padBound` supplies `L`, its ciphertext padding
bound and `1 ≤ L.eval n`; then `hS.padded_cpa L hL hmsg` supplies the CPA claim for
`S.padded L hL hmsg`. Alternatively compose the existing
`TrapdoorCollection.tdpBitScheme_padded_cpa` directly, retaining all premises.

The key bridge `BitPublicKeyScheme.SingleBitSecure.padded_cpa` is currently an admission on
the Gate 06 integration branch. Its statement gate and fill are prerequisites for calling
this a completed CPA implication. The wrapper itself needs no new reduction proof.

## Concrete assumptions: index their actual current endpoints

| Assumption | Existing endpoint | Extra premises | Missing work before a generic CPA-PKE existence theorem |
|---|---|---|---|
| `RSAAssumption` | `(rsaTrapdoor H).OneWay`, via `rsaCollection_oneWay` and `rsaTrapdoor_oneWay` (`Candidates/RSA.lean:2206`, `:2221`) | `H : ArithmeticFP` (`Candidates/Arithmetic.lean:314`) | Goldreich–Levin padding needs a genuine length bridge; exact CPA then needs the Gate 06C bridge. |
| `FactoringAssumption` | `(rabinBlumTrapdoor H).OneWay` (`Candidates/Rabin.lean:3392`) | `ArithmeticFP`, `BlumDensity` remains a hypothesis | Same encoding-length issue and CPA bridge. The plain factoring collection is not itself a trapdoor-permutation conclusion. |
| `DDHAssumption (egGroupGen H G)` | `(elGamal H G).Secure` in `GroupPKScheme` (`Candidates/ElGamal.lean:2211`) | `ArithmeticFP`, `G : SafePrimeGen`, negligible full-length-exception bound `hbig` | Preserve the group-message security/correctness model; a conversion to another PKE record/security game is separate work. |

RSA's construction is `Candidates/RSA.lean:1493`; its concrete RSA root-extraction assumption
is `:105`/`:118`. The generic padding documentation explicitly states the cost:
`Asymptotic/HardCoreCollection.lean:85–91`. Generated RSA elements have width `2*max(n,2)`,
Rabin's width is `2*max(n,3)`; no current candidate satisfies the exact `PolyExpr` equality as
parameterized. The documented per-index-width/bounded-length version is not formalized.

**Do not declare a candidate-level theorem by adding that impossible premise.** A future
normalization or generalized padding construction must have a real public contract and proof.
Its statement/fill work is separate from the short Implications wrappers.

## Review and implementation checks

- Every final theorem has an explicit mathematical header, an accurate source docstring and
  all retained hypotheses. Use source-level proof terms through public APIs only.
- Show each witness's actual scheme and security model. Keep the paired correctness theorem
  when the source record does not contain it (GroupPKScheme).
- Check axiom dependencies of the entire composition. Distinguish existing admissions from
  proof completion, even if the new wrapper has no local sorry.
- Use an isolated PR worktree, precise imports, topic facade/root exports and serial module
  checks. No new host is needed for the generic pilot.

**Not yet clear to merge — proposed contents, no new Lean wrapper module checked yet.**
