# BilinearGroup.pairVec_expVec_left proof draft

Status: proof draft after root native reuse searches; not natively elaborated here.
No live edits, Lean, lake, build, or Git commands. No further helper or import is proposed.

## Deliverable

`ExponentsPairVecExpVecLeft.lean.inc` preserves the proposed full docstring, proof sketch,
source tag, and exact searched header:

```lean
theorem pairVec_expVec_left [Fintype ι] (g : B.G) (v : ι → ZMod B.order)
    (u : ι → B.G) :
    B.pairVec (B.expVec g v) u = B.pair g (groupDot u v)
```

Context: existing namespace `TCSlib.Cryptography.Pairing.BilinearGroup`, with
`{ι κ υ : Type*}` and `{wG wT : ℕ} (B : BilinearGroup wG wT)`. The additional indices
κ and υ are not parameters of this theorem. Suggested placement is beside the existing
pairing/vector transport laws in the owned Exponents module.

The only proof block is:

```lean
  simp only [B.pairVec_eq, B.expVec_apply, groupDot_eq, map_prod,
    B.pair_pow_left, B.pair_pow_right]
```

A Python assertion matched the exact anonymous target header in the archived root probe
(changing only `example` to the proposed name). Width <=100, one tactic block, no admitted
term or additional helper.

## Existing theorem reuse

`B.pairVec_eq` and `B.expVec_apply` read the left side as
`prod i, B.pair (g ^ (v i).val) (u i)`. `B.pair_pow_left` makes each coordinate
`B.pair g (u i) ^ (v i).val`.

`groupDot_eq` reads the right side as `B.pair g (prod i, u i ^ (v i).val)`.
The already-published monoid hom `B.pair g : B.G ->* B.GT` consumes `map_prod`;
`B.pair_pow_right` gives exactly the same coordinate powers. This reuses the generic
homomorphism/finite-product law rather than proving a new distribution theorem.

Exact inspected sources:

- Pairing/Exponents:154, `BilinearGroup.pairVec_eq`.
- Same module :119, `BilinearGroup.expVec_apply`.
- Same module :67, `groupDot_eq`.
- Pairing/Group:183, `BilinearGroup.pair_pow_left`.
- Same module :187, `BilinearGroup.pair_pow_right`.
- Mathlib Algebra/BigOperators/Group/Finset/Defs:342, global `map_prod`.

No pairing symmetry, generator-surjectivity witness, scalar witness for u, encoding
inverse, group logarithm, group inverse operation, or modular arithmetic theorem is
needed. The scalar vector v is supplied by the statement. The arbitrary u is only
multiplied, raised to known natural representatives and paired. Empty ι is handled by
the generic finite-product/homomorphism equations. No admitted dependency is used.

Only the listed published readers and equations appear in simp; no foreign definition
or generated defining equation is explicitly unfolded. The current Exponents import
closure already provides these APIs, so no new root/import is expected.

## Native reuse-search evidence (parent-run)

Read `evidence/search/arbitrary-group-and-expansion/run/results.jsonl` and the two
archived ArbitraryGroupTransport source targets.

- Exact module rc1, exactly two expected no-proof errors across the two helper targets,
  zero warnings/sorries; source SHA-256
  `db26ae5961df3e4fa78632a02c792a8f1d80b642a1876a0096dced77f4ef41b1`.
- Apply module rc1, one error plus one partial proof/warning across those targets;
  source SHA-256
  `f1d1e9fec9eb2e279f3a33eb16ccc844c751dbe71bf203ac30a97b6d624b97b0`.
- Parent reports the pairVec target's apply? result specifically found no relevant lemma;
  the other target had only partial suggestions. There were no typing errors or full
  matches. These are completed reuse probes, not proof validation of this candidate.

The probe imports the already-proved Exponents module and no proposed helper placeholder.
No native search or proof command was executed by this agent.

## Actual reads/searches in this invocation

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
rg --files evidence/search/arbitrary-group-and-expansion | head -25
cat evidence/search/arbitrary-group-and-expansion/run/results.jsonl
sed -n '146,157p' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '178,189p' TCSlib/Cryptography/Pairing/Group.lean
sed -n '338,347p' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean
rg -n -A 16 -B 6 'pairVec_expVec_left|example.*Fintype|B.pairVec \(B.expVec g v\)' evidence/search/arbitrary-group-and-expansion/*.lean.txt
rg -n 'pairVec_expVec_left|pair_pow_left|pair_pow_right|map_prod.*pair|pair.*map_prod' TCSlib/Cryptography/Pairing/Exponents.lean TCSlib/Cryptography/Pairing/Group.lean | head -30
cat /private/tmp/io-phfe-drafts/proofs-fe/LinearDecFirstCorrect.helper-targets.lean.inc
```

The broader actual name/shape search record preceding the native probes remains in
`LinearDecFirstCorrect-DECOMPOSITION.md`. The new arbitrary-group matrix associativity
helper is not proved or drafted in this invocation.

## Validation limits

Static header/doc equality, one-block, width and no-admission checks passed. Root native
elaboration, standard-axiom validation, new declaration/readers audit inventory and
Exponents module-size checks remain pending. No false claim or mathematical gap found.
