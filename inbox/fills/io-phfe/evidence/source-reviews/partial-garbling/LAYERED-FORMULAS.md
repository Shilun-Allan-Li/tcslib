# Concrete layered partial-garbling formulas

These are derived formulas for the specialization of [AGW20, Appendix A,
(28)–(32), pp.37–38] to the polynomial tensor representation. They are not
additional claims quoted from the papers. The proof route is forward and
backward path sums, then a translation; no determinant, ABP datatype, or
[IK02] lemma is needed.

## Parameters and indexing

Let R=ZMod p, with p prime in the cryptographic use. The algebraic identities
below hold over any commutative ring; exact uniform sampling additionally
requires a finite ring (for ZMod p, ensure p≠0). Neither d nor n′ needs to be
positive. Let A=Fin(ℓ+1), J=Fin n′, and

    C : J → (Fin d → A) → R.
    xhat(i.castSucc)=x(i), xhat(Fin.last ℓ)=1.
    f_C(x)(j)=Σ_{τ : Fin d→A} C(j,τ) Π_{i : Fin d} xhat(τ(i)).

Use the exact index types proposed in design-r3:

    M := Σ k : Fin(d+1), (Fin k.val → A).
    T := Σ k : Fin d, (Fin(k.val+1) → A).
    Q := T ⊕ J.                 -- randomness coordinates
    O := J ⊕ M.                 -- garbling coordinates, in (31)'s order

The root m0∈M has depth 0 and the unique empty tuple. A T-coordinate
v=⟨k,τ⟩ has a node node(v)∈M of depth k+1, parent(v)∈M of depth k with
tuple Fin.init τ, and label last(v)=τ(Fin.last k). Define leaf(τ)∈M of
depth d for τ:Fin d→A.

    m=|M|=Σ_{k=0}^d (ℓ+1)^k.
    |T|=Σ_{k=0}^{d−1}(ℓ+1)^(k+1)=m−1.
    t_rng=|Q|=|T|+n′=m+n′−1.
    |O|=m+n′.

For natural-number proofs, first show m=1+|T| and t_rng+1=m+n′; derive
the subtraction form afterward. Index types and dimensions depend only on
ℓ,d,n′, not on the tensor C. Thus the same m works for adaptive key queries.
The conceptual polynomial computation has m polynomial nodes, n′ output
nodes, and one sink: |V|=m+n′+1. The output length is |V|−1 as in
[IW14, Theorem 3] at t_tail=1.

## Exact L1 and L0 formulas

Write [P] for 1 if proposition P holds and 0 otherwise. Define

    L1_C : Matrix Q (Fin ℓ × M) R
    L0_C : Matrix Q M R.

For a non-root polynomial row v∈T, a public-variable index i, and u∈M:

    L1_C(inl v,(i,u))
      = [u=parent(v)] · [last(v)=Fin.castSucc i].

    L0_C(inl v,u)
      = [u=parent(v)] · [last(v)=Fin.last ℓ] − [u=node(v)].

For an output row j∈J:

    L1_C(inr j,(i,u))=0.
    L0_C(inr j,u)=Σ_{τ : Fin d→A} [u=leaf(τ)] · C(j,τ).

The finite-sum leaf formula avoids dependent tuple transport/casts. An
implementation may replace it with a depth-equality branch, but must prove
an equation reader relating it to this formula. In particular, no x appears
in L0_C or L1_C.

Represent the singleton-index-tidied x⊗I_M matrix explicitly as

    K_x((i,u),v)=[u=v] · x(i),
    B_C(x)=L1_C * K_x + L0_C.

Its key entry readers are

    B_C(x)(inl v,u)
      = [u=parent(v)] · xhat(last(v)) − [u=node(v)],
    B_C(x)(inr j,u)=Σ_τ [u=leaf(τ)] · C(j,τ).

Here K_x is (x⊗I_M) with the Fin 1 factor removed by its canonical equivalence;
it has rows Fin ℓ×M and columns M. This is the orientation required by (32).
Using pair-indexed rows/columns, rather than flattening into Fin(ℓ*m), is
an explicitly disclosed encoding/order choice. Do not transpose K_x again.

## Canonical garbling and reconstruction

For t:Q→R, define tJ(j)=t(inr j), and e0:M→R by e0(u)=[u=m0].
The interface's garblings are DERIVED DEFINITIONS, not independent fields:

    pgb(C,x,z,t)(inl j)=z(j)−tJ(j).
    pgb(C,x,z,t)(inr u)=(t ᵥ* B_C(x))(u).

    pgbStar(C,x,μ,t)(inl j)=−tJ(j).
    pgbStar(C,x,μ,t)(inr u)=(t ᵥ* B_C(x))(u)+μ·e0(u).

For u=⟨k,τ⟩∈M define the forward value

    D_x(u)=Π_{i : Fin k.val} xhat(τ(i)).

The reconstruction vector is

    rec(C,x)(inl j)=f_C(x)(j).
    rec(C,x)(inr u)=D_x(u).

Then D_x(m0)=1, and the two forward identities are

    (B_C(x) *ᵥ D_x)(inl v)=0,
    (B_C(x) *ᵥ D_x)(inr j)=f_C(x)(j).

For a polynomial-node row, the first equation is exactly
D_x(parent(v))*xhat(last(v))−D_x(node(v))=0. Summing the two blocks gives

    pgb(C,x,z,t) ⬝ᵥ rec(C,x)=z ⬝ᵥ f_C(x)

for EVERY t. This proves the raw interface's rec_spec. The distinguished
coordinate also satisfies rec(C,x)(inr m0)=1, yielding AGW20's shift reader
if later consumers need it.

## Backward values and exact privacy

Define backward values S_C,x,z on M. At depth d:

    S(leaf τ)=Σ_j C(j,τ) · z(j).

At a node u of depth k<d:

    S(u)=Σ_{a:A} xhat(a) · S(child(u,a)).

A completely explicit nonrecursive choice is available. For u=⟨k,τ⟩,
let append(τ,σ):Fin d→A be Fin.append of the prefix τ and a suffix
σ:Fin(d−k)→A, transported along k+(d−k)=d. Define

    S(u)=Σ_{σ : Fin(d−k)→A}
             (Σ_j C(j,append(τ,σ)) · z(j)) · Π_i xhat(σ(i)).

This is total also at k=0 and k=d. The leaf/branch equations above are its
required readers: use Fin.consEquiv to split a nonempty suffix, Fin.snoc to
append its first letter to the prefix, and Fin.prod_univ_succ for the suffix
product. This avoids well-founded recursion and any choice of witnesses.

Set s:Q→R by s(inl v)=S(node(v)) and s(inr j)=z(j). The backward
identities are

    S(m0)=μ, where μ=z ⬝ᵥ f_C(x),
    s ᵥ* B_C(x)=μ·e0.

The second is a column identity: the weighted sum of child/output backward
values equals the node's backward value, which cancels the −1 diagonal
except at the root (the root has no randomness row).

The POINTWISE identity has this sign:

    pgb(C,x,z,t)=pgbStar(C,x,μ,t−s).

Indeed −(tJ−z)=z−tJ and (t−s)B+μe0=tB. Translation
t↦t−s is the equivalence Equiv.addRight (−s), with inverse t↦t+s.
Use ProbComp.expect_sample_equiv on this equivalence to conclude exact
law equality for every real-valued test. There is no failure event or
partial-garbling slack, including the zero-dimensional cases below.

## Group-lifted simulator reader (no discrete log)

Given h=g^μ as a GROUP ELEMENT, define group garbling directly:

    inl j ↦ g^(-tJ(j)).val,
    inr u ↦ g^((t ᵥ* B_C(x))(u)).val · (if u=m0 then h else 1).

Prove this equals expVec g (pgbStar(C,x,μ,t)) when h=g^μ.
The implementation never recovers μ from h; multiplication and exponentiation
by known scalars suffice. This reader is what the Pi simulator needs.

## Zero-dimensional boundary checks

### d=0, arbitrary ℓ,n′

M is a singleton root, T is empty, Q≃J. There is one depth-zero tuple.
Writing c_j=C(j,empty), L1=0 and L0(j,root)=c_j. Consequently

    pgb(z,t)=(z−t, Σ_j t_j c_j),
    pgbStar(μ,t)=(−t, Σ_j t_j c_j+μ),
    rec=(c,1), μ=Σ_j z_j c_j, s=z.

The same reconstruction and translation identities hold. No child, parent,
or positive-depth witness is required.

### n′=0, arbitrary ℓ,d

J is empty, C/f/z are the unique empty families, μ=0, and every backward
value S is 0. L0 has no output rows, Q=T, and s=0. Real and ideal garblings
are pointwise identical even before averaging. Reconstruction remains valid.

### d=0 and n′=0

M is the singleton root, Q is empty. The unique garbling is the singleton
zero vector on M; rec(root)=1. Both laws are point masses at that vector.
The formulas t_rng=m+n′−1 and |O|=m+n′ give 0 and 1 respectively.

### ℓ=0 (additional consistency check)

Every tuple label is the padded constant 1; M has d+1 nodes and T has d.
L1 has no columns, while L0 is the constant-chain incidence matrix with
terminal C entries. The same formulas apply.

## Proposed Lean architecture (no public files changed)

1. `PartialGarbling.lean` (roughly 200–400 lines): Raw data, canonical
   matrix-defined pgb/pgbStar, rec_spec/privacy interface clauses and readers;
   efficient interface extending Raw with lgen_eff/rec_eff. Uniform string
   efficiency witnesses precede κ and public parameters. Ensure p≠0 (or the
   stronger prime instance) wherever uniform residue draws are formed.
2. `PartialGarbling/Layered.lean` (roughly 500–900 lines): fixed finite node
   indices/root, tensor specialization, L0/L1/rec explicit definitions and
   readers, forward/backward identities, translation, and layeredPG_raw.
   If approaching 1000 lines, split permitted children into `Indices.lean`,
   `Matrices.lean`, and `Privacy.lean`, with Layered as their facade.
3. `Wee20/Targets.lean`: PGTargets and its iff reader, then layeredPG hT;
   prove layeredPG_toRaw by pure assembly. No efficient PartialGarbling
   instance is constructed elsewhere.

One declaration-order detail needs attention when writing the interface:
Raw.rec_spec/privacy cannot refer forward to pgb defined after Raw. Either
state these fields with their expanded canonical matrix formula and publish
readers in pgb notation, or place a small generic matrix-formula definition
before Raw and let both fields and pgb refer to it. Do NOT make pgb/pgbStar
freely chosen fields just to solve this Lean ordering issue.

Recommended proof dependencies to search/reuse before any helper proof:
Fin.snoc/init and their readers, Fin.snocEquiv, Fin.prod_univ_castSucc,
Fintype.sum_sigma, Matrix mulVec/vecMul/dotProduct readers, and
ProbComp.expect_sample_equiv with Equiv.addRight. No new helper is being
claimed proved or checked in this note; exact?/apply? and elaboration are
pending the lead's permitted LeanInfoView route.

## Independent finite arithmetic check

`formula_sanity.py` checked the exact incidence formulas, matrix assembly,
forward/backward identities, translation sign and reconstruction on 2,430
finite arithmetic instances: p∈{2,3,5}, ℓ,d,n′∈{0,1,2}, thirty coefficient/
input/coin draws per combination. All passed; see `formula-sanity.log`.
This checks signs/index conventions and requested empty cases, and is not
claimed as a formal proof or an exhaustive check for unbounded parameters.
