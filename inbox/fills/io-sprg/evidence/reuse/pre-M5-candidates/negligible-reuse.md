# Negligibility reuse for raw JLS security

Snapshot HEAD: `55cb1147ff84f750a6b94f48103f6cc72d4fa036`. `Security.lean` SHA256:
`1d4ea88eede96184453c6e160527f950778fb062f2ae3239acfe4e02eea9f857`. This is read-only proof planning; no Lean, Lake, build, cache,
exact?/apply?, source edit, or independent validation was performed. The optional
candidate is **unelaborated** and conditional on the prerequisite results below.
No local variant of `Negligible`, realization, or security is introduced.

## Exact source obligation and prerequisite boundary

`jls_secure` (`StructuredSeed/Security.lean:102`) assumes fixed arbitrary `P` and
prime schedule `pi`, locality, `P.Realizable pi`, Boolean `G.Secure`, and the
construction's own raw LPN-family `Assumption`. It concludes raw sPRG `Secure`,
meaning negligible advantage for every NUPPT via `SPRG.Raw.secure_iff`
(`Defs.lean:263`). It does not construct a realiser or machine.

The candidate invokes these **prerequisites, not validated facts**:

- `prop41` (`Security.lean:84`), which is still a source obligation in the inspected
  draft: advice families exist before **every** BL/BG realiser and **every** kappa;
- `claim42` (`Claim42.lean:155`): one threshold before all public primes, bounding
  the exact error by `2^-kappa` eventually;
- parameter theorem `Params.le_n` (`Params.lean:373`), the existing public bound
  that n grows at least as fast as its input. Its current sorried body was not used
  as evidence. Reuse this prerequisite when filled; do not reprove its published
  arithmetic claim inline in M5. The candidate was refreshed to consume it directly.

The proved `ell_eq` (Lean `ℓ_eq`), `n_eq`, the realization/assumption/security readers,
and existing library closure lemmas are the remaining inputs. No current sorried
body, self result, downstream security/existence result, or final assembly theorem
is treated as validation or as a search fact.

## Existing public negligibility API

All names below are in `TCSlib.Cryptography`, in
`TCSlib/Cryptography/Foundations/Negligible.lean`.

| Name and location | Exact signature shape | Selected use |
| --- | --- | --- |
| `Negligible.comp_of_le`, line 237 | `Negligible mu -> (phi : Nat -> Nat) -> (forall N, N <= phi N) -> Negligible (fun N => mu (phi N))` | Reindex assumption advantages along `ell` and `n`; no new polynomial-composition lemma is needed. The public result actually handles every map dominating identity. |
| `Negligible.mul_pow`, line 126 | `Negligible mu -> (d : Nat) -> Negligible (fun n => (n:Real)^d * mu n)` | Instantiate d=1 for the kappa LPN-hybrid factor. |
| `Negligible.const_mul`, line 143 | `Negligible mu -> (a : Real) -> Negligible (fun n => a * mu n)` | Multiply the LPN term and exponential error majorant by 2. |
| `Negligible.add`, line 86 | `Negligible mu -> Negligible nu -> Negligible (fun n => mu n + nu n)` | Add the LPN, Boolean-PRG, and exponential-majorant terms with the same association as prop41. |
| `negligible_two_pow_neg`, line 153 | `Negligible (fun n => (2:Real)^(-1)^n)` (Lean notation `(2:Real)⁻¹ ^ n`) | Exact negligible error majorant, no exponential proof repeated. |
| `Negligible.mono`, line 74 | `Negligible mu -> (exists n0, forall n>=n0, abs(nu n)<=abs(mu n)) -> Negligible nu` | Final eventual absolute-value domination. |
| `negligible_iff`, line 62 | Reader for the inverse-polynomial threshold definition | Available, but the selected proof need not open the definition. |

`Negligible.mul` also exists (line 110), but kappa is not negligible, so it is not
the right lemma for a polynomial hybrid factor. Use `mul_pow`, not multiplication
of two negligible functions. No `Asymptotic.Ensembles`/`EnsemblesLemmas`/`OneWay`
import or generic polynomial-loss helper is required.

## Parameter-map lower bounds: existing core facts

| Existing public fact | Exact source | Use |
| --- | --- | --- |
| `Nat.le_pow` | `/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/Nat/Lemmas.lean:1239` | `0<b -> a<=a^b`, including a=0. E>=1 yields kappa<=kappa^E; the n bound is read through Params.le_n. |
| `Params.ℓ_eq` | `StructuredSeed/Params.lean:73` | Owner reader: ell(kappa)=kappa^E. |
| `Params.n_eq` | same file `:79` | Owner reader: n(kappa)=ell(kappa)^D. |
| `Params.le_n` | same file `:373` | Public pointwise kappa<=n bound; prerequisite, not independently proved here. |

Thus the needed bookkeeping is `kappa <= ell(kappa)` and the published `kappa <= n(kappa)`. It works at
zero, so `comp_of_le` receives its required pointwise lower bound, not merely an
eventual one. One may read n as kappa^(E*D) mathematically, but the proof needs no
flattening or new cast/power identity. `Nat.le_self_pow` also exists in the same
core file at line 1258; `Nat.le_pow` is the direct positive-exponent form.

## Shared readers and sourceprop41 quantifier order

- `Params.realizable_iff` (`Security.lean:49`) exposes the conjunction.
- `Params.LPNRealizable_iff` (`Reductions/LPN.lean:420`) and
  `Params.PRGRealizable_iff` (`Reductions/PRG.lean:294`) supply a realiser for each
  A and each advice family, over the shared `RealizesOn` and exact coin layout
  `A.coins.subst .var`.
- `LPNFamily.Raw.assumption_iff` (`LPN.lean:181`) gives negligible own-family
  advantage for every NUPPT; `BoolPRG.secure_iff` (`BoolPRG.lean:194`) supplies the
  Boolean assumption's corresponding fact.
- `SPRG.Raw.adv_eq` (`Defs.lean:255`) and existing
  `Games.advantage_nonneg` (`Games/Advantage.lean:86`) give raw advantage
  nonnegativity without unfolding its foreign definition.

The candidate first extracts `omegaL,omegaG,hprop` from prop41. Only afterwards
it selects BL and BG from the realization hypothesis for those exact families.
It then passes both realiser proofs to the universally quantified `hprop`. This
preserves the required exists-advice / forall-realisers order. It neither weakens
prop41 to selected realisers nor assumes advice can depend on the realiser.

## Recommended majorant and exact closure path

For the selected BL and BG, set

`mu(kappa) = 2*kappa*LPNadv BL(ell kappa) + Gadv BG(n kappa) + 2*(2^-kappa)`.

1. Read assumption negligibility at BL and BG, then use `comp_of_le` with the
   pointwise parameter lower bounds.
2. Apply `.mul_pow 1` then `.const_mul 2` to the LPN term. Only public equations
   `pow_one` and `mul_assoc` are needed to match `2*kappa*LPNadv`.
3. Use two `.add` applications, and `negligible_two_pow_neg.const_mul 2`, to obtain
   `Negligible mu`.
4. At Claim4.2's threshold, replace `2*errProb` by `2*(2^-kappa)` using
   `mul_le_mul_of_nonneg_left ... zero_le_two`, and add that inequality to prop41.
5. Read raw advantage's nonnegativity. Since `rawAdv<=mu`, this also gives `0<=mu`.
   Rewrite both absolute values through `abs_of_nonneg` and apply shared `.mono`.

This path needs neither `errProb_nonneg` nor nonnegativity of each LPN/PRG term:
the final majorant's nonnegativity follows from its domination of a nonnegative
raw advantage. It also avoids a separate new theorem asserting the exact error
function is negligible. If such a theorem is later useful, shared `.mono` plus
Claim4.2 and the existing `ProbComp.prob_nonneg` (`Games/Probability.lean:230`) through
`errProb_eq` (`Claim42.lean:98`) suffice; do not rederive the generic closure.

## Candidate and remaining uncertainty

`negligible/01-jls_secure.proof` is intended to replace the current theorem's body
with the existing context/binders. It has one outer tactic block, no nested
block, no new helper declaration, no machine/sampler construction, and no new
import. Only owner readers and public theorem equations are passed to rewriting.

The candidate has not been elaborated. Remaining mechanical checks are field-name
inference for the realization readers, lambda association in the closure result,
and rewriting the absolute majorant after prop41's transitive inequality. All
public theorem signatures were read directly. The prerequisite bodies remain the
lead's proof work; successful source search is not evidence that prop41/Claim4.2
or the theorem itself has been proved. No exact?/apply? probe is claimed.

Text searches before this plan covered the Foundations/Negligible API, existing
cryptographic uses of closure/domination, and the core natural-power bounds.
The canonical own-family assumption and existing security readers were reused;
no generic negligible fact is reproved inline. Initial queries included absent
`Cryptography/Lattice`, `Encryption/LWE`, and `Data/Nat/Pow` paths; actual existing
LWE and core paths were then located. This note makes no exhaustive-search claim.

Candidate: 32 lines, max width 77, 1 tactic-block opener.
SHA256 `a045b13e6084204d8e9859d456e30fff94a46faa35448434d5d703bfd5ecd2d6`.
