/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalRecursion

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical comparison of sequential phase prefixes

A padded repeated-prover specification supplies the original phase's message count. A
pointwise prover-message bound makes real phase views fixed points of normalization. The
one-phase statistical comparison therefore applies to each normalized prefix extension,
and the public sampler-recursion bound accumulates the error. [PS10, Theorem 175.1].

## Main definitions

There are no new definitions.

## Main results

* `PaddedProverSpec.statClose_step`: raw one-phase closeness bounds every prefix update.
* `PaddedProverSpec.statClose_prefix`: `q` phase updates accumulate at most `q * δ` error.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK.PaddedProverSpec

open Complexity

/-- For `d : PaddedProverSpec π ρ x q p`, verifier `V`, simulator `S`, inputs `y,z`, tape
`rV`, cap `B`, and error `δ`, a uniform `B` bound on `π.P.next` and raw `δ`-close phase views
at every auxiliary input imply `δ`-close `realStep` and `simStep` at every index `i` and
prefix `pre`. No shape assumption on `pre` and no efficiency assumption on `S` is required.
[PS10, Theorem 175.1; Gol01, §4.3.4].
`StatClose (realStep π V x y z rV p i pre) (simStep S x z rV (π.rounds.eval x.length) B p i pre) δ`.

**Proof sketch.** Instantiate the zero-verifier normalization comparison with the original
protocol whose verifier is the phase wrapper. The published wrapper reader supplies its
zero coin length, and the specification supplies its exact received-message count. The
published `withV` field readers preserve the original prover, move count and first mover.
Transport the prover seed by the equality of its coin lengths; the public `ofFn` reader
shows that this transport preserves its raw tape. The two update readers then identify
exactly the real and normalized steps, with the same empty padding and error. -/
theorem statClose_step {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (d : PaddedProverSpec π ρ x q p) (V : Strategy) (S : NUPPT)
    (y z rV : List Bool) (B : ℕ) (δ : ℝ)
    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B)
    (hclose : ∀ aux : List Bool,
      StatClose (fun r : (π.withV (phaseVerifier V)).ExecCoins
        (π.withV (phaseVerifier V)).P x =>
          ((π.withV (phaseVerifier V)).viewV x y aux r).encode) (S.simulate x aux) δ)
    (i : ℕ) (pre : List (List Bool)) :
    StatClose (realStep π V x y z rV p i pre)
      (simStep S x z rV (π.rounds.eval x.length) B p i pre) δ := by
  -- Read the wrapper's zero-coin contract and the original phase-count equation.
  let aux := phaseAux z rV i pre
  have hcoins : (π.withV (phaseVerifier V)).V.coinLen x.length = 0 := by
    rw [Protocol.withV_V, phaseVerifier_coinLen]
  have hP : ∀ r hist, ((π.withV (phaseVerifier V)).P.next x y r hist).length ≤ B := by
    rw [Protocol.withV_P]
    exact hbound
  have hcount : ∀ r : List Bool,
      (exec (π.withV (phaseVerifier V)).P (π.withV (phaseVerifier V)).V
        (π.withV (phaseVerifier V)).verifierFirst x y aux r []
        ((π.withV (phaseVerifier V)).rounds.eval x.length)).2.length = p := by
    intro r
    rw [Protocol.withV_P, Protocol.withV_V, Protocol.withV_verifierFirst,
      Protocol.withV_rounds]
    exact d.original_count (phaseVerifier V) y aux r []
  let F : (π.withV (phaseVerifier V)).P.Coins x.length → List (List Bool) :=
    fun r => pre ++
      ((exec (π.withV (phaseVerifier V)).P (π.withV (phaseVerifier V)).V
        (π.withV (phaseVerifier V)).verifierFirst x y aux (List.ofFn r) []
        ((π.withV (phaseVerifier V)).rounds.eval x.length)).2 ++
          List.replicate ((π.withV (phaseVerifier V)).rounds.eval x.length - p) [])
  let G : S.Coins x.length → List (List Bool) :=
    fun r => pre ++ (normalizePhaseMsgs x aux p B (S.simulate x aux r) ++
      List.replicate ((π.withV (phaseVerifier V)).rounds.eval x.length - p) [])
  have hn : StatClose F G δ := by
    with_reducible exact (statClose_normalized_step (π.withV (phaseVerifier V)) S x y aux
      pre p B δ hcoins hP hcount (hclose aux))
  -- Reindex the unchanged prover tape through its explicit coin-length equality.
  have hlen : π.P.coinLen x.length = (π.withV (phaseVerifier V)).P.coinLen x.length := by
    rw [Protocol.withV_P]
  let e : π.P.Coins x.length ≃ (π.withV (phaseVerifier V)).P.Coins x.length :=
    Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  have hword (r : π.P.Coins x.length) : List.ofFn (e r) = List.ofFn r :=
    (List.ofFn_congr hlen r).symm
  have hindex : StatClose (fun r : π.P.Coins x.length => F (e r)) G δ :=
    StatClose.comp_equiv_left (X := F) (Y := G) hn e
  -- Identify both concrete samplers with the public prefix-update readers.
  have hleft : (fun r : π.P.Coins x.length => F (e r)) =
      realStep π V x y z rV p i pre := by
    funext r
    dsimp only [F]
    rw [hword, Protocol.withV_P, Protocol.withV_V, Protocol.withV_verifierFirst,
      Protocol.withV_rounds, realStep_eq]
  have hright : G = simStep S x z rV (π.rounds.eval x.length) B p i pre := by
    funext r
    dsimp only [G]
    rw [Protocol.withV_rounds, simStep_eq]
  rw [hleft, hright] at hindex
  exact hindex

/-- For `d : PaddedProverSpec π ρ x q p`, verifier `V`, simulator `S`, inputs `y,z`, tape
`rV`, cap `B`, and error `δ`, suppose `∀ r hist, |π.P.next x y r hist| ≤ B` and every raw
phase-view sampler is `δ`-close to `S.simulate x aux`. Then
`StatClose (realPrefix π V x y z rV p q)
  (simPrefix S x z rV (π.rounds.eval |x|) B p q) ((q : ℝ) * δ)`.
No uniformity or efficiency premise on `S` is needed. [PS10, Theorem 175.1; Gol01, §4.3.4].

**Proof sketch.** The raw comparison at any auxiliary input gives `0 ≤ δ`. The preceding
step comparison applies at every possible prefix, including malformed simulated prefixes.
Instantiate the generic sampler-recursion theorem with the real and simulated prefix folds,
their published empty-table and snoc equations, and that uniform step comparison. Its
linear accumulation gives exactly the stated `q * δ` error, also when `q = 0`. -/
theorem statClose_prefix {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (d : PaddedProverSpec π ρ x q p) (V : Strategy) (S : NUPPT)
    (y z rV : List Bool) (B : ℕ) (δ : ℝ)
    (hbound : ∀ r hist, (π.P.next x y r hist).length ≤ B)
    (hclose : ∀ aux : List Bool,
      StatClose (fun r : (π.withV (phaseVerifier V)).ExecCoins
        (π.withV (phaseVerifier V)).P x =>
          ((π.withV (phaseVerifier V)).viewV x y aux r).encode) (S.simulate x aux) δ) :
    StatClose (realPrefix π V x y z rV p q)
      (simPrefix S x z rV (π.rounds.eval x.length) B p q) ((q : ℝ) * δ) := by
  have hδ : 0 ≤ δ := StatClose.nonneg
    (X := fun r : (π.withV (phaseVerifier V)).ExecCoins
      (π.withV (phaseVerifier V)).P x =>
        ((π.withV (phaseVerifier V)).viewV x y [] r).encode)
    (Y := S.simulate x []) (hclose [])
  with_reducible exact (statClose_recursion
    (α := π.P.Coins x.length) (β := S.Coins x.length) (State := List (List Bool))
    (realPrefix π V x y z rV p) (simPrefix S x z rV (π.rounds.eval x.length) B p) []
    (realStep π V x y z rV p) (simStep S x z rV (π.rounds.eval x.length) B p)
    (realPrefix_zero π V x y z rV p)
    (simPrefix_zero S x z rV (π.rounds.eval x.length) B p)
    (realPrefix_snoc π V x y z rV p)
    (simPrefix_snoc S x z rV (π.rounds.eval x.length) B p) q δ hδ
    (fun i _ pre => d.statClose_step V S y z rV B δ hbound hclose i pre))

end TCSlib.Cryptography.SequentialZK.PaddedProverSpec
