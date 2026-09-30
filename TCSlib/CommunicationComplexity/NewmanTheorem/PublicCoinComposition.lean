/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinFiniteMessage
import TCSlib.CommunicationComplexity.DeterministicCC.DetComposition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition Operations for Public-Coin Protocols

Combinators for building public-coin finite-message protocols out of smaller ones: mapping
the output, sequential composition (`bind`, with the same or with fresh randomness),
reindexing the randomness space, and parallel products (binary, `k`-fold, and with a
deterministic protocol). `map` and `bind` are the deterministic combinators of
`DeterministicCC.DetComposition` applied verbatim (the shared randomness is simply part of
the inputs); `comapRandomness`, `prod`, `pi`, `rbind` and `prodDet` additionally use
`Deterministic.FiniteMessage.Protocol.comap` to route the shared randomness to the
components. Each combinator comes with a `rrun` lemma describing its output, and all except
`bind` with a `complexity` lemma computing its cost (for `rbind` only when the continuation
has constant complexity). The protocol model is that of [RY20, Ch. 3]; the combinators
themselves are original to this formalization and have no textbook counterpart, so they carry
no citations.

## Main definitions

- `PublicCoin.FiniteMessage.Protocol.map`: post-compose the output with a function.
- `PublicCoin.FiniteMessage.Protocol.bind`: run a protocol, then a continuation chosen by its
  output, with the same shared randomness.
- `PublicCoin.FiniteMessage.Protocol.comapRandomness`: reindex the randomness space along a
  map `Ω' → Ω`.
- `PublicCoin.FiniteMessage.Protocol.prod`, `PublicCoin.FiniteMessage.Protocol.pi`: run two,
  resp. `k`, protocols on the same inputs with independent randomness and pair (resp. tuple)
  the outputs.
- `PublicCoin.FiniteMessage.Protocol.rbind`: sequential composition where the continuation
  uses fresh randomness.
- `PublicCoin.FiniteMessage.Protocol.prodDet`: run a public-coin protocol alongside a
  deterministic one and pair the outputs.

## Main results

- `PublicCoin.FiniteMessage.Protocol.map_rrun`, `PublicCoin.FiniteMessage.Protocol.map_complexity`:
  mapping a function over the output commutes with running and preserves complexity.
- `PublicCoin.FiniteMessage.Protocol.bind_rrun`: bind runs the protocol and then the
  continuation selected by its output.
- `PublicCoin.FiniteMessage.Protocol.comapRandomness_rrun`,
  `PublicCoin.FiniteMessage.Protocol.comapRandomness_complexity`: reindexing randomness
  commutes with running and preserves complexity.
- `PublicCoin.FiniteMessage.Protocol.prod_rrun`,
  `PublicCoin.FiniteMessage.Protocol.prod_complexity`: the product runs component-wise and
  its complexity is the sum of the complexities.
- `PublicCoin.FiniteMessage.Protocol.pi_rrun`, `PublicCoin.FiniteMessage.Protocol.pi_complexity`:
  the `k`-fold product runs each component independently and its complexity is the sum of
  the component complexities.
- `PublicCoin.FiniteMessage.Protocol.rbind_rrun`,
  `PublicCoin.FiniteMessage.Protocol.rbind_complexity_const`: bind with fresh randomness runs
  sequentially, and its complexity is additive when the continuation has constant complexity.
- `PublicCoin.FiniteMessage.Protocol.prodDet_rrun`,
  `PublicCoin.FiniteMessage.Protocol.prodDet_complexity`: the product with a deterministic
  protocol runs component-wise and has summed complexity.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace PublicCoin.FiniteMessage.Protocol

variable {Ω Ω' Ω₁ Ω₂ X Y α α₁ α₂ β : Type*}

/-- Map a function over the output of a public-coin protocol. -/
abbrev map (g : α → β) (p : Protocol Ω X Y α) : Protocol Ω X Y β :=
  Deterministic.FiniteMessage.Protocol.map g p

/-- Running `p.map g` on inputs `x`, `y` with randomness `ω` gives `g` applied to the
output of `p` on the same inputs and randomness. -/
@[simp]
theorem map_rrun (g : α → β) (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (p.map g).rrun x y ω = g (p.rrun x y ω) := by
  simp [map, rrun, Deterministic.FiniteMessage.Protocol.map_run]

/-- Mapping a function over the output of a public-coin protocol does not change its
complexity: no message is added or removed. -/
@[simp]
theorem map_complexity (g : α → β) (p : Protocol Ω X Y α) :
    (p.map g).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.map_complexity g p

/-- Bind: replace each output `a` in `p` with `q a`. -/
abbrev bind (p : Protocol Ω X Y α) (q : α → Protocol Ω X Y β) :
    Protocol Ω X Y β :=
  Deterministic.FiniteMessage.Protocol.bind p q

/-- Running `p.bind q` on inputs `x`, `y` with randomness `ω` first runs `p`, obtaining an
output `a`, and then runs the continuation `q a` on the same inputs and the same randomness;
the result is the output of `q a`. -/
@[simp]
theorem bind_rrun (p : Protocol Ω X Y α)
    (q : α → Protocol Ω X Y β)
    (x : X) (y : Y) (ω : Ω) :
    (p.bind q).rrun x y ω =
      (q (p.rrun x y ω)).rrun x y ω := by
  simp [bind, rrun, Deterministic.FiniteMessage.Protocol.bind_run]

/-- Reindex the randomness space of a public-coin protocol via `h : Ω' → Ω`. -/
abbrev comapRandomness (h : Ω' → Ω)
    (p : Protocol Ω X Y α) : Protocol Ω' X Y α :=
  p.comap (Prod.map h id) (Prod.map h id)

/-- Running the reindexed protocol `comapRandomness h p` with randomness `ω' : Ω'` is the
same as running `p` with randomness `h ω'`. -/
@[simp]
theorem comapRandomness_rrun (h : Ω' → Ω)
    (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω') :
    (comapRandomness h p).rrun x y ω = p.rrun x y (h ω) := by
  simp [comapRandomness, rrun, Deterministic.FiniteMessage.Protocol.comap_run]

/-- Reindexing the randomness space of a public-coin protocol does not change its
complexity. -/
@[simp]
theorem comapRandomness_complexity (h : Ω' → Ω)
    (p : Protocol Ω X Y α) :
    (comapRandomness h p).complexity = p.complexity := by
  simp [comapRandomness]

/-- Product of two public-coin protocols with different randomness
spaces. The result uses `Ω₁ × Ω₂` as shared randomness. -/
abbrev prod (p1 : Protocol Ω₁ X Y α₁) (p2 : Protocol Ω₂ X Y α₂) :
    Protocol (Ω₁ × Ω₂) X Y (α₁ × α₂) :=
  (Deterministic.FiniteMessage.Protocol.prod p1 p2).comap
    (fun ((ω₁, ω₂), x) => ((ω₁, x), (ω₂, x)))
    (fun ((ω₁, ω₂), y) => ((ω₁, y), (ω₂, y)))

/-- Running the product `prod p1 p2` on inputs `x`, `y` with randomness `(ω₁, ω₂)` gives the
pair of the outputs of `p1` with randomness `ω₁` and of `p2` with randomness `ω₂`, both on
the same inputs. -/
@[simp]
theorem prod_rrun (p1 : Protocol Ω₁ X Y α₁)
    (p2 : Protocol Ω₂ X Y α₂)
    (x : X) (y : Y) (ω : Ω₁ × Ω₂) :
    (prod p1 p2).rrun x y ω =
      (p1.rrun x y ω.1, p2.rrun x y ω.2) := by
  simp [prod, rrun, Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.prod_run]

/-- The complexity of the product of two public-coin protocols is the sum of their
complexities: the product runs one after the other. -/
theorem prod_complexity (p1 : Protocol Ω₁ X Y α₁)
    (p2 : Protocol Ω₂ X Y α₂) :
    (prod p1 p2).complexity = p1.complexity + p2.complexity := by
  simp [prod, Deterministic.FiniteMessage.Protocol.prod_complexity]

variable {k : ℕ} {Ωf : Fin k → Type*} {αf : Fin k → Type*}

/-- Pi (k-fold product) of public-coin protocols with heterogeneous
randomness and output types. -/
abbrev pi (p : (i : Fin k) → Protocol (Ωf i) X Y (αf i)) :
    Protocol ((i : Fin k) → Ωf i) X Y ((i : Fin k) → αf i) :=
  (Deterministic.FiniteMessage.Protocol.pi
    (Xf := fun i => Ωf i × X) (Yf := fun i => Ωf i × Y) p).comap
    (fun (ω, x) i => (ω i, x))
    (fun (ω, y) i => (ω i, y))

/-- Running the `k`-fold product `pi p` on inputs `x`, `y` with randomness `ω` (a family
`ω i : Ωf i`) gives the family of outputs of the components, the `i`-th component being run
with randomness `ω i`. -/
@[simp]
theorem pi_rrun (p : (i : Fin k) → Protocol (Ωf i) X Y (αf i))
    (x : X) (y : Y) (ω : (i : Fin k) → Ωf i) :
    (pi p).rrun x y ω = fun i => (p i).rrun x y (ω i) := by
  simp [pi, rrun, Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.pi_run]

/-- The complexity of the `k`-fold product of public-coin protocols is the sum of the
complexities of the components. -/
theorem pi_complexity (p : (i : Fin k) → Protocol (Ωf i) X Y (αf i)) :
    (pi p).complexity = ∑ i, (p i).complexity := by
  simp [pi, Deterministic.FiniteMessage.Protocol.pi_complexity]

/-- Bind with fresh randomness: runs `p` with randomness `Ω`, then
`q` with independent randomness `Ω'`. The combined randomness is `Ω × Ω'`. -/
abbrev rbind (p : Protocol Ω X Y α)
    (q : α → Protocol Ω' X Y β) :
    Protocol (Ω × Ω') X Y β :=
  (p.comap (fun ((ω, _), x) => (ω, x)) (fun ((ω, _), y) => (ω, y))).bind
    (fun a => (q a).comap
      (fun ((_, ω'), x) => (ω', x)) (fun ((_, ω'), y) => (ω', y)))

/-- Running `rbind p q` on inputs `x`, `y` with randomness `(ω, ω')` first runs `p` with
randomness `ω`, obtaining an output `a`, and then runs the continuation `q a` on the same
inputs with the fresh randomness `ω'`. -/
@[simp]
theorem rbind_rrun (p : Protocol Ω X Y α)
    (q : α → Protocol Ω' X Y β)
    (x : X) (y : Y) (ω : Ω × Ω') :
    (rbind p q).rrun x y ω =
      (q (p.rrun x y ω.1)).rrun x y ω.2 := by
  simp [rbind, rrun,
    Deterministic.FiniteMessage.Protocol.bind_run,
    Deterministic.FiniteMessage.Protocol.comap_run]

/-- If every continuation `q a` has the same complexity `c`, then the complexity of
`rbind p q` is the complexity of `p` plus `c`. -/
theorem rbind_complexity_const (p : Protocol Ω X Y α)
    (q : α → Protocol Ω' X Y β)
    (c : ℕ) (hc : ∀ a, (q a).complexity = c) :
    (rbind p q).complexity = p.complexity + c := by
  simp only [rbind]
  rw [Deterministic.FiniteMessage.Protocol.bind_complexity_const _ _ c]
  · simp
  · intro a; simp [hc]

/-- Product of a public-coin protocol with a deterministic protocol.
Runs both on the same inputs and pairs their outputs. -/
abbrev prodDet (p1 : Protocol Ω X Y α₁)
    (p2 : Deterministic.FiniteMessage.Protocol X Y α₂) :
    Protocol Ω X Y (α₁ × α₂) :=
  p1.bind (fun a1 =>
    (p2.comap Prod.snd Prod.snd).map (fun a2 => (a1, a2)))

/-- Running `prodDet p1 p2` on inputs `x`, `y` with randomness `ω` gives the pair of the
output of the public-coin protocol `p1` (with randomness `ω`) and the output of the
deterministic protocol `p2`, both on the same inputs. -/
@[simp]
theorem prodDet_rrun (p1 : Protocol Ω X Y α₁)
    (p2 : Deterministic.FiniteMessage.Protocol X Y α₂)
    (x : X) (y : Y) (ω : Ω) :
    (prodDet p1 p2).rrun x y ω =
      (p1.rrun x y ω, p2.run x y) := by
  simp [prodDet, rrun,
    Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.map_run,
    Deterministic.FiniteMessage.Protocol.bind_run]

/-- The complexity of the product of a public-coin protocol with a deterministic protocol
is the sum of their complexities. -/
theorem prodDet_complexity (p1 : Protocol Ω X Y α₁)
    (p2 : Deterministic.FiniteMessage.Protocol X Y α₂) :
    (prodDet p1 p2).complexity = p1.complexity + p2.complexity := by
  simp only [prodDet]
  apply Deterministic.FiniteMessage.Protocol.bind_complexity_const
  intro a1; simp

end PublicCoin.FiniteMessage.Protocol

end CommunicationComplexity
