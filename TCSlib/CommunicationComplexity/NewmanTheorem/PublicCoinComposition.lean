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

## Main results

- `PublicCoin.FiniteMessage.Protocol.map_rrun`: mapping a function over the output of a protocol commutes with running it
- `PublicCoin.FiniteMessage.Protocol.map_complexity`: mapping preserves complexity
- `PublicCoin.FiniteMessage.Protocol.bind_rrun`: bind commutes with running
- `PublicCoin.FiniteMessage.Protocol.comapRandomness_rrun`: reindexing randomness commutes with running
- `PublicCoin.FiniteMessage.Protocol.prod_rrun`: product protocol runs component-wise
- `PublicCoin.FiniteMessage.Protocol.prod_complexity`: product complexity is the sum of complexities
- `PublicCoin.FiniteMessage.Protocol.pi_rrun`: pi protocol runs each component independently
- `PublicCoin.FiniteMessage.Protocol.pi_complexity`: pi complexity is the sum of component complexities
- `PublicCoin.FiniteMessage.Protocol.rbind_rrun`: rbind with fresh randomness runs sequentially
- `PublicCoin.FiniteMessage.Protocol.rbind_complexity_const`: rbind complexity when continuation has constant complexity
- `PublicCoin.FiniteMessage.Protocol.prodDet_rrun`: product with deterministic protocol runs component-wise
- `PublicCoin.FiniteMessage.Protocol.prodDet_complexity`: product with deterministic protocol has summed complexity

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace PublicCoin.FiniteMessage.Protocol

variable {Ω Ω' Ω₁ Ω₂ X Y α α₁ α₂ β : Type*}

/-- Map a function over the output of a public-coin protocol. -/
abbrev map (g : α → β) (p : Protocol Ω X Y α) : Protocol Ω X Y β :=
  Deterministic.FiniteMessage.Protocol.map g p

@[simp]
theorem map_rrun (g : α → β) (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (p.map g).rrun x y ω = g (p.rrun x y ω) := by
  simp [map, rrun, Deterministic.FiniteMessage.Protocol.map_run]

@[simp]
theorem map_complexity (g : α → β) (p : Protocol Ω X Y α) :
    (p.map g).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.map_complexity g p

/-- Bind: replace each output `a` in `p` with `q a`. -/
abbrev bind (p : Protocol Ω X Y α) (q : α → Protocol Ω X Y β) :
    Protocol Ω X Y β :=
  Deterministic.FiniteMessage.Protocol.bind p q

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

@[simp]
theorem comapRandomness_rrun (h : Ω' → Ω)
    (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω') :
    (comapRandomness h p).rrun x y ω = p.rrun x y (h ω) := by
  simp [comapRandomness, rrun, Deterministic.FiniteMessage.Protocol.comap_run]

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

@[simp]
theorem prod_rrun (p1 : Protocol Ω₁ X Y α₁)
    (p2 : Protocol Ω₂ X Y α₂)
    (x : X) (y : Y) (ω : Ω₁ × Ω₂) :
    (prod p1 p2).rrun x y ω =
      (p1.rrun x y ω.1, p2.rrun x y ω.2) := by
  simp [prod, rrun, Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.prod_run]

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

@[simp]
theorem pi_rrun (p : (i : Fin k) → Protocol (Ωf i) X Y (αf i))
    (x : X) (y : Y) (ω : (i : Fin k) → Ωf i) :
    (pi p).rrun x y ω = fun i => (p i).rrun x y (ω i) := by
  simp [pi, rrun, Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.pi_run]

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

@[simp]
theorem rbind_rrun (p : Protocol Ω X Y α)
    (q : α → Protocol Ω' X Y β)
    (x : X) (y : Y) (ω : Ω × Ω') :
    (rbind p q).rrun x y ω =
      (q (p.rrun x y ω.1)).rrun x y ω.2 := by
  simp [rbind, rrun,
    Deterministic.FiniteMessage.Protocol.bind_run,
    Deterministic.FiniteMessage.Protocol.comap_run]

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

theorem prodDet_complexity (p1 : Protocol Ω X Y α₁)
    (p2 : Deterministic.FiniteMessage.Protocol X Y α₂) :
    (prodDet p1 p2).complexity = p1.complexity + p2.complexity := by
  simp only [prodDet]
  apply Deterministic.FiniteMessage.Protocol.bind_complexity_const
  intro a1; simp

end PublicCoin.FiniteMessage.Protocol

end CommunicationComplexity
