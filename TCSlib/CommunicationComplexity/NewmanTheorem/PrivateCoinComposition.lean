/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinFiniteMessage
import TCSlib.CommunicationComplexity.DeterministicCC.DetComposition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition Operations for Private-Coin Protocols

## Main results

- `PrivateCoin.FiniteMessage.Protocol.map`: Map a function over the output of a private-coin protocol
- `PrivateCoin.FiniteMessage.Protocol.bind`: Monadic bind for private-coin protocols
- `PrivateCoin.FiniteMessage.Protocol.comapRandomness`: Reindex both randomness spaces
- `PrivateCoin.FiniteMessage.Protocol.prod`: Product of two private-coin protocols
- `PrivateCoin.FiniteMessage.Protocol.pi`: k-fold product of private-coin protocols
- `PrivateCoin.FiniteMessage.Protocol.rbind`: Bind with fresh independent randomness
- `PrivateCoin.FiniteMessage.Protocol.prodDet`: Product of a private-coin protocol with a deterministic protocol

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace PrivateCoin.FiniteMessage.Protocol

variable {Ω_X Ω_Y Ω_X' Ω_Y' Ω_X1 Ω_X2 Ω_Y1 Ω_Y2 X Y α α₁ α₂ β : Type*}

/-- Map a function over the output of a private-coin protocol. -/
abbrev map (g : α → β) (p : Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y β :=
  Deterministic.FiniteMessage.Protocol.map g p

@[simp]
theorem map_rrun (g : α → β) (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (p.map g).rrun x y ω_x ω_y = g (p.rrun x y ω_x ω_y) := by
  simp [map, rrun, Deterministic.FiniteMessage.Protocol.map_run]

@[simp]
theorem map_complexity (g : α → β) (p : Protocol Ω_X Ω_Y X Y α) :
    (p.map g).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.map_complexity g p

/-- Bind: replace each output `a` in `p` with `q a`. -/
abbrev bind (p : Protocol Ω_X Ω_Y X Y α)
    (q : α → Protocol Ω_X Ω_Y X Y β) :
    Protocol Ω_X Ω_Y X Y β :=
  Deterministic.FiniteMessage.Protocol.bind p q

@[simp]
theorem bind_rrun (p : Protocol Ω_X Ω_Y X Y α)
    (q : α → Protocol Ω_X Ω_Y X Y β)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (p.bind q).rrun x y ω_x ω_y =
      (q (p.rrun x y ω_x ω_y)).rrun x y ω_x ω_y := by
  simp [bind, rrun, Deterministic.FiniteMessage.Protocol.bind_run]

/-- Reindex both randomness spaces of a private-coin protocol. -/
abbrev comapRandomness (hX : Ω_X' → Ω_X) (hY : Ω_Y' → Ω_Y)
    (p : Protocol Ω_X Ω_Y X Y α) : Protocol Ω_X' Ω_Y' X Y α :=
  p.comap (Prod.map hX id) (Prod.map hY id)

@[simp]
theorem comapRandomness_rrun (hX : Ω_X' → Ω_X) (hY : Ω_Y' → Ω_Y)
    (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X') (ω_y : Ω_Y') :
    (comapRandomness hX hY p).rrun x y ω_x ω_y =
      p.rrun x y (hX ω_x) (hY ω_y) := by
  simp [comapRandomness, rrun, Deterministic.FiniteMessage.Protocol.comap_run]

@[simp]
theorem comapRandomness_complexity (hX : Ω_X' → Ω_X) (hY : Ω_Y' → Ω_Y)
    (p : Protocol Ω_X Ω_Y X Y α) :
    (comapRandomness hX hY p).complexity = p.complexity := by
  simp [comapRandomness]

/-- Product of two private-coin protocols with different randomness
spaces. The result uses `Ω_X1 × Ω_X2` and `Ω_Y1 × Ω_Y2`. -/
abbrev prod (p1 : Protocol Ω_X1 Ω_Y1 X Y α₁)
    (p2 : Protocol Ω_X2 Ω_Y2 X Y α₂) :
    Protocol (Ω_X1 × Ω_X2) (Ω_Y1 × Ω_Y2) X Y (α₁ × α₂) :=
  (Deterministic.FiniteMessage.Protocol.prod p1 p2).comap
    (fun ((ωx1, ωx2), x) => ((ωx1, x), (ωx2, x)))
    (fun ((ωy1, ωy2), y) => ((ωy1, y), (ωy2, y)))

@[simp]
theorem prod_rrun (p1 : Protocol Ω_X1 Ω_Y1 X Y α₁)
    (p2 : Protocol Ω_X2 Ω_Y2 X Y α₂)
    (x : X) (y : Y) (ω_x : Ω_X1 × Ω_X2) (ω_y : Ω_Y1 × Ω_Y2) :
    (prod p1 p2).rrun x y ω_x ω_y =
      (p1.rrun x y ω_x.1 ω_y.1, p2.rrun x y ω_x.2 ω_y.2) := by
  simp [prod, rrun, Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.prod_run]

theorem prod_complexity (p1 : Protocol Ω_X1 Ω_Y1 X Y α₁)
    (p2 : Protocol Ω_X2 Ω_Y2 X Y α₂) :
    (prod p1 p2).complexity = p1.complexity + p2.complexity := by
  simp [prod, Deterministic.FiniteMessage.Protocol.prod_complexity]

variable {k : ℕ}
  {Ω_Xf : Fin k → Type*} {Ω_Yf : Fin k → Type*}
  {αf : Fin k → Type*}

/-- Pi (k-fold product) of private-coin protocols with heterogeneous
randomness and output types. -/
abbrev pi (p : (i : Fin k) → Protocol (Ω_Xf i) (Ω_Yf i) X Y (αf i)) :
    Protocol ((i : Fin k) → Ω_Xf i) ((i : Fin k) → Ω_Yf i) X Y
      ((i : Fin k) → αf i) :=
  (Deterministic.FiniteMessage.Protocol.pi
    (Xf := fun i => Ω_Xf i × X) (Yf := fun i => Ω_Yf i × Y) p).comap
    (fun (ω, x) i => (ω i, x))
    (fun (ω, y) i => (ω i, y))

@[simp]
theorem pi_rrun
    (p : (i : Fin k) → Protocol (Ω_Xf i) (Ω_Yf i) X Y (αf i))
    (x : X) (y : Y)
    (ω_x : (i : Fin k) → Ω_Xf i) (ω_y : (i : Fin k) → Ω_Yf i) :
    (pi p).rrun x y ω_x ω_y =
      fun i => (p i).rrun x y (ω_x i) (ω_y i) := by
  simp [pi, rrun, Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.pi_run]

theorem pi_complexity
    (p : (i : Fin k) → Protocol (Ω_Xf i) (Ω_Yf i) X Y (αf i)) :
    (pi p).complexity = ∑ i, (p i).complexity := by
  simp [pi, Deterministic.FiniteMessage.Protocol.pi_complexity]

/-- Bind with fresh randomness: runs `p` with randomness `Ω_X, Ω_Y`,
then `q` with independent randomness `Ω_X', Ω_Y'`. -/
abbrev rbind (p : Protocol Ω_X Ω_Y X Y α)
    (q : α → Protocol Ω_X' Ω_Y' X Y β) :
    Protocol (Ω_X × Ω_X') (Ω_Y × Ω_Y') X Y β :=
  (p.comap (fun ((ωx, _), x) => (ωx, x)) (fun ((ωy, _), y) => (ωy, y))).bind
    (fun a => (q a).comap
      (fun ((_, ωx'), x) => (ωx', x)) (fun ((_, ωy'), y) => (ωy', y)))

@[simp]
theorem rbind_rrun (p : Protocol Ω_X Ω_Y X Y α)
    (q : α → Protocol Ω_X' Ω_Y' X Y β)
    (x : X) (y : Y) (ω_x : Ω_X × Ω_X') (ω_y : Ω_Y × Ω_Y') :
    (rbind p q).rrun x y ω_x ω_y =
      (q (p.rrun x y ω_x.1 ω_y.1)).rrun x y ω_x.2 ω_y.2 := by
  simp [rbind, rrun,
    Deterministic.FiniteMessage.Protocol.bind_run,
    Deterministic.FiniteMessage.Protocol.comap_run]

theorem rbind_complexity_const (p : Protocol Ω_X Ω_Y X Y α)
    (q : α → Protocol Ω_X' Ω_Y' X Y β)
    (c : ℕ) (hc : ∀ a, (q a).complexity = c) :
    (rbind p q).complexity = p.complexity + c := by
  simp only [rbind]
  rw [Deterministic.FiniteMessage.Protocol.bind_complexity_const _ _ c]
  · simp
  · intro a; simp [hc]

/-- Product of a private-coin protocol with a deterministic protocol.
Runs both on the same inputs and pairs their outputs. -/
abbrev prodDet (p1 : Protocol Ω_X Ω_Y X Y α₁)
    (p2 : Deterministic.FiniteMessage.Protocol X Y α₂) :
    Protocol Ω_X Ω_Y X Y (α₁ × α₂) :=
  p1.bind (fun a1 =>
    (p2.comap Prod.snd Prod.snd).map (fun a2 => (a1, a2)))

@[simp]
theorem prodDet_rrun (p1 : Protocol Ω_X Ω_Y X Y α₁)
    (p2 : Deterministic.FiniteMessage.Protocol X Y α₂)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (prodDet p1 p2).rrun x y ω_x ω_y =
      (p1.rrun x y ω_x ω_y, p2.run x y) := by
  simp [prodDet, rrun,
    Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.map_run,
    Deterministic.FiniteMessage.Protocol.bind_run]

theorem prodDet_complexity (p1 : Protocol Ω_X Ω_Y X Y α₁)
    (p2 : Deterministic.FiniteMessage.Protocol X Y α₂) :
    (prodDet p1 p2).complexity = p1.complexity + p2.complexity := by
  simp only [prodDet]
  apply Deterministic.FiniteMessage.Protocol.bind_complexity_const
  intro a1; simp

end PrivateCoin.FiniteMessage.Protocol

end CommunicationComplexity
