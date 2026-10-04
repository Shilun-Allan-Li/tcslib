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

Combinators for building private-coin finite-message protocols out of smaller ones: mapping
the output, sequential composition (`bind`, with the same or with fresh randomness),
reindexing the two randomness spaces, and parallel products (binary, `k`-fold, and with a
deterministic protocol). Each combinator is the corresponding deterministic combinator of
`DeterministicCC.DetComposition`; where the components use separate randomness (`prod`, `pi`,
`rbind`, `prodDet`) it is pre-composed with a `Deterministic.FiniteMessage.Protocol.comap`
that routes each player's private randomness to the components. Each combinator comes with a
`rrun` lemma describing its output and a `complexity` lemma computing its cost. The protocol
model
is that of [RY20, Ch. 3]; the combinators themselves are original to this formalization and
have no textbook counterpart, so they carry no citations. This file is the private-coin
twin of `PublicCoinComposition`.

## Main definitions

- `PrivateCoin.FiniteMessage.Protocol.map`: post-compose the output with a function.
- `PrivateCoin.FiniteMessage.Protocol.bind`: run a protocol, then a continuation chosen by
  its output, with the same private randomness.
- `PrivateCoin.FiniteMessage.Protocol.comapRandomness`: reindex both randomness spaces along
  maps `Ω_X' → Ω_X` and `Ω_Y' → Ω_Y`.
- `PrivateCoin.FiniteMessage.Protocol.prod`, `PrivateCoin.FiniteMessage.Protocol.pi`: run
  two, resp. `k`, protocols on the same inputs with independent randomness and pair (resp.
  tuple) the outputs.
- `PrivateCoin.FiniteMessage.Protocol.rbind`: sequential composition where the continuation
  uses fresh randomness.
- `PrivateCoin.FiniteMessage.Protocol.prodDet`: run a private-coin protocol alongside a
  deterministic one and pair the outputs.

## Main results

- `PrivateCoin.FiniteMessage.Protocol.map_rrun`,
  `PrivateCoin.FiniteMessage.Protocol.map_complexity`: mapping a function over the output
  commutes with running and preserves complexity.
- `PrivateCoin.FiniteMessage.Protocol.bind_rrun`: bind runs the protocol and then the
  continuation selected by its output.
- `PrivateCoin.FiniteMessage.Protocol.comapRandomness_rrun`,
  `PrivateCoin.FiniteMessage.Protocol.comapRandomness_complexity`: reindexing randomness
  commutes with running and preserves complexity.
- `PrivateCoin.FiniteMessage.Protocol.prod_rrun`,
  `PrivateCoin.FiniteMessage.Protocol.prod_complexity`: the product runs component-wise and
  its complexity is the sum of the complexities.
- `PrivateCoin.FiniteMessage.Protocol.pi_rrun`, `PrivateCoin.FiniteMessage.Protocol.pi_complexity`:
  the `k`-fold product runs each component independently and its complexity is the sum of
  the component complexities.
- `PrivateCoin.FiniteMessage.Protocol.rbind_rrun`,
  `PrivateCoin.FiniteMessage.Protocol.rbind_complexity_const`: bind with fresh randomness
  runs sequentially, and its complexity is additive when the continuation has constant
  complexity.
- `PrivateCoin.FiniteMessage.Protocol.prodDet_rrun`,
  `PrivateCoin.FiniteMessage.Protocol.prodDet_complexity`: the product with a deterministic
  protocol runs component-wise and has summed complexity.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace PrivateCoin.FiniteMessage.Protocol

variable {Ω_X Ω_Y Ω_X' Ω_Y' Ω_X1 Ω_X2 Ω_Y1 Ω_Y2 X Y α α₁ α₂ β : Type*}

/-- Map a function over the output of a private-coin protocol. -/
abbrev map (g : α → β) (p : Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y β :=
  Deterministic.FiniteMessage.Protocol.map g p

/-- Running `p.map g` on inputs `x`, `y` with randomness `ω_x`, `ω_y` gives `g` applied to
the output of `p` on the same inputs and randomness. -/
@[simp]
theorem map_rrun (g : α → β) (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (p.map g).rrun x y ω_x ω_y = g (p.rrun x y ω_x ω_y) := by
  simp [map, rrun, Deterministic.FiniteMessage.Protocol.map_run]

/-- Mapping a function over the output of a private-coin protocol does not change its
complexity: no message is added or removed. -/
@[simp]
theorem map_complexity (g : α → β) (p : Protocol Ω_X Ω_Y X Y α) :
    (p.map g).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.map_complexity g p

/-- Bind: replace each output `a` in `p` with `q a`. -/
abbrev bind (p : Protocol Ω_X Ω_Y X Y α)
    (q : α → Protocol Ω_X Ω_Y X Y β) :
    Protocol Ω_X Ω_Y X Y β :=
  Deterministic.FiniteMessage.Protocol.bind p q

/-- Running `p.bind q` on inputs `x`, `y` with randomness `ω_x`, `ω_y` first runs `p`,
obtaining an output `a`, and then runs the continuation `q a` on the same inputs and the
same randomness; the result is the output of `q a`. -/
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

/-- Running the reindexed protocol `comapRandomness hX hY p` with randomness `ω_x : Ω_X'`,
`ω_y : Ω_Y'` is the same as running `p` with randomness `hX ω_x`, `hY ω_y`. -/
@[simp]
theorem comapRandomness_rrun (hX : Ω_X' → Ω_X) (hY : Ω_Y' → Ω_Y)
    (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X') (ω_y : Ω_Y') :
    (comapRandomness hX hY p).rrun x y ω_x ω_y =
      p.rrun x y (hX ω_x) (hY ω_y) := by
  simp [comapRandomness, rrun, Deterministic.FiniteMessage.Protocol.comap_run]

/-- Reindexing the randomness spaces of a private-coin protocol does not change its
complexity. -/
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

/-- Running the product `prod p1 p2` on inputs `x`, `y` with randomness `(ωx1, ωx2)` for
Alice and `(ωy1, ωy2)` for Bob gives the pair of the outputs of `p1` with randomness
`ωx1`, `ωy1` and of `p2` with randomness `ωx2`, `ωy2`, both on the same inputs. -/
@[simp]
theorem prod_rrun (p1 : Protocol Ω_X1 Ω_Y1 X Y α₁)
    (p2 : Protocol Ω_X2 Ω_Y2 X Y α₂)
    (x : X) (y : Y) (ω_x : Ω_X1 × Ω_X2) (ω_y : Ω_Y1 × Ω_Y2) :
    (prod p1 p2).rrun x y ω_x ω_y =
      (p1.rrun x y ω_x.1 ω_y.1, p2.rrun x y ω_x.2 ω_y.2) := by
  simp [prod, rrun, Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.prod_run]

/-- The complexity of the product of two private-coin protocols is the sum of their
complexities: the product runs one after the other. -/
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

/-- Running the `k`-fold product `pi p` on inputs `x`, `y` with randomness `ω_x`, `ω_y`
(families `ω_x i : Ω_Xf i` and `ω_y i : Ω_Yf i`) gives the family of outputs of the
components, the `i`-th component being run with randomness `ω_x i`, `ω_y i`. -/
@[simp]
theorem pi_rrun
    (p : (i : Fin k) → Protocol (Ω_Xf i) (Ω_Yf i) X Y (αf i))
    (x : X) (y : Y)
    (ω_x : (i : Fin k) → Ω_Xf i) (ω_y : (i : Fin k) → Ω_Yf i) :
    (pi p).rrun x y ω_x ω_y =
      fun i => (p i).rrun x y (ω_x i) (ω_y i) := by
  simp [pi, rrun, Deterministic.FiniteMessage.Protocol.comap_run,
    Deterministic.FiniteMessage.Protocol.pi_run]

/-- The complexity of the `k`-fold product of private-coin protocols is the sum of the
complexities of the components. -/
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

/-- Running `rbind p q` on inputs `x`, `y` with randomness `(ωx, ωx')` for Alice and
`(ωy, ωy')` for Bob first runs `p` with randomness `ωx`, `ωy`, obtaining an output `a`, and
then runs the continuation `q a` on the same inputs with the fresh randomness `ωx'`,
`ωy'`. -/
@[simp]
theorem rbind_rrun (p : Protocol Ω_X Ω_Y X Y α)
    (q : α → Protocol Ω_X' Ω_Y' X Y β)
    (x : X) (y : Y) (ω_x : Ω_X × Ω_X') (ω_y : Ω_Y × Ω_Y') :
    (rbind p q).rrun x y ω_x ω_y =
      (q (p.rrun x y ω_x.1 ω_y.1)).rrun x y ω_x.2 ω_y.2 := by
  simp [rbind, rrun,
    Deterministic.FiniteMessage.Protocol.bind_run,
    Deterministic.FiniteMessage.Protocol.comap_run]

/-- If every continuation `q a` has the same complexity `c`, then the complexity of
`rbind p q` is the complexity of `p` plus `c`. -/
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

/-- Running `prodDet p1 p2` on inputs `x`, `y` with randomness `ω_x`, `ω_y` gives the pair
of the output of the private-coin protocol `p1` (with randomness `ω_x`, `ω_y`) and the
output of the deterministic protocol `p2`, both on the same inputs. -/
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

/-- The complexity of the product of a private-coin protocol with a deterministic protocol
is the sum of their complexities. -/
theorem prodDet_complexity (p1 : Protocol Ω_X Ω_Y X Y α₁)
    (p2 : Deterministic.FiniteMessage.Protocol X Y α₂) :
    (prodDet p1 p2).complexity = p1.complexity + p2.complexity := by
  simp only [prodDet]
  apply Deterministic.FiniteMessage.Protocol.bind_complexity_const
  intro a1; simp

end PrivateCoin.FiniteMessage.Protocol

end CommunicationComplexity
