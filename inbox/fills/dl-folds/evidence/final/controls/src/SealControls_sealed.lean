/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Forwarding
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward

/-! Paired controls of the dl-folds seals: each example reads one TCSlib definition through its
body (`rfl`), so it passes unsealed and fails once that definition is irreducible. They cover the
definitions that the promoted lemmas and the published readers of this unit are about. -/

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability

attribute [local irreducible] _root_.Complexity.PolyExpr.eval _root_.TCSlib.Cryptography.Games.iterEmit _root_.TCSlib.Cryptography.Games.InteractiveHandler.rAns _root_.TCSlib.Cryptography.Games.InteractiveHandler.finA _root_.TCSlib.Cryptography.Games.ansRead _root_.TCSlib.Cryptography.Games.cntRead _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.Composability.NMCCA2.logEmit _root_.TCSlib.Cryptography.Composability.NMSim.chunkMap _root_.TCSlib.Cryptography.Games.fwdHandler

example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
example (s e : List Bool → List Bool) (x : List Bool) : iterEmit s e 0 x = [] := rfl
example (w : List Bool) : InteractiveHandler.rAns w = pairSndD (pairSndD (pairFstD (pairSndD (pairSndD (pairSndD w))))) := rfl
example (w : List Bool) : InteractiveHandler.finA w = pairFstD (pairSndD (pairSndD w)) := rfl
example (v : List Bool) : ansRead v = pairSndD (pairSndD (pairFstD v)) := rfl
example : cntRead [] = [] := rfl
example (B i : ℕ) (r : List Bool) : coinBlock B i r = (r.drop (i * B)).take B := rfl
example (G : List Bool → List Bool) (L : List Bool) : NMCCA2.logEmit G L = iterEmit pairSndD G (L.length + 1) L := rfl
example (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    NMSim.chunkMap c f x = iterEmit (NMSim.chunkStep c) (NMSim.chunkEmit c f) (x.length + 1) x := rfl
example {k : ℕ} (din dout : Fin k → PolyExpr) (sl : PolyExpr) (a : List Bool → List Bool)
    (ha : PolyTimeComputable a) (o f : PolyExpr) (r : List Bool → List Bool)
    (hr : PolyTimeComputable r) : (fwdHandler din dout sl a ha o f r hr).perCall = .const 1 := rfl
