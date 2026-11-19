/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Renumber.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Renumber.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header.
* added input, output, coin and halving constructs, and threaded output and coin indices
  through the affected syntax, semantics and run witnesses.
The remaining content is unchanged.
-/
import TCSlib.Programs.Light.Logic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, Apache-2.0: the source of
  this file (`ThreeSumApsp/Lang/Renumber.lean`); see the header and the repository NOTICE.
-/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The statement with n added to the number of every procedure that it calls. -/
def Stmt.shift (n : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s t => .seq (s.shift n) (t.shift n)
  | .ite c s t => .ite c (s.shift n) (t.shift n)
  | .while c s => .while c (s.shift n)
  | .call p args x => .call (p + n) args x
  | .inBit x e => .inBit x e
  | .emit e => .emit e
  | .coin x => .coin x
  | .half x e => .half x e

/-- Reading procedure relocation on `skip`. -/
theorem Stmt.shift_skip (n : ℕ)  :
    (Stmt.skip).shift n = .skip := rfl

/-- Reading procedure relocation on `set`. -/
theorem Stmt.shift_set (n : ℕ) (x : ℕ) (e : Expr) :
    (Stmt.set x e).shift n = .set x e := rfl

/-- Reading procedure relocation on `store`. -/
theorem Stmt.shift_store (n : ℕ) (a e : Expr) :
    (Stmt.store a e).shift n = .store a e := rfl

/-- Reading procedure relocation on `seq`. -/
theorem Stmt.shift_seq (n : ℕ) (s t : Stmt) :
    (Stmt.seq s t).shift n = .seq (s.shift n) (t.shift n) := rfl

/-- Reading procedure relocation on `ite`. -/
theorem Stmt.shift_ite (n : ℕ) (c : Cond) (s t : Stmt) :
    (Stmt.ite c s t).shift n = .ite c (s.shift n) (t.shift n) := rfl

/-- Reading procedure relocation on `while`. -/
theorem Stmt.shift_while (n : ℕ) (c : Cond) (s : Stmt) :
    (Stmt.while c s).shift n = .while c (s.shift n) := rfl

/-- Reading procedure relocation on `call`. -/
theorem Stmt.shift_call (n : ℕ) (p : ℕ) (args : List Expr) (x : ℕ) :
    (Stmt.call p args x).shift n = .call (p + n) args x := rfl

/-- Reading procedure relocation on `inBit`. -/
theorem Stmt.shift_inBit (n : ℕ) (x : ℕ) (e : Expr) :
    (Stmt.inBit x e).shift n = .inBit x e := rfl

/-- Reading procedure relocation on `emit`. -/
theorem Stmt.shift_emit (n : ℕ) (e : Expr) :
    (Stmt.emit e).shift n = .emit e := rfl

/-- Reading procedure relocation on `coin`. -/
theorem Stmt.shift_coin (n : ℕ) (x : ℕ) :
    (Stmt.coin x).shift n = .coin x := rfl

/-- Reading procedure relocation on `half`. -/
theorem Stmt.shift_half (n : ℕ) (x : ℕ) (e : Expr) :
    (Stmt.half x e).shift n = .half x e := rfl

/-- The program P placed behind the program Q. -/
def Program.behind (Q P : Program) : Program := Q ++ P.map (Stmt.shift Q.length)

/-- Reading program relocation: the prefix followed by shifted procedure bodies. -/
theorem Program.behind_eq (Q P : Program) :
    Program.behind Q P = Q ++ P.map (Stmt.shift Q.length) := rfl

/-- Procedure p of P is procedure `p + Q.length` of P placed behind Q, with its calls
shifted. -/
theorem Program.getElem?_behind_right (Q : Program) {p : ℕ} {body : Stmt} (h : P[p]? = some body) :
    (Program.behind Q P)[p + Q.length]? = some (body.shift Q.length) := by
  rw [Program.behind, List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
    List.getElem?_map, h]
  rfl

/-- **Relocation.**  A run in P is a run, with the same states and the same number of steps, of
the shifted statement in P placed behind Q. -/
theorem Exec.shift {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ σ' : State}
    {o r : List Bool} {c : ℕ} (h : Exec lim P d s σ σ' o r c) (Q : Program) :
    Exec lim (Program.behind Q P) d (s.shift Q.length) σ σ' o r c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (Program.getElem?_behind_right Q h₂) h₃ ih
  | inBit hs => exact .inBit hs
  | emit hs => exact .emit hs
  | coin b => exact .coin b
  | half hs => exact .half hs

/-- What is proved about a statement in P holds for the shifted statement in P placed behind
Q. -/
theorem Ends.shift {s σ T post} (h : Ends lim P d s σ T post) (Q : Program) :
    Ends lim (Program.behind Q P) d (s.shift Q.length) σ T post := by
  obtain ⟨σ', o, r, c, he, hc, hq⟩ := h
  exact ⟨σ', o, r, c, he.shift Q, hc, hq⟩

/-- The same with more procedures appended behind. -/
theorem Ends.shift_append {s σ T post} (h : Ends lim P d s σ T post) (Q R : Program) :
    Ends lim (Program.behind Q P ++ R) d (s.shift Q.length) σ T post :=
  (h.shift Q).append R

end Light
