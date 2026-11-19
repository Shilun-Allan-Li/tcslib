/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.Light.Logic
import Mathlib.Data.List.Infix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Traces and determinism of Light execution

The input, output and random-bit extension of the Light language of [AFM26].

## Main definitions

The execution relation is defined in `Light.Syntax`.

## Main results

`Exec.det` fixes a run on a stream; trace lengths are bounded by the cost.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, folder `3sum-apsp`,
  commit e1a4e6508154ea59f030480661590a9fe3018011, Apache-2.0: the language extended here.
-/

namespace Light

/-- After an initial consumed word, the remaining word prefixes the remaining stream. -/
private theorem rest_prefix {a b ρ : List Bool} (h : a ++ b <+: ρ) :
    b <+: ρ.drop a.length := by
  simpa only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero, List.nil_append]
    using h.drop a.length

/-- The total number of emitted bits and consumed coins is bounded by the run cost.

**Proof sketch.** Induct on `Exec`. Sequential and loop rules add the trace lengths and costs;
`coin` and `emit` each add one trace bit and at least one step. -/
private theorem trace_length {lim : Limits} {P : Program} {d : ℕ} {s : Stmt}
    {σ σ' : State} {o r : List Bool} {c : ℕ} (h : Exec lim P d s σ σ' o r c) :
    r.length + o.length ≤ c := by
  induction h <;>
    (try simp_all only [List.length_append, List.length_nil, List.length_singleton]) <;> omega

section
variable {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ σ' : State}
  {o r : List Bool} {c : ℕ}

/-- Each coin costs one step, so a run of `c` steps consumes at most `c` coins: streams of
length `c` suffice.

**Proof sketch.** Apply the joint trace bound `trace_length` and discard the output length. -/
theorem Exec.coins_length_le (h : Exec lim P d s σ σ' o r c) : r.length ≤ c := by
  have ht := trace_length h
  omega

/-- Each emitted bit costs at least one step. -/
theorem Exec.output_length_le (h : Exec lim P d s σ σ' o r c) : o.length ≤ c := by
  have ht := trace_length h
  omega

/-- **Determinism.** Two runs of the same statement from the same state whose consumed words are
both prefixes of one stream `ρ` are the same run: same final state, output, consumed word and
cost. Randomized acceptance (`acceptProb`) needs it.

**Proof sketch.** Induction on the first run, inversion on the second. A test's outcome is a
function of the state, so both runs take the same rule. For `seq` and `whileTrue` the first
parts' consumed words are prefixes of `ρ`, so the induction hypothesis makes them equal; the
second parts then consume prefixes of the same rest of `ρ`. For `coin` the two bits are the
first bit of `ρ`. -/
theorem Exec.det {σ₁ σ₂ : State} {o₁ o₂ r₁ r₂ : List Bool} {c₁ c₂ : ℕ} {ρ : List Bool}
    (h₁ : Exec lim P d s σ σ₁ o₁ r₁ c₁) (h₂ : Exec lim P d s σ σ₂ o₂ r₂ c₂)
    (hr₁ : r₁ <+: ρ) (hr₂ : r₂ <+: ρ) : σ₁ = σ₂ ∧ o₁ = o₂ ∧ r₁ = r₂ ∧ c₁ = c₂ := by
  induction h₁ generalizing σ₂ o₂ r₂ c₂ ρ with
  | skip => cases h₂; exact ⟨rfl, rfl, rfl, rfl⟩
  | set hs => cases h₂; exact ⟨rfl, rfl, rfl, rfl⟩
  | store ha he hA => cases h₂; exact ⟨rfl, rfl, rfl, rfl⟩
  | seq h₁ h₁' ih₁ ih₂ =>
    cases h₂ with
    | seq h₂ h₂' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih₁ h₂
        ((List.prefix_append _ _).trans hr₁) ((List.prefix_append _ _).trans hr₂)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih₂ h₂' (rest_prefix hr₁) (rest_prefix hr₂)
      exact ⟨rfl, rfl, rfl, rfl⟩
  | iteTrue hs hc h ih =>
    cases h₂ with
    | iteTrue _ _ h' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih h' hr₁ hr₂
      exact ⟨rfl, rfl, rfl, rfl⟩
    | iteFalse _ hn _ => exact (hn hc).elim
  | iteFalse hs hn h ih =>
    cases h₂ with
    | iteTrue _ hc _ => exact (hn hc).elim
    | iteFalse _ _ h' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih h' hr₁ hr₂
      exact ⟨rfl, rfl, rfl, rfl⟩
  | whileFalse hs hn =>
    cases h₂ with
    | whileFalse => exact ⟨rfl, rfl, rfl, rfl⟩
    | whileTrue _ hc _ _ => exact (hn hc).elim
  | whileTrue hs hc h₁ h₁' ih₁ ih₂ =>
    cases h₂ with
    | whileFalse _ hn => exact (hn hc).elim
    | whileTrue _ _ h₂ h₂' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih₁ h₂
        ((List.prefix_append _ _).trans hr₁) ((List.prefix_append _ _).trans hr₂)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih₂ h₂' (rest_prefix hr₁) (rest_prefix hr₂)
      exact ⟨rfl, rfl, rfl, rfl⟩
  | call ha hp hd h ih =>
    cases h₂ with
    | call _ hp' _ h' =>
      have he := Option.some.inj (hp.symm.trans hp')
      subst he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih h' hr₁ hr₂
      exact ⟨rfl, rfl, rfl, rfl⟩
  | inBit hs => cases h₂; exact ⟨rfl, rfl, rfl, rfl⟩
  | emit hs => cases h₂; exact ⟨rfl, rfl, rfl, rfl⟩
  | coin b =>
    cases h₂ with
    | coin b' =>
      have he : b = b' := by
        cases ρ with
        | nil => simp only [List.prefix_nil, List.cons_ne_self] at hr₁
        | cons a ρ =>
          exact (List.cons_prefix_cons.1 hr₁).1.trans (List.cons_prefix_cons.1 hr₂).1.symm
      subst b'
      exact ⟨rfl, rfl, rfl, rfl⟩
  | half hs => cases h₂; exact ⟨rfl, rfl, rfl, rfl⟩


/-- **Inversion for `inBit`**: its only run sets `x` to the input bit, emits and
consumes nothing, and costs `e.cost + 1`. -/
theorem Exec.inBit_inv {x : ℕ} {e : Expr} (h : Exec lim P d (.inBit x e) σ σ' o r c) :
    e.Safe lim σ ∧
      σ' = { σ with loc := Function.update σ.loc x (inBitVal lim.input (e.val σ)) } ∧
      o = [] ∧ r = [] ∧ c = e.cost + 1 := by
  cases h with
  | inBit hs => exact ⟨hs, rfl, rfl, rfl, rfl⟩

/-- **Inversion for `emit`**: its only run emits the one bit "`e ≠ 0`", keeps the state, consumes
nothing, and costs `e.cost + 1`. -/
theorem Exec.emit_inv {e : Expr} (h : Exec lim P d (.emit e) σ σ' o r c) :
    e.Safe lim σ ∧ σ' = σ ∧ o = [decide (e.val σ ≠ 0)] ∧ r = [] ∧ c = e.cost + 1 := by
  cases h with
  | emit hs => exact ⟨hs, rfl, rfl, rfl, rfl⟩

/-- **Inversion for `coin`**: a run consumes one bit `b`, sets `x` to it, emits nothing, and
costs `1`. -/
theorem Exec.coin_inv {x : ℕ} (h : Exec lim P d (.coin x) σ σ' o r c) :
    ∃ b : Bool, σ' = { σ with loc := Function.update σ.loc x (if b then 1 else 0) } ∧
      o = [] ∧ r = [b] ∧ c = 1 := by
  cases h with
  | coin b => exact ⟨b, rfl, rfl, rfl, rfl⟩

/-- **Inversion for `half`**: its only run sets `x` to `⌊e / 2⌋`, emits and consumes nothing, and
costs `e.cost + 1`. -/
theorem Exec.half_inv {x : ℕ} {e : Expr} (h : Exec lim P d (.half x e) σ σ' o r c) :
    e.Safe lim σ ∧ σ' = { σ with loc := Function.update σ.loc x (e.val σ / 2) } ∧
      o = [] ∧ r = [] ∧ c = e.cost + 1 := by
  cases h with
  | half hs => exact ⟨hs, rfl, rfl, rfl, rfl⟩

end

end Light
