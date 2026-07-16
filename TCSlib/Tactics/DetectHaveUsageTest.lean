import Mathlib

/-!
# Metaprogram detection of haves consumed by a later `simp_all`

A have consumed by `simp_all` leaves no syntactic trace (and `simp_all?`
suggestions never list local hypotheses). But after elaboration the have
survives in the proof term as a redex — `(fun key => rest) v` from the `have`
tactic, or `letFun v (fun key => rest)` from term-mode `have` — so consumption
is exactly "does the bound variable occur in `rest`", i.e. `hasLooseBVar 0`.
`#detect_have_usage thm` walks the stored proof term and reports USED/UNUSED
for every have-redex, with no re-execution of any tactic.

Two other metaprogram routes (not demoed here): calling `Meta.simpAll`
directly and reading `Simp.Stats.usedTheorems` (its `.fvar` origins are the
hypothesis usages that the `simp_all?` pretty-printer filters out), and
ablation in `MetaM` (`withoutModifyingState`: clear the fvar, re-run
`simpAll`, catch failure) which tests necessity rather than usage.
-/

open Lean Meta Elab Command

namespace DetectHaveUsage

/-- Collect have-style redexes — `(fun x => b) v` and `letFun v (fun x => b)` —
    from a proof term, recording whether the bound variable occurs in `b`. -/
partial def collect (e : Expr) (acc : Array (Name × Bool)) : Array (Name × Bool) :=
  if e.isAppOfArity ``letFun 4 then
    let args := e.getAppArgs
    let v := args[2]!
    match args[3]! with
    | .lam n _ b _ => collect b (collect v (acc.push (n, b.hasLooseBVar 0)))
    | f => collect f (collect v acc)
  else
    match e with
    | .app (.lam n _ b _) v => collect b (collect v (acc.push (n, b.hasLooseBVar 0)))
    | .app f a => collect a (collect f acc)
    | .lam _ _ b _ => collect b acc
    | .forallE _ _ b _ => collect b acc
    | .letE n _ v b _ => collect b (collect v (acc.push (n, b.hasLooseBVar 0)))
    | .mdata _ b => collect b acc
    | .proj _ _ b => collect b acc
    | _ => acc

elab "#detect_have_usage " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some info := (← getEnv).find? name | throwError "unknown constant {name}"
  let some val := info.value? | throwError "{name} has no proof term"
  let results := collect val #[]
  if results.isEmpty then
    logInfo m!"{name}: no have-redexes found"
  for (n, used) in results do
    let verdict := if used then "USED" else "UNUSED"
    logInfo m!"{name}: have '{n}' is {verdict} downstream"

end DetectHaveUsage

-- `key` carries content the later simp_all cannot rederive → must be USED.
theorem det_necessary (a b : ℕ) (hle : a ≤ b) (hge : b ≤ a) : a = b := by
  have key : a = b := Nat.le_antisymm hle hge
  simp_all

-- junk `key` the later simp_all cannot need → must be UNUSED.
theorem det_junk (a b : ℕ) (hab : a = b) (hb : b = 0) : a + b = 0 := by
  have key : 2 + 2 = 4 := by norm_num
  simp_all

-- redundant-but-available `key` — empirically interesting which route simp_all
-- takes; proof-term occurrence reports actual usage either way.
theorem det_redundant (a b : ℕ) (hab : a = b) (hb : b = 0) : a + b = 0 := by
  have key : a = 0 := by simp_all
  simp_all

#detect_have_usage det_necessary
#detect_have_usage det_junk
#detect_have_usage det_redundant
