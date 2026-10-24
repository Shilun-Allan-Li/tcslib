"""mkseal.py <head module> <outdir> : rule-10 seal files.
  <outdir>/F3C2RevSeal.lean          the module, its runner home (from `/-! ### The runner -/` to the last
                                      `end Turing`, the target included) in a section sealing SEAL, with the
                                      controls at the top of that section
  <outdir>/F3C2RevCtlUnsealed.lean   the controls alone, nothing sealed (same imports as the module)
  <outdir>/F3C2RevCtlSealed.lean     the controls alone, under the same seal
  <outdir>/F3C2RevSealBody.lean      the sealed module without the controls"""
import sys, os
head, outdir = sys.argv[1], sys.argv[2]
SEAL = ['Cfg.InWindow', 'Cfg.inputSymbol', 'Cfg.mapState', 'Cfg.workTapeSymbols', 'FinTM.bufferTape',
        'FinTM.configBound', 'MultiTapeTM.runFrom', 'MultiTapeTM.spaceUsed', 'MultiTapeTM.step',
        'MultiTapeTM.spaceUsedByTape', 'MultiTapeTM.visitedByTapeHead', 'RecSym.digitEmb', 'RecordAt',
        'Segment', 'cfgRecord', 'clearTM', 'copyMapTM', 'fieldOffset', 'fieldsTape', 'joinFields',
        'moveInputPos', 'phaseHostTM', 'posWidth', 'recordLength', 'skipBackTM', 'skipTM', 'tapeAction',
        'windowRun', 'wordPatch', 'instDecidableEqSeekPhase', 'instDecidableEqSweepPhase',
        'instDecidableEqWindowExit', 'instFintypeSeekPhase', 'instFintypeSweepPhase']
CTL = {
 'Cfg.InWindow': '''example {k : ℕ} {S : Type} {x : List Bool} (s : ℕ) (c : Cfg k Bool S x) :
    c.InWindow s = ((∀ i, |c.workTapePos i| ≤ (s : ℤ)) ∧
      ∀ (i : Fin k) (z : ℤ), (s : ℤ) < |z| → c.workTapes i z = none) := rfl''',
 'Cfg.inputSymbol': '''example : Cfg.inputSymbol
    (⟨none, 0, fun _ _ => none, fun _ => 0, []⟩ : Cfg 0 Bool Unit [true]) = none := rfl''',
 'Cfg.mapState': '''example {k : ℕ} {S S' : Type} {x : List Bool} (f : S → S') (c : Cfg k Bool S x) :
    (c.mapState f).workTapes = c.workTapes := rfl''',
 'Cfg.workTapeSymbols': '''example {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) (i : Fin k) :
    c.workTapeSymbols i = c.workTapes i (c.workTapePos i) := rfl''',
 'FinTM.bufferTape': '''example : FinTM.bufferTape [true] 0 = some true := rfl''',
 'FinTM.configBound': '''example (M : FinTM Bool) (n s : ℕ) : M.configBound n s =
    (Fintype.card M.State + 1) * (n + 2) * 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k := rfl''',
 'MultiTapeTM.runFrom': '''example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) : tm.runFrom c 1 = tm.step c := rfl''',
 'MultiTapeTM.spaceUsed': '''example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (t : ℕ) : tm.spaceUsed c t = ∑ i, tm.spaceUsedByTape c t i := rfl''',
 'MultiTapeTM.step': '''example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) : tm.step { c with state := none } = { c with state := none } := rfl''',
 'MultiTapeTM.spaceUsedByTape': '''example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape c t i = (tm.visitedByTapeHead c t i).card := rfl''',
 'MultiTapeTM.visitedByTapeHead': '''example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (t : ℕ) (i : Fin k) : tm.visitedByTapeHead c t i =
      (Finset.range (t + 1)).image fun t' => (tm.runFrom c t').workTapePos i := rfl''',
 'RecSym.digitEmb': '''example (Q T : Type) (b : Bool) : RecSym.digitEmb Q T b = RecSym.digit b := rfl''',
 'RecordAt': '''example {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (fs : List (List Bool)) : RecordAt d r fs = ∀ p : ℤ, -1 ≤ p →
      p ≤ ((joinFields fs).length : ℤ) → d.workTapes r (d.workTapePos r + p) = fieldsTape fs p :=
  rfl''',
 'Segment': '''example {k : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM k Bool S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Bool S x) (t : ℕ) : Segment M F P a b t =
      (M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
        ∀ u ≤ t, P (M.runFrom a u).workTapePos) := rfl''',
 'cfgRecord': '''example {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) :
    (cfgRecord s c τ).head? = some [RecSym.st c.state] := rfl''',
 'clearTM': '''example {k : ℕ} (i : Fin k) : (clearTM (Symbol := Bool) k i).q₀ = .sweep := rfl''',
 'copyMapTM': '''example {k : ℕ} (src dst : Fin k) :
    (copyMapTM (Symbol := Bool) k src dst (fun _ => ()) (fun _ _ => true)).q₀ = .sweep := rfl''',
 'fieldOffset': '''example : fieldOffset ([[true], [false, true]] : List (List Bool)) 1 = 2 := rfl''',
 'fieldsTape': '''example (fs : List (List Bool)) (z : ℤ) :
    fieldsTape fs z = if 0 ≤ z then ((joinFields fs)[z.toNat]?).join else none := rfl''',
 'joinFields': '''example (fs : List (List Bool)) :
    joinFields fs = List.intercalate [none] (fs.map (List.map some)) := rfl''',
 'moveInputPos': '''example : (moveInputPos (0 : Fin 3) .pos).val = 1 := rfl''',
 'phaseHostTM': '''example {k : ℕ} {I : Type} {Ph : I → Type} (M : (i : I) → MultiTapeTM k Bool (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) :
    (phaseHostTM M q0 red).q₀ = q0 := rfl''',
 'posWidth': '''example (n : ℕ) : posWidth n = (Nat.bits (n + 1)).length := rfl''',
 'recordLength': '''example (k n s : ℕ) : recordLength k n s = k * (2 * s + 1) + posWidth n + k + 4 := rfl''',
 'skipBackTM': '''example {k : ℕ} (i : Fin k) : (skipBackTM (Symbol := Bool) k i).q₀ = .run := rfl''',
 'skipTM': '''example {k : ℕ} (i : Fin k) : (skipTM (Symbol := Bool) k i).q₀ = .run := rfl''',
 'tapeAction': '''example {k : ℕ} {S : Type} (i : Fin k) (q : S) :
    (tapeAction (Symbol := Bool) i 0 none 0 q).state = some q := rfl''',
 'windowRun': '''example {k : ℕ} {Q T : Type} {x : List Bool} (M : MultiTapeTM k Bool Q) (s : ℕ)
    (upd : T → Option Bool → T) (c : Cfg k Bool Q x) (τ : T) :
    windowRun M s upd 0 c τ = (.exhausted, c, τ) := rfl''',
 'wordPatch': '''example (ct : ℤ → Option Bool) (cp : ℤ) (u : List Bool) (q : ℤ) : wordPatch ct cp u q =
    if cp ≤ q ∧ q < cp + (u.length : ℤ) then FinTM.bufferTape u (q - cp) else ct q := rfl''',
 'instDecidableEqSeekPhase': '''example : (if SeekPhase.run = SeekPhase.done then 1 else 0) = 0 := rfl''',
 'instDecidableEqSweepPhase': '''example : (if SweepPhase.sweep = SweepPhase.done then 1 else 0) = 0 := rfl''',
 'instDecidableEqWindowExit': '''example : (if WindowExit.halted = WindowExit.left then 1 else 0) = 0 := rfl''',
 'instFintypeSeekPhase': '''example : (Finset.univ : Finset SeekPhase).card = 4 := rfl''',
 'instFintypeSweepPhase': '''example : (Finset.univ : Finset SweepPhase).card = 3 := rfl''',
}
assert set(CTL) == set(SEAL), set(SEAL) ^ set(CTL)
src = open(head, encoding='utf-8').read()
marker = '/-! ### The runner -/\n'
assert src.count(marker) == 1
pre, rest = src.split(marker)
k = rest.rindex('end Turing')
attrs = ''.join(f'attribute [local irreducible] Turing.{n}\n' for n in SEAL)
ctl = ''.join(f'/-- Control {i + 1}: closes only by unfolding `Turing.{n}`. -/\n{CTL[n]}\n\n'
              for i, n in enumerate(SEAL))
sealed = pre + marker + '\nsection F3C2RevSeal\n\n' + attrs + '\n' + ctl + rest[:k] + 'end F3C2RevSeal\n\n' + rest[k:]
body = pre + marker + '\nsection F3C2RevSeal\n\n' + attrs + '\n' + rest[:k] + 'end F3C2RevSeal\n\n' + rest[k:]
imports = ''.join(l + '\n' for l in src.split('\n') if l.startswith('import '))
hdr = imports + '\nset_option autoImplicit false\n\nnamespace Turing\n\n'
unsealed = hdr + ctl + 'end Turing\n'
csealed = hdr + 'section F3C2RevSeal\n\n' + attrs + '\n' + ctl + 'end F3C2RevSeal\n\nend Turing\n'
for name, txt in [('F3C2RevSeal', sealed), ('F3C2RevSealBody', body), ('F3C2RevCtlUnsealed', unsealed),
                  ('F3C2RevCtlSealed', csealed)]:
    open(os.path.join(outdir, name + '.lean'), 'w', encoding='utf-8').write(txt)
# line numbers of the controls in the sealed module, for matching errors
ln = (pre + marker + '\nsection F3C2RevSeal\n\n' + attrs + '\n').count('\n') + 1
first = ln; last = (pre + marker + '\nsection F3C2RevSeal\n\n' + attrs + '\n' + ctl).count('\n')
print('sealed definitions', len(SEAL), '; controls in F3C2RevSeal.lean lines', first, '-', last)
