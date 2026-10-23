"""mkseal.py <head module> <outdir> : the seal variants of the delivered module.
S1: every other-file semireducible, non-projection, non-instance definition reached (36) `local irreducible`
    from the start of the home (after `namespace Turing`) to `end Turing`, with controls at the top and the end.
S2: S1 plus `attribute [-simp]` on the four `@[simp]` definitions among them.
W : the worker's seal as REPORT describes it (28 names, from the new region's first line to `end Turing`),
    with the worker's one control (`pairEncode [] [] = [false, true]`) at the end.
CU: the controls alone, unsealed (the module's imports only).
CS: the controls alone, sealed (S2's attributes)."""
import sys, os
head, outd = sys.argv[1:3]
src = open(head, encoding='utf-8').read()
L = src.split('\n')
ins = [k for k, l in enumerate(L) if l == 'namespace Turing']
assert len(ins) == 1, ins
NS = ins[0] + 1   # insert after `namespace Turing` (115 in the head)
iend = max(k for k, l in enumerate(L) if l == 'end Turing')
hh = [k for k, l in enumerate(L) if l.startswith("/-! ### The setup machine's pieces")]
assert len(hh) == 1, hh
HOME = hh[0]      # the home's first line (head 227)
imps = [l for l in L if l.startswith('import ')]
SEAL = """Turing.Action.apply Turing.Cfg.init Turing.Cfg.inputSymbol Turing.Cfg.mapState Turing.Cfg.workTapeSymbols
Turing.CodeNDTM.toFinNDTM Turing.FinNDTM.AcceptsWithin Turing.FinTM.bufferTape Turing.FinTM.bufferedCompTM
Turing.FinTM.bufferedSecondCfg Turing.FinTM.controlAction Turing.FinTM.pairExtractTM Turing.FinTM.tapeBlocks
Turing.GuessRunPhase.State Turing.MultiTapeTM.initCfg Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.step
Turing.NDTM.HaltsWithin Turing.NDTM.initCfg Turing.NDTM.runWith Turing.clearTM Turing.counterLoopCfg
Turing.counterOverhead Turing.counterValue Turing.embedSilentCfg Turing.embedSilentRetTM Turing.embedSilentTM
Turing.expandTM Turing.guessRunTM Turing.moveInputPos Turing.pairEncode Turing.prefixCanonTM Turing.rewindTM
Turing.seamCompTM Turing.streamStartCfg Turing.universalPrefixTM""".split()
assert len(SEAL) == 36 and len(set(SEAL)) == 36
SIMP = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg', 'Turing.NDTM.initCfg']
WORKER = """pairEncode FinTM.bufferTape Cfg.mapState embedSilentCfg MultiTapeTM.initCfg MultiTapeTM.runFrom
MultiTapeTM.step Action.apply Cfg.init FinTM.bufferedSecondCfg FinTM.bufferedCompTM seamCompTM embedSilentRetTM
rewindTM clearTM expandTM counterLoopCfg counterValue counterOverhead prefixCanonTM universalPrefixTM
FinTM.pairExtractTM FinTM.controlAction FinTM.tapeBlocks moveInputPos Cfg.inputSymbol Cfg.workTapeSymbols
Cfg.ofWords""".split()
assert len(WORKER) == 28
# one control per sealed definition: (name, statement and proof); each closes only by unfolding that name
C = [
 ('Turing.MultiTapeTM.runFrom', "example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :\n    tm.runFrom c 0 = c := rfl"),
 ('Turing.FinTM.bufferTape', "example : FinTM.bufferTape [true] 0 = some true := by rfl"),
 ('Turing.Cfg.mapState', "example {k : ℕ} {S S' : Type} {x : List Bool} (f : S → S') (c : Cfg k Bool S x) :\n    (c.mapState f).inputPos = c.inputPos := rfl"),
 ('Turing.clearTM', "example {k : ℕ} (i : Fin k) : (clearTM (Symbol := Bool) k i).q₀ = .sweep := rfl"),
 ('Turing.pairEncode', "example : pairEncode [] [true] = [false, true, true] := by rfl"),
 ('Turing.seamCompTM', "example {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (e : S₁)\n    (M₂ : MultiTapeTM k Bool S₂) (q : S₂) : (seamCompTM M₁ e M₂ q).q₀ = Sum.inl M₁.q₀ := rfl"),
 ('Turing.MultiTapeTM.initCfg', "example {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S) (x : List Bool) :\n    tm.initCfg x = Cfg.init tm.q₀ x := rfl"),
 ('Turing.Cfg.init', "example {k : ℕ} {S : Type} (q : S) (x : List Bool) :\n    (Cfg.init (k := k) (Symbol := Bool) q x).state = some q := rfl"),
 ('Turing.FinTM.controlAction', "example {k : ℕ} {S : Type} (m : SignType) (q : Option S) :\n    (FinTM.controlAction (k := k) m q).state = q := rfl"),
 ('Turing.FinTM.bufferedCompTM', "example (M₁ M₂ : FinTM Bool) : (FinTM.bufferedCompTM M₁ M₂).k = M₁.k + (1 + M₂.k) := rfl"),
 ('Turing.embedSilentCfg', "example {m n : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin n) (cap : Fin n)\n    (c : Cfg m Bool S x) :\n    (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] [] c).state = c.state := rfl"),
 ('Turing.Cfg.workTapeSymbols', "example {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) (i : Fin k) :\n    c.workTapeSymbols i = c.workTapes i (c.workTapePos i) := rfl"),
 ('Turing.Action.apply', "example {k : ℕ} {S : Type} {x : List Bool} (a : Action k Bool S) (c : Cfg k Bool S x) :\n    (a.apply c).state = a.state := rfl"),
 ('Turing.moveInputPos', "example : (moveInputPos (0 : Fin 3) .pos).val = 1 := rfl"),
 ('Turing.embedSilentRetTM', "example {m n : ℕ} {S : Type} (ι : Fin m ↪ Fin n) (cap : Fin n) (M : MultiTapeTM m Bool S) :\n    (embedSilentRetTM ι cap M).q₀ = Sum.inl M.q₀ := rfl"),
 ('Turing.prefixCanonTM', "example (F : FinTM Bool) : prefixCanonTM F = FinTM.bufferedCompTM universalPrefixTM F := rfl"),
 ('Turing.universalPrefixTM', "example : universalPrefixTM.k = 0 := rfl"),
 ('Turing.Cfg.inputSymbol', "example : (⟨some (0 : Fin 1), 0, fun _ _ => none, fun _ => 0, []⟩ :\n    Cfg 0 Bool (Fin 1) []).inputSymbol = none := rfl"),
 ('Turing.FinTM.bufferedSecondCfg', "example (M₁ M₂ : FinTM Bool) {x y : List Bool} (c : Cfg M₂.k Bool M₂.State y) (b : Bool)\n    (p : Fin (x.length + 2)) (tp : Fin M₁.k → ℤ → Option Bool) (hd : Fin M₁.k → ℤ) :\n    (FinTM.bufferedSecondCfg M₁ M₂ c b p tp hd).inputPos = p := rfl"),
 ('Turing.FinTM.tapeBlocks', "example (a : Fin 1 → ℕ) (b : ℕ) (c : Fin 1 → ℕ) :\n    FinTM.tapeBlocks a b c = Fin.addCases a (Fin.addCases (fun _ => b) c) := rfl"),
 ('Turing.MultiTapeTM.step', "example {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) :\n    tm.step { c with state := none } = { c with state := none } := rfl"),
 ('Turing.FinTM.pairExtractTM', "example : (FinTM.pairExtractTM true false).k = 1 := rfl"),
 ('Turing.rewindTM', "example {k : ℕ} (i : Fin k) : (rewindTM (Symbol := Bool) k i).q₀ = .start := rfl"),
 ('Turing.expandTM', "example (k : ℕ) (i : Fin k) (pat : List Bool) :\n    expandTM k i pat = counterLoopTM (writeAdvTM k i pat) 0 none := rfl"),
 ('Turing.counterLoopCfg', "example {k : ℕ} {S : Type} {x : List Bool} (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)\n    (ct : ℤ → Option Bool) (cp : ℤ) : (counterLoopCfg q c ct cp).state = q := rfl"),
 ('Turing.counterValue', "example (w : List Bool) : counterValue w = Nat.ofDigits 2 (w.map Bool.toNat) := rfl"),
 ('Turing.counterOverhead', "example (w : List Bool) (r : ℕ) : counterOverhead w r =\n    Finset.sum (Finset.range r) (fun j => 2 * ((counterWord w j).takeWhile not).length + 2) := rfl"),
 ('Turing.guessRunTM', "example {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ] (P : MultiTapeTM k Bool SP)\n    (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ) (qe acc rej : SQ) :\n    guessRunTM P pexit j Q qe acc rej =\n      NDTM.phaseHostND (guessRunPhases P j Q) ⟨.pre, P.q₀⟩ (guessRunRed pexit qe acc rej) := rfl"),
 ('Turing.embedSilentTM', "example {m n : ℕ} {S : Type} (ι : Fin m ↪ Fin n) (cap : Fin n) (M : MultiTapeTM m Bool S) :\n    (embedSilentTM ι cap M).q₀ = M.q₀ := rfl"),
 ('Turing.streamStartCfg', "example {K : ℕ} {S : Type} (z : List Bool) (j : Fin K) (q : S) (s : List Bool) :\n    (streamStartCfg z j q s).inputPos = 1 := rfl"),
 ('Turing.NDTM.runWith', "example {k : ℕ} {S : Type} {x : List Bool} (tm : NDTM k Bool S) (c : Cfg k Bool S x) :\n    tm.runWith [] c = c := rfl"),
 ('Turing.NDTM.initCfg', "example {k : ℕ} {S : Type} (tm : NDTM k Bool S) (x : List Bool) :\n    tm.initCfg x = Cfg.init tm.q₀ x := rfl"),
 ('Turing.FinNDTM.AcceptsWithin', "example (N : FinNDTM Bool) (x : List Bool) (t : ℕ) : N.AcceptsWithin x t =\n    ∃ w : List Bool, w.length = t ∧ (N.tm.runWith w (N.tm.initCfg x)).state = none ∧\n      (N.tm.runWith w (N.tm.initCfg x)).output = [true] := rfl"),
 ('Turing.NDTM.HaltsWithin', "example {k : ℕ} {S : Type} (tm : NDTM k Bool S) (x : List Bool) (t : ℕ) : tm.HaltsWithin x t =\n    ∀ w : List Bool, w.length = t → (tm.runWith w (tm.initCfg x)).state = none := rfl"),
 ('Turing.CodeNDTM.toFinNDTM', "example (M : CodeNDTM) : M.toFinNDTM.k = 2 := rfl"),
 ('Turing.GuessRunPhase.State', "example (SP SQ : Type) : GuessRunPhase.State SP SQ .pre = SP := rfl"),
]
SIMPC = [
 ('Turing.Action.apply', "example {k : ℕ} {S : Type} {x : List Bool} (a : Action k Bool S) (c : Cfg k Bool S x) :\n    (a.apply c).state = a.state := by simp"),
 ('Turing.Cfg.init', "example {k : ℕ} {S : Type} (q : S) (x : List Bool) :\n    (Cfg.init (k := k) (Symbol := Bool) q x).inputPos = 1 := by simp"),
 ('Turing.MultiTapeTM.initCfg', "example {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S) (x : List Bool) :\n    (tm.initCfg x).output = [] := by simp"),
 ('Turing.NDTM.initCfg', "example {k : ℕ} {S : Type} (tm : NDTM k Bool S) (x : List Bool) :\n    (tm.initCfg x).output = [] := by simp"),
]
assert sorted(n for n, _ in C) == sorted(SEAL), set(SEAL) ^ set(n for n, _ in C)
def controls(tag, simp=True):
    out = []
    for i, (n, s) in enumerate(C + (SIMPC if simp else []), 1):
        kind = 'by simp' if i > len(C) else 'rfl'
        out.append(f'/-- Control {tag}-{i}: closes only by unfolding `{n}` ({kind}). -/\n{s}\n')
    return '\n'.join(out)
def attrs(names, simp):
    a = ''.join(f'attribute [local irreducible] {n}\n' for n in names)
    if simp: a += ''.join(f'attribute [-simp] {n}\n' for n in SIMP)
    return a
def variant(names, simp, ctl, start, sec):
    pre = L[:start]; mid = L[start:iend]; post = L[iend:]
    top = f'section {sec}\n' + attrs(names, simp) + ('\n' + controls('top') if ctl else '')
    end = ('\n' + controls('end') if ctl else '') + f'\nend {sec}\n'
    return '\n'.join(pre) + '\n' + top + '\n'.join(mid) + '\n' + end + '\n'.join(post)
os.makedirs(outd, exist_ok=True)
open(os.path.join(outd, 'UNSealS1.lean'), 'w', encoding='utf-8').write(variant(SEAL, False, True, NS, 'UNSeal'))
open(os.path.join(outd, 'UNSealS2.lean'), 'w', encoding='utf-8').write(variant(SEAL, True, True, NS, 'UNSeal'))
wsrc = variant(['Turing.' + n for n in WORKER], False, False, HOME, 'UNWorkerSeal')
wsrc = wsrc.replace('\nend UNWorkerSeal\n', '\nexample : pairEncode [] [] = [false, true] := rfl\n\nend UNWorkerSeal\n', 1)
open(os.path.join(outd, 'UNSealWorker.lean'), 'w', encoding='utf-8').write(wsrc)
hdr = '\n'.join(imps) + '\n\nnamespace Turing\n\n'
open(os.path.join(outd, 'UNControlUnsealed.lean'), 'w', encoding='utf-8').write(hdr + controls('unsealed') + '\nend Turing\n')
open(os.path.join(outd, 'UNControlSealed.lean'), 'w', encoding='utf-8').write(hdr + 'section UNSeal\n' + attrs(SEAL, True) + '\n' + controls('sealed') + '\nend UNSeal\n\nend Turing\n')
print('controls', len(C), '+', len(SIMPC), 'seal', len(SEAL), 'worker', len(WORKER), 'end Turing at', iend + 1)
