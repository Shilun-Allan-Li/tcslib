"""wrap.py <NDCodeSimulator.lean>: rewrap the five lines the re-point pushed past 100 characters."""
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
def rep(a, b, n=1):
    global s
    c = s.count(a); assert c == n, (a[:60], c); s = s.replace(a, b)
rep("  let St₂ : Type := ((prefixCanonTM (FinTM.pairExtractTM true false)).State ⊕ Unit) ⊕ InputRewindPhase\n",
    "  let St₂ : Type :=\n    ((prefixCanonTM (FinTM.pairExtractTM true false)).State ⊕ Unit) ⊕ InputRewindPhase\n")
rep("  have hd₇st : ((e₆.mapState (Sum.inr : _ → St₆)).mapState (fun _ => InputRewindPhase.start)).state =\n      some .start := by\n",
    "  have hd₇st :\n      ((e₆.mapState (Sum.inr : _ → St₆)).mapState (fun _ => InputRewindPhase.start)).state =\n        some .start := by\n")
rep("    show ((e₆.mapState (Sum.inr : _ → St₆)).mapState (fun _ => InputRewindPhase.start)).workTapes j q = _\n",
    "    show ((e₆.mapState (Sum.inr : _ → St₆)).mapState\n      (fun _ => InputRewindPhase.start)).workTapes j q = _\n")
rep("    show ((e₆.mapState (Sum.inr : _ → St₆)).mapState (fun _ => InputRewindPhase.start)).workTapePos j = _\n",
    "    show ((e₆.mapState (Sum.inr : _ → St₆)).mapState\n      (fun _ => InputRewindPhase.start)).workTapePos j = _\n")
rep("  set TPRE := T₁ + 1 + ((e₁.mapState (fun _ => InputRewindPhase.start)).inputPos.val + 1) + 1 + T₃ + 1 +\n",
    "  set TPRE := T₁ + 1 + ((e₁.mapState (fun _ => InputRewindPhase.start)).inputPos.val + 1) + 1 +\n    T₃ + 1 +\n")
bad = [(i, len(l)) for i, l in enumerate(s.split('\n'), 1) if len(l) > 100]
assert not bad, bad
open(p, 'w', encoding='utf-8').write(s)
print('ok')
