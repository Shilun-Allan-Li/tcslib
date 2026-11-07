"""Build a complete cumulative inert proposal; no actual source or Git writes."""
from pathlib import Path
import difflib
import hashlib
import json

OUT = Path(__file__).resolve().parent
namespace = {'__file__': str(OUT / 'proposal-tools.py')}
exec(compile((OUT / 'proposal-tools.py').read_text(), 'own-proposal-tools', 'exec'), namespace)
chunks, split, sha = namespace['chunks'], namespace['split'], namespace['sha']
before = (OUT / 'Loop-terminal-base.lean.txt').read_text()
A = {n: (p, t) for n, p, t in chunks(before)}
names = ['Turing.FinTM.emCall_bank_initial', 'Turing.FinTM.emCall_bank_final']
helper_name = 'Turing.FinTM.emCall_bank_embed'
assert helper_name not in A
helper = '''/-- Embedding one cleaner into a bank frame realizes any target cleaned prefix that
agrees with the original prefix away from the selected bank. The cleaner supplies exactly
the target bank's three tapes and common head, and its state supplies the target control.

**Proof sketch.** Apply `embedEmitCfg_mapState_eq`. The selected-bank equation is the
three-slot layout equation. Off the selection, the two administrative slots agree directly;
every other bank agrees because its cleaned-prefix membership is unchanged. -/
private lemma emCall_bank_embed (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (i : Fin M.k) (j : ℕ) (q : Fin 4)
    (hrest : ∀ l : Fin M.k, l ≠ i → (l.val < i.val ↔ l.val < j)) :
    let frame := emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))
    emCallEmbeddedCfg (emCallTripleEmbedding M i) (fun s => .inr (.inl (i.castSucc, s)))
      frame.workTapes frame.workTapePos
      (emCallClearCfg x 1 q
        (if i.val < j then fun _ => none else
          (M.tm.runFrom (M.tm.initCfg arg) T).workTapes i)
        (if i.val < j then fun _ => none else
          emCallSpan (emCallLo M arg T i) (emCallHi M arg T i))
        (if i.val < j then fun _ => none else bufferTape [true])
        (if i.val < j then 0 else (M.tm.runFrom (M.tm.initCfg arg) T).workTapePos i)) =
      emCallBankFrame M emit x arg cap T j (.inr (.inl (i.castSucc, q))) := by
  dsimp only
  simp only [emCallEmbeddedCfg]
  refine embedEmitCfg_mapState_eq _ _ _ _ [] _ _ ?_ ?_ ?_ ?_ ?_
  · simp only [emCallClearCfg, emCallBankFrame, emCallFrame, Option.map_some]
  · rfl
  · rfl
  · intro r
    fin_cases r <;> constructor <;>
      simp [emCallClearCfg, emCallBankFrame, emCallFrame, emCall_layout_triple]
  · intro k hk
    rcases emCall_layout_cases M k with h | h | ⟨l, r, h⟩
    · subst k
      constructor <;> simp only [emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst k
      constructor <;> simp only [emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst k
      have he : l ≠ i := by
        intro he
        subst l
        exact hk ⟨r, rfl⟩
      constructor <;> simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, hrest l he]

'''
bodies = [
''' by
  dsimp only
  simpa only [Nat.lt_irrefl, ↓reduceIte] using
    emCall_bank_embed M emit x arg cap T i i.val 0 (fun _ _ => Iff.rfl)''',
''' by
  dsimp only
  simpa only [Nat.lt_succ_self, ↓reduceIte] using
    emCall_bank_embed M emit x arg cap T i (i.val + 1) 3 (by
      intro l hl
      have hi : l.val ≠ i.val := fun h => hl (Fin.ext h)
      omega)'''
]
after = before
for name, body in zip(names, bodies):
    text = A[name][1]
    header, _ = split(text)
    assert text.count(header) == 1
    assert after.count(text) == 1
    after = after.replace(text, header + ':=' + body, 1)
first_header, _ = split(A[names[0]][1])
first_doc = first_header.split('private lemma emCall_bank_initial', 1)[0]
assert after.count(first_doc) == 1
after = after.replace(first_doc, helper + first_doc, 1)
B = {n: (p, t) for n, p, t in chunks(after)}
assert set(B) - set(A) == {helper_name} and not set(A) - set(B)
assert B[helper_name][0]


def compare(base, proposed, label, changed, added):
    X = {n: (p, t) for n, p, t in chunks(base)}
    Y = {n: (p, t) for n, p, t in chunks(proposed)}
    rows = []
    for n, (p, text) in X.items():
        p1, text1 = Y[n]
        h, b = split(text)
        h1, b1 = split(text1)
        assert p == p1 and h == h1, n
        if n not in changed:
            assert text == text1, n
        rows.append(dict(name=n, private=p, header_literal_equal=True,
                         declaration_literal_equal=text == text1,
                         header_sha256=sha(h), body_sha256_before=sha(b) if b else None,
                         body_sha256_after=sha(b1) if b1 else None))
    assert set(Y) - set(X) == set(added) and not set(X) - set(Y)
    assert all(Y[n][0] for n in added)
    assert [n for n, _, _ in chunks(proposed) if n in X] == [n for n, _, _ in chunks(base)]
    import re
    assert re.findall(r'^import .*', base, re.M) == re.findall(r'^import .*', proposed, re.M)
    result = dict(label=label, base_sha256=sha(base), proposed_sha256=sha(proposed),
                  public_before=sum(not p for p, _ in X.values()), public_after=sum(not p for p, _ in Y.values()),
                  private_before=sum(p for p, _ in X.values()), private_after=sum(p for p, _ in Y.values()),
                  changed=changed, added=added, removed=[], shared_count=len(X),
                  all_shared_headers_and_docstrings_literal_equal=True,
                  all_other_declarations_literal_equal=True, imports_order_equal=True,
                  retained_relative_order_equal=True, declarations=rows)
    (OUT / ('freeze-' + label + '-v1.json')).write_text(json.dumps(result, indent=2) + '\n')
    return {k: v for k, v in result.items() if k != 'declarations'}


proposed = OUT / 'Loop-cumulative-proposed-v1.lean.txt'
assert not proposed.exists()
proposed.write_text(after)
delta = ''.join(difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True),
    fromfile='a/TCSlib/Complexity/TuringMachine/Build/Loop.lean',
    tofile='b/TCSlib/Complexity/TuringMachine/Build/Loop.lean'))
(OUT / 'Loop-bank-only-v1.patch').write_text(delta)
live = (OUT / 'Loop-original-live.lean.txt').read_text()
cumulative = ''.join(difflib.unified_diff(live.splitlines(keepends=True), after.splitlines(keepends=True),
    fromfile='a/TCSlib/Complexity/TuringMachine/Build/Loop.lean',
    tofile='b/TCSlib/Complexity/TuringMachine/Build/Loop.lean'))
(OUT / 'Loop-cumulative-v1.patch').write_text(cumulative)
print(json.dumps(compare(before, after, 'terminal-base', names, [helper_name]), indent=2))
print(json.dumps(compare(live, after, 'original-live',
    ['Turing.FinTM.loopHostTM_decides', 'Turing.FinTM.loopHostTM_finds', 'Turing.FinTM.emitLoopTM_computes'] + names,
    ['Turing.FinTM.loop_computes_of_startup', helper_name]), indent=2))
roots = ['Turing.FinTM.loop_computes_of_startup', 'Turing.FinTM.loopHostTM_decides',
         'Turing.FinTM.loopHostTM_finds', 'Turing.FinTM.emitLoopTM_computes', helper_name] + names
suffix = '\n' + '\n'.join('#print axioms ' + n for n in roots) + '\n'
(OUT / 'Loop-native-v1.lean.txt').write_text(after + suffix)
(OUT / 'native-instrumentation-v1.json').write_text(json.dumps(dict(appendix=suffix,
    removal_restores_source_bytes=True, roots=roots), indent=2) + '\n')
