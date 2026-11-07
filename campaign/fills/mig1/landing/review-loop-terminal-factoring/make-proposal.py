"""Produce an inert proof-only proposal; never write the actual Loop source."""
from pathlib import Path
import difflib
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
ns = {}
tool = (ROOT / 'devtools/seyoon/declfreeze.py').read_text()
exec(compile(tool.split('a = chunks(')[0], 'trusted-declfreeze-helper', 'exec'), ns)
chunks = ns['chunks']


def assignment(s):
    stack = []
    comment = 0
    string = False
    i = 0
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    while i < len(s):
        if comment:
            if s.startswith('/-', i):
                comment += 1
                i += 2
                continue
            if s.startswith('-/', i):
                comment -= 1
                i += 2
                continue
            i += 1
            continue
        if string:
            if s[i] == '\\':
                i += 2
                continue
            if s[i] == '"':
                string = False
            i += 1
            continue
        if s.startswith('/-', i):
            comment = 1
            i += 2
            continue
        if s.startswith('--', i):
            end = s.find('\n', i)
            i = len(s) if end < 0 else end + 1
            continue
        c = s[i]
        if c == '"':
            string = True
        elif c in '([{⟨':
            stack.append(c)
        elif c in pairs:
            assert stack and stack.pop() == pairs[c], (i, c)
        elif not stack and s.startswith(':=', i):
            return i
        i += 1
    return None


def split(s):
    i = assignment(s)
    return (s, None) if i is None else (s[:i], s[i + 2:])


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


before = (OUT / 'Loop-before.lean.txt').read_text()
before_chunks = chunks(before)
A = {name: (private, text) for name, private, text in before_chunks}
names = ['loopHostTM_decides', 'loopHostTM_finds', 'emitLoopTM_computes']
qualified = ['Turing.FinTM.' + name for name in names]
helper_name = 'Turing.FinTM.loop_computes_of_startup'
assert helper_name not in A
helper = '''/-- A bounded startup followed by a halted segment yields a computation in time
`B * (N + 1)` when startup costs at most `B` and the segment costs at most `N * B`.

**Proof sketch.** Compose the two runs with `MultiTapeTM.runFrom_add`, read the halt and
output with `computesInTime_iff`, and enlarge the summed time by `ComputesInTime.mono`. -/
private theorem loop_computes_of_startup (M : FinTM Bool) (x output : List Bool)
    (c : Cfg M.k Bool M.State x) (startup t B N : ℕ)
    (hs : startup ≤ B) (hinit : M.tm.runFrom (M.tm.initCfg x) startup = c)
    (ht : t ≤ N * B) (hhalt : (M.tm.runFrom c t).state = none)
    (hout : (M.tm.runFrom c t).output = output) :
    M.ComputesInTime x output (B * (N + 1)) := by
  have hrun := M.tm.runFrom_add (M.tm.initCfg x) startup t
  rw [hinit] at hrun
  have hcompute : M.ComputesInTime x output (startup + t) := by
    refine (computesInTime_iff _ _ _ _).mpr ⟨?_, ?_⟩
    · rw [hrun]; exact hhalt
    · rw [hrun]; exact hout
  apply hcompute.mono
  calc startup + t ≤ B + N * B := Nat.add_le_add hs ht
    _ = B * (N + 1) := by rw [Nat.mul_succ, Nat.mul_comm N, Nat.add_comm]

'''
suffix_start = '  have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t\n'
after = before
replacement_rows = []
for name in qualified:
    original = A[name][1]
    assert original.count(suffix_start) == 1, name
    prefix, suffix = original.split(suffix_start)
    if name.endswith('emitLoopTM_computes'):
        call = '''  exact loop_computes_of_startup E x _ (candidate 0) startup t
    (10 * (T x.length + 1)) (R x.length + 1) hs hinit ht hhalt
    (by simpa only [List.nil_append, orbit] using houtput)'''
    else:
        call = '''  exact loop_computes_of_startup E x _ (cfg 0) startup t
    (10 * (T x.length + 1)) (R x.length + 1) hs hinit ht hhalt houtput'''
    new = prefix + call
    assert before.count(original) == after.count(original) == 1
    after = after.replace(original, new, 1)
    replacement_rows.append(dict(name=name, old_suffix=suffix_start + suffix,
                                 new_suffix=call, prefix_sha256=sha(prefix),
                                 prefix_literal_equal=True))
first_doc = A[qualified[0]][1].split('theorem loopHostTM_decides', 1)[0]
assert after.count(first_doc) == 1
after = after.replace(first_doc, helper + first_doc, 1)
B = {name: (private, text) for name, private, text in chunks(after)}
assert set(B) - set(A) == {helper_name}
assert not set(A) - set(B)
assert B[helper_name][0]
assert [name for name, _, _ in chunks(after) if name in A] == [name for name, _, _ in before_chunks]
rows = []
for name, (private, text) in A.items():
    next_private, next_text = B[name]
    h0, b0 = split(text)
    h1, b1 = split(next_text)
    assert private == next_private and h0 == h1, name
    if name not in qualified:
        assert text == next_text, name
    rows.append(dict(name=name, private=private, header_literal_equal=True,
                     declaration_literal_equal=text == next_text,
                     header_sha256=sha(h0), body_sha256_before=sha(b0) if b0 else None,
                     body_sha256_after=sha(b1) if b1 else None))
assert re.findall(r'^import .*', before, re.M) == re.findall(r'^import .*', after, re.M)
output = OUT / 'Loop-proposed-v1.lean.txt'
assert not output.exists()
output.write_text(after)
(OUT / 'Loop-body-only-v1.patch').write_text(''.join(difflib.unified_diff(
    before.splitlines(keepends=True), after.splitlines(keepends=True),
    fromfile='a/TCSlib/Complexity/TuringMachine/Build/Loop.lean',
    tofile='b/TCSlib/Complexity/TuringMachine/Build/Loop.lean')))
freeze = dict(source_sha256=sha(before), proposed_sha256=sha(after),
              source_bytes=len(before.encode()), proposed_bytes=len(after.encode()),
              public_before=sum(not p for p, _ in A.values()),
              public_after=sum(not p for p, _ in B.values()),
              private_before=sum(p for p, _ in A.values()),
              private_after=sum(p for p, _ in B.values()),
              added=[helper_name], removed=[], changed=qualified,
              all_shared_headers_and_docstrings_literal_equal=True,
              all_other_declarations_literal_equal=True,
              imports_order_equal=True, retained_relative_order_equal=True,
              no_actual_source_write=True, preserved_prefixes=replacement_rows,
              declarations=rows)
(OUT / 'freeze-v1.json').write_text(json.dumps(freeze, indent=2) + '\n')
print(json.dumps({k: v for k, v in freeze.items() if k not in ['declarations', 'preserved_prefixes']}, indent=2))
