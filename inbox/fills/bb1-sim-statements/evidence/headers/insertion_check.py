r"""insertion_check.py <base-file> <head-file> <AFTER_LINE:BLOCK_FILE>... (bb1-sim-statements, lead).
Pure-insertion check: each block (the exact lines of BLOCK_FILE) must sit in <head-file> right after
base line AFTER_LINE (shifted by the blocks inserted above it); removing the blocks must give
<base-file> byte for byte. Prints each block's status, every difference of the remainder against the
base (difflib opcodes, base line numbers), both SHA-256s, and PASS or FAIL. Exit 0 iff PASS."""
import sys, hashlib, difflib
base_p, head_p, specs = sys.argv[1], sys.argv[2], sys.argv[3:]
rb, rh = open(base_p, 'rb').read(), open(head_p, 'rb').read()
base, head = rb.decode('utf-8').split('\n'), rh.decode('utf-8').split('\n')
blocks = []
for s in specs:
    n, f = s.split(':', 1)
    t = open(f, encoding='utf-8').read()
    blocks.append((int(n), t[:-1].split('\n'), f))
blocks.sort(key=lambda b: b[0])
ok, shift, keep = True, 0, [True] * len(head)
for n, bl, f in blocks:
    pos = n + shift
    at = head[pos:pos + len(bl)] == bl
    where = [i for i in range(len(head) - len(bl) + 1) if head[i:i + len(bl)] == bl]
    if at:
        print(f'BLOCK {f.rsplit("/", 1)[-1]}: at its anchor (after base line {n}; head lines '
              f'{pos + 1}-{pos + len(bl)})')
        for i in range(pos, pos + len(bl)): keep[i] = False
    else:
        ok = False
        print(f'BLOCK {f.rsplit("/", 1)[-1]}: NOT at its anchor (after base line {n}, head line '
              f'{pos + 1}); found at head lines {[w + 1 for w in where]}')
        if where:
            for i in range(where[0], where[0] + len(bl)): keep[i] = False
    shift += len(bl)
rest = [l for l, k in zip(head, keep) if k]
ops = [o for o in difflib.SequenceMatcher(a=base, b=rest, autojunk=False).get_opcodes() if o[0] != 'equal']
for tag, i1, i2, j1, j2 in ops:
    ok = False
    print(f'DIFF {tag}: base lines {i1 + 1}-{i2} ({i2 - i1}) vs remainder lines {j1 + 1}-{j2} ({j2 - j1})')
    for l in base[i1:i2]: print('  - ' + l)
    for l in rest[j1:j2]: print('  + ' + l)
print(f'differences: {len(ops)} ({", ".join(o[0] for o in ops) or "none"})')
print('base sha256', hashlib.sha256(rb).hexdigest(), base_p)
print('head sha256', hashlib.sha256(rh).hexdigest(), head_p)
print('PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
