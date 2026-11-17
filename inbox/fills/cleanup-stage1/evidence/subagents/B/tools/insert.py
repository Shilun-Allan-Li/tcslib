"""Pure insertion helper (sub-agent B): insert a file's text after line N of a target,
checking that line N equals an expected string. Usage:
  python3 -I insert.py TARGET N EXPECTED_LINE BLOCKFILE"""
import sys
target, n, expected, block = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
lines = open(target, encoding='utf-8').read().split('\n')
if lines[n - 1] != expected:
    sys.exit(f"anchor mismatch at {target}:{n}: {lines[n-1]!r} != {expected!r}")
ins = open(block, encoding='utf-8').read()
if ins.endswith('\n'):
    ins = ins[:-1]
new = lines[:n] + ins.split('\n') + lines[n:]
open(target, 'w', encoding='utf-8').write('\n'.join(new))
print(f"inserted {len(ins.split(chr(10)))} lines after {target}:{n}")
