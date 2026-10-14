"""Append the pre-ship checks (fit examples and axiom prints) to the B6-F1 or B6-F2 overlay.

Usage: python3 -I mkchecks.py <overlay.lean> <checks.lean.txt> <out.lean>
The output is the overlay byte for byte, followed by the checks block (asserted)."""
import sys
ov_p, ch_p, out_p = sys.argv[1:4]
ov = open(ov_p, encoding='utf-8').read()
ch = open(ch_p, encoding='utf-8').read()
assert ov.endswith('end Turing\n') or ov.endswith('end Turing'), 'overlay end'
out = ov + ('' if ov.endswith('\n') else '\n') + ch
assert out.startswith(ov)
open(out_p, 'w', encoding='utf-8').write(out)
print(f'checks: {ch.count(chr(10))} lines appended; {ch.count("#print axioms")} axiom prints, '
      f'{ch.count("example")} examples')
