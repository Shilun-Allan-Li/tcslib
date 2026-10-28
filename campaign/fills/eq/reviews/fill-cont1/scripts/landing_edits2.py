"""The review's landing edits on the head file (python3 -I).  Every edit is asserted against the
head's text at its head line number before it is applied (E1, E3, E4), and the blank-line
deletions (E2) are applied last, bottom up.
  E1  campaign labels out of 22 docstring lines ("(checkpoint N)", "leaf L3", "leaf L6", "L2",
      "L6's") — text only;
  E2  the seven double blank lines in region (b) become single;
  E3  `qy_bits_len_mono` and `qy_lt_two_pow_bits` cite Mathlib (`Nat.size_le_size`,
      `Nat.lt_size_self`, through `Nat.size_eq_bits_len`) instead of re-deriving them;
  E4  the module header's status line for the target: "(sorried; C1-E's first fill)" ->
      "(proved)" (header line 69).
usage: python3 -I landing_edits2.py <head.lean> <out.lean> [E1 E2 E3 E4 ...]  (default: all)"""
import sys
src, out = sys.argv[1:3]
which = set(sys.argv[3:]) or {'E1', 'E2', 'E3', 'E4'}
L = open(src, encoding='utf-8').read().split('\n')
assert len(L) == 5403, len(L)
def sub(n, old, new):
    l = L[n - 1]
    assert l.count(old) == 1, (n, old, l)
    L[n - 1] = l.replace(old, new)
E1 = [(1000, ' (leaf L3, the unary compare).', '.'),
      (1197, ' (leaf L6).', '.'),
      (3049, ' (checkpoint 2):', ':'), (3176, ' (checkpoint 2):', ':'),
      (3395, ' (checkpoint 3):', ':'), (3535, ' (checkpoint 3):', ':'),
      (3542, '(L2, `qy_cmp_run`;', '(`qy_cmp_run`;'),
      (3905, ' (checkpoint 3):', ':'), (4019, ' (checkpoint 3):', ':'),
      (4023, '`k` (L2), then', '`k`, then'),
      (4208, ' (checkpoint 3), as', ', as'),
      (4392, ' (checkpoint 4):', ':'), (4601, ' (checkpoint 5):', ':'),
      (4669, ' (checkpoint 5):', ':'), (4692, ' (checkpoint 5):', ':'),
      (4722, ' (checkpoint 5):', ':'),
      (4757, "(L6's three emissions)", "(three emissions)"),
      (4826, ' (checkpoint 6):', ':'), (4918, ' (checkpoint 6):', ':'),
      (5096, ' (checkpoint 7):', ':'), (5207, ' (checkpoint 7):', ':'),
      (5255, '(checkpoint 7, the target', '(the target')]
assert len(E1) == 22
if 'E1' in which:
    for n, o, w in E1: sub(n, o, w)
if 'E3' in which:
    a = L[3224 - 1:3231 - 1]
    assert a == ['private theorem qy_bits_len_mono {a b : ℕ} (h : a ≤ b) :',
                 '    (Nat.bits a).length ≤ (Nat.bits b).length := by',
                 '  rcases Nat.eq_zero_or_pos a with rfl | ha',
                 '  · rw [Nat.zero_bits, List.length_nil]',
                 '    exact Nat.zero_le _',
                 '  · rw [← qy_log_bits ha, ← qy_log_bits (ha.trans_le h)]',
                 '    exact Nat.succ_le_succ (Nat.log_mono_right h)'], a
    b = L[3233 - 1:3239 - 1]
    assert b == ['private theorem qy_lt_two_pow_bits (n : ℕ) : n < 2 ^ (Nat.bits n).length := by',
                 '  rcases Nat.eq_zero_or_pos n with rfl | hn',
                 '  · rw [Nat.zero_bits, List.length_nil]',
                 '    exact Nat.one_pos',
                 '  · rw [← qy_log_bits hn]',
                 '    exact Nat.lt_pow_succ_log_self (by norm_num) n'], b
    assert L[3231 - 1] == '' and L[3239 - 1] == '' and L[3232 - 1].startswith('/-- Every number'), (L[3230], L[3238])
    newa = a[:2] + ['  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]',
                    '  exact Nat.size_le_size h']
    newb = b[:1] + ['  rw [Nat.size_eq_bits_len]', '  exact Nat.lt_size_self n']
    # replace b first (later lines), then a
    L[3233 - 1:3239 - 1] = newb
    L[3224 - 1:3231 - 1] = newa
    shift = (len(newa) - len(a)) + (len(newb) - len(b))
else:
    shift = 0
if 'E4' in which:
    sub(69, '(sorried; C1-E\'s first fill)', '(proved)')
if 'E2' in which:
    blanks = [630, 1027, 1183, 1652, 1896, 2250, 2531]
    for n in sorted(blanks, reverse=True):
        assert L[n - 1] == '' and L[n] == '', (n, L[n - 1], L[n])
        del L[n]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('applied', sorted(which), '; lines', len(L) - 1, '(head 5402)')
