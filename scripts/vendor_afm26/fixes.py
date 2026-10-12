# Per-module fixes for the v4.33.1 -> v4.25.0 port of [AFM26]; each must apply exactly once.
FIXES = {
 'ThreeSumApsp.Util.List': [
  ('List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i',
   'List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by simpa using hU) h i',
   'beta: v4.25 leaves the instantiated motive unreduced')],
 'ThreeSumApsp.Lang.Lib.Logs': [
  ('    rw [show 2 ^ (i + 1 + 1) = 2 ^ (i + 1) + 2 ^ (i + 1) by ring]',
   '    beta_reduce\n    rw [show 2 ^ (i + 1 + 1) = 2 ^ (i + 1) + 2 ^ (i + 1) by ring]',
   'beta: v4.25 leaves the loop rule\'s invariant applied to its round unreduced'),
  ('    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring]',
   '    beta_reduce\n    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring]',
   'beta: as above')],
 'ThreeSumApsp.Lang.Compiler.Cells': [
  ('  · simp [Int.toNat_of_nonneg hnonneg]\n  · rw [Function.update_of_ne (by omega)]',
   '  · rw [Function.update_apply, if_pos (by omega)]\n    simp\n  · rw [Function.update_of_ne (by omega)]',
   'simp: v4.25 does not rewrite the cast in this position')],
 'ThreeSumApsp.Lang.Compiler.CallFrames': [
  ('      split_ifs <;> rw [Function.update_of_ne (by cells), A.cell (by cells)]\n',
   '      split_ifs <;> rw [Function.update_of_ne (by cells), A.cell (by cells)] <;> simp [*]\n',
   'split_ifs: v4.25 leaves the `if` inside the argument')],
 'ThreeSumApsp.Lang.Lib.CountSort': [
  ('    rw [show A.nb - (r + 1) = s by omega]', '    beta_reduce\n    rw [show A.nb - (r + 1) = s by omega]', 'beta: loop invariant applied to its round')],
 'ThreeSumApsp.Lang.Lib.Emod': [
  ('    rw [hnext]', '    beta_reduce\n    rw [hnext]', 'beta: loop invariant applied to its round'),
  ('    rw [show emodRounds a Mo - (i + 1) = c by omega]', '    beta_reduce\n    rw [show emodRounds a Mo - (i + 1) = c by omega]', 'beta: as above')],
 'ThreeSumApsp.Lang.Lib.Sqrt': [
  ('    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]', '    beta_reduce\n    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]', 'beta: loop invariant applied to its round')],
}
