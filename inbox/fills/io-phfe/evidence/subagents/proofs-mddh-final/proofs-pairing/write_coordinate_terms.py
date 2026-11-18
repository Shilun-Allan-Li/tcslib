from pathlib import Path
root=Path('/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange')
out=Path('/private/tmp/io-phfe-drafts/proofs-pairing')
s=(root/'TCSlib/Cryptography/Pairing/Exponents.lean').read_text()
terms={
'pow_val_add_GT': '''  (congrArg (fun n : ℕ => gT ^ n) (ZMod.val_add a b)).trans
    ((congrArg (fun n : ℕ => gT ^ ((a.val + b.val) % n)) B.card_GT).symm.trans
      ((pow_mod_card gT (a.val + b.val)).trans (pow_add gT a.val b.val)))''',
'pow_val_neg_GT': '''  eq_inv_iff_mul_eq_one.mpr
    ((B.pow_val_add_GT gT (-a) a).symm.trans
      ((congrArg (fun z : ZMod B.order => gT ^ z.val) (neg_add_cancel a)).trans
        ((congrArg (fun n : ℕ => gT ^ n) (ZMod.val_zero (n := B.order))).trans
          (pow_zero gT))))''',
'expVec_neg': '''  funext fun i =>
    (B.expVec_apply g (-a) i).trans
      ((B.pow_val_neg g (a i)).trans
        (congrArg (fun x : B.G => x⁻¹) (B.expVec_apply g a i).symm))''',
'expVec_smul': '''  funext fun i =>
    (show B.expVec g (c • a) i = g ^ (c * a i).val from
      B.expVec_apply g (c • a) i).trans
      ((B.pow_val_mul g c (a i)).trans
        ((congrArg (fun n : ℕ => g ^ n) (Nat.mul_comm c.val (a i).val)).trans
          ((pow_mul g (a i).val c.val).trans
            (congrArg (fun x : B.G => x ^ c.val) (B.expVec_apply g a i).symm))))''',
'expVecT_add': '''  funext fun i =>
    (B.expVecT_apply gT (a + b) i).trans
      ((B.pow_val_add_GT gT (a i) (b i)).trans
        (congrArg₂ (fun x y : B.GT => x * y)
          (B.expVecT_apply gT a i).symm (B.expVecT_apply gT b i).symm))''',
'expVecT_neg': '''  funext fun i =>
    (B.expVecT_apply gT (-a) i).trans
      ((B.pow_val_neg_GT gT (a i)).trans
        (congrArg (fun x : B.GT => x⁻¹) (B.expVecT_apply gT a i).symm))''',
'expVecT_smul': '''  funext fun i =>
    (show B.expVecT gT (c • a) i = gT ^ (c * a i).val from
      B.expVecT_apply gT (c • a) i).trans
      ((B.pow_val_mul_GT gT c (a i)).trans
        ((congrArg (fun n : ℕ => gT ^ n) (Nat.mul_comm c.val (a i).val)).trans
          ((pow_mul gT (a i).val c.val).trans
            (congrArg (fun x : B.GT => x ^ c.val) (B.expVecT_apply gT a i).symm))))''',
'pairTensor_expVec': '''  funext fun ij =>
    (B.pairTensor_apply (B.expVec g a) (B.expVec h b) ij).trans
      ((congrArg₂ B.pair (B.expVec_apply g a ij.1) (B.expVec_apply h b ij.2)).trans
        ((B.bilinear_pow g h (a ij.1).val (b ij.2).val).trans
          ((B.pow_val_mul_GT (B.pair g h) (a ij.1) (b ij.2)).symm.trans
            (B.expVecT_apply (B.pair g h)
              (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm)))''',
'expVec_tensor_left': '''  funext fun ij =>
    (congrArg (fun x : B.G => x ^ (b ij.2).val) (B.expVec_apply g a ij.1)).trans
      ((pow_mul g (a ij.1).val (b ij.2).val).symm.trans
        ((B.pow_val_mul g (a ij.1) (b ij.2)).symm.trans
          (B.expVec_apply g (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm))''',
'expVec_tensor_right': '''  funext fun ij =>
    (congrArg (fun x : B.G => x ^ (a ij.1).val) (B.expVec_apply g b ij.2)).trans
      ((pow_mul g (b ij.2).val (a ij.1).val).symm.trans
        ((B.pow_val_mul g (b ij.2) (a ij.1)).symm.trans
          ((congrArg (fun z : ZMod B.order => g ^ z.val) (mul_comm (b ij.2) (a ij.1))).trans
            (B.expVec_apply g (fun ij : ι × κ => a ij.1 * b ij.2) ij).symm)))''',
}
for name,term in terms.items():
 pos=s.index('theorem '+name+' ')
 start=s.rfind('/--',0,pos)
 end=s.index(':= sorry',pos)
 fragment=s[start:end]+':=\n'+term+'\n'
 (out/(name+'.proof.lean.inc')).write_text(fragment)
 print(name,len(fragment.splitlines()),max(map(len,fragment.splitlines())))
print('No live edits; preserved headers/docstrings from the read source.')
