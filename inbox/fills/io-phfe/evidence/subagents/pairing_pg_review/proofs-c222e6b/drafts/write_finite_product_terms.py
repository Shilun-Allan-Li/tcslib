from pathlib import Path
root=Path('/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange')
out=Path('/private/tmp/io-phfe-drafts/proofs-pairing')
s=(root/'TCSlib/Cryptography/Pairing/Exponents.lean').read_text()
terms={}
for name,base,typ,reader,add,mul in [
 ('groupDot_expVec','g','B.G','expVec_apply','pow_val_add','pow_val_mul'),
 ('groupDot_expVecT','gT','B.GT','expVecT_apply','pow_val_add_GT','pow_val_mul_GT')]:
 terms[name]=f'''  let exponentMap : ZMod B.order →+ Additive {typ} :=
    {{ toFun := fun x => Additive.ofMul ({base} ^ x.val)
      map_zero' :=
        (show Additive.ofMul ({base} ^ (0 : ZMod B.order).val) = (0 : Additive {typ}) from
          congrArg Additive.ofMul
            ((congrArg (fun n : ℕ => {base} ^ n) (ZMod.val_zero (n := B.order))).trans
              (pow_zero {base})))
      map_add' := fun x y =>
        (show Additive.ofMul ({base} ^ (x + y).val) =
            Additive.ofMul ({base} ^ x.val) + Additive.ofMul ({base} ^ y.val) from
          congrArg Additive.ofMul (B.{add} {base} x y)) }}
  have hSum : {base} ^ (dotProduct a b).val = ∏ i, {base} ^ (a i * b i).val :=
    (show {base} ^ (dotProduct a b).val = (∑ i, exponentMap (a i * b i)).toMul from
      congrArg Additive.toMul (map_sum exponentMap (fun i => a i * b i) Finset.univ)).trans
      (show (∑ i, exponentMap (a i * b i)).toMul = ∏ i, {base} ^ (a i * b i).val from
        toMul_sum Finset.univ (fun i => exponentMap (a i * b i)))
  have hCoordinate : ∀ i, (B.{reader.removesuffix('_apply')} {base} a i) ^ (b i).val =
      {base} ^ (a i * b i).val :=
    fun i => (congrArg (fun x : {typ} => x ^ (b i).val) (B.{reader} {base} a i)).trans
      ((pow_mul {base} (a i).val (b i).val).symm.trans (B.{mul} {base} (a i) (b i)).symm)
  (groupDot_eq (B.{reader.removesuffix('_apply')} {base} a) b).trans
    ((Finset.prod_congr rfl (fun i _ => hCoordinate i)).trans hSum.symm)'''
terms['expMat_mulVec']='''  funext fun i =>
    (groupMulVec_apply (B.expMat g M) a i).trans
      ((congrArg (fun row : κ → B.G => groupDot row a)
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)).trans
        ((B.groupDot_expVec g (M i) a).trans
          (show g ^ (dotProduct (M i) a).val = B.expVec g (M *ᵥ a) i from
            (B.expVec_apply g (M *ᵥ a) i).symm)))'''
terms['expVec_vecMul']='''  funext fun j =>
    (groupVecMul_apply a (B.expMat g M) j).trans
      ((congrArg (fun column : ι → B.G => groupDot column a)
        (funext fun i => (B.expMat_apply g M i j).trans
          (B.expVec_apply g (fun i => M i j) i).symm)).trans
        ((B.groupDot_expVec g (fun i => M i j) a).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (dotProduct_comm (fun i => M i j) a)).trans
            (show g ^ (dotProduct a (fun i => M i j)).val = B.expVec g (a ᵥ* M) j from
              (B.expVec_apply g (a ᵥ* M) j).symm))))'''
terms['expMat_mul']='''  funext fun i => funext fun j =>
    (groupMatMul_apply (B.expMat g M) N i j).trans
      ((congrArg (fun row : κ → B.G => groupDot row (fun k => N k j))
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)).trans
        ((B.groupDot_expVec g (M i) (fun k => N k j)).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
            (B.expMat_apply g (M * N) i j).symm)))'''
terms['expMat_mul_left']='''  funext fun i => funext fun j =>
    (matMulGroup_apply M (B.expMat g N) i j).trans
      ((congrArg (fun column : κ → B.G => groupDot column (M i))
        (funext fun k => (B.expMat_apply g N k j).trans
          (B.expVec_apply g (fun k => N k j) k).symm)).trans
        ((B.groupDot_expVec g (fun k => N k j) (M i)).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (dotProduct_comm (fun k => N k j) (M i))).trans
            ((congrArg (fun x : ZMod B.order => g ^ x.val)
              (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
              (B.expMat_apply g (M * N) i j).symm))))'''
terms['expMatT_mulVec']='''  funext fun i =>
    (groupMulVec_apply (B.expMatT gT M) a i).trans
      ((congrArg (fun row : κ → B.GT => groupDot row a)
        (funext fun k => (B.expMatT_apply gT M i k).trans
          (B.expVecT_apply gT (M i) k).symm)).trans
        ((B.groupDot_expVecT gT (M i) a).trans
          (show gT ^ (dotProduct (M i) a).val = B.expVecT gT (M *ᵥ a) i from
            (B.expVecT_apply gT (M *ᵥ a) i).symm)))'''
terms['pair_expVec']='''  (B.pairVec_eq (B.expVec g a) (B.expVec h b)).trans
    ((Finset.prod_congr rfl (fun i _ =>
      (congrArg₂ B.pair (B.expVec_apply g a i) (B.expVec_apply h b i)).trans
        ((B.bilinear_pow g h (a i).val (b i).val).trans
          ((pow_mul (B.pair g h) (a i).val (b i).val).trans
            (congrArg (fun x : B.GT => x ^ (b i).val)
              (B.expVecT_apply (B.pair g h) a i).symm))))).trans
      ((groupDot_eq (B.expVecT (B.pair g h) a) b).symm.trans
        (B.groupDot_expVecT (B.pair g h) a b)))'''
terms['pair_expMat']='''  funext fun i => funext fun j =>
    (B.pairMat_apply (B.expMat g M) (B.expMat h N) i j).trans
      ((congrArg₂ B.pairVec
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)
        (funext fun k => (B.expMat_apply h N k j).trans
          (B.expVec_apply h (fun k => N k j) k).symm)).trans
        ((B.pair_expVec g h (M i) (fun k => N k j)).trans
          ((congrArg (fun x : ZMod B.order => B.pair g h ^ x.val)
            (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
            (B.expMatT_apply (B.pair g h) (M * N) i j).symm)))'''
for name,term in terms.items():
 pos=s.index('theorem '+name+' ');start=s.rfind('/--',0,pos);end=s.index(':= sorry',pos)
 frag=s[start:end]+':=\n'+term+'\n'
 (out/(name+'.proof.lean.inc')).write_text(frag)
 print(name,len(frag.splitlines()),max(map(len,frag.splitlines())))
print('No new public helper or live edit; copied existing headers/docstrings exactly.')
