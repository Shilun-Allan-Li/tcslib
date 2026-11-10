import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Games.Bridges.Machines
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

#check @NUPPT.coinLen_eq
#check @decodeOracleMove_pairEncode_false
#check @decodeOracleMove_pairEncode_ofFn
#check @decodeOracleMove_true_two
#check @decodeOracleMove_pairEncode_false_of_length_ne
#check @decodeOracleMove_of_ne
#check @decodeFin_eq_some_iff
#check @decodeBitMove_query
#check @decodeBitMove_ret
#check @decodeBitMove_of_not_canonical
#check @GGMRed.stateLoopFun
#check @GGMRed.stateLoopFun_poly
#check @GGMRed.stateLoopFun_eval
#check @GGMRed.pairEncode_append_right
#check @NUPPT.exists_comp
#check @NUPPT.exists_split
#check @NUPPT.exists_withAdvice
#check @NUPPT.toCompOn_eq
#check @NUPPT.toCompOn_costBoundedBy
#check @simulate_costBoundedBy
#check @OracleComp.CostBoundedBy.bind
#check @NUPPT.ofPolyTimeUniform
#check @exists_handlerMachine
#check @exists_interactiveHandlerMachine
#check @exists_toCompOn_of_toComp
#check @exists_toOracleAdversary_of_bitCodec
#print axioms GGMRed.stateLoopFun_poly
#print axioms GGMRed.stateLoopFun_eval
#print axioms decodeOracleMove_of_ne
#print axioms decodeBitMove_of_not_canonical

attribute [local irreducible] decodeOracleMove decodeBitMove decodeFin
attribute [local irreducible] GGMRed.stateLoopFun StateLoop.orbit pairEncode pairSndD

theorem zeroWidthQuery (x : Fin 0 → Bool) :
    decodeBitMove (fun _ : Fin 1 => 0) (fun _ => 1) 1
      (pairEncode [false] (pairEncode [] (List.ofFn x))) = .query 0 x ∧
    decodeOracleMove 0 (pairEncode [false] (List.ofFn x)) = .query x := by
  exact ⟨decodeBitMove_query (fun _ : Fin 1 => 0) (fun _ => 1) 1 0 x,
    decodeOracleMove_pairEncode_ofFn 0 x⟩

theorem zeroWidthVerdict (b : Bool) :
    decodeBitMove (fun _ : Fin 1 => 0) (fun _ => 1) 1
      (pairEncode [true] [b]) = .ret (fun _ => b) ∧
    decodeOracleMove 0 [true, b] = .ret b := by
  exact ⟨by simpa only [List.ofFn_const, List.replicate_succ, List.replicate_zero] using
    decodeBitMove_ret (fun _ : Fin 1 => 0) (fun _ => 1) 1 (fun _ => b),
    decodeOracleMove_true_two 0 b⟩

theorem zeroWidthWrongLength :
    decodeOracleMove 0 (pairEncode [false] [true]) = .ret false :=
  decodeOracleMove_pairEncode_false_of_length_ne 0 (by decide)

theorem zeroWidthMalformed :
    decodeBitMove (fun _ : Fin 1 => 0) (fun _ => 1) 1 [] = .ret (zeroBits 1) ∧
    decodeOracleMove 0 [] = .ret false := by
  have hne (a b : List Bool) : [] ≠ pairEncode a b := by
    intro h
    have hlen := congrArg List.length h
    rw [List.length_nil, length_pairEncode] at hlen
    omega
  exact ⟨decodeBitMove_of_not_canonical (fun _ _ => hne _ _) (fun _ => hne _ _),
    decodeOracleMove_of_ne 0 (fun _ => hne _ _) (by intro b h; cases h)⟩

theorem toyOneRound :
    GGMRed.stateLoopFun (fun _ => [false]) (fun _ => [true])
      (fun w => w == pairEncode [] [true]) pairSndD (.const 1) (.const 1) [] = [true] := by
  have hOne : StateLoop.orbit (fun _ => [false]) (fun _ => [true]) [] 1 = [true] :=
    StateLoop.orbit_succ (fun _ => [false]) (fun _ => [true]) [] 0
  refine (GGMRed.stateLoopFun_eval _ _ _ _ _ _ [] 1 ?_ ?_ ?_ ?_).trans ?_
  · rw [PolyExpr.eval_const]
  · intro i hi
    have hcase : i = 0 ∨ i = 1 := by omega
    rcases hcase with rfl | rfl
    · simp only [StateLoop.orbit_zero, PolyExpr.eval_const]
      decide
    · simp only [hOne, PolyExpr.eval_const]
      decide
  · intro i hi
    have : i = 0 := by omega
    subst i
    rw [StateLoop.orbit_zero]
    have hne : pairEncode ([] : List Bool) [false] ≠ pairEncode [] [true] := by
      intro h
      have hs := congrArg pairSndD h
      rw [pairSndD_pairEncode, pairSndD_pairEncode] at hs
      cases hs
    simpa only [beq_eq_false_iff_ne] using hne
  · simp only [hOne, beq_self_eq_true]
  · simp only [hOne, pairSndD_pairEncode]

#print axioms toyOneRound
#print axioms zeroWidthMalformed
