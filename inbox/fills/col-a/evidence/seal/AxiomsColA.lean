import TCSlib.Cryptography.ZeroKnowledge.NP
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Simulator
open TCSlib.Cryptography
-- the filled targets
#print axioms R3COL_witnessRelation
#print axioms colRep_efficientProverProof
-- their consumers
#print axioms colRep_interactiveProof
#print axioms col_zeroKnowledgeProof
#print axioms zk_proof_of_levinReduction
#print axioms zk_proof_of_owp_levinReduction
#print axioms exists_commitment_zk_proof_of_owp_levinReduction
#print axioms zk_proof_of_witnessRelation
#print axioms zk_proof_of_witnessRelation_of_owp
#print axioms zk_proof_of_mem_NP
#print axioms zk_proof_of_mem_NP_of_owp
-- the new public declarations of the helper modules
#print axioms ColRep.decGraph_fst
#print axioms ColRep.r3colTest_eq
#print axioms ColRep.r3colTest_iff
#print axioms ColRep.r3colTest_poly
#print axioms ColRep.R3COL_decidable
#print axioms ColRep.chView_zero
#print axioms ColRep.chView_succ
#print axioms ColRep.length_chView
#print axioms ColRep.chView_congr
#print axioms ColRep.exec_four_mul
#print axioms ColRep.blockRead_eq
#print axioms ColRep.pushesUniform_blockRead
#print axioms ColRep.drop_take_ofFn_blockRead
#print axioms ColRep.statClose_edgeBlocks
#print axioms ColRep.mul_edgeCount_le
