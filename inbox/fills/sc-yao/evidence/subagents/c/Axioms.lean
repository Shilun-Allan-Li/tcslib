import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.OTInputs
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TwoMoveViews
import Lean

set_option maxErrors 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_spEncStr_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_spEncStr_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.encodeMsgs_eq_encWords
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.encodeMsgs_eq_encWords
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledRow_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledRow_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledTable_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledTable_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTable_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTable_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTables_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTables_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_keys_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_keys_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_message_of_parts_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_message_of_parts_le
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_layout
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_layout
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputA
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputA
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_layout
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_layout
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputB
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputB
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcriptWith_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcriptWith_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcript_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcript_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewP_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewP_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewV_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewV_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewP_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewP_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewV_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewV_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outV_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outV_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outP_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outP_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realA_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realA_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realB_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realB_eq

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_spEncStr_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_nestedSpecial_enc_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.encodeMsgs_eq_encWords,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledRow_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_garbledTable_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTable_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_garbledTables_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_keys_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_encoded_pairs_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.length_message_of_parts_le,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputA_layout,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputA,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.otInputB_layout,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs.polyTimeComputable_otInputB,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcriptWith_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.transcript_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewP_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.viewV_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewP_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.encode_viewV_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outV_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.outP_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realA_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews.realB_eq]
  for root in roots do
    let mut pending := [root]
    let mut seen : NameSet := {}
    let mut found : Array Name := #[]
    let mut count := 0
    while !pending.isEmpty do
      let current := pending.head!
      pending := pending.tail
      if seen.contains current then
        continue
      seen := seen.insert current
      count := count + 1
      if let some info := env.find? current then
        if let some value := info.value? true then
          if value.hasSorry then
            found := found.push current
        pending := info.getUsedConstantsAsSet.toList ++ pending
    logInfo m!"DEPENDENCY {root}: closure={count} sorried={found}"
