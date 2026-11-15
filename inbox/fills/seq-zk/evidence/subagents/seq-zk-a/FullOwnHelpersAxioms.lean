import TCSlib.Cryptography.Composability.SequentialZK.Normalization
import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
import TCSlib.Cryptography.Composability.SequentialZK.Statistical
import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalRecursion
import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPrefix
import TCSlib.Cryptography.Composability.SequentialZK.BoundedMetadata
import TCSlib.Cryptography.Composability.SequentialZK.RealPrefixBounds

open TCSlib.Cryptography TCSlib.Cryptography.SequentialZK

example (n a v q h : ℕ) : Fintype (PhaseMetadata n a v q h) := inferInstance
example (n a v q h : ℕ) : Nonempty (PhaseMetadata n a v q h) := inferInstance

#print axioms TCSlib.Cryptography.SequentialZK.encodeMsgs_eq_encWords
#print axioms TCSlib.Cryptography.SequentialZK.normalizeMsgs
#print axioms TCSlib.Cryptography.SequentialZK.normalizeMsgs_eq
#print axioms TCSlib.Cryptography.SequentialZK.length_normalizeMsgs
#print axioms TCSlib.Cryptography.SequentialZK.length_le_of_mem_normalizeMsgs
#print axioms TCSlib.Cryptography.SequentialZK.normalizeMsgs_encodeMsgs
#print axioms TCSlib.Cryptography.SequentialZK.length_encodeMsgs_normalizeMsgs_le
#print axioms TCSlib.Cryptography.SequentialZK.polyTimeComputable_encWords_decWords
#print axioms TCSlib.Cryptography.SequentialZK.polyTimeComputable_decWords_getD
#print axioms TCSlib.Cryptography.SequentialZK.polyTimeComputable_encode_normalizeMsgs
#print axioms TCSlib.Cryptography.SequentialZK.phaseViewPayload
#print axioms TCSlib.Cryptography.SequentialZK.phaseViewPayload_eq
#print axioms TCSlib.Cryptography.SequentialZK.normalizePhaseMsgs
#print axioms TCSlib.Cryptography.SequentialZK.normalizePhaseMsgs_eq
#print axioms TCSlib.Cryptography.SequentialZK.phaseViewPayload_of_encode
#print axioms TCSlib.Cryptography.SequentialZK.phaseViewPayload_of_ne
#print axioms TCSlib.Cryptography.SequentialZK.normalizePhaseMsgs_of_encode
#print axioms TCSlib.Cryptography.SequentialZK.length_normalizePhaseMsgs
#print axioms TCSlib.Cryptography.SequentialZK.length_le_of_mem_normalizePhaseMsgs
#print axioms TCSlib.Cryptography.SequentialZK.length_encodeMsgs_normalizePhaseMsgs_le
#print axioms TCSlib.Cryptography.SequentialZK.normalizePhaseMsgs_of_ne
#print axioms TCSlib.Cryptography.SequentialZK.polyTimeComputable_phaseViewPayload
#print axioms TCSlib.Cryptography.SequentialZK.polyTimeComputable_encode_normalizePhaseMsgs
#print axioms TCSlib.Cryptography.SequentialZK.statClose_average
#print axioms TCSlib.Cryptography.SequentialZK.statClose_chain
#print axioms TCSlib.Cryptography.SequentialZK.exec_snd_bounded
#print axioms TCSlib.Cryptography.SequentialZK.exec_snd_slice_bounded
#print axioms TCSlib.Cryptography.SequentialZK.length_encodeMsgs_exec_snd_le
#print axioms TCSlib.Cryptography.SequentialZK.statClose_recursion
#print axioms TCSlib.Cryptography.SequentialZK.normalizePhaseMsgs_viewV
#print axioms TCSlib.Cryptography.SequentialZK.statClose_normalized_step
#print axioms TCSlib.Cryptography.SequentialZK.PaddedProverSpec.statClose_step
#print axioms TCSlib.Cryptography.SequentialZK.PaddedProverSpec.statClose_prefix
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata_eq
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.toData
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.toData_eq
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.word_lengths
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.toData_length_le
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.cover
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.cover_data
#print axioms TCSlib.Cryptography.SequentialZK.PaddedProverSpec.realPrefix_bounds
