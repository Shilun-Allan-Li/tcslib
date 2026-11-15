import TCSlib.Cryptography.Composability.SequentialZK.BoundedMetadata
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPrefix

open TCSlib.Cryptography TCSlib.Cryptography.SequentialZK

example (n a v q h : ℕ) : Fintype (PhaseMetadata n a v q h) := inferInstance
example (n a v q h : ℕ) : Nonempty (PhaseMetadata n a v q h) := inferInstance

#print axioms TCSlib.Cryptography.SequentialZK.normalizePhaseMsgs_viewV
#print axioms TCSlib.Cryptography.SequentialZK.statClose_normalized_step
#print axioms TCSlib.Cryptography.SequentialZK.PaddedProverSpec.statClose_step
#print axioms TCSlib.Cryptography.SequentialZK.PaddedProverSpec.statClose_prefix
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.word_lengths
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.toData_length_le
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.cover
#print axioms TCSlib.Cryptography.SequentialZK.PhaseMetadata.cover_data
