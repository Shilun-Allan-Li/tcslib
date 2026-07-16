import Mathlib.Tactic.ExtractGoal
import TCSlib.Tactics.ExtractHavesFile
import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy

open ExtractHavesFile

#extract_haves_iter_to "TCSlib/CommunicationComplexity/NewmanTheorem/Entropy.lean" "TCSlib/CommunicationComplexity/NewmanTheorem/Entropy_iter_output.lean"
