import Parity
open Parity
-- Goal 1: (F5) even lattices of odd determinant
#print axioms even_det_odd
-- Goal 2: vertex lattice of a centred representation (basis via Mathlib's PID theory)
#print axioms centred_lattice
#print axioms centred_lattice_mod4
-- SRG side: G^2 = l G from IsSRGWith, and Corollary 4.1
#print axioms srg_param
#print axioms centred_sq
#print axioms srg_parity
#print axioms srg_parity_mod4
#print axioms srg_parity_paper
-- worked example and Corollary 4.2
#print axioms no_srg_169_42_5_12
#print axioms no_srg_NL
-- statements, for the record
#check @no_srg_169_42_5_12
#check @no_srg_NL
#check @srg_parity_paper
