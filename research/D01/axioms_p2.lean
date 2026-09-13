import NSFormalization.Section4.D01.LeraySymbol

/-!
Conformance check for D01 unit P2, piece (d) S-level: the Leray complement fiber
symbol algebra (`formalization/NSFormalization/Section4/D01/LeraySymbol.lean`).

Run with, from `verification/`:
  lake env lean ../research/D01/axioms_p2.lean

Every result must depend only on the standard logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

open NSFormalization.Section4.D01.Leray

-- Explicit rank-one formula `(I−P)(ξ)v = (⟨ξ,v⟩/‖ξ‖²) ξ`  (the matrix `ξξᵀ/‖ξ‖²`).
#print axioms complementSymbol_apply
-- The four requested algebraic facts.
#print axioms complementSymbol_idempotent          -- projection
#print axioms norm_complementSymbol_le             -- operator norm ≤ 1 (pointwise)
#print axioms complementSymbol_opNorm_le_one       -- operator norm ≤ 1 (bundled)
#print axioms complementSymbol_neg                 -- even in ξ
-- Complementarity with the reused HeliCorgi solenoidal symbol `P = MNS2.r3LeraySymbol`.
#print axioms leraySymbol_add_complementSymbol
#print axioms leraySymbol_eq_sub
#print axioms complementSymbol_eq_sub
-- Fiber membership / fixed vectors.
#print axioms complementSymbol_apply_mem
#print axioms complementSymbol_fixed_of_mem
#print axioms complementSymbol_self
-- Fibre facts (SL4 kills-solenoidal / SL5 fixes-gradient bypass of unit L3) + 0-homogeneity.
#print axioms complementSymbol_eq_zero_of_inner_eq_zero
#print axioms complementSymbol_smul_self
#print axioms complementSymbol_smul
