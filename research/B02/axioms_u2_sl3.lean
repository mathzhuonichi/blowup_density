import NSFormalization.Section4.B02.AnnularReal

/-!
Axiom audit for B02 unit 2, sub-lemmas SL3 (reality), SL4a (slice), SL4b
(integrability), SL4c (pairing), the assembly `annularSchwartz` (the spec field),
and the unconditional diagonal `spatialApproxHomogeneous`, in module
`NSFormalization.Section4.B02.AnnularReal`.

Every public declaration must depend on exactly the three standard axioms
`[propext, Classical.choice, Quot.sound]`.  Run with
`lake env lean research/B02/axioms_u2_sl3.lean` from `verification/`.
-/

open NSFormalization.Section4.B02
open NSFormalization.Paper3
open NavierStokes.ProblemStatement (Space)

-- Conformance: `annularSchwartz` inhabits the spec field type verbatim
-- (`research/B02/Spec.lean:362-364`), with the local (NSFormalization) predicate
-- restatements that are token-for-token the contract ones.
example : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
    ∀ W : RealVectorSobolev s, IsAnnularDatum δ R W →
    ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W :=
  annularSchwartz

-- Supporting angular-Fourier facts (SL3 route).
#print axioms angularFourier_conj
#print axioms angularFourier_schwartz_add
#print axioms angularFourier_schwartz_smul
#print axioms postcompReCLM_ofReal_eq
#print axioms angularFourier_realPart_apply

-- SL3: reality of the realized homogeneous weight (a.e.).
#print axioms angularFourier_realPart_ae

-- SL4a: the complexified real Schwartz vector realizes the slice distribution.
#print axioms isSliceDistribution_schwartzVector

-- SL4b: integrability of the homogeneous pairing.
#print axioms integrable_weight_annular

-- SL4c: the homogeneous pairing identity.
#print axioms angularFourierDistribution_realPart_pairing

-- SL4: the spec field `annularSchwartz`, and the unconditional stage-4 diagonal.
#print axioms annularSchwartz
#print axioms spatialApproxHomogeneous
