import NSFormalization.Section4.C01.MomentumCarrierB

/-!
Transitive-axiom audit for lane 143-C01-e3-e4 (`Section4/C01/MomentumCarrierB.lean`).
Every declaration must depend on exactly `[propext, Classical.choice, Quot.sound]`.

Non-vacuity of the *carrier* range: `SmoothL2Field Space` is inhabited (`zeroField`),
so the four slice packagings (`velocitySliceField`, `pressureGradientField`,
`temporalSliceField`, `forceSliceField`) land in a nonempty type.  A full
non-vacuity witness for the theorems (which quantify over `ClassicalSolutionR`)
would require inhabiting that class — all-order Sobolev datum paths + `MemForceR` —
and was not built here (see `research/C01/ATTEMPTS_E3E4.md`).  Lane 144 (PR #145) has
since landed `A04.zeroSol : ClassicalSolutionR ν 0 0 T` with `memForceR_zero`, so the
C01 SIMP pass can retarget this file to a genuine witness (deferred; the module itself
was reviewed with a real classical solution's field types, `REVIEW_E3E4.md`).
-/

open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit

namespace NSFormalization.Section4.C01

-- Row Ep: the packagings and their `_field`/gradient/divergence facts.
#print axioms velocitySliceField
#print axioms pressureGradientField
#print axioms temporalSliceField
#print axioms forceSliceField
#print axioms pressureGradientField_field
#print axioms pressureGradientField_eq_gradient
#print axioms contDiff_pressureSlice
#print axioms velocitySliceField_divergence

-- Row E3: the vendor-field identifications and the momentum split.
#print axioms advectionField_velocitySlice_field
#print axioms laplacianField_velocitySlice_field
#print axioms momentum_split_toLp

-- Payoff (modulo row E4): the classical energy identity from the derivative fact.
#print axioms energyIdentity_classical

-- Non-vacuity of the carrier range.
example : Nonempty (SmoothL2Field Space) := ⟨zeroField⟩

end NSFormalization.Section4.C01
