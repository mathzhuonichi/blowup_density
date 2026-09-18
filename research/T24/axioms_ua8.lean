/-
Transitive-axiom audit for T24a unit Ua8 (lane 424), the `nonisolated` field of
`AffineVariationAPI` (`research/T24/Spec.lean:1104`).

Run: `cd verification && lake env lean ../research/T24/axioms_ua8.lean`
Expected: every line prints `[propext, Classical.choice, Quot.sound]`.

The nonzero-witness instantiation is audited separately inside
`research/T24/probes/affine_nonisolated_closes.lean`.
-/
import NSFormalization.Section3.T24.AffineNonisolated

open NSFormalization.Section3.T24

-- §1 seminorm algebra
#print axioms enn_mul_biSup
#print axioms affineCkSeminorm_const_smul
#print axioms affineCkSeminorm_add_le
#print axioms affineCkSeminorm_lt_top

-- §2 the scaling identities
#print axioms contDiff_crossAdvection_self
#print axioms affineForce_smul_sub
#print axioms affineVelocity_smul_sub

-- §3 the Ua8 target
#print axioms nonisolated
