# T18 U5/U6 attempts — lane 433

## Successful routes

### U5 (`Section3/T18/CrossTransport.lean`)

- The whole unit runs through the Section 4 lemma
  `NSFormalization.Source.cross_advection_eq_zero` (`Source/Insertion.lean:52`).
  Its hypothesis is exactly "the background vanishes on a neighbourhood of every
  point of the packet's spatial support", and it already does the outside-the-
  support half (`fderiv_of_notMem_tsupport`), so U5 needs no new locality work.
- `correction.potential.correction_cancels` (`T16/LocalPotential.lean:158`) is
  stated in the T16 spelling `periodicScaledPacket u x₀ T ε`, while the Spec's
  cross-transport fields use the T15 spelling
  `periodizedScaledVelocity u x₀ T ε`. These are **`rfl`-equal**: T16's
  `latticeVector` (`WithLp.toLp 2`) and T13's (`(EuclideanSpace.equiv _ _).symm`)
  are definitionally the same map, and `scaledVelocity_eq_parabolicVelocity`
  is already `rfl`. Recorded as `periodicScaledPacket_eq`; the statements then
  unify without any rewriting.
- From the open set `O` of `correction_cancels`, the eventual-vanishing
  hypothesis is one `filter_upwards [hO.mem_nhds (hsub hy)]`.
- The pre-activation branch (`t < T - ε²`) is **not** a support argument: the
  periodized packet slice is literally the constant zero function, because
  `scaledSourcePoint` has time coordinate `(ε⁻¹)² (t - (T - ε²)) ≤ 0` and
  `zeroPastField` is the `if 0 < z.1` conditional. This is stronger than
  lane 426's `packet_quiet` (which is pointwise, at `t ≤ T - 2ε²`) and is what
  makes `fderiv` of the slice vanish, so `packet_slice_zero` states the slice
  equality `(fun y ↦ U_ε (t, y)) = fun _ ↦ 0` at the sharper threshold
  `t ≤ T - ε²`. The two branches meet exactly at `T - ε²`, which is also the
  lower endpoint of `correction_cancels`' interval `Ico (T - ε²) T`, so no gap.
- Nothing in U5 needs `scaling.velocity_singleCopy`, `latticeLift_cancels`, or
  the placement geometry: `correction_cancels` already carries the neighbourhood.

### U6 (`Section3/T18/Momentum.lean`)

- `NSFormalization.Source.residual ν u p t x` is **`rfl`-equal** to
  `NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x`, so the whole
  Section 4 residual calculus (`residual_add`, `corrected_background`) applies
  to the torus statement with no transport lemma.
- `Source.corrected_background` gives `NS(v + w_ε, π) = NS(v, π) + H_ε` where
  `H_ε` is `Source.correctionForce`; `T17.correctionForce_eq_source` converts to
  the T17 spelling used by `force`. `correctedBackground v D.correction ε` is
  syntactically `fun z ↦ v z + D.correction ε z`, so a `show … from rfl` rewrite
  is enough to feed it to that lemma.
- The pressure gauge is handled by one lemma,
  `pressureGradient_normalizePressureT`: `normalizePressureT q (t, ·)` is
  `q (t, ·) - pressureMeanT q t`, a *spatially constant* shift, so
  `fderiv_sub_const` closes it with **no** integrability hypothesis. This is the
  reason lane 426's `integral_add` route (needed for `pressure_smooth`) is not
  needed again here. It applies twice: once to the inserted pressure
  `normalizePressureT (π + P_ε)`, once to the packet's own pinned pressure
  `normalizedScaledPressure = normalizePressureT P_ε`, which is how
  `scaling.solution`'s `momentum` field is turned into the raw-gauge equation
  `NS(U_ε, P_ε) = F_ε`.
- `DifferentiableAt` of the *raw* periodized packet pressure slice is obtained
  from `S.pressure_smooth` plus `.add_const`, using
  `periodizedScaledPressure (t, y) = S.pressure (t, y) + pressureMeanT … t`.
  There is no regularity field for the raw periodized pressure in `ScalingAPI`.
- Interior-time differentiability needs the slab to be a neighbourhood: mono to
  `Ioo 0 T ×ˢ univ` (open), then `ContDiffOn.contDiffAt`. Spatial slices use
  lane 426's `ContDiffOn.comp_contDiff` pattern, which also covers `t = 0`
  (unused here, since `momentum` is on `Ioo 0 T`).

## Failed / rejected approaches

- `Source.exact_insertion` (`Source/Insertion.lean:70`) proves exactly the U6
  goal in one step, but its `hremove` hypothesis is the *neighbourhood removal*
  statement, which is strictly stronger than the two Spec cross-transport
  fields. Using it would have made U6 re-derive U5's content instead of
  consuming it, so `residual_add` + the two U5 theorems was used instead.
- `simp only [spatialDerivative, hz, fderiv_const]` does not close
  `fderiv ℝ (fun x ↦ 0) x = 0` at this pin: `fderiv_const` is the funext form
  (`fderiv 𝕜 (fun _ ↦ c) = 0`), so the applied form needs `Pi.zero_apply` too.
  A plain `simp` after `simp only [spatialDerivative, hz]` works.
- `ContDiff.of_le (by exact_mod_cast le_top)` fails for `ContDiff ℝ ∞ → ContDiff ℝ 2`
  (`mod_cast has type ?m ≤ ⊤ but is expected to have type 2 ≤ ∞`), because `∞`
  is `((⊤ : ℕ∞) : WithTop ℕ∞)` and not the top of `WithTop ℕ∞`. Use the
  `ResidualCalculus` spelling `WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)`,
  isolated here as `contDiff_two_of_smooth`.
- The helper `slice_contDiff` had to be stated for a general normed-space
  codomain: pressures are `SpaceTimeScalar`, and the `SpaceTimeField`-only
  version silently leaves the field as a metavariable and then reports a type
  mismatch at the use site.
- Rewriting the goal with `rw [show pressure data ε = normalizePressureT … from rfl]`
  before applying `residual_normalizePressureT` left an unsolvable metavariable
  (`?m.699`) because the velocity arguments on the two sides are defeq but not
  syntactically equal; an explicit `show … = _` changing the whole LHS by
  definitional unfolding works.
- `push_neg` is deprecated at this pin (`Prefer using push Not`); `rw [not_lt]`
  is used instead.

## Residual gaps

None for the three targeted fields: `crossTransport_background_advects_packet`,
`crossTransport_packet_advects_background` and `momentum` are proved outright
from the threaded `scaling`/`correction`/`reference` records, with no named
input and no extra hypothesis. As for U1–U4, non-vacuity of the whole record
still waits on the T15/T17 assembly witnesses (T15 U15, T17 U12).
