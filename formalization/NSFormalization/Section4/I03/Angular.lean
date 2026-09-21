import NSFormalization.Paper3.AngularRealVectorBochner
import NSFormalization.Source.VectorForceNorms

/-!
# I03: the angular Sobolev datum path of a smooth compactly supported force

`verification/Contracts/V1/Data.lean` measures a Section 4 force through
`forceSobolevENorm q s f`, an infimum of `eLpNorm G q forceTimeMeasure` over all
strongly measurable paths `G : ℝ → RealVectorSobolev s` that are *angular*
order-`s` data of `f`: for every component `i` and every Schwartz test `ψ`,
`angularRealization s (G t i) ψ = ∫ x, ψ x * (f (t, x) i : ℂ)`.

Nothing upstream produces such a path from a physical field.  What exists is the
*cycles*-convention machinery: `Paper3.realVectorSlice` sends a smooth compactly
supported force to its weighted Fourier `L²` trajectory, whose Euclidean norm is
`Source.vectorFourierSobolevNorm`, and `Paper3.cyclesToAngularRealVector`
transports that to the unitary angular normalization at the cost of the explicit
factor `frequencyUnit ^ |s|`.

This module assembles the two into one named object, `angularPath`, and records
the four facts the binding needs about it:

* `angularPath_pairing` — literally the pairing shape of `IsSobolevDatum`, so
  the path is admissible for `IsSobolevPath` at *every* time, not merely a.e.;
* `memLp_angularPath` — `MemLp` on `positiveTimeMeasure`, which supplies the
  `AEStronglyMeasurable` side condition of the infimum's index type;
* `norm_angularPath_le` and `eLpNorm_angularPath_le` — the pointwise and the
  time-integrated bound by the cycles-convention norm, on all of `volume` rather
  than on `Ioi 0`.

The infimum step itself is not taken here: it belongs to `verification/Bindings`,
which may see the contract.  `norm_realVectorSlice` is exported as well, since
the binding otherwise has to re-derive the `PiLp 2` identification of the
untransported slice norm.
-/

noncomputable section

namespace NSFormalization.Section4.I03

open NavierStokes.ProblemStatement MeasureTheory Filter Topology
open scoped ContDiff ENNReal

/-- The three real components of a physical vector field, in the shape
`Paper3.realVectorSlice` and `Paper3.angularRealVectorSlice` consume.  This is
`Source.coordinateForce` before the coercion `ℝ → ℂ`. -/
def components (F : VelocityField) : Fin 3 → ℝ × Space → ℝ := fun i z => F z i

@[simp] theorem components_apply (F : VelocityField) (i : Fin 3) (z : ℝ × Space) :
    components F i z = F z i := rfl

/-- Each component of a smooth field is smooth: composition with a coordinate
projection, which is a continuous linear map on the Euclidean fibre. -/
theorem components_smooth {F : VelocityField} (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    ContDiff ℝ ∞ (components F i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hF

/-- Each component of a compactly supported field is compactly supported. -/
theorem components_compact {F : VelocityField} (hc : HasCompactSupport F) (i : Fin 3) :
    HasCompactSupport (components F i) :=
  hc.comp_left (g := fun v : Space => v i) (by simp)

/-- The components are exactly the real parts of `Source.coordinateForce`. -/
theorem coordinateForce_components (F : VelocityField) (i : Fin 3) (z : ℝ × Space) :
    Source.coordinateForce F i z = ((components F i z : ℝ) : ℂ) := rfl

/-- The cycles-convention Euclidean norm of the untransported Sobolev slice is
exactly the manuscript's vector Fourier Sobolev norm.  Same `PiLp 2` argument as
`Source.norm_compactVectorFourierLp`, run through the real subspace. -/
theorem norm_realVectorSlice (s : ℝ) (F : VelocityField) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (t : ℝ) :
    ‖Paper3.realVectorSlice s (components F) (components_smooth hF) (components_compact hc) t‖ =
      Source.vectorFourierSobolevNorm s F t := by
  have hi (i : Fin 3) :
      ‖Paper3.realVectorSlice s (components F) (components_smooth hF)
          (components_compact hc) t i‖ =
        Source.fourierSobolevNorm s (fun x => Source.coordinateForce F i (t, x)) := by
    change ‖(Paper3.realCompactSobolevTimeSlice s (components F i) (components_smooth hF i)
      (components_compact hc i) t : Source.RealSobolev.FourierData)‖ = _
    rw [Paper3.coe_realCompactSobolevTimeSlice]
    exact Paper3.norm_compactFourierLp s _ _ _
  rw [PiLp.norm_eq_of_L2]
  simp only [hi, Source.fourierSobolevNorm,
    Real.sq_sqrt (Source.fourierSobolevSq_nonneg _ _)]
  rfl

/-- The angular order-`s` datum path of a smooth compactly supported physical
force: the cycles-convention Sobolev trajectory, renormalized to the unitary
angular Fourier convention of `01-introduction.tex:91`. -/
def angularPath (s : ℝ) (F : VelocityField) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ℝ → Paper3.RealVectorSobolev s :=
  Paper3.angularRealVectorSlice s (components F) (components_smooth hF) (components_compact hc)

/-- `angularPath` is a datum path in exactly the sense of
`Contracts.V1.Data.IsSobolevDatum`: its angular realization pairs with every
Schwartz test as the original real component does, at every time. -/
theorem angularPath_pairing (s : ℝ) (F : VelocityField) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (t : ℝ) (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    Paper3.angularRealization s
        ((angularPath s F hF hc t i : Source.RealSobolev.FourierData)) ψ =
      ∫ x : Space, ψ x * ((F (t, x) i : ℝ) : ℂ) :=
  Paper3.angularRealVectorSlice_pairing s (components F) (components_smooth hF)
    (components_compact hc) t i ψ

/-- The path is Bochner `Lq` on positive time for every exponent, so in
particular strongly measurable: the second half of the admissibility condition
in the `forceSobolevENorm` infimum. -/
theorem memLp_angularPath (s : ℝ) (F : VelocityField) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    MemLp (angularPath s F hF hc) q Paper3.positiveTimeMeasure :=
  Paper3.memLp_angularRealVectorSlice s (components F) (components_smooth hF)
    (components_compact hc) q

/-- Pointwise in time, the angular datum is bounded by the cycles-convention
norm with the explicit convention constant `frequencyUnit ^ |s|`. -/
theorem norm_angularPath_le (s : ℝ) (F : VelocityField) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (t : ℝ) :
    ‖angularPath s F hF hc t‖ ≤
      Source.frequencyUnit ^ |s| * Source.vectorFourierSobolevNorm s F t := by
  rw [← norm_realVectorSlice s F hF hc t]
  exact Paper3.cyclesToAngularRealVector_norm_le s _

/-- The time seminorm of the datum path on `(0,∞)` is bounded by the convention
constant times the cycles-convention norm on all of `ℝ`.  The last step drops
`positiveTimeMeasure = volume.restrict (Ioi 0)` to `volume`, which only
increases the right-hand side. -/
theorem eLpNorm_angularPath_le (s : ℝ) (F : VelocityField) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    eLpNorm (angularPath s F hF hc) q Paper3.positiveTimeMeasure ≤
      ENNReal.ofReal (Source.frequencyUnit ^ |s|) *
        eLpNorm (Source.vectorFourierSobolevNorm s F) q volume := by
  calc eLpNorm (angularPath s F hF hc) q Paper3.positiveTimeMeasure
      ≤ eLpNorm ((Source.frequencyUnit ^ |s|) • Source.vectorFourierSobolevNorm s F) q
          Paper3.positiveTimeMeasure :=
        eLpNorm_mono_real (fun t => norm_angularPath_le s F hF hc t)
    _ = ENNReal.ofReal (Source.frequencyUnit ^ |s|) *
          eLpNorm (Source.vectorFourierSobolevNorm s F) q Paper3.positiveTimeMeasure := by
        rw [eLpNorm_const_smul,
          Real.enorm_eq_ofReal (Real.rpow_nonneg Source.frequencyUnit_pos.le _)]
    _ ≤ ENNReal.ofReal (Source.frequencyUnit ^ |s|) *
          eLpNorm (Source.vectorFourierSobolevNorm s F) q volume :=
        mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _

end NSFormalization.Section4.I03
