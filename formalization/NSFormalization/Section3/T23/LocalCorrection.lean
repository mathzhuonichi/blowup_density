import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T15.Bridges
import NSFormalization.Source.Insertion

/-! Raw, un-periodised local correction vocabulary for T23.
The seven fields are copied verbatim from research/T23/Spec.lean.
No placement record or contract is imported. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set Filter
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology

structure CutoffData where
  /-- Spatial cutoff from the Urysohn construction;
  `paper/sections/03-torus.tex:167-172,181`.

  Non-vacuity: this is a concrete real-valued function on physical space. -/
  θ : Space → ℝ
  /-- Temporal cutoff used in `eq:cutoff`;
  `paper/sections/03-torus.tex:173-174,182-186`.

  Non-vacuity: this is a concrete real-valued function of physical time. -/
  η : ℝ → ℝ
  /-- Open plateau on which `θ` is one;
  `paper/sections/03-torus.tex:172,181`.

  Non-vacuity: the set is retained as data and is constrained below to contain
  the prescribed compact set. -/
  plateau : Set Space
  /-- Fixed support radius for `θ`;
  `paper/sections/03-torus.tex:168-172,212`.

  Non-vacuity: the API requires this actual real radius to be strictly
  positive and to bound `tsupport θ`. -/
  θRadius : ℝ
  /-- Common upper threshold for every sufficiently small `ε`;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: the API requires one strictly positive threshold shared by all
  scale-dependent conclusions. -/
  ε₀ : ℝ
  /-- Radial vector potential `A` from `eq:potential`;
  `paper/sections/03-torus.tex:177-181`.

  Non-vacuity: this is a concrete time-first spacetime vector field whose
  formula and curl are fixed below. -/
  potential : SpaceTimeField
  /-- Scale-indexed correction family `w_ε` from `eq:cutoff`;
  `paper/sections/03-torus.tex:183-193`.

  Non-vacuity: this is one concrete family shared by smoothness, periodicity,
  support, divergence, and cancellation fields. -/
  correction : ℝ → SpaceTimeField


open NSFormalization.Section3.T15 (scaledVelocity scaledSourcePoint scaledStartTime)

/-- The un-periodised packet vanishes on the entire slice before activation,
including the endpoint. No smoothness or packet hypotheses are needed. -/
theorem packet_slice_zero (U : VelocityField) (x₀ : Space) (T ε t : ℝ)
    (ht : t ≤ T - ε ^ 2) :
    (fun y : Space => scaledVelocity U x₀ T ε (t, y)) = fun _ => 0 := by
  funext y
  have hnonpos : (ε⁻¹) ^ 2 * (t - scaledStartTime T ε) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    exact sub_nonpos.mpr ht
  simp only [scaledVelocity, NSFormalization.Source.PacketScaling.zeroPastField,
    scaledSourcePoint]
  simp only [not_lt.mpr hnonpos, ite_false, smul_zero]

end NSFormalization.Section3.T23
