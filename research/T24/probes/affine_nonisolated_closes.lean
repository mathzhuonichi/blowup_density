import Contracts.V1.Data
import Contracts.V1.Packet
import Bindings.Packet
import NSFormalization.Section3.T24.AffineNonisolated
import NavierStokes.SpatialCurl
import NavierStokes.OscillatoryCurl
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Ua8 probe — the registered `nonisolated` field on the canonical packet

Run from `verification/` with
`lake env lean ../research/T24/probes/affine_nonisolated_closes.lean`.

* `§0` rebuilds lane 398's **nonzero** admissible witness `b := ∇ × A`,
  `A(t,x) = θ(t) φ(x) e₁`, on the cylinder `ball 0 1 × (1/4,3/4)` (probes are
  standalone `lake env lean` files, not library modules, so the construction is
  rebuilt rather than imported; lane 417's shared `Section3/T24/AffineWitness.lean`
  is not on this base).
* `§1` restates the `prop:affine` affine vocabulary and the `C^m` seminorm
  `ckSeminormE` byte-for-byte from `research/T24/Spec.lean:961-999` in the
  **registered** `Contracts.V1` operator tokens, and records the six `rfl`
  bridges to the canonical `NSFormalization.Section3.T24` spellings (in
  particular `ckSeminormE ≡ affineCkSeminorm`, `AffineBasics.lean:50`).
* `§2` `nonisolated_on_canonical` discharges the `AffineVariationAPI.nonisolated`
  obligation (`research/T24/Spec.lean:1104-1111`) on the selected packet
  `Bindings.packet ν hν`, fed only the packet's own `velocity_smooth` field.
* `§3` non-vacuity: the field instantiated at the nonzero witness, and the proof
  that the quantity driven to `0` is **not** identically `0` — at `λ = 1` and
  `m = 0` the velocity seminorm of a nonzero `b` is strictly positive, so the two
  `Tendsto` statements are genuine limits rather than limits of the zero function.
-/

noncomputable section

/-! ## §0 lane 398's nonzero admissible witness, rebuilt -/

namespace BlowupDensity.T24.NonisolatedProbe.Witness

open NavierStokes.ProblemStatement NavierStokes.SpatialCurl Set
open NSFormalization.Section3.T24
open scoped ContDiff

/-- Time bump: plateau radius `1/16`, support radius `1/8`, centred at `1/2`. -/
def timeBump : ContDiffBump ((1 : ℝ) / 2) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

/-- Spatial bump: plateau radius `1/2`, support radius `3/4`, centred at `0`. -/
def spaceBump : ContDiffBump (0 : Space) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

/-- The smooth compactly supported vector potential `A(t,x) = θ(t) φ(x) e₁`. -/
def potentialA : VelocityField :=
  fun z => (timeBump z.1 * spaceBump z.2) • coordinateVector 0

/-- The perturbation `b := ∇ × A`. -/
def bWitness : VelocityField := spatialCurl potentialA

/-- The `e₂`-component of the curl of `g • e₁` is `∂₃ g` (`fderiv g x e₃`). -/
theorem curl_component_one (g : Space → ℝ) (x : Space)
    (hg : DifferentiableAt ℝ g x) :
    (curl (fun y => g y • coordinateVector 0) x) 1 =
      fderiv ℝ g x (coordinateVector 2) := by
  unfold curl
  rw [fderiv_smul_const hg, curlLinear_apply_one]
  simp [coordinateVector, ContinuousLinearMap.smulRight_apply]

/-- The compact carrier `closedBall(1/2, 1/8) × closedBall(0, 3/4)`. -/
def carrierK : Set SpaceTime :=
  Metric.closedBall ((1 : ℝ) / 2) (1 / 8) ×ˢ Metric.closedBall (0 : Space) (3 / 4)

theorem potentialA_contDiff : ContDiff ℝ ∞ potentialA := by
  have hw : ContDiff ℝ ∞ (fun z : SpaceTime => timeBump z.1 * spaceBump z.2) :=
    (timeBump.contDiff.comp contDiff_fst).mul (spaceBump.contDiff.comp contDiff_snd)
  exact hw.smul contDiff_const

theorem tsupport_potentialA_subset_carrier : tsupport potentialA ⊆ carrierK := by
  apply closure_minimal _ (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)
  intro z hz
  have hne : timeBump z.1 * spaceBump z.2 ≠ 0 := by
    intro h0
    apply hz
    show (timeBump z.1 * spaceBump z.2) • coordinateVector 0 = 0
    rw [h0, zero_smul]
  have h1 : timeBump z.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : spaceBump z.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hz1 : z.1 ∈ tsupport (⇑timeBump) := subset_tsupport _ (Function.mem_support.mpr h1)
  have hz2 : z.2 ∈ tsupport (⇑spaceBump) := subset_tsupport _ (Function.mem_support.mpr h2)
  rw [timeBump.tsupport_eq] at hz1
  rw [spaceBump.tsupport_eq] at hz2
  exact ⟨hz1, hz2⟩

theorem carrierK_subset_cylinder :
    carrierK ⊆ affineCylinder (0 : Space) 1 (1 / 4) (3 / 4) := by
  apply Set.prod_mono
  · rw [Real.closedBall_eq_Icc]
    exact Icc_subset_Ioo (by norm_num) (by norm_num)
  · exact Metric.closedBall_subset_ball (by norm_num)

theorem potentialA_hasCompactSupport : HasCompactSupport potentialA := by
  have hK : IsCompact carrierK :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  apply HasCompactSupport.intro hK
  intro z hz
  by_contra h
  exact hz (tsupport_potentialA_subset_carrier (subset_tsupport potentialA h))

theorem bWitness_contDiff : ContDiff ℝ ∞ bWitness :=
  contDiff_spatialCurl potentialA_contDiff (by simp)

theorem bWitness_hasCompactSupport : HasCompactSupport bWitness :=
  potentialA_hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    (NavierStokes.OscillatoryCurl.spatialCurl_tsupport_subset potentialA)

theorem bWitness_tsupport_subset :
    tsupport bWitness ⊆ affineCylinder (0 : Space) 1 (1 / 4) (3 / 4) :=
  (NavierStokes.OscillatoryCurl.spatialCurl_tsupport_subset potentialA).trans
    (tsupport_potentialA_subset_carrier.trans carrierK_subset_cylinder)

theorem bWitness_divergence_free :
    ∀ t : ℝ, ∀ x : Space, spatialDivergence bWitness t x = 0 := by
  intro t x
  have hslice : ContDiffAt ℝ 2 (fun y : Space => potentialA (t, y)) x :=
    ((potentialA_contDiff.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le
      (by norm_num)
  exact spatialDivergence_spatialCurl potentialA t x hslice

/-- The nonzero admissible witness (lane 398). -/
theorem bWitness_admissible :
    AffineAdmissible (0 : Space) 1 (1 / 4) (3 / 4) bWitness :=
  ⟨bWitness_contDiff, bWitness_hasCompactSupport, bWitness_tsupport_subset,
    bWitness_divergence_free⟩

theorem bWitness_ne_zero : bWitness ≠ 0 := by
  intro hb0
  have hφsmooth : ContDiff ℝ ∞ (⇑spaceBump) := spaceBump.contDiff
  have hcurl0 : ∀ x : Space,
      curl (fun y => spaceBump y • coordinateVector 0) x = 0 := by
    intro x
    have hslice : (fun y : Space => potentialA ((1 : ℝ) / 2, y)) =
        (fun y : Space => spaceBump y • coordinateVector 0) := by
      funext y
      have h1 : timeBump ((1 : ℝ) / 2) = 1 :=
        timeBump.one_of_mem_closedBall (Metric.mem_closedBall_self timeBump.rIn_pos.le)
      show (timeBump ((1 : ℝ) / 2) * spaceBump y) • coordinateVector 0 =
        spaceBump y • coordinateVector 0
      rw [h1, one_mul]
    have hz : spatialCurl potentialA ((1 : ℝ) / 2, x) = 0 := by
      have := congrFun hb0 ((1 : ℝ) / 2, x)
      simpa [bWitness] using this
    calc curl (fun y => spaceBump y • coordinateVector 0) x
        = curl (fun y => potentialA ((1 : ℝ) / 2, y)) x := by rw [hslice]
      _ = spatialCurl potentialA ((1 : ℝ) / 2, x) := rfl
      _ = 0 := hz
  have hpartial : ∀ x : Space, fderiv ℝ (⇑spaceBump) x (coordinateVector 2) = 0 := by
    intro x
    have hcomp := curl_component_one (⇑spaceBump) x
      (hφsmooth.differentiable (by simp) x)
    have hzero := congrArg (fun v : Space => v 1) (hcurl0 x)
    rw [hcomp] at hzero
    simpa using hzero
  have hψ_diff : Differentiable ℝ (fun s : ℝ => spaceBump (s • coordinateVector 2)) :=
    (hφsmooth.differentiable (by simp)).comp (differentiable_id.smul_const _)
  have hψ_deriv : ∀ s : ℝ,
      deriv (fun s : ℝ => spaceBump (s • coordinateVector 2)) s = 0 := by
    intro s
    have hline : HasDerivAt (fun r : ℝ => r • coordinateVector 2)
        (coordinateVector 2) s := by
      simpa using (hasDerivAt_id s).smul_const (coordinateVector 2)
    have hd : DifferentiableAt ℝ (⇑spaceBump) (s • coordinateVector 2) :=
      (hφsmooth.differentiable (by simp)).differentiableAt
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt s hline
    have hderiv := hcomp.deriv
    rw [hpartial (s • coordinateVector 2)] at hderiv
    exact hderiv
  have hconst := is_const_of_deriv_eq_zero hψ_diff hψ_deriv
  have h10 : (fun s : ℝ => spaceBump (s • coordinateVector 2)) 1 =
      (fun s : ℝ => spaceBump (s • coordinateVector 2)) 0 := hconst 1 0
  have hψ0 : (fun s : ℝ => spaceBump (s • coordinateVector 2)) 0 = 1 := by
    show spaceBump ((0 : ℝ) • coordinateVector 2) = 1
    rw [zero_smul]
    exact spaceBump.one_of_mem_closedBall (Metric.mem_closedBall_self spaceBump.rIn_pos.le)
  have hψ1 : (fun s : ℝ => spaceBump (s • coordinateVector 2)) 1 = 0 := by
    show spaceBump ((1 : ℝ) • coordinateVector 2) = 0
    rw [one_smul]
    apply image_eq_zero_of_notMem_tsupport (f := ⇑spaceBump)
    rw [spaceBump.tsupport_eq]
    have hnorm : ‖coordinateVector 2‖ = 1 := by simp [coordinateVector]
    simp only [Metric.mem_closedBall, dist_zero_right, hnorm, not_le]
    show spaceBump.rOut < 1
    norm_num [spaceBump]
  rw [hψ0, hψ1] at h10
  exact absurd h10 (by norm_num)

end BlowupDensity.T24.NonisolatedProbe.Witness

/-! ## §1-§3 the registered field -/

namespace BlowupDensity.T24.NonisolatedProbe

open Set Filter Topology
open BlowupDensity.Contracts.V1
open scoped ContDiff ENNReal BigOperators

/-! ### §1 Registered-vocabulary affine defs (verbatim `research/T24/Spec.lean:961-999`) -/

def affineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

def AffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : VelocityField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ affineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space, spatialDivergence b t x = 0)

def crossAdvection (v w : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative w t x (v (t, x))

def affineVelocity (U b : VelocityField) : VelocityField :=
  fun z ↦ U z + b z

def affineForce (ν : ℝ) (U F b : VelocityField) : VelocityField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 - ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 +
    crossAdvection b b z.1 z.2

def ckSeminormE (K : Set SpaceTime) (m : ℕ) (f : VelocityField) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (m + 1), ⨆ z ∈ K, ‖iteratedFDeriv ℝ k f z‖ₑ

/-! ### The `rfl` bridges to the canonical `Section3/T24` spellings -/

/-- `research/T24/Spec.lean` spells the fields `SpaceTimeField`; that is a
reducible alias of the registered `VelocityField` used below
(`Contracts/V1/Data.lean:104`). -/
theorem SpaceTimeField_eq :
    BlowupDensity.Contracts.V1.Data.SpaceTimeField = VelocityField := rfl

theorem affineCylinder_eq (c : Space) (r τ₀ τ₁ : ℝ) :
    affineCylinder c r τ₀ τ₁ = NSFormalization.Section3.T24.affineCylinder c r τ₀ τ₁ := rfl

theorem AffineAdmissible_eq (c : Space) (r τ₀ τ₁ : ℝ) (b : VelocityField) :
    AffineAdmissible c r τ₀ τ₁ b = NSFormalization.Section3.T24.AffineAdmissible c r τ₀ τ₁ b :=
  rfl

theorem crossAdvection_eq (v w : VelocityField) (t : ℝ) (x : Space) :
    crossAdvection v w t x = NSFormalization.Section3.T24.crossAdvection v w t x := rfl

theorem affineVelocity_eq (U b : VelocityField) :
    affineVelocity U b = NSFormalization.Section3.T24.affineVelocity U b := rfl

theorem affineForce_eq (ν : ℝ) (U F b : VelocityField) :
    affineForce ν U F b = NSFormalization.Section3.T24.affineForce ν U F b := rfl

/-- The seminorm of `research/T24/Spec.lean:998` is the canonical
`affineCkSeminorm` of `AffineBasics.lean:50`, on the nose. -/
theorem ckSeminormE_eq (K : Set SpaceTime) (m : ℕ) (f : VelocityField) :
    ckSeminormE K m f = NSFormalization.Section3.T24.affineCkSeminorm K m f := rfl

/-! ### §2 The registered Ua8 field, discharged on the canonical packet -/

/-- `AffineVariationAPI.nonisolated` (`research/T24/Spec.lean:1104-1111`) for the
selected packet `Bindings.packet ν hν`, in registered `Contracts.V1` vocabulary.
The cylinder hypotheses `0 < τ₀`, `τ₁ < 1` are the parameter hypotheses of
`affineVariationStatement` (`:1117`); the only packet clause consumed is
`velocity_smooth`. -/
theorem nonisolated_on_canonical (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b → b ≠ 0 → ∀ m : ℕ,
      Tendsto (fun lam : ℝ ↦ ckSeminormE (tsupport b) m
          (fun z ↦ affineVelocity (BlowupDensity.Bindings.packet ν hν).velocity (lam • b) z -
            (BlowupDensity.Bindings.packet ν hν).velocity z)) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun lam : ℝ ↦ ckSeminormE (tsupport b) m
          (fun z ↦ affineForce ν (BlowupDensity.Bindings.packet ν hν).velocity
            (BlowupDensity.Bindings.packet ν hν).force (lam • b) z -
            (BlowupDensity.Bindings.packet ν hν).force z)) (𝓝 0) (𝓝 0) := by
  intro b hb hbne m
  exact NSFormalization.Section3.T24.nonisolated c r τ₀ τ₁ hτ₀ hτ₁
    (BlowupDensity.Bindings.packet ν hν).velocity_smooth b hb hbne m

/-! ### §3 Non-vacuity -/

/-- The witness is admissible in the registered vocabulary too (`rfl` bridge). -/
theorem bWitness_admissible' :
    AffineAdmissible (0 : Space) 1 (1 / 4) (3 / 4) Witness.bWitness :=
  Witness.bWitness_admissible

/-- Both `nonisolated` limits at the **nonzero** admissible witness on the
registered packet. -/
theorem nonzero_admissible_nonisolated (ν : ℝ) (hν : 0 < ν) (m : ℕ) :
    Tendsto (fun lam : ℝ ↦ ckSeminormE (tsupport Witness.bWitness) m
        (fun z ↦ affineVelocity (BlowupDensity.Bindings.packet ν hν).velocity
          (lam • Witness.bWitness) z -
          (BlowupDensity.Bindings.packet ν hν).velocity z)) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun lam : ℝ ↦ ckSeminormE (tsupport Witness.bWitness) m
        (fun z ↦ affineForce ν (BlowupDensity.Bindings.packet ν hν).velocity
          (BlowupDensity.Bindings.packet ν hν).force (lam • Witness.bWitness) z -
          (BlowupDensity.Bindings.packet ν hν).force z)) (𝓝 0) (𝓝 0) :=
  nonisolated_on_canonical ν hν (0 : Space) 1 (1 / 4) (3 / 4) (by norm_num) (by norm_num)
    Witness.bWitness bWitness_admissible' Witness.bWitness_ne_zero m

/-- The `C^0` seminorm on `tsupport b` of a nonzero field is nonzero: the
supremum is at least `‖b z₀‖ₑ > 0` at a point where `b` does not vanish. -/
theorem ckSeminormE_zero_ne_zero {b : VelocityField} (hb : b ≠ 0) :
    ckSeminormE (tsupport b) 0 b ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ : ∃ z, b z ≠ 0 := by
    by_contra h
    exact hb (funext fun z => not_not.mp (fun hzz => h ⟨z, hzz⟩))
  have hmem : z₀ ∈ tsupport b := subset_tsupport b (Function.mem_support.mpr hz₀)
  have hpos : (0 : ℝ≥0∞) < ‖b z₀‖ₑ := by
    simpa using hz₀
  have hle : ‖b z₀‖ₑ ≤ ⨆ z ∈ tsupport b, ‖iteratedFDeriv ℝ 0 b z‖ₑ := by
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun z (_ : z ∈ tsupport b) => ‖iteratedFDeriv ℝ 0 b z‖ₑ) z₀ hmem)
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]
  have : ckSeminormE (tsupport b) 0 b = ⨆ z ∈ tsupport b, ‖iteratedFDeriv ℝ 0 b z‖ₑ := by
    unfold ckSeminormE
    rw [Finset.sum_range_one]
  rw [this]
  exact (lt_of_lt_of_le hpos hle).ne'

/-- The quantity driven to `0` is **not** identically `0`: at `λ = 1` and `m = 0`
the velocity seminorm of the nonzero witness is strictly positive.  So the two
`Tendsto` statements of `nonisolated` are genuine limits, not limits of the zero
function. -/
theorem nonisolated_nontrivial (ν : ℝ) (hν : 0 < ν) :
    ckSeminormE (tsupport Witness.bWitness) 0
        (fun z ↦ affineVelocity (BlowupDensity.Bindings.packet ν hν).velocity
          ((1 : ℝ) • Witness.bWitness) z -
          (BlowupDensity.Bindings.packet ν hν).velocity z) ≠ 0 := by
  have hfun : (fun z ↦ affineVelocity (BlowupDensity.Bindings.packet ν hν).velocity
      ((1 : ℝ) • Witness.bWitness) z -
      (BlowupDensity.Bindings.packet ν hν).velocity z) = Witness.bWitness := by
    funext z
    simp [affineVelocity]
  rw [hfun]
  exact ckSeminormE_zero_ne_zero Witness.bWitness_ne_zero

#print axioms SpaceTimeField_eq
#print axioms ckSeminormE_eq
#print axioms affineForce_eq
#print axioms nonisolated_on_canonical
#print axioms bWitness_admissible'
#print axioms nonzero_admissible_nonisolated
#print axioms ckSeminormE_zero_ne_zero
#print axioms nonisolated_nontrivial

end BlowupDensity.T24.NonisolatedProbe
