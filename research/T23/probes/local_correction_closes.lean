import NSFormalization.Section3.T23.LocalCorrection
import NSFormalization.Section3.T23.LocalCorrectionBridge

noncomputable section
open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T23
open scoped ContDiff Topology

-- A genuine existential constructor, with no assumed correction/API.
example (ν : ℝ) (v U : VelocityField) (K Ω : Set Space) (x₀ : Space)
    (r T δ : ℝ) (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ)
    (hK : IsCompact K) (hΩ : closure (ball x₀ r) ⊆ Ω)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
      spatialDivergence v t x = 0)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) :
    ∃ D : CutoffData, LocalCorrectionCore v U K x₀ r T δ D ∧
      ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        ContDiff ℝ ∞ (correctionForce ν v D ε) ∧
        HasCompactSupport (correctionForce ν v D ε) ∧
        tsupport (D.correction ε) ⊆ Ioo (0 : ℝ) (T + δ) ×ˢ Ω ∧
        tsupport (correctionForce ν v D ε) ⊆
          Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ ball x₀ (ε * D.θRadius) :=
  exists_localCorrection_in_domain ν v U K Ω x₀ r T δ hr hT hδ hK hΩ hv hd hU

-- The derivative and value both vanish at the closed initial endpoint.
example (U : VelocityField) (x₀ x : Space) (T ε : ℝ) (h : ε ^ 2 ≤ T)
    (b : VelocityField) :
    spatialDerivative (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε) 0 x
      (b (0, x)) = 0 ∧
    spatialDerivative b 0 x
      (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε (0, x)) = 0 := by
  have hz := packet_slice_zero U x₀ T ε 0 (by linarith)
  have hd : spatialDerivative (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε) 0 x = 0 := by
    simp only [spatialDerivative, hz]
    simp
  exact ⟨by rw [hd]; simp, by rw [congrFun hz x]; exact map_zero _⟩

-- Exact support-independent force transport; no exterior smoothness premise.
example (ν : ℝ) (v V : VelocityField) (D : CutoffData) (ε : ℝ)
    (O : Set SpaceTime) (hO : IsOpen O) (hs : tsupport (D.correction ε) ⊆ O)
    (he : EqOn v V O) : correctionForce ν v D ε = correctionForce ν V D ε :=
  correctionForce_eq_of_open_agreement ν v V D ε hO hs he

-- The solenoidal extension is constructed, rather than supplied as an input.
example (v : VelocityField) (x₀ : Space) (r T δ : ℝ)
    (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
      spatialDivergence v t x = 0) :
    ∃ V : VelocityField, ContDiff ℝ ∞ V ∧
      (∀ t x, spatialDivergence V t x = 0) ∧
      EqOn V v (Icc (T - min T δ / 2) (T + min T δ / 2) ×ˢ ball x₀ (r / 2)) :=
  exists_solenoidal_window_extension hr hT hδ hv hd

-- The final constructor shares one actual D and threshold across all jet orders.
example (ν : ℝ) (v U : VelocityField)
    (K Ω : Set Space) (x₀ : Space) (r T δ : ℝ)
    (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ) (hK : IsCompact K)
    (hΩ : closure (ball x₀ r) ⊆ Ω)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
      spatialDivergence v t x = 0)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) :
    ∃ D : CutoffData, LocalCorrectionCore v U K x₀ r T δ D ∧ D.ε₀ ≤ 1 ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        ContDiff ℝ ∞ (correctionForce ν v D ε) ∧
        HasCompactSupport (correctionForce ν v D ε) ∧
        tsupport (D.correction ε) ⊆ Ioo (0 : ℝ) (T + δ) ×ˢ Ω ∧
        tsupport (correctionForce ν v D ε) ⊆
          Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ ball x₀ (ε * D.θRadius)) ∧
      (∀ j m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
        ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (D.correction ε) z
          (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
            (fun i => ((0 : ℝ), u i)))‖ ≤ C * (ε⁻¹) ^ (2 * j + m)) ∧
      (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
        ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (correctionForce ν v D ε) z
          (fun i => ((0 : ℝ), u i))‖ ≤ C * (ε⁻¹) ^ (2 + m)) :=
  exists_localCorrection_with_derivative_bounds ν v U K Ω x₀ r T δ hr hT hδ hK hΩ hv hdiv hU
