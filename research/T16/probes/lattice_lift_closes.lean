import NSFormalization.Section3.T16.LatticeLift

/-! Lane 352 probe: the seven `correction_*` field types of `LocalPotentialAPI`
(verbatim bodies, with `D.correction ε := latticeLift (W ε)`) are provided by
`correction_fields_of_chart`; plus a non-vacuity witness (a nonzero smooth bump
whose lift is nonzero and periodic). -/

open NSFormalization.Section3.T16
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (spatialCutoff temporalCutoff)
open Set Metric
open scoped ContDiff Topology

noncomputable section

/- ### Part A: each canonical `correction_*` field type, realized by the lift. -/
section FieldTypes
variable (v U : SpaceTimeField) (x₀ : Space) (θ : Space → ℝ) (η : ℝ → ℝ)
  (A : SpaceTimeField) (r T ε₀ θRadius : ℝ) (W : ℝ → SpaceTimeField)
  (hr2 : r < 1 / 2) (hθR : 0 < θRadius) (hv_per : IsPeriodicOn univ v)
  (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θRadius < r)
  (hWsmooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (W ε))
  (hWcompact : ∀ ε ∈ Ioc (0 : ℝ) ε₀, HasCompactSupport (W ε))
  (hWdiv : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t x, spatialDivergence (W ε) t x = 0)
  (hWtsupp : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      tsupport (W ε) ⊆ Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ ball x₀ (ε * θRadius))
  (hWformula : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, ∀ x ∈ ball x₀ r,
      W ε (t, x) = -SpatialCurl.curl (fun y =>
        (temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • A (t, y)) x)
  (hWcancel : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
      ∀ x ∈ ball x₀ r, v (t, x) + W ε (t, x) = 0)
  (hpacket : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
      tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ periodicSet (ball x₀ r))

/-- `correction_formula` (verbatim). -/
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, ∀ x ∈ ball x₀ r,
    latticeLift (W ε) (t, x) =
      -SpatialCurl.curl (fun y =>
        (temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • A (t, y)) x :=
  (correction_fields_of_chart v U x₀ θ η A r T ε₀ θRadius W hr2 hθR hv_per
    hεspace hWsmooth hWcompact hWdiv hWtsupp hWformula hWcancel hpacket).1

/-- `correction_smooth` (verbatim). -/
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (latticeLift (W ε)) :=
  (correction_fields_of_chart v U x₀ θ η A r T ε₀ θRadius W hr2 hθR hv_per
    hεspace hWsmooth hWcompact hWdiv hWtsupp hWformula hWcancel hpacket).2.1

/-- `correction_periodic` (verbatim). -/
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀, IsPeriodicOn univ (latticeLift (W ε)) :=
  (correction_fields_of_chart v U x₀ θ η A r T ε₀ θRadius W hr2 hθR hv_per
    hεspace hWsmooth hWcompact hWdiv hWtsupp hWformula hWcancel hpacket).2.2.1

/-- `correction_divergence_free` (verbatim). -/
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t x,
    spatialDivergence (latticeLift (W ε)) t x = 0 :=
  (correction_fields_of_chart v U x₀ θ η A r T ε₀ θRadius W hr2 hθR hv_per
    hεspace hWsmooth hWcompact hWdiv hWtsupp hWformula hWcancel hpacket).2.2.2.1

/-- `correction_support` (verbatim). -/
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    tsupport (latticeLift (W ε)) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ (univ : Set Space) :=
  (correction_fields_of_chart v U x₀ θ η A r T ε₀ θRadius W hr2 hθR hv_per
    hεspace hWsmooth hWcompact hWdiv hWtsupp hWformula hWcancel hpacket).2.2.2.2.1

/-- `correction_support_ball` (verbatim). -/
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t,
    tsupport (fun x => latticeLift (W ε) (t, x)) ⊆ periodicSet (ball x₀ r) :=
  (correction_fields_of_chart v U x₀ θ η A r T ε₀ θRadius W hr2 hθR hv_per
    hεspace hWsmooth hWcompact hWdiv hWtsupp hWformula hWcancel hpacket).2.2.2.2.2.1

/-- `correction_cancels` (verbatim). -/
example : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
    ∃ O : Set Space, IsOpen O ∧
      tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ O ∧
      ∀ x ∈ O, correctedBackground v (fun ε => latticeLift (W ε)) ε (t, x) = 0 :=
  (correction_fields_of_chart v U x₀ θ η A r T ε₀ θRadius W hr2 hθR hv_per
    hεspace hWsmooth hWcompact hWdiv hWtsupp hWformula hWcancel hpacket).2.2.2.2.2.2

end FieldTypes

/- ### Part B: non-vacuity — a nonzero smooth bump whose lift is nonzero and periodic. -/
section NonVacuity

/-- A scalar `ContDiffBump` at the origin of radii `1/8 < 1/4`. -/
def bumpF : ContDiffBump (0 : Space) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A concrete nonzero smooth compactly supported chart correction. -/
def wBump : SpaceTimeField := fun z => bumpF z.2 • coordinateVector 0

example : ContDiff ℝ ∞ wBump :=
  (bumpF.contDiff.comp contDiff_snd).smul contDiff_const

example : IsPeriodicOn univ (latticeLift wBump) := latticeLift_periodic wBump

/-- The lift is genuinely nonzero: it agrees with the bump at the origin. -/
example : latticeLift wBump (0, (0 : Space)) ≠ 0 := by
  have hslice : ∀ (t : ℝ) (y : Space), wBump (t, y) ≠ 0 → y ∈ ball (0 : Space) (1 / 4) := by
    intro t y hy
    have hb : bumpF y ≠ 0 := by
      intro h0; apply hy; simp [wBump, h0]
    have hmem : y ∈ Function.support (fun z => bumpF z) := hb
    rw [bumpF.support_eq] at hmem
    exact hmem
  have hx0 : (0 : Space) ∈ ball (0 : Space) (1 / 4 : ℝ) := by
    rw [mem_ball, dist_self]; norm_num
  have heq : latticeLift wBump (0, (0 : Space)) = wBump (0, (0 : Space)) :=
    latticeLift_eq_of_ball hslice (by norm_num) hx0
  rw [heq]
  have hf0 : bumpF (0 : Space) = 1 := by
    apply bumpF.one_of_mem_closedBall
    rw [mem_closedBall, dist_self]; exact bumpF.rIn_pos.le
  show bumpF (0 : Space) • coordinateVector 0 ≠ 0
  rw [hf0, one_smul]
  intro hcontra
  have h1 : (coordinateVector 0 : Space) 0 = (0 : Space) 0 := by rw [hcontra]
  simp [coordinateVector] at h1

end NonVacuity
