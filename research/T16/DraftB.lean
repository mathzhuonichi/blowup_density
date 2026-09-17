import Contracts.V1.Correction

/-! Independent T16 draft B. Statements only; `03-torus.tex:167-215`.
The physical layer is periodic fields on R³. No Sobolev quantity occurs in
this node: the coefficient datum/norm layer belongs to T10 and the estimates
to T17. The new periodic vocabulary below needs registration / to be aligned
with T10. Euclidean operators and scaled cutoffs are reused verbatim from
Contracts.V1.Correction, whose binding already guards their spellings. -/

noncomputable section
namespace BlowupDensity.T16.DraftB
open BlowupDensity.Contracts.V1
open Set MeasureTheory
open scoped ContDiff Topology

/-- Integer translations of the unit torus (`02-preliminaries.tex:28`).
Needs registration / to be aligned with T10. -/
def latticeVector (k : Fin 3 → ℤ) : Space := WithLp.toLp 2 (fun i => (k i : ℝ))

/-- Physical periodicity (`02-preliminaries.tex:28`).
Needs registration / to be aligned with T10. -/
def IsPeriodic (f : VelocityField) : Prop :=
  ∀ t x k, f (t, x + latticeVector k) = f (t, x)

/-- Lift of a torus support to R³ (`03-torus.tex:188,212`).
Needs registration / to be aligned with T10. -/
def periodicSet (S : Set Space) : Set Space :=
  {x | ∃ k : Fin 3 → ℤ, x - latticeVector k ∈ S}

/-- Periodic extension of a localized packet (`03-torus.tex:112-119,214`).
Only used for compact spatially supported slices, where the sum is locally
finite. Needs registration / to be aligned with T10/T15. -/
def periodicScaledPacket (U : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  fun z => ∑' k : Fin 3 → ℤ, scaledPacket U x₀ T ε (z.1, z.2 - latticeVector k)

/-- The corrected background b_ε = v + w_ε (`03-torus.tex:190-192`).
Needs registration / to be aligned with T10. -/
def correctedBackground (v : VelocityField) (w : ℝ → VelocityField) (ε : ℝ) :
    VelocityField := fun z => v z + w ε z

/-- Construction witnesses, chosen before ε (`03-torus.tex:179-188,212`).
Data live in Type so the clause record itself can live in Prop. These are
radii/thresholds, not universal estimate constants (there are none in T16). -/
structure CutoffData where
  θ : Space → ℝ
  η : ℝ → ℝ
  plateau : Set Space
  θRadius : ℝ
  ε₀ : ℝ
  potential : VelocityField
  correction : ℝ → VelocityField

/-- Clauses of lem:potential, `03-torus.tex:176-215`. All witnesses are shared
across all sufficiently small ε. The local curl formula is stated in the
chosen chart; its periodic extension has translated, not compact R³ support.
Field names agree with I02 wherever the mathematical objects coincide. -/
structure LocalPotentialAPI (v U : VelocityField) (K : Set Space)
    (x₀ : Space) (r T δ : ℝ) (D : CutoffData) : Prop where
  /-- Smooth Urysohn cutoff, `03-torus.tex:167-181`. -/
  theta_smooth : ContDiff ℝ ∞ D.θ
  /-- `03-torus.tex:172,181`. -/
  theta_compactSupport : HasCompactSupport D.θ
  /-- `03-torus.tex:172`. -/
  theta_range : ∀ x, D.θ x ∈ Icc (0 : ℝ) 1
  /-- `03-torus.tex:181`, neighborhood rather than equality on K alone. -/
  plateau_open : IsOpen D.plateau
  /-- Prescribed enlarged K_*, as in I02 V2; `03-torus.tex:101,181`. -/
  prescribed_subset_plateau : K ⊆ D.plateau
  /-- `03-torus.tex:181`. -/
  theta_one : EqOn D.θ (fun _ => 1) D.plateau
  /-- Auxiliary support radius, `03-torus.tex:212`. -/
  theta_radius_pos : 0 < D.θRadius
  /-- `03-torus.tex:181,212`. -/
  theta_support : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius
  /-- `03-torus.tex:174,182`. -/
  eta_smooth : ContDiff ℝ ∞ D.η
  /-- `03-torus.tex:182`. -/
  eta_compactSupport : HasCompactSupport D.η
  /-- `03-torus.tex:172-174`. -/
  eta_range : ∀ t, D.η t ∈ Icc (0 : ℝ) 1
  /-- `03-torus.tex:182`. -/
  eta_one : EqOn D.η (fun _ => 1) (Icc (-1 : ℝ) 1)
  /-- `03-torus.tex:182`. -/
  eta_support : tsupport D.η ⊆ Ioo (-2 : ℝ) 2
  /-- `03-torus.tex:188,212`. -/
  eps_pos : 0 < D.ε₀
  /-- `03-torus.tex:212`. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, 2 * ε ^ 2 < min T δ
  /-- `03-torus.tex:212`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ε * D.θRadius < r
  /-- Local smoothness only; `03-torus.tex:177-180`. -/
  potential_smooth : ContDiffOn ℝ ∞ D.potential
    (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r)
  /-- Radial formula eq:potential; `03-torus.tex:179`. -/
  potential_formula : ∀ t x, D.potential (t, x) =
    ∫ ρ in (0 : ℝ)..1, ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)
  /-- `03-torus.tex:181,196-210`. -/
  potential_curl : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
    curl (fun y => D.potential (t, y)) x = v (t, x)
  /-- eq:cutoff in the chart; scaled cutoff definitions are imported verbatim.
  `03-torus.tex:183-187,212`. -/
  correction_formula : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t, ∀ x ∈ Metric.ball x₀ r,
    D.correction ε (t, x) = -curl (fun y =>
      (scaledTemporalCutoff D.η T ε t * scaledSpatialCutoff D.θ x₀ ε y) •
        D.potential (t, y)) x
  /-- Global smoothness including through T; `03-torus.tex:188,212`. -/
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ContDiff ℝ ∞ (D.correction ε)
  /-- `03-torus.tex:212`. -/
  correction_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, IsPeriodic (D.correction ε)
  /-- `03-torus.tex:188,212`. -/
  correction_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t x,
    spatialDivergence (D.correction ε) t x = 0
  /-- Temporal support; `03-torus.tex:188-189,212`. -/
  correction_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (D.correction ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ (univ : Set Space)
  /-- Spatial support on the torus, expressed on its periodic lift;
  `03-torus.tex:188,212`. -/
  correction_support_ball : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
    tsupport (fun x => D.correction ε (t, x)) ⊆ periodicSet (Metric.ball x₀ r)
  /-- eq:bgzero during the active interval, including its left endpoint;
  `03-torus.tex:190-193,214-215`. -/
  correction_cancels : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
    ∃ O : Set Space, IsOpen O ∧
      tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ O ∧
      ∀ x ∈ O, correctedBackground v D.correction ε (t, x) = 0

/-- Exact construction quantifiers (`03-torus.tex:101-105,164-188,212-215`).
The ball is an injective Euclidean chart (r < 1/2). Only smoothness and
incompressibility locally are used, not the reference momentum equation.
U is arbitrary with the packet's spatial support property; no packet theorem
is assumed. All witnesses precede ε, which is quantified inside the API. -/
def localPotentialStatement : Prop :=
  ∀ (v U : VelocityField) (K : Set Space) (x₀ : Space) (r T δ : ℝ),
    0 < r → r < 1 / 2 → 0 < T → 0 < δ → IsCompact K →
    IsPeriodic v →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) →
    ∃ D : CutoffData, LocalPotentialAPI v U K x₀ r T δ D

end BlowupDensity.T16.DraftB
