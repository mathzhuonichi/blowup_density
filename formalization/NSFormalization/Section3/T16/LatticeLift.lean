import NSFormalization.Section3.T16.LocalPotential
import NavierStokes.PeriodicLocalization
import NavierStokes.ResidualRegularity
import NavierStokes.CompactForceDecay

/-!
# T16 (`lem:potential`), gap 2: the unit-periodic lift of a compactly supported chart correction

This module supplies the reusable analytic content behind the seven `correction_*`
fields of `NSFormalization.Section3.T16.LocalPotentialAPI`
(`Section3/T16/LocalPotential.lean`): the **lattice lift** of a chart correction
`w` (smooth on `ℝ × ℝ³`, spatial slice support in `ball x₀ ρ`, `ρ < 1/2`).

The lift is the genuine sum over integer lattice translations
`latticeLift w z = ∑' k, w (z.1, z.2 - latticeVector k)`.  It is **definitionally**
OpenAI's `NavierStokes.PeriodicLocalization.periodize` (the frequency lattice
`latticeVector = lattice` agrees by `rfl`, and the index types agree), so all
local-finiteness, smoothness and periodicity infrastructure of that module is
reused verbatim through `latticeLift_eq_periodize`.

For each field we prove the transport lemma "property of `w` ⇒ property of
`latticeLift w`":

* `latticeLift_smooth`      — `ContDiff ℝ ∞` (upstream `contDiff_periodize`);
* `latticeLift_periodic`    — `IsPeriodicOn univ` (upstream `unitSpatialPeriodsOn_periodize`);
* `latticeLift_eq_of_ball`  — on `ball x₀ r` (with `r + ρ ≤ 1`) the lift is its
  `k = 0` term `w`, by disjointness of the translated balls (`tsum_eq_single 0`);
* `latticeLift_divergence_zero` — divergence of the lift is zero, through the local
  finite sum and translation invariance of the spatial derivative;
* `latticeLift_timeSupport` — the compact time support is inherited;
* `latticeLift_sliceSupport` — each spatial slice is supported in `periodicSet (ball x₀ r)`;
* `latticeLift_cancels`     — the periodic corrected background vanishes on `periodicSet (ball x₀ r)`.

The packaged theorem `correction_fields_of_chart` collects the seven canonical
field statements for a scale-indexed chart family `W`, so lane 353 (assembly)
fills `LocalPotentialAPI.correction` with `fun ε => latticeLift (W ε)` by projection.
-/

noncomputable section

namespace NSFormalization.Section3.T16

open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.RadialPotential (cross)
open NSFormalization.Paper1.CorrectionProfile (spatialCutoff temporalCutoff)
open scoped ContDiff Topology BigOperators

/-! ## 0. The lift and its identification with the upstream periodization -/

/-- `03-torus.tex:188,212`: the unit-periodic lift to `R³` of a chart correction,
the genuine sum over integer lattice translations. -/
def latticeLift (w : SpaceTimeField) : SpaceTimeField :=
  fun z => ∑' k : NSFormalization.Section3.T10.PeriodicFrequency,
    w (z.1, z.2 - latticeVector k)

/-- The lattice frequency vector agrees coordinatewise with the raw integer. -/
theorem latticeVector_apply (k : NSFormalization.Section3.T10.PeriodicFrequency)
    (i : Fin 3) : latticeVector k i = (k i : ℝ) := rfl

/-- The zero frequency maps to the spatial origin. -/
theorem latticeVector_zero :
    latticeVector (0 : NSFormalization.Section3.T10.PeriodicFrequency) = 0 := by
  ext i
  simp [latticeVector_apply]

/-- The lift is definitionally OpenAI's spatial periodization: the frequency
lattice vectors coincide (`latticeVector = lattice` by `rfl`) and the index
types coincide, so the two `tsum`s are the same term. -/
theorem latticeLift_eq_periodize (w : SpaceTimeField) :
    latticeLift w = periodize w := rfl

/-! ## 1. Support bookkeeping -/

/-- Spatial slice support inside a ball forces the cube support bound OpenAI's
periodization machinery consumes. -/
theorem supportedInCube_of_ball {w : SpaceTimeField} {x₀ : Space} {ρ : ℝ}
    (h : ∀ z : SpaceTime, w z ≠ 0 → z.2 ∈ ball x₀ ρ) :
    SupportedInCube (ρ + ‖x₀‖) w := by
  intro z hz i
  have hb := h z hz
  rw [mem_ball, dist_eq_norm] at hb
  have h1 : |(z.2 - x₀) i| ≤ ‖z.2 - x₀‖ := by
    have := PiLp.norm_apply_le (z.2 - x₀) i
    rwa [Real.norm_eq_abs] at this
  have h1' : |z.2 i - x₀ i| ≤ ‖z.2 - x₀‖ := by
    have he : (z.2 - x₀) i = z.2 i - x₀ i := by simp
    rwa [he] at h1
  have h2 : |x₀ i| ≤ ‖x₀‖ := by
    have := PiLp.norm_apply_le x₀ i
    rwa [Real.norm_eq_abs] at this
  have h3 : |z.2 i| ≤ |z.2 i - x₀ i| + |x₀ i| := by
    calc |z.2 i| = |(z.2 i - x₀ i) + x₀ i| := by ring_nf
      _ ≤ |z.2 i - x₀ i| + |x₀ i| := abs_add_le _ _
  linarith

/-- A Euclidean ball is contained in the coordinatewise cube of the same radius. -/
theorem coord_of_ball {x₀ x : Space} {ρ : ℝ} (i : Fin 3) (hx : x ∈ ball x₀ ρ) :
    |x i - x₀ i| < ρ := by
  rw [mem_ball, dist_eq_norm] at hx
  have h1 : |(x - x₀) i| ≤ ‖x - x₀‖ := by
    have := PiLp.norm_apply_le (x - x₀) i
    rwa [Real.norm_eq_abs] at this
  have he : (x - x₀) i = x i - x₀ i := by simp
  rw [he] at h1
  linarith

/-! ## 2. Smoothness and periodicity (reused verbatim from OpenAI) -/

/-- The lift of a smooth, spatially compactly supported chart correction is
globally smooth. -/
theorem latticeLift_smooth {w : SpaceTimeField} {x₀ : Space} {ρ : ℝ}
    (hcd : ContDiff ℝ ∞ w)
    (hsupp : ∀ z : SpaceTime, w z ≠ 0 → z.2 ∈ ball x₀ ρ) :
    ContDiff ℝ ∞ (latticeLift w) := by
  rw [latticeLift_eq_periodize]
  exact contDiff_periodize (supportedInCube_of_ball hsupp) hcd

/-- The lift is unit-periodic in space. -/
theorem latticeLift_periodic (w : SpaceTimeField) :
    IsPeriodicOn univ (latticeLift w) := by
  intro t ht x i
  rw [latticeLift_eq_periodize]
  exact unitSpatialPeriodsOn_periodize w univ t ht x i

/-! ## 3. Ball locality: the lift equals its `k = 0` term -/

/-- On `ball x₀ r`, with `r + ρ ≤ 1` and slice support in `ball x₀ ρ`, the
translated supports are pairwise disjoint, so the lift collapses to the chart
correction itself.  This is `tsum_eq_single 0` from the coordinate estimate. -/
theorem latticeLift_eq_of_ball {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 1) {t : ℝ} {x : Space} (hx : x ∈ ball x₀ r) :
    latticeLift w (t, x) = w (t, x) := by
  have hzero : ∀ k : NSFormalization.Section3.T10.PeriodicFrequency, k ≠ 0 →
      w (t, x - latticeVector k) = 0 := by
    intro k hk
    by_contra hne
    apply hk
    funext i
    have hyi : |(x - latticeVector k) i - x₀ i| < ρ :=
      coord_of_ball i (hslice t (x - latticeVector k) hne)
    have hxi : |x i - x₀ i| < r := coord_of_ball i hx
    have hsub : (x - latticeVector k) i = x i - (k i : ℝ) := by
      simp [latticeVector_apply]
    rw [hsub] at hyi
    have hy2 := abs_lt.mp hyi
    have hx2 := abs_lt.mp hxi
    have hlo : (-1 : ℝ) < (k i : ℝ) := by linarith [hy2.1, hy2.2, hx2.1, hx2.2]
    have hhi : (k i : ℝ) < 1 := by linarith [hy2.1, hy2.2, hx2.1, hx2.2]
    have a1 : (-1 : ℤ) < k i := by exact_mod_cast hlo
    have a2 : k i < (1 : ℤ) := by exact_mod_cast hhi
    have : k i = 0 := by omega
    simpa using this
  show (∑' k : NSFormalization.Section3.T10.PeriodicFrequency,
      w (t, x - latticeVector k)) = w (t, x)
  rw [tsum_eq_single (0 : NSFormalization.Section3.T10.PeriodicFrequency) hzero,
    latticeVector_zero, sub_zero]

/-! ## 4. Divergence-free -/

/-- Local agreement of the spatial slices at a fixed time transports the
Euclidean divergence. -/
theorem sdiv_congr {u v : VelocityField} (t : ℝ) (x : Space)
    (h : u =ᶠ[𝓝 (t, x)] v) : spatialDivergence u t x = spatialDivergence v t x := by
  have hslice : (fun y : Space => u (t, y)) =ᶠ[𝓝 x] (fun y : Space => v (t, y)) :=
    h.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  simp only [spatialDivergence, spatialDerivative]
  rw [hslice.fderiv_eq]

/-- A spatial lattice translation shifts the argument of the divergence. -/
theorem spatialDivergence_translate {w : SpaceTimeField} (hcd : ContDiff ℝ ∞ w)
    (n : Lattice) (t : ℝ) (x : Space) :
    spatialDivergence (translate w n) t x = spatialDivergence w t (x - lattice n) := by
  have hslice : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hcd.comp (contDiff_const.prodMk contDiff_id)
  have h1 : HasFDerivAt (fun y : Space => w (t, y))
      (fderiv ℝ (fun y : Space => w (t, y)) (x - lattice n)) (x - lattice n) :=
    (hslice.differentiable (by simp) (x - lattice n)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Space => y - lattice n)
      (ContinuousLinearMap.id ℝ Space) x := (hasFDerivAt_id x).sub_const (lattice n)
  have hcomp := h1.comp x h2
  have hsd : spatialDerivative (translate w n) t x
      = spatialDerivative w t (x - lattice n) := by
    show fderiv ℝ (fun y : Space => translate w n (t, y)) x
       = fderiv ℝ (fun y : Space => w (t, y)) (x - lattice n)
    calc fderiv ℝ (fun y : Space => translate w n (t, y)) x
        = fderiv ℝ ((fun y : Space => w (t, y)) ∘ (fun y : Space => y - lattice n)) x := rfl
      _ = (fderiv ℝ (fun y : Space => w (t, y)) (x - lattice n)).comp
            (ContinuousLinearMap.id ℝ Space) := hcomp.fderiv
      _ = fderiv ℝ (fun y : Space => w (t, y)) (x - lattice n) := by
            rw [ContinuousLinearMap.comp_id]
  simp only [spatialDivergence, hsd]

/-- The Euclidean divergence is additive on spatially differentiable fields. -/
theorem spatialDivergence_add {u v : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (hv : DifferentiableAt ℝ (fun y : Space => v (t, y)) x) :
    spatialDivergence (fun z => u z + v z) t x
      = spatialDivergence u t x + spatialDivergence v t x := by
  simp only [spatialDivergence, spatialDerivative, fderiv_fun_add hu hv,
    add_apply, PiLp.add_apply, Finset.sum_add_distrib]

/-- The Euclidean divergence of a finite sum of spatially differentiable fields
is the sum of the divergences. -/
theorem spatialDivergence_finsetSum {ι : Type*} (s : Finset ι) (F : ι → VelocityField)
    (t : ℝ) (x : Space)
    (hF : ∀ n : ι, DifferentiableAt ℝ (fun y : Space => F n (t, y)) x) :
    spatialDivergence (fun z => ∑ n ∈ s, F n z) t x
      = ∑ n ∈ s, spatialDivergence (F n) t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spatialDivergence, spatialDerivative]
  | @insert a s ha ih =>
    have hfun : (fun z : SpaceTime => ∑ n ∈ insert a s, F n z)
        = (fun z : SpaceTime => F a z + ∑ n ∈ s, F n z) := by
      funext z; rw [Finset.sum_insert ha]
    have hsum : DifferentiableAt ℝ (fun y : Space => ∑ n ∈ s, F n (t, y)) x :=
      DifferentiableAt.fun_sum (fun n _ => hF n)
    rw [Finset.sum_insert ha, hfun, spatialDivergence_add (hF a) hsum, ih]

/-- The lift of a divergence-free chart correction is divergence free. -/
theorem latticeLift_divergence_zero {w : SpaceTimeField} {x₀ : Space} {ρ : ℝ}
    (hcd : ContDiff ℝ ∞ w)
    (hsupp : ∀ z : SpaceTime, w z ≠ 0 → z.2 ∈ ball x₀ ρ)
    (hdivw : ∀ t x, spatialDivergence w t x = 0) (t : ℝ) (x : Space) :
    spatialDivergence (latticeLift w) t x = 0 := by
  rw [latticeLift_eq_periodize]
  obtain ⟨N, hN⟩ := periodize_locally_eq_sum (supportedInCube_of_ball hsupp) (t, x)
  rw [sdiv_congr t x hN]
  rw [spatialDivergence_finsetSum _ (fun n => translate w n) t x (fun n => ?diff)]
  · apply Finset.sum_eq_zero
    intro n _
    rw [spatialDivergence_translate hcd n t x]
    exact hdivw t (x - lattice n)
  · exact (hcd.comp (contDiff_const.prodMk (contDiff_id.sub contDiff_const))).differentiable
      (by simp) x

/-! ## 5. Time support and spatial slice support -/

/-- Spatial periodization preserves the compact time support: only the same
time coordinates carry any mass. -/
theorem latticeLift_timeSupport {w : SpaceTimeField} {a b : ℝ}
    (hcs : HasCompactSupport w)
    (htsupp : tsupport w ⊆ Ioo a b ×ˢ (univ : Set Space)) :
    tsupport (latticeLift w) ⊆ Ioo a b ×ˢ (univ : Set Space) := by
  rw [latticeLift_eq_periodize]
  have hsuppsub : Function.support (periodize w)
      ⊆ (Prod.fst '' tsupport w) ×ˢ (univ : Set Space) := by
    intro z hz
    have hex : ∃ n : Lattice, translate w n z ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hz (by simp only [periodize, hcon, tsum_zero])
    obtain ⟨n, hn⟩ := hex
    refine ⟨⟨(z.1, z.2 - lattice n), subset_tsupport w hn, rfl⟩, mem_univ _⟩
  have hcl : IsClosed ((Prod.fst '' tsupport w) ×ˢ (univ : Set Space)) :=
    (IsCompact.image hcs continuous_fst).isClosed.prod isClosed_univ
  refine (closure_minimal hsuppsub hcl).trans ?_
  apply Set.prod_mono _ (subset_refl _)
  rintro _ ⟨p, hp, rfl⟩
  exact (htsupp hp).1

/-- Each spatial slice of the lift is supported in the periodic lift of the
coordinate ball `ball x₀ r`. -/
theorem latticeLift_sliceSupport {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : ρ < r) (t : ℝ) :
    tsupport (fun x => latticeLift w (t, x)) ⊆ periodicSet (ball x₀ r) := by
  have hsc : SupportedInCube (ρ + ‖x₀‖) w :=
    supportedInCube_of_ball (fun z hz => hslice z.1 z.2 hz)
  intro x hx
  by_contra hxnot
  obtain ⟨N, hN⟩ := periodize_locally_eq_sum hsc (t, x)
  have hNs : (fun y => latticeLift w (t, y)) =ᶠ[𝓝 x]
      (fun y => ∑ n ∈ latticeBoxFinset N, translate w n (t, y)) := by
    have htend : Tendsto (fun y : Space => (t, y)) (𝓝 x) (𝓝 (t, x)) :=
      (continuousAt_const.prodMk continuousAt_id)
    filter_upwards [htend.eventually hN] with y hy
    rw [latticeLift_eq_periodize]
    exact hy
  have hterm : ∀ n ∈ latticeBoxFinset N,
      (fun y => translate w n (t, y)) =ᶠ[𝓝 x] 0 := by
    intro n hn
    rw [← notMem_tsupport_iff_eventuallyEq]
    intro hxin
    have hsuppn : Function.support (fun y : Space => translate w n (t, y))
        ⊆ ball (x₀ + lattice n) ρ := by
      intro y hy
      have hyne : w (t, y - lattice n) ≠ 0 := hy
      have hyb := hslice t (y - lattice n) hyne
      rw [mem_ball, dist_eq_norm] at hyb ⊢
      have heq : y - (x₀ + lattice n) = y - lattice n - x₀ := by abel
      rw [heq]
      exact hyb
    have htsuppn : tsupport (fun y : Space => translate w n (t, y))
        ⊆ closedBall (x₀ + lattice n) ρ :=
      closure_minimal (hsuppn.trans ball_subset_closedBall) isClosed_closedBall
    have hxball := htsuppn hxin
    rw [mem_closedBall, dist_eq_norm] at hxball
    apply hxnot
    refine ⟨n, ?_⟩
    rw [mem_ball, dist_eq_norm]
    have hlv : latticeVector n = lattice n := rfl
    rw [hlv]
    have heq : x - lattice n - x₀ = x - (x₀ + lattice n) := by abel
    rw [heq]
    exact lt_of_le_of_lt hxball hρr
  have hzero : (fun y => ∑ n ∈ latticeBoxFinset N, translate w n (t, y)) =ᶠ[𝓝 x] 0 := by
    have hall : ∀ᶠ y in 𝓝 x, ∀ n ∈ latticeBoxFinset N, translate w n (t, y) = 0 :=
      (eventually_all_finset _).mpr (fun n hn => hterm n hn)
    filter_upwards [hall] with y hy
    simp only [Pi.zero_apply]
    exact Finset.sum_eq_zero hy
  exact absurd hx (notMem_tsupport_iff_eventuallyEq.mpr (hNs.trans hzero))

/-! ## 6. Cancellation: the periodic corrected background vanishes -/

/-- A unit-periodic spacetime field is invariant under every integer lattice
translation.  This is OpenAI's `periodic_integerShift` transported through the
coordinate identification `integerShift = latticeVector`. -/
theorem isPeriodicOn_sub_latticeVector {E : Type*} {f : SpaceTime → E}
    (hf : IsPeriodicOn univ f) (t : ℝ) (x : Space)
    (k : NSFormalization.Section3.T10.PeriodicFrequency) :
    f (t, x - latticeVector k) = f (t, x) := by
  have hshift : NavierStokes.CompactForceDecay.integerShift k = latticeVector k := by
    ext i
    simp [NavierStokes.CompactForceDecay.integerShift_apply, latticeVector_apply]
  have hp := NavierStokes.CompactForceDecay.periodic_integerShift (g := f) hf t k
  have := hp.sub_eq x
  rw [hshift] at this
  exact this

/-- The corrected background `v + latticeLift w` vanishes on the entire periodic
lift of `ball x₀ r`, given the chart cancellation on `ball x₀ r` and periodicity
of `v`.  Packaged as the existential of `correction_cancels`, with the open set
`periodicSet (ball x₀ r)` and a supplied packet-support bound. -/
theorem latticeLift_cancels {v w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hv_per : IsPeriodicOn univ v)
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 1)
    {t : ℝ} (hcancel : ∀ x ∈ ball x₀ r, v (t, x) + w (t, x) = 0)
    {P : Space → Space} (hpacket : tsupport (fun x => P x) ⊆ periodicSet (ball x₀ r)) :
    ∃ O : Set Space, IsOpen O ∧ tsupport (fun x => P x) ⊆ O ∧
      ∀ x ∈ O, v (t, x) + latticeLift w (t, x) = 0 := by
  refine ⟨periodicSet (ball x₀ r), ?_, hpacket, ?_⟩
  · -- `periodicSet (ball x₀ r)` is a union of open balls, hence open.
    have hEq : periodicSet (ball x₀ r)
        = ⋃ k : NSFormalization.Section3.T10.PeriodicFrequency,
            (fun x : Space => x - latticeVector k) ⁻¹' ball x₀ r := by
      ext x
      simp only [periodicSet, mem_setOf_eq, mem_iUnion, mem_preimage]
    rw [hEq]
    exact isOpen_iUnion fun k =>
      (isOpen_ball.preimage (continuous_id.sub continuous_const))
  · intro x hx
    obtain ⟨k, hk⟩ := hx
    -- reduce both fields to the fundamental copy `x - latticeVector k ∈ ball x₀ r`
    have hvx : v (t, x) = v (t, x - latticeVector k) :=
      (isPeriodicOn_sub_latticeVector hv_per t x k).symm
    have hwx : latticeLift w (t, x) = latticeLift w (t, x - latticeVector k) :=
      (isPeriodicOn_sub_latticeVector (latticeLift_periodic w) t x k).symm
    have hwsingle : latticeLift w (t, x - latticeVector k) = w (t, x - latticeVector k) :=
      latticeLift_eq_of_ball hslice hρr hk
    rw [hvx, hwx, hwsingle]
    exact hcancel (x - latticeVector k) hk

/-! ## 7. Packaged conclusion for the assembly (`correction_*` fields) -/

/-- The seven `correction_*` fields of `LocalPotentialAPI`, in their exact
canonical spellings, realized by the lattice lift `fun ε => latticeLift (W ε)`
of a scale-indexed chart-correction family `W`.

Every hypothesis is a transportable chart fact (smoothness, compact support,
divergence-freeness, the product support bound `Ioo … ×ˢ ball x₀ (ε·θRadius)`,
the chart curl formula, the chart cancellation on `ball x₀ r`, and the T14 packet
support bound); the conclusion transports each to the periodic lift.  Lane 353
fills `LocalPotentialAPI.correction := fun ε => latticeLift (W ε)` by projection. -/
theorem correction_fields_of_chart
    (v U : SpaceTimeField) (x₀ : Space) (θ : Space → ℝ) (η : ℝ → ℝ) (A : SpaceTimeField)
    (r T ε₀ θRadius : ℝ) (W : ℝ → SpaceTimeField)
    (hr2 : r < 1 / 2) (hθR : 0 < θRadius)
    (hv_per : IsPeriodicOn univ v)
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
      tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ periodicSet (ball x₀ r)) :
    (∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, ∀ x ∈ ball x₀ r,
        latticeLift (W ε) (t, x) =
          -SpatialCurl.curl (fun y =>
            (temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • A (t, y)) x) ∧
    (∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (latticeLift (W ε))) ∧
    (∀ ε ∈ Ioc (0 : ℝ) ε₀, IsPeriodicOn univ (latticeLift (W ε))) ∧
    (∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t x, spatialDivergence (latticeLift (W ε)) t x = 0) ∧
    (∀ ε ∈ Ioc (0 : ℝ) ε₀,
      tsupport (latticeLift (W ε)) ⊆
        Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ (univ : Set Space)) ∧
    (∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t,
      tsupport (fun x => latticeLift (W ε) (t, x)) ⊆ periodicSet (ball x₀ r)) ∧
    (∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
      ∃ O : Set Space, IsOpen O ∧
        tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ O ∧
        ∀ x ∈ O, correctedBackground v (fun ε => latticeLift (W ε)) ε (t, x) = 0) := by
  -- the per-scale support facts shared by every field
  have hslice : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ (t : ℝ) (y : Space),
      W ε (t, y) ≠ 0 → y ∈ ball x₀ (ε * θRadius) := by
    intro ε hε t y hy
    exact ((hWtsupp ε hε) (subset_tsupport _ hy)).2
  have hsupp : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z : SpaceTime,
      W ε z ≠ 0 → z.2 ∈ ball x₀ (ε * θRadius) := by
    intro ε hε z hz
    exact ((hWtsupp ε hε) (subset_tsupport _ hz)).2
  have hsum : ∀ ε ∈ Ioc (0 : ℝ) ε₀, r + ε * θRadius ≤ 1 := by
    intro ε hε
    have := hεspace ε hε
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- correction_formula
    intro ε hε t x hx
    rw [latticeLift_eq_of_ball (hslice ε hε) (hsum ε hε) hx]
    exact hWformula ε hε t x hx
  · -- correction_smooth
    intro ε hε
    exact latticeLift_smooth (hWsmooth ε hε) (hsupp ε hε)
  · -- correction_periodic
    intro ε _
    exact latticeLift_periodic (W ε)
  · -- correction_divergence_free
    intro ε hε t x
    exact latticeLift_divergence_zero (hWsmooth ε hε) (hsupp ε hε) (hWdiv ε hε) t x
  · -- correction_support (time window)
    intro ε hε
    exact latticeLift_timeSupport (hWcompact ε hε)
      ((hWtsupp ε hε).trans (Set.prod_mono (subset_refl _) (subset_univ _)))
  · -- correction_support_ball (spatial slice)
    intro ε hε t
    exact latticeLift_sliceSupport (hslice ε hε) (hεspace ε hε) t
  · -- correction_cancels
    intro ε hε t ht
    exact latticeLift_cancels hv_per (hslice ε hε) (hsum ε hε)
      (hWcancel ε hε t ht) (hpacket ε hε t ht)

end NSFormalization.Section3.T16
