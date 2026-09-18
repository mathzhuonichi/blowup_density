import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section4.I02.Reference

/-!
# T17 (`lem:correction`), unit U2: the concrete correction data and the
force-operator transport

This module (`research/T17/T17_SPLIT.md`, unit U2 — the critical-path bridge
that U5–U11 rewrite through) provides:

* `correctionData` — T16's `localPotentialData` witness, re-run at the
  placement data, whose `correction` field is by construction the unit-periodic
  lattice lift `latticeLift (physicalCorrection v x₀ T θ η ε)` of the single
  Euclidean copy on which Section 4's `I02.CorrectionAPI` is built
  (`correctionData_correction`, `rfl`);
* `correctionForce` — the T17 spelling of `eq:H` (`03-torus.tex:219-223`,
  copied verbatim from `research/T17/Spec.lean:726-733`): `∂ₜw − ν•Δw + Dw(v) +
  Dv(w) + advection w`, with `(v·∇)w` third and `(w·∇)v` fourth;
* `force_eq` — the transport identity (`03-torus.tex:219-223`): with a periodic
  reference `v`, the T17 correction force of the periodized correction equals the
  periodization `latticeLift (Source.correctionForce ν v (physicalCorrection …))`
  of the Section 4 single-copy correction force;
* `correctionForce_periodic` — periodicity of the force (`03-torus.tex:225`), a
  corollary via `T16.latticeLift_periodic`.

## Route of `force_eq`

Both differential operators are local, so the identity is proved pointwise, by
cases on whether `x` lies in a periodic copy of the reference ball
`periodicSet (ball x₀ r)`:

* **inside** — the lift equals a single translate near `x`
  (`T16.latticeLift_eq_of_ball` + `T16.latticeLift_periodic` +
  `T16.isPeriodicOn_sub_latticeVector`), and each operator is
  translation-equivariant (`temporalDerivative_translate`,
  `spatialDerivative_translate`, `spatialLaplacian_translate`,
  `advection_translate`, the analogues of `T16.spatialDivergence_translate`).
  The two `v`-cross terms are matched by periodicity of `v` (its value, and its
  derivative on the reference cylinder where it is smooth);
* **outside** — the lift is locally zero (`T16.latticeLift_sliceSupport`) and the
  single-copy force is supported in `closedBall x₀ (ε·θRadius)`
  (`source_correctionForce_support`), so both sides vanish.

No new estimate is proved; the whole content is transport plus the local
structure already established in T16.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization (lattice Lattice periodize SupportedInCube latticeBoxFinset)
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open NSFormalization.Source.PhysicalRemoval (physical_support physical_compact)
open scoped ContDiff Topology BigOperators

/-! ## Translation equivariance of the differential operators -/

/-- Time derivative commutes with a spatial lattice translation (definitional). -/
theorem temporalDerivative_translate (w : SpaceTimeField) (n : Lattice) (t : ℝ) (x : Space) :
    temporalDerivative (PeriodicLocalization.translate w n) t x
      = temporalDerivative w t (x - lattice n) := rfl

/-- Spatial derivative commutes with a spatial lattice translation.  Same proof
pattern as `T16.spatialDivergence_translate`. -/
theorem spatialDerivative_translate {w : SpaceTimeField} (hcd : ContDiff ℝ ∞ w)
    (n : Lattice) (t : ℝ) (x : Space) :
    spatialDerivative (PeriodicLocalization.translate w n) t x
      = spatialDerivative w t (x - lattice n) := by
  have hslice : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hcd.comp (contDiff_const.prodMk contDiff_id)
  have h1 : HasFDerivAt (fun y : Space => w (t, y))
      (fderiv ℝ (fun y : Space => w (t, y)) (x - lattice n)) (x - lattice n) :=
    (hslice.differentiable (by simp) (x - lattice n)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Space => y - lattice n)
      (ContinuousLinearMap.id ℝ Space) x := (hasFDerivAt_id x).sub_const (lattice n)
  have hcomp := h1.comp x h2
  show fderiv ℝ (fun y : Space => PeriodicLocalization.translate w n (t, y)) x
     = fderiv ℝ (fun y : Space => w (t, y)) (x - lattice n)
  calc fderiv ℝ (fun y : Space => PeriodicLocalization.translate w n (t, y)) x
      = fderiv ℝ ((fun y : Space => w (t, y)) ∘ (fun y : Space => y - lattice n)) x := rfl
    _ = (fderiv ℝ (fun y : Space => w (t, y)) (x - lattice n)).comp
          (ContinuousLinearMap.id ℝ Space) := hcomp.fderiv
    _ = fderiv ℝ (fun y : Space => w (t, y)) (x - lattice n) := by
          rw [ContinuousLinearMap.comp_id]

/-- The map `z ↦ spatialDerivative w t z eᵢ` is smooth when `w` is. -/
theorem contDiff_spatialDerivative_apply {w : SpaceTimeField} (hcd : ContDiff ℝ ∞ w)
    (t : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : Space => spatialDerivative w t z (coordinateVector i)) := by
  have hslice : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hcd.comp (contDiff_const.prodMk contDiff_id)
  have hfd : ContDiff ℝ ∞ (fun z : Space => fderiv ℝ (fun y : Space => w (t, y)) z) :=
    hslice.fderiv_right (le_refl _)
  simp only [spatialDerivative]
  exact hfd.clm_apply (contDiff_const (c := coordinateVector i))

/-- Spatial Laplacian commutes with a spatial lattice translation. -/
theorem spatialLaplacian_translate {w : SpaceTimeField} (hcd : ContDiff ℝ ∞ w)
    (n : Lattice) (t : ℝ) (x : Space) :
    spatialLaplacian (PeriodicLocalization.translate w n) t x
      = spatialLaplacian w t (x - lattice n) := by
  simp only [spatialLaplacian]
  apply Finset.sum_congr rfl
  intro i _
  have hfun : (fun y : Space => spatialDerivative (PeriodicLocalization.translate w n) t y
        (coordinateVector i))
      = (fun y : Space => spatialDerivative w t (y - lattice n) (coordinateVector i)) := by
    funext y; rw [spatialDerivative_translate hcd n t y]
  rw [hfun]
  have hg : ContDiff ℝ ∞ (fun z : Space => spatialDerivative w t z (coordinateVector i)) :=
    contDiff_spatialDerivative_apply hcd t i
  have h1 : HasFDerivAt (fun z : Space => spatialDerivative w t z (coordinateVector i))
      (fderiv ℝ (fun z : Space => spatialDerivative w t z (coordinateVector i)) (x - lattice n))
      (x - lattice n) := (hg.differentiable (by simp) (x - lattice n)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Space => y - lattice n)
      (ContinuousLinearMap.id ℝ Space) x := (hasFDerivAt_id x).sub_const (lattice n)
  have hcomp := h1.comp x h2
  calc fderiv ℝ (fun y : Space => spatialDerivative w t (y - lattice n) (coordinateVector i)) x
        (coordinateVector i)
      = fderiv ℝ ((fun z : Space => spatialDerivative w t z (coordinateVector i)) ∘
          (fun y : Space => y - lattice n)) x (coordinateVector i) := rfl
    _ = ((fderiv ℝ (fun z : Space => spatialDerivative w t z (coordinateVector i))
          (x - lattice n)).comp (ContinuousLinearMap.id ℝ Space)) (coordinateVector i) := by
          rw [hcomp.fderiv]
    _ = fderiv ℝ (fun z : Space => spatialDerivative w t z (coordinateVector i)) (x - lattice n)
          (coordinateVector i) := by rw [ContinuousLinearMap.comp_id]

/-- Advection commutes with a spatial lattice translation. -/
theorem advection_translate {w : SpaceTimeField} (hcd : ContDiff ℝ ∞ w)
    (n : Lattice) (t : ℝ) (x : Space) :
    advection (PeriodicLocalization.translate w n) t x = advection w t (x - lattice n) := by
  simp only [advection]
  rw [spatialDerivative_translate hcd n t x]
  rfl

/-! ## The correction force respects germ equality and translation -/

/-- `Source.correctionForce` at a point depends on the correction only through
its germ there. -/
theorem source_correctionForce_congr {ν : ℝ} {v w w' : SpaceTimeField} {t : ℝ} {x : Space}
    (h : w =ᶠ[𝓝 (t, x)] w') :
    NSFormalization.Source.correctionForce ν v w (t, x)
      = NSFormalization.Source.correctionForce ν v w' (t, x) := by
  have hspace : (fun y : Space => w (t, y)) =ᶠ[𝓝 x] (fun y : Space => w' (t, y)) :=
    h.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  have htime : (fun s : ℝ => w (s, x)) =ᶠ[𝓝 t] (fun s : ℝ => w' (s, x)) :=
    h.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
  have hval : w (t, x) = w' (t, x) := h.eq_of_nhds
  have hSD : spatialDerivative w t x = spatialDerivative w' t x := by
    simp only [spatialDerivative]; exact hspace.fderiv_eq
  have hTD : temporalDerivative w t x = temporalDerivative w' t x := by
    simp only [temporalDerivative]; rw [htime.fderiv_eq]
  have hLap : spatialLaplacian w t x = spatialLaplacian w' t x := by
    simp only [spatialLaplacian]
    apply Finset.sum_congr rfl
    intro i _
    have hfde : fderiv ℝ (fun y : Space => w (t, y)) =ᶠ[𝓝 x]
        fderiv ℝ (fun y : Space => w' (t, y)) := hspace.fderiv
    have hfd : (fun y : Space => spatialDerivative w t y (coordinateVector i))
        =ᶠ[𝓝 x] (fun y : Space => spatialDerivative w' t y (coordinateVector i)) := by
      filter_upwards [hfde] with y hy
      simp only [spatialDerivative]; rw [hy]
    rw [hfd.fderiv_eq]
  have hAdv : advection w t x = advection w' t x := by
    simp only [advection, hSD, hval]
  simp only [NSFormalization.Source.correctionForce, hTD, hLap, hSD, hval, hAdv]

/-- The clean translation law of the whole force: modulo the two `v`-facts
(periodicity of the value and of the derivative applied to the shifted
correction), the force of a translated correction is the force at the shifted
point. -/
theorem source_force_translate {ν : ℝ} {v W : SpaceTimeField} (hW : ContDiff ℝ ∞ W)
    (n : Lattice) (t : ℝ) (x : Space)
    (hval : v (t, x) = v (t, x - lattice n))
    (hderiv : spatialDerivative v t x (W (t, x - lattice n))
      = spatialDerivative v t (x - lattice n) (W (t, x - lattice n))) :
    NSFormalization.Source.correctionForce ν v (PeriodicLocalization.translate W n) (t, x)
      = NSFormalization.Source.correctionForce ν v W (t, x - lattice n) := by
  simp only [NSFormalization.Source.correctionForce]
  rw [temporalDerivative_translate W n t x, spatialLaplacian_translate hW n t x,
    advection_translate hW n t x, spatialDerivative_translate hW n t x,
    show PeriodicLocalization.translate W n (t, x) = W (t, x - lattice n) from rfl,
    hderiv, hval]

/-! ## Vanishing of the force off the (slice) support -/

/-- The force vanishes at a point where the correction's spatial slice is
eventually zero and its time-fibre is identically zero. -/
theorem source_correctionForce_eq_zero {ν : ℝ} {v w : SpaceTimeField} {t : ℝ} {x : Space}
    (hslice : (fun y : Space => w (t, y)) =ᶠ[𝓝 x] 0)
    (htime : ∀ s : ℝ, w (s, x) = 0) :
    NSFormalization.Source.correctionForce ν v w (t, x) = 0 := by
  have hval : w (t, x) = 0 := htime t
  have hSD : spatialDerivative w t x = 0 := by
    simp only [spatialDerivative]; rw [hslice.fderiv_eq]; simp
  have hTD : temporalDerivative w t x = 0 := by
    have hz : (fun s : ℝ => w (s, x)) = fun _ => (0 : Space) := funext htime
    simp only [temporalDerivative, hz]; simp
  have hLap : spatialLaplacian w t x = 0 := by
    simp only [spatialLaplacian]
    apply Finset.sum_eq_zero
    intro i _
    have h0 : fderiv ℝ (fun y : Space => w (t, y)) =ᶠ[𝓝 x]
        (0 : Space → Space →L[ℝ] Space) := by simpa using hslice.fderiv
    have hfde : (fun y : Space => spatialDerivative w t y (coordinateVector i))
        =ᶠ[𝓝 x] (fun _ : Space => (0 : Space)) := by
      filter_upwards [h0] with y hy
      simp only [spatialDerivative, hy]; rfl
    rw [hfde.fderiv_eq]; simp
  simp only [NSFormalization.Source.correctionForce, hval, hSD, hTD, hLap, map_zero,
    zero_apply, advection]
  simp

/-- The force of the single-copy correction is spatially supported in
`closedBall x₀ ρ`, because each of its terms is a local operator of `W`. -/
theorem source_correctionForce_support {ν : ℝ} {v W : SpaceTimeField} {x₀ : Space} {ρ : ℝ}
    (hWslice : ∀ (s : ℝ) (y : Space), W (s, y) ≠ 0 → y ∈ ball x₀ ρ)
    (t : ℝ) (y : Space) (hy : y ∉ closedBall x₀ ρ) :
    NSFormalization.Source.correctionForce ν v W (t, y) = 0 := by
  have hsupp : tsupport (fun z : Space => W (t, z)) ⊆ closedBall x₀ ρ := by
    apply closure_minimal _ isClosed_closedBall
    intro z hz
    exact ball_subset_closedBall (hWslice t z hz)
  have hynot : y ∉ tsupport (fun z : Space => W (t, z)) := fun h => hy (hsupp h)
  have hslice : (fun z : Space => W (t, z)) =ᶠ[𝓝 y] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hynot
  have htime : ∀ s : ℝ, W (s, y) = 0 := by
    intro s
    by_contra hne
    exact hy (ball_subset_closedBall (hWslice s y hne))
  exact source_correctionForce_eq_zero hslice htime

/-! ## The concrete correction data and the T17 force -/

/-- The concrete `CutoffData` witness of T17: T16's `localPotentialData` re-run
at the placement's data.  Its `correction` field is the lattice lift of the
single Euclidean copy `physicalCorrection`. -/
def correctionData (v : SpaceTimeField) (x₀ : Space) (T : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ)
    (O : Set Space) (θR ε₀ : ℝ) : CutoffData :=
  localPotentialData v x₀ T θ η O θR ε₀

/-- The correction of `correctionData` is, definitionally, the lattice lift of
the single Euclidean copy. -/
theorem correctionData_correction (v : SpaceTimeField) (x₀ : Space) (T : ℝ) (θ : Space → ℝ)
    (η : ℝ → ℝ) (O : Set Space) (θR ε₀ ε : ℝ) :
    (correctionData v x₀ T θ η O θR ε₀).correction ε
      = latticeLift (physicalCorrection v x₀ T θ η ε) := rfl

/-- `03-torus.tex:219-223`: the T17 spelling of `eq:H`,
`∂ₜw − ν•Δw + Dw(v) + Dv(w) + advection w`, with `(v·∇)w` third and `(w·∇)v`
fourth.  Verbatim from `research/T17/Spec.lean:726-733` (only the namespace
changes). -/
def correctionForce (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    SpaceTimeField :=
  fun z =>
    temporalDerivative (D.correction ε) z.1 z.2 -
      ν • spatialLaplacian (D.correction ε) z.1 z.2 +
      spatialDerivative (D.correction ε) z.1 z.2 (v z) +
      spatialDerivative v z.1 z.2 (D.correction ε z) +
      advection (D.correction ε) z.1 z.2

/-- The T17 force spelling equals the Section 4 `Source.correctionForce`; the two
middle summands are written in the opposite (commutative) order. -/
theorem correctionForce_eq_source (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    correctionForce ν v D ε = NSFormalization.Source.correctionForce ν v (D.correction ε) := by
  funext z
  simp only [correctionForce, NSFormalization.Source.correctionForce]
  abel

/-! ## The transport identity -/

/-- **U2 (b)**: the force operator transports through the lattice lift.  With a
periodic reference `v`, the T17 correction force of the periodized correction is
the periodization of the Section 4 single-copy correction force. -/
theorem force_eq {ν : ℝ} {v : SpaceTimeField} {x₀ : Space} {T δ r : ℝ} {θ : Space → ℝ}
    {η : ℝ → ℝ} {O : Set Space} {θR ε₀ ε : ℝ}
    (hv : IsPeriodicOn univ v)
    (hvsm : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hθsm : ContDiff ℝ ∞ θ) (hηsm : ContDiff ℝ ∞ η)
    (hθcs : HasCompactSupport θ) (hηcs : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε : 0 < ε) (hεspace : ε * θR < r) (hεtime : 2 * ε ^ 2 < min T δ) :
    correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε
      = latticeLift (NSFormalization.Source.correctionForce ν v
          (physicalCorrection v x₀ T θ η ε)) := by
  rw [correctionForce_eq_source, correctionData_correction]
  set W := physicalCorrection v x₀ T θ η ε with hWdef
  have hWcd : ContDiff ℝ ∞ W := by
    rw [hWdef]
    exact physicalCorrection_contDiff hθsm hηsm hθcs hηcs hθsupp hηsupp hvsm hεtime hεspace hε
  have hWtsupp : tsupport W ⊆ Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ ball x₀ (ε * θR) := by
    rw [hWdef]
    exact physical_support hε v x₀ T hθcs hηcs hθsupp hηsupp
  have hWslice : ∀ (s : ℝ) (y : Space), W (s, y) ≠ 0 → y ∈ ball x₀ (ε * θR) := by
    intro s y hne; exact (hWtsupp (subset_tsupport W hne)).2
  have hρlt : ε * θR < r := hεspace
  have hsum : r + ε * θR ≤ 1 := by linarith
  have h2r : r + r ≤ 1 := by linarith
  have hGslice : ∀ (s : ℝ) (y : Space),
      NSFormalization.Source.correctionForce ν v W (s, y) ≠ 0 → y ∈ ball x₀ r := by
    intro s y hne
    by_contra hy
    apply hne
    apply source_correctionForce_support hWslice s y
    intro hyc
    exact hy (closedBall_subset_ball hρlt hyc)
  funext z
  obtain ⟨t, x⟩ := z
  by_cases hx : x ∈ periodicSet (ball x₀ r)
  · -- the copy near `x` is the single active translate `k`
    obtain ⟨k, hk⟩ := hx
    have hnb : {z : SpaceTime | z.2 - latticeVector k ∈ ball x₀ r} ∈ 𝓝 (t, x) :=
      (isOpen_ball.preimage
        (by fun_prop : Continuous fun z : SpaceTime => z.2 - latticeVector k)).mem_nhds hk
    have hgerm : latticeLift W =ᶠ[𝓝 (t, x)] PeriodicLocalization.translate W k := by
      filter_upwards [hnb] with z hz
      have h1 : latticeLift W z = latticeLift W (z.1, z.2 - latticeVector k) :=
        (isPeriodicOn_sub_latticeVector (latticeLift_periodic W) z.1 z.2 k).symm
      have h2 : latticeLift W (z.1, z.2 - latticeVector k) = W (z.1, z.2 - latticeVector k) :=
        latticeLift_eq_of_ball hWslice hsum hz
      rw [h1, h2]; rfl
    show NSFormalization.Source.correctionForce ν v (latticeLift W) (t, x)
      = latticeLift (NSFormalization.Source.correctionForce ν v W) (t, x)
    rw [source_correctionForce_congr hgerm]
    have hRHS : latticeLift (NSFormalization.Source.correctionForce ν v W) (t, x)
        = NSFormalization.Source.correctionForce ν v W (t, x - latticeVector k) := by
      rw [(isPeriodicOn_sub_latticeVector
        (latticeLift_periodic (NSFormalization.Source.correctionForce ν v W)) t x k).symm]
      exact latticeLift_eq_of_ball hGslice h2r hk
    rw [hRHS]
    have hvalper : v (t, x) = v (t, x - lattice k) :=
      (isPeriodicOn_sub_latticeVector hv t x k).symm
    have hderiv : spatialDerivative v t x (W (t, x - lattice k))
        = spatialDerivative v t (x - lattice k) (W (t, x - lattice k)) := by
      by_cases hW0 : W (t, x - lattice k) = 0
      · rw [hW0, map_zero, map_zero]
      · have hmem := hWtsupp (subset_tsupport W hW0)
        have ht : t ∈ Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) := hmem.1
        have hxb : x - lattice k ∈ ball x₀ (ε * θR) := hmem.2
        have hT0 : (0 : ℝ) < T - 2 * ε ^ 2 := by
          have : 2 * ε ^ 2 < T := lt_of_lt_of_le hεtime (min_le_left _ _)
          linarith
        have hTd : T + 2 * ε ^ 2 < T + δ := by
          have : 2 * ε ^ 2 < δ := lt_of_lt_of_le hεtime (min_le_right _ _)
          linarith
        have htcyl : t ∈ Ioo (0 : ℝ) (T + δ) := ⟨lt_trans hT0 ht.1, lt_trans ht.2 hTd⟩
        have hxcyl : x - lattice k ∈ ball x₀ r := ball_subset_ball (le_of_lt hρlt) hxb
        have hopen : IsOpen (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r) := isOpen_Ioo.prod isOpen_ball
        have hcontat : ContDiffAt ℝ ∞ v (t, x - lattice k) :=
          hvsm.contDiffAt (hopen.mem_nhds ⟨htcyl, hxcyl⟩)
        have hvdiff : DifferentiableAt ℝ (fun z : Space => v (t, z)) (x - lattice k) := by
          have h := hcontat.differentiableAt (by simp)
          exact h.comp (x - lattice k) ((differentiableAt_const t).prodMk differentiableAt_id)
        have hper_fun : (fun y : Space => v (t, y)) = fun y : Space => v (t, y - lattice k) := by
          funext y; exact (isPeriodicOn_sub_latticeVector hv t y k).symm
        have hchain : fderiv ℝ (fun y : Space => v (t, y - lattice k)) x
            = fderiv ℝ (fun y : Space => v (t, y)) (x - lattice k) := by
          have h2 : HasFDerivAt (fun y : Space => y - lattice k)
              (ContinuousLinearMap.id ℝ Space) x := (hasFDerivAt_id x).sub_const (lattice k)
          have h1 : HasFDerivAt (fun z : Space => v (t, z))
              (fderiv ℝ (fun z : Space => v (t, z)) (x - lattice k)) (x - lattice k) :=
            hvdiff.hasFDerivAt
          have hc0 := h1.comp x h2
          rw [show ((fun z : Space => v (t, z)) ∘ fun y : Space => y - lattice k)
              = fun y : Space => v (t, y - lattice k) from rfl] at hc0
          rw [hc0.fderiv, ContinuousLinearMap.comp_id]
        have hDv : spatialDerivative v t x = spatialDerivative v t (x - lattice k) := by
          simp only [spatialDerivative]
          conv_lhs => rw [hper_fun]
          exact hchain
        rw [hDv]
    exact source_force_translate hWcd k t x hvalper hderiv
  · -- the point lies off every periodic copy: both sides vanish
    show NSFormalization.Source.correctionForce ν v (latticeLift W) (t, x)
      = latticeLift (NSFormalization.Source.correctionForce ν v W) (t, x)
    have hxslice : x ∉ tsupport (fun y : Space => latticeLift W (t, y)) :=
      fun h => hx (latticeLift_sliceSupport hWslice hρlt t h)
    have hslicezero : (fun y : Space => latticeLift W (t, y)) =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hxslice
    have htimezero : ∀ s : ℝ, latticeLift W (s, x) = 0 := by
      intro s
      by_contra hne
      exact hx (latticeLift_sliceSupport hWslice hρlt s (subset_tsupport _ hne))
    have hLHS : NSFormalization.Source.correctionForce ν v (latticeLift W) (t, x) = 0 :=
      source_correctionForce_eq_zero hslicezero htimezero
    have hRHS : latticeLift (NSFormalization.Source.correctionForce ν v W) (t, x) = 0 := by
      have hz : ∀ k : NSFormalization.Section3.T10.PeriodicFrequency,
          NSFormalization.Source.correctionForce ν v W (t, x - latticeVector k) = 0 := by
        intro k
        apply source_correctionForce_support hWslice t (x - latticeVector k)
        intro hyc
        exact hx ⟨k, closedBall_subset_ball hρlt hyc⟩
      simp only [latticeLift]
      rw [tsum_congr hz, tsum_zero]
    rw [hLHS, hRHS]

/-- **U2 (c)**: the T17 correction force is unit-periodic, being a lattice lift.
`03-torus.tex:225`. -/
theorem correctionForce_periodic {ν : ℝ} {v : SpaceTimeField} {x₀ : Space} {T δ r : ℝ}
    {θ : Space → ℝ} {η : ℝ → ℝ} {O : Set Space} {θR ε₀ ε : ℝ}
    (hv : IsPeriodicOn univ v)
    (hvsm : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hθsm : ContDiff ℝ ∞ θ) (hηsm : ContDiff ℝ ∞ η)
    (hθcs : HasCompactSupport θ) (hηcs : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε : 0 < ε) (hεspace : ε * θR < r) (hεtime : 2 * ε ^ 2 < min T δ) :
    IsPeriodicOn univ (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) := by
  rw [force_eq hv hvsm hθsm hηsm hθcs hηcs hθsupp hηsupp hr2 hε hεspace hεtime]
  exact latticeLift_periodic _

end NSFormalization.Section3.T17
