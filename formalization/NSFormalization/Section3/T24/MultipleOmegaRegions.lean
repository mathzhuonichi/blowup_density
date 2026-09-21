import NSFormalization.Section3.T24.MultipleOmega
import NSFormalization.Section3.T15.Energy

/-!
# P5.3–P5.4: separate singularities and energy on Ω

`paper/revised/sections/03-torus.tex:528-531`:
"On B_j the velocity equals U_j, proving the stated separate limsup for each ball.
Disjoint supports also give" the energy upper bound and the dissipation equality.

The component velocities, their raw scaling pins, placement, global supports,
and disjointness are explicit hypotheses supplied by P5.1–P5.2. No component
constructor or assembled solution is assumed here. The local sum has exactly
the body of `finiteVelocitySum`, so its assembly bridge is definitional.
-/
noncomputable section
namespace NSFormalization.Section3.T24.OmegaRegions
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15 NSFormalization.Section3.T23
open NSFormalization.Source.PacketScaling
open NSFormalization.Section4.I02 (spatialGradient)

variable {N : ℕ} {T : ℝ} {c : Fin N → Space} {r : Fin N → ℝ}
  {w : Fin N → VelocityField}

/-- The explicit finite superposition used by the assembly lane. -/
def assembledVelocity (w : Fin N → VelocityField) : VelocityField :=
  finiteVelocitySum w

variable (regions_disjoint : Pairwise (fun i j : Fin N =>
    Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j))))
  (component_support : ∀ j, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    x ∉ Metric.ball (c j) (r j) → w j (t, x) = 0)

include regions_disjoint component_support

/-- On each prescribed ball all the other summands vanish. -/
theorem region_agreement : ∀ j, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (c j) (r j), assembledVelocity w (t, x) = w j (t, x) := by
  intro j t ht x hx
  classical
  change (∑ i, w i (t, x)) = _
  apply Finset.sum_eq_single j
  · intro i _ hij
    exact component_support i t ht x
      (fun hi => Set.disjoint_left.mp (regions_disjoint hij) hi hx)
  · simp

/-- Raw Euclidean blow-up witnesses are nonzero, hence lie in their own ball. -/
theorem region_blowup {u : VelocityField} {x₀ : Fin N → Space} {ε : Fin N → ℝ}
    (component_pin : ∀ j, w j = scaledVelocity u (x₀ j) T (ε j))
    (eps_pos : ∀ j, 0 < ε j) (eps_time : ∀ j, ε j ^ 2 < T)
    (blowup : SpeedUnboundedAtOne u) :
    ∀ j, SpeedUnboundedAtOn T (Metric.ball (c j) (r j)) (assembledVelocity w) := by
  intro j A hA δ hδ
  have hinv : (((ε j)⁻¹ : ℝ) ^ 2)⁻¹ = ε j ^ 2 := by rw [inv_pow, inv_inv]
  have hb : SpeedUnboundedAt T (w j) := by
    rw [component_pin j, scaledVelocity_eq_parabolicVelocity, ← hinv]
    exact speed_unbounded_at_target (inv_pos.mpr (eps_pos j))
      (by simpa [hinv] using (eps_time j).le) (x₀ j) (zeroPastField_speed blowup)
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hb A hA δ hδ
  have hx : x ∈ Metric.ball (c j) (r j) := by
    by_contra hout
    rw [component_support j t ⟨ht.1.le, ht.2⟩ x hout, norm_zero] at hlarge
    linarith
  refine ⟨t, x, ht, hnear, hx, ?_⟩
  rw [region_agreement regions_disjoint component_support j t ⟨ht.1.le, ht.2⟩ x hx]
  exact hlarge

omit regions_disjoint component_support

/-- At most one nonzero summand implies squared-norm additivity. -/
theorem disjoint_enorm_sq_sum {E : Type*} [NormedAddCommGroup E]
    (v : Fin N → E) (hd : Pairwise (fun i j : Fin N =>
      Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j))))
    (x : Space) (hz : ∀ j, x ∉ Metric.ball (c j) (r j) → v j = 0) :
    ‖∑ j, v j‖ₑ ^ (2 : ℕ) = ∑ j, ‖v j‖ₑ ^ (2 : ℕ) := by
  classical
  by_cases hb : ∃ j, x ∈ Metric.ball (c j) (r j)
  · obtain ⟨j, hj⟩ := hb
    have hzero : ∀ i, i ≠ j → v i = 0 := fun i hij =>
      hz i (fun hi => Set.disjoint_left.mp (hd hij) hi hj)
    rw [Finset.sum_eq_single j (fun i _ hij => hzero i hij) (by simp)]
    symm
    apply Finset.sum_eq_single j
    · intro i _ hij
      simp [hzero i hij]
    · simp
  · have hzero : ∀ j, v j = 0 := fun j => hz j (fun hj => hb ⟨j, hj⟩)
    simp [hzero]

variable {u f : VelocityField} {p : PressureField} {K Ω : Set Space} {M D : ℝ}
  {ε : Fin N → ℝ} (placement : Fin N → DomainPlacementData u p f K)
  (packet : NSFormalization.Section4.I03.PacketData u K M D)
  (placement_time : ∀ j, (placement j).T = T)
  (placement_chart : ∀ j, (placement j).chartCenter = c j ∧
    (placement j).chartRadius = r j)
  (eps_admissible : ∀ j, ε j ∈ Ioc (0 : ℝ) (placement j).ε₀)
  (component_pin : ∀ j, w j = scaledVelocity u (placement j).x₀ T (ε j))
  (region_interior : ∀ j, closure (Metric.ball (c j) (r j)) ⊆ Ω)

include packet component_pin eps_admissible in
/-- Global spatial smoothness follows from the raw scaling pin. -/
theorem component_slice_contDiff (j : Fin N) (t : ℝ) (ht : t < T) :
    ContDiff ℝ ∞ (fun x => w j (t, x)) := by
  rw [component_pin j]
  exact scaledVelocity_slice_contDiff packet.extension_smooth (eps_admissible j).1 ht

include packet component_pin eps_admissible placement_chart in
/-- The closed slice support lies strictly inside the prescribed ball. -/
theorem component_tsupport (j : Fin N) (t : ℝ) (ht : t < T) :
    tsupport (fun x => w j (t, x)) ⊆ Metric.ball (c j) (r j) := by
  rw [component_pin j, ← (placement_chart j).1, ← (placement_chart j).2]
  exact (scaledVelocity_tsupp_subset (eps_admissible j).1 packet.carrier_compact
    packet.support (placement j).carrier_subset ht).trans
      (affineImage_subset_ball (eps_admissible j) (placement j).eps_space)

include packet component_pin eps_admissible placement_chart in
/-- The full Euclidean gradient vanishes outside the same ball. -/
theorem component_gradient_support (j : Fin N) (t : ℝ) (ht : t < T)
    (x : Space) (hout : x ∉ Metric.ball (c j) (r j)) :
    spatialGradient (w j) t x = 0 := by
  have hn : x ∉ tsupport (fun y => w j (t, y)) :=
    fun hx => hout (component_tsupport placement packet placement_chart eps_admissible
      component_pin j t ht hx)
  simp only [spatialGradient, spatialDerivative, fderiv_of_notMem_tsupport ℝ hn]
  rfl

include packet component_pin eps_admissible in
/-- Differentiation commutes with the finite superposition. -/
theorem gradient_sum (t : ℝ) (ht : t < T) (x : Space) :
    spatialGradient (assembledVelocity w) t x = ∑ j, spatialGradient (w j) t x := by
  have hd := fderiv_fun_sum (u := Finset.univ)
    (fun j _ => (component_slice_contDiff placement packet eps_admissible component_pin
      j t ht).differentiable (by simp) x)
  ext i k
  simp only [spatialGradient, spatialDerivative, assembledVelocity, finiteVelocitySum,
    hd, sum_apply, WithLp.ofLp_sum, WithLp.ofLp_toLp, Finset.sum_apply]

include component_support region_interior in
/-- Restricting a component slice to Ω preserves its whole-space norm. -/
theorem component_norm_restrict (j : Fin N) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    eLpNorm (fun x => w j (t, x)) 2 (volume.restrict Ω) =
      eLpNorm (fun x => w j (t, x)) 2 volume := by
  apply eLpNorm_restrict_eq_of_support_subset
  intro x hx
  apply region_interior j
  apply subset_closure
  by_contra hout
  exact hx (component_support j t ht x hout)

include packet component_pin eps_admissible placement_chart region_interior in
/-- The full gradient restriction also preserves its whole-space norm. -/
theorem component_gradient_restrict (j : Fin N) (t : ℝ) (ht : t < T) :
    eLpNorm (fun x => spatialGradient (w j) t x) 2 (volume.restrict Ω) =
      eLpNorm (fun x => spatialGradient (w j) t x) 2 volume := by
  apply eLpNorm_restrict_eq_of_support_subset
  intro x hx
  apply region_interior j
  apply subset_closure
  by_contra hout
  exact hx (component_gradient_support placement packet placement_chart eps_admissible
    component_pin j t ht x hout)

end NSFormalization.Section3.T24.OmegaRegions

