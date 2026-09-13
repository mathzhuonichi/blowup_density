import NSFormalization.Paper1.BoundaryReferenceRestriction

/-! Composition of two supported boundary insertions.  This is pure boundary
bookkeeping and does not assert existence or regularity of either field. -/
noncomputable section
namespace NSFormalization.Paper1.BoundaryCorollary
open Set
open NavierStokes NavierStokes.ProblemStatement

/-- If an intermediate field differs from a no-slip reference only inside `B`,
and a final field differs from the intermediate field only inside `C`, with
both regions disjoint from the boundary, then the final field is no-slip. -/
theorem noSlip_of_composed_supported_differences
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    (href : BoundedReference Ω ν T δ a v π g)
    {B C : Set Space}
    (hB : ∀ x ∈ B, x ∉ frontier Ω)
    (hC : ∀ x ∈ C, x ∉ frontier Ω)
    {U W : VelocityField}
    (hU : ∀ t : ℝ, tsupport (fun x : Space => U (t, x) - v (t, x)) ⊆ B)
    (hW : ∀ t : ℝ, tsupport (fun x : Space => W (t, x) - U (t, x)) ⊆ C) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ frontier Ω, W (t, x) = 0 := by
  intro t ht x hx
  have hv : v (t, x) = 0 := href.no_slip t ⟨ht.1,
    ht.2.trans (le_add_of_nonneg_right (le_of_lt href.positive_extension))⟩ x hx
  have hxU : x ∉ tsupport (fun y : Space => U (t, y) - v (t, y)) := by
    intro hxs
    exact (hB x (hU t hxs)) hx
  have hUdiff : U (t, x) - v (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun y : Space => U (t, y) - v (t, y)) hxU
  have hxW : x ∉ tsupport (fun y : Space => W (t, y) - U (t, y)) := by
    intro hxs
    exact (hC x (hW t hxs)) hx
  have hWdiff : W (t, x) - U (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun y : Space => W (t, y) - U (t, y)) hxW
  have hUeq : U (t, x) = 0 := by
    rw [hv, sub_zero] at hUdiff
    exact hUdiff
  rw [hUeq, sub_zero] at hWdiff
  exact hWdiff

end NSFormalization.Paper1.BoundaryCorollary
