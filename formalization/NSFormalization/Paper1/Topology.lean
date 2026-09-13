import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Topological deductions in Paper 1

These are general interface theorems. They do not assert existence of the
Navier–Stokes insertion or critical regularity estimate. The analytic hypotheses
are explicit arguments; no analytic conclusion is replaced by a new axiom.
-/

namespace NSFormalization.Paper1

/-- The singular-reference / regular-reference dichotomy used in Proposition 4.1.
The nontrivial analytic input is approximation at points outside the singular set. -/
theorem dense_of_insertion {F : Type*} [PseudoMetricSpace F] (S : Set F)
    (insert : ∀ g, g ∉ S → ∀ r : ℝ, 0 < r → ∃ f ∈ S, dist g f < r) :
    Dense S := by
  intro g
  apply Metric.mem_closure_iff.mpr
  intro r hr
  by_cases hg : g ∈ S
  · exact ⟨g, hg, by simpa using hr⟩
  · exact insert g hg r hr

/-- A regular open ball supplies a genuine topological obstruction. -/
theorem not_dense_of_regular_ball {F : Type*} [PseudoMetricSpace F]
    (S : Set F) (g : F) (r : ℝ) (hr : 0 < r)
    (regular : ∀ f, dist g f < r → f ∉ S) : ¬ Dense S := by
  intro h
  obtain ⟨f, hf, hdist⟩ := Metric.mem_closure_iff.mp (h g) r hr
  exact regular f hdist hf

/-- Dense fibers imply density in the product for *any* topology on initial data. -/
theorem dense_relation_of_dense_fibers {A F : Type*}
    [TopologicalSpace A] [TopologicalSpace F] (R : Set (A × F))
    (fibers : ∀ a, Dense {f | (a, f) ∈ R}) : Dense R := by
  rintro ⟨a, f⟩
  have h : (a, f) ∈ closure ((fun x : F => (a, x)) '' {x | (a, x) ∈ R}) :=
    mem_closure_image (continuous_const.prodMk continuous_id).continuousAt (fibers a f)
  exact closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hx) h

/-- Fiberwise density has the quantifier order ∀ a, ∃ f. -/
theorem projection_eq_univ_of_dense_fibers {A F : Type*}
    [TopologicalSpace F] [Nonempty F] (R : Set (A × F))
    (fibers : ∀ a, Dense {f | (a, f) ∈ R}) : Prod.fst '' R = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  obtain ⟨f, hf⟩ := (fibers a).nonempty
  exact ⟨(a, f), hf, rfl⟩

/-- Restricting the initial velocity to one point changes its projection to a singleton. -/
theorem fixed_slice_projection {A F : Type*} (a : A) (S : Set F)
    (hS : S.Nonempty) : Prod.fst '' ({a} ×ˢ S) = {a} := by
  ext b
  constructor
  · rintro ⟨⟨x, f⟩, ⟨hx, hf⟩, rfl⟩
    exact hx
  · intro hb
    obtain ⟨f, hf⟩ := hS
    exact ⟨(b, f), ⟨hb, hf⟩, rfl⟩

/-- Simultaneous approximation of a velocity-force pair implies product closure. -/
theorem pair_mem_closure_of_approximation {V F : Type*}
    [PseudoMetricSpace V] [PseudoMetricSpace F]
    (S : Set (V × F)) (v : V) (g : F)
    (approximation : ∀ r : ℝ, 0 < r → ∃ u f, (u, f) ∈ S ∧
      dist v u < r ∧ dist g f < r) : (v, g) ∈ closure S := by
  apply Metric.mem_closure_iff.mpr
  intro r hr
  obtain ⟨u, f, hs, hv, hf⟩ := approximation r hr
  exact ⟨(u, f), hs, by simpa only [Prod.dist_eq, max_lt_iff] using And.intro hv hf⟩

/-- The final threshold deduction; the positive and negative analytic branches
remain separately visible in the theorem type. -/
theorem density_threshold {F : Type*} [TopologicalSpace F]
    (S : ℝ → Set F)
    (subcritical : ∀ s, s < (1 : ℝ) / 2 → Dense (S s))
    (critical : ∀ s, (1 : ℝ) / 2 ≤ s → ¬ Dense (S s)) (s : ℝ) :
    Dense (S s) ↔ s < (1 : ℝ) / 2 := by
  constructor
  · intro h
    exact lt_of_not_ge (fun hs => critical s hs h)
  · exact subcritical s

end NSFormalization.Paper1
