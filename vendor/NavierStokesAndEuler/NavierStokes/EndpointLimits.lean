import Mathlib.Analysis.Calculus.FDeriv.Extend
import NavierStokes.EndpointExtension

/-!
# Endpoint regularity from finite limits of successive derivatives

For a family of curves `f n`, assume that `f (n+1)` is the actual derivative
of `f n` strictly to the left of `a`, and that every `f n` has a finite left
limit `L n`. Assigning these limiting values at `a` produces a curve smooth
on the closed left half-line, whose actual within-derivative jets equal `L`.

The endpoint derivative step uses Mathlib's mean-value extension theorem.
Closed-side smoothness and compatibility of the limiting jets are proved,
not assumed. Arbitrary right-hand jet realization is a separate problem.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.EndpointLimits

/-- Keep the curve on the open left half-line and assign its limiting value
at the endpoint. Values to the right are also set to that constant, but no
smoothness across the endpoint is claimed for this function alone. -/
def leftExtension {V : Type*} (a : ℝ) (L : V) (f : ℝ → V) (x : ℝ) : V :=
  if x < a then f x else L

theorem leftExtension_of_lt {V : Type*} {a x : ℝ} {L : V} {f : ℝ → V}
    (hx : x < a) : leftExtension a L f x = f x := by
  simp only [leftExtension, ite_eq_left hx]

@[simp] theorem leftExtension_at {V : Type*} (a : ℝ) (L : V) (f : ℝ → V) :
    leftExtension a L f a = L := by
  simp only [leftExtension, lt_self_iff_false, ite_false]

/-- The assigned endpoint value makes the extension continuous from the left. -/
theorem continuousWithinAt_leftExtension {V : Type*} [TopologicalSpace V]
    {a : ℝ} {L : V} {f : ℝ → V}
    (hf : Tendsto f (𝓝[<] a) (𝓝 L)) :
    ContinuousWithinAt (leftExtension a L f) (Iio a) a := by
  change Tendsto (leftExtension a L f) (𝓝[<] a) (𝓝 (leftExtension a L f a))
  rw [leftExtension_at]
  apply hf.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (leftExtension_of_lt hx).symm

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Altering the endpoint and the right side does not change an interior
left derivative. -/
theorem hasDerivAt_leftExtension {a x : ℝ} {L v : V} {f : ℝ → V}
    (hx : x < a) (hf : HasDerivAt f v x) :
    HasDerivAt (leftExtension a L f) v x := by
  apply hf.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact leftExtension_of_lt hy

/-- The mean-value theorem identifies the derivative at the endpoint from
the separate limits of the curve and its derivative. -/
theorem hasDerivWithinAt_leftExtension_endpoint {a : ℝ} {L L' : V}
    {f f' : ℝ → V}
    (hderiv : ∀ x < a, HasDerivAt f (f' x) x)
    (hlim : Tendsto f (𝓝[<] a) (𝓝 L))
    (hlim' : Tendsto f' (𝓝[<] a) (𝓝 L')) :
    HasDerivWithinAt (leftExtension a L f) L' (Iic a) a := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Iio a)
    (fun x hx => (hasDerivAt_leftExtension hx (hderiv x hx)).differentiableAt.differentiableWithinAt)
    (continuousWithinAt_leftExtension hlim) self_mem_nhdsWithin
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hasDerivAt_leftExtension (L := L) hx (hderiv x hx)).deriv.symm

/-- Every extended member of a successive-derivative family has the next
extended member as its derivative throughout the closed left half-line. -/
theorem hasDerivWithinAt_extended_family {a : ℝ} {f : ℕ → ℝ → V} {L : ℕ → V}
    (hderiv : ∀ n : ℕ, ∀ x < a, HasDerivAt (f n) (f (n + 1) x) x)
    (hlim : ∀ n : ℕ, Tendsto (f n) (𝓝[<] a) (𝓝 (L n)))
    (n : ℕ) {x : ℝ} (hx : x ≤ a) :
    HasDerivWithinAt (leftExtension a (L n) (f n))
      (leftExtension a (L (n + 1)) (f (n + 1)) x) (Iic a) x := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · rw [leftExtension_of_lt hlt]
    exact (hasDerivAt_leftExtension hlt (hderiv n x hlt)).hasDerivWithinAt
  · subst x
    rw [leftExtension_at]
    exact hasDerivWithinAt_leftExtension_endpoint (hderiv n) (hlim n) (hlim (n + 1))

/-- The actual iterated derivatives of the extended original curve agree,
on the full closed half-line, with the given successive-derivative family. -/
theorem iteratedDerivWithin_leftExtension {a : ℝ} {f : ℕ → ℝ → V} {L : ℕ → V}
    (hderiv : ∀ n : ℕ, ∀ x < a, HasDerivAt (f n) (f (n + 1) x) x)
    (hlim : ∀ n : ℕ, Tendsto (f n) (𝓝[<] a) (𝓝 (L n))) (n : ℕ) :
    EqOn (iteratedDerivWithin n (leftExtension a (L 0) (f 0)) (Iic a))
      (leftExtension a (L n) (f n)) (Iic a) := by
  induction n with
  | zero => simp only [iteratedDerivWithin_zero, eqOn_refl]
  | succ n ih =>
    intro x hx
    rw [iteratedDerivWithin_succ]
    calc
      derivWithin (iteratedDerivWithin n (leftExtension a (L 0) (f 0)) (Iic a))
          (Iic a) x = derivWithin (leftExtension a (L n) (f n)) (Iic a) x :=
        derivWithin_congr ih (ih hx)
      _ = leftExtension a (L (n + 1)) (f (n + 1)) x :=
        (hasDerivWithinAt_extended_family hderiv hlim n hx).derivWithin
          (uniqueDiffOn_Iic a x hx)

/-- Finite limits of every successive derivative imply genuine `C∞`
regularity up to the endpoint. Closed-side smoothness is the conclusion. -/
theorem contDiffOn_leftExtension {a : ℝ} {f : ℕ → ℝ → V} {L : ℕ → V}
    (hderiv : ∀ n : ℕ, ∀ x < a, HasDerivAt (f n) (f (n + 1) x) x)
    (hlim : ∀ n : ℕ, Tendsto (f n) (𝓝[<] a) (𝓝 (L n))) :
    ContDiffOn ℝ ∞ (leftExtension a (L 0) (f 0)) (Iic a) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro n _ x hx
  exact ((hasDerivWithinAt_extended_family hderiv hlim n hx).congr_of_mem
    (fun y hy => iteratedDerivWithin_leftExtension hderiv hlim n hy) hx).differentiableWithinAt

/-- Each member of the successive-derivative family, not only its zeroth
member, extends smoothly to the closed left half-line. -/
theorem all_leftExtensions_contDiffOn {a : ℝ} {f : ℕ → ℝ → V} {L : ℕ → V}
    (hderiv : ∀ n : ℕ, ∀ x < a, HasDerivAt (f n) (f (n + 1) x) x)
    (hlim : ∀ n : ℕ, Tendsto (f n) (𝓝[<] a) (𝓝 (L n))) (k : ℕ) :
    ContDiffOn ℝ ∞ (leftExtension a (L k) (f k)) (Iic a) := by
  have hshift : ∀ n : ℕ, ∀ x < a,
      HasDerivAt (f (k + n)) (f (k + (n + 1)) x) x := by
    intro n x hx
    simpa only [Nat.add_assoc] using hderiv (k + n) x hx
  simpa only [Nat.add_zero] using
    contDiffOn_leftExtension hshift (fun n => hlim (k + n))

/-- The limiting data are exactly the endpoint jets of the constructed
closed-side smooth curve. -/
theorem endpoint_jets_eq_limits {a : ℝ} {f : ℕ → ℝ → V} {L : ℕ → V}
    (hderiv : ∀ n : ℕ, ∀ x < a, HasDerivAt (f n) (f (n + 1) x) x)
    (hlim : ∀ n : ℕ, Tendsto (f n) (𝓝[<] a) (𝓝 (L n))) (n : ℕ) :
    iteratedDerivWithin n (leftExtension a (L 0) (f 0)) (Iic a) a = L n := by
  simpa only [leftExtension_at] using
    iteratedDerivWithin_leftExtension hderiv hlim n (le_refl a)

/-- A constructive existence statement for a smooth left endpoint extension
with exactly the limiting jets. It asserts no extension to an open right side. -/
theorem exists_smooth_left_extension {a : ℝ} {f : ℕ → ℝ → V} {L : ℕ → V}
    (hderiv : ∀ n : ℕ, ∀ x < a, HasDerivAt (f n) (f (n + 1) x) x)
    (hlim : ∀ n : ℕ, Tendsto (f n) (𝓝[<] a) (𝓝 (L n))) :
    ∃ g : ℝ → V, EqOn g (f 0) (Iio a) ∧ ContDiffOn ℝ ∞ g (Iic a) ∧
      ∀ n : ℕ, iteratedDerivWithin n g (Iic a) a = L n := by
  exact ⟨leftExtension a (L 0) (f 0), fun _ hx => leftExtension_of_lt hx,
    contDiffOn_leftExtension hderiv hlim, endpoint_jets_eq_limits hderiv hlim⟩

/-- Explicit bridge to the gluing theorem. A right branch is a concrete input
with its own smoothness and jet equalities; its existence is not asserted. -/
theorem contDiff_glue_of_left_limits {a : ℝ} {f : ℕ → ℝ → V} {L : ℕ → V}
    {right : ℝ → V}
    (hderiv : ∀ n : ℕ, ∀ x < a, HasDerivAt (f n) (f (n + 1) x) x)
    (hlim : ∀ n : ℕ, Tendsto (f n) (𝓝[<] a) (𝓝 (L n)))
    (hright : ContDiffOn ℝ ∞ right (Ici a))
    (hrightJet : ∀ n : ℕ, iteratedDerivWithin n right (Ici a) a = L n) :
    ContDiff ℝ ∞ (EndpointExtension.glue a (leftExtension a (L 0) (f 0)) right) := by
  apply EndpointExtension.contDiff_glue (contDiffOn_leftExtension hderiv hlim) hright
  intro n
  exact (endpoint_jets_eq_limits hderiv hlim n).trans (hrightJet n).symm

end Normed

end NavierStokes.EndpointLimits
