import Contracts.V1.Packet
import Contracts.V1.Data
import Bindings.Packet
import NSFormalization.Section3.T24.AffineFamily

/-!
# Probe: T24a Ua7 `infinite_dimensional` closes against the registered spelling

Run from `verification/` with
`lake env lean ../research/T24/probes/affine_family_closes.lean`.

Four checks, in the pattern of `research/T24/probes/affine_energy_closes.lean`:

1. the `Spec.lean:961-990` affine vocabulary, rewritten here in the registered
   `Contracts.V1` types, is `rfl`-equal to the canonical `Section3.T24`
   spellings imported from `AffineBasics.lean`;
2. the `Spec.lean:1085-1087` field `infinite_dimensional`, written in the
   registered vocabulary over `BlowupDensity.Bindings.packet ν hν`, is
   discharged by `NSFormalization.Section3.T24.infinite_dimensional`.  The field
   itself does not mention the packet (the admissible class depends only on the
   cylinder `Ioo τ₀ τ₁ ×ˢ ball c r`), so the packet-free form is recorded too;
3. non-vacuity of the produced family: the two members `b 0` and `b 1` are
   distinct, each is nonzero, and the corresponding affine velocities
   `U + b 0 ≠ U + b 1` on the registered packet velocity — so the sequence is
   not a disguised constant family and `b ↦ U + b` really moves it;
4. the explicit geometry: `b 0` and `b 1` are supported in disjoint spatial
   balls inside `ball c r`.
-/

noncomputable section

namespace BlowupDensity.T24.ProbeUa7

open Set
open scoped ContDiff

/-- The registered spacetime vector field type. -/
local notation "Field" => BlowupDensity.Contracts.V1.VelocityField

/-- The registered spatial type. -/
local notation "Pt" => BlowupDensity.Contracts.V1.Space

/-! ## 1. The `Spec.lean` affine vocabulary in registered types -/

namespace AffineSpec

def specAffineCylinder (c : Pt) (r τ₀ τ₁ : ℝ) : Set BlowupDensity.Contracts.V1.SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

def specAffineAdmissible (c : Pt) (r τ₀ τ₁ : ℝ) (b : Field) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ specAffineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Pt,
      BlowupDensity.Contracts.V1.spatialDivergence b t x = 0)

def specAffineVelocity (U b : Field) : Field :=
  fun z ↦ U z + b z

end AffineSpec

example (c : Pt) (r τ₀ τ₁ : ℝ) :
    AffineSpec.specAffineCylinder c r τ₀ τ₁ =
      NSFormalization.Section3.T24.affineCylinder c r τ₀ τ₁ := rfl

example (c : Pt) (r τ₀ τ₁ : ℝ) (b : Field) :
    AffineSpec.specAffineAdmissible c r τ₀ τ₁ b =
      NSFormalization.Section3.T24.AffineAdmissible c r τ₀ τ₁ b := rfl

example (u b : Field) :
    AffineSpec.specAffineVelocity u b =
      NSFormalization.Section3.T24.affineVelocity u b := rfl

/-- `Spec.lean` writes the field with `SpaceTimeField`; that is literally the
registered `VelocityField` (`Contracts/V1/Data.lean:104`). -/
example : BlowupDensity.Contracts.V1.Data.SpaceTimeField =
    BlowupDensity.Contracts.V1.VelocityField := rfl

/-- The field in `Spec.lean`'s own spelling, with `SpaceTimeField`. -/
example (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) :
    ∃ b : ℕ → BlowupDensity.Contracts.V1.Data.SpaceTimeField,
      (∀ n : ℕ, AffineSpec.specAffineAdmissible c r τ₀ τ₁ (b n)) ∧
        LinearIndependent ℝ b :=
  NSFormalization.Section3.T24.infinite_dimensional c r τ₀ τ₁ hr hτ

/-! ## 2. `Spec.lean:1085-1087` on the registered packet -/

/-- The registered field `infinite_dimensional`, token-for-token as
`Spec.lean:1085-1087` carries it inside `AffineVariationAPI`.  The field itself
mentions no packet clause, so no packet argument is consumed. -/
example (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) :
    ∃ b : ℕ → Field,
      (∀ n : ℕ, AffineSpec.specAffineAdmissible c r τ₀ τ₁ (b n)) ∧
        LinearIndependent ℝ b :=
  NSFormalization.Section3.T24.infinite_dimensional c r τ₀ τ₁ hr hτ

/-- The packet-level form, i.e. the whole sentence of `03-torus.tex:688-691`
including "the map `b ↦ U+b` is injective and affine, so its image is infinite
dimensional", on `BlowupDensity.Bindings.packet ν hν`: the same admissible
linearly independent sequence, together with injectivity of
`n ↦ U + b n` for the registered packet velocity. -/
example (ν : ℝ) (hν : 0 < ν) (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) :
    ∃ b : ℕ → Field,
      (∀ n : ℕ, AffineSpec.specAffineAdmissible c r τ₀ τ₁ (b n)) ∧
        LinearIndependent ℝ b ∧
        Function.Injective (fun n : ℕ => AffineSpec.specAffineVelocity
          (BlowupDensity.Bindings.packet ν hν).velocity (b n)) := by
  refine ⟨NSFormalization.Section3.T24.AffineFamily.bFam c r τ₀ τ₁ hr hτ,
    NSFormalization.Section3.T24.AffineFamily.bFam_admissible c r τ₀ τ₁ hr hτ,
    NSFormalization.Section3.T24.AffineFamily.bFam_linearIndependent c r τ₀ τ₁ hr hτ,
    ?_⟩
  intro n m h
  by_contra hnm
  exact NSFormalization.Section3.T24.distinct
    (BlowupDensity.Bindings.packet ν hν).velocity _ _
    (NSFormalization.Section3.T24.AffineFamily.bFam_admissible c r τ₀ τ₁ hr hτ n)
    (NSFormalization.Section3.T24.AffineFamily.bFam_admissible c r τ₀ τ₁ hr hτ m)
    (fun e => hnm ((NSFormalization.Section3.T24.AffineFamily.bFam_linearIndependent
      c r τ₀ τ₁ hr hτ).injective e)) h

/-! ## 3. Non-vacuity of the produced family -/

/-- The explicit witness sequence. -/
def fam (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) : ℕ → Field :=
  NSFormalization.Section3.T24.AffineFamily.bFam c r τ₀ τ₁ hr hτ

example (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) (n : ℕ) :
    AffineSpec.specAffineAdmissible c r τ₀ τ₁ (fam c r τ₀ τ₁ hr hτ n) :=
  NSFormalization.Section3.T24.AffineFamily.bFam_admissible c r τ₀ τ₁ hr hτ n

/-- Each member is a nonzero perturbation, so the family is not the zero family. -/
example (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) (n : ℕ) :
    fam c r τ₀ τ₁ hr hτ n ≠ 0 :=
  NSFormalization.Section3.T24.AffineFamily.bFam_ne_zero c r τ₀ τ₁ hr hτ n

/-- `b 0 ≠ b 1`: the sequence is injective, being linearly independent. -/
example (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) :
    fam c r τ₀ τ₁ hr hτ 0 ≠ fam c r τ₀ τ₁ hr hτ 1 := by
  intro h
  have := (NSFormalization.Section3.T24.AffineFamily.bFam_linearIndependent
    c r τ₀ τ₁ hr hτ).injective h
  exact absurd this (by norm_num)

/-- The whole sequence is injective. -/
example (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) :
    Function.Injective (fam c r τ₀ τ₁ hr hτ) :=
  (NSFormalization.Section3.T24.AffineFamily.bFam_linearIndependent
    c r τ₀ τ₁ hr hτ).injective

/-- On the registered packet: the affine velocities `U + b 0` and `U + b 1` are
distinct, via the `Spec.lean:1091-1094` field `distinct`
(`AffineBasics.distinct`).  This is the "`b ↦ U+b` is injective, so its image is
infinite dimensional" half of `03-torus.tex:691`. -/
example (ν : ℝ) (hν : 0 < ν) (c : Pt) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) :
    AffineSpec.specAffineVelocity (BlowupDensity.Bindings.packet ν hν).velocity
        (fam c r τ₀ τ₁ hr hτ 0) ≠
      AffineSpec.specAffineVelocity (BlowupDensity.Bindings.packet ν hν).velocity
        (fam c r τ₀ τ₁ hr hτ 1) := by
  refine NSFormalization.Section3.T24.distinct _ _ _
    (NSFormalization.Section3.T24.AffineFamily.bFam_admissible c r τ₀ τ₁ hr hτ 0)
    (NSFormalization.Section3.T24.AffineFamily.bFam_admissible c r τ₀ τ₁ hr hτ 1) ?_
  intro h
  have := (NSFormalization.Section3.T24.AffineFamily.bFam_linearIndependent
    c r τ₀ τ₁ hr hτ).injective h
  exact absurd this (by norm_num)

/-! ## 4. The explicit disjoint geometry -/

open NSFormalization.Section3.T24.AffineFamily in
/-- The `0`-th and `1`-st spatial balls are disjoint. -/
example (c : Pt) (r : ℝ) (hr : 0 < r) (y : Pt)
    (hy : y ∈ Metric.closedBall (center c r 0) (ballRadius r 0)) :
    y ∉ Metric.closedBall (center c r 1) (ballRadius r 1) :=
  notMem_closedBall_of_ne hr (by norm_num) hy

open NSFormalization.Section3.T24.AffineFamily in
/-- Every ball of the sequence sits inside `ball c r`. -/
example (c : Pt) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Metric.closedBall (center c r n) (ballRadius r n) ⊆ Metric.ball c r :=
  closedBall_subset_ball hr n

open NSFormalization.Section3.T24.AffineFamily in
/-- The time bump lives strictly inside the window. -/
example (τ₀ τ₁ : ℝ) (hτ : τ₀ < τ₁) :
    Metric.closedBall ((τ₀ + τ₁) / 2) (timeBump τ₀ τ₁ hτ).rOut ⊆ Ioo τ₀ τ₁ :=
  timeBump_support τ₀ τ₁ hτ

/-! ## 5. Both hypotheses are load-bearing

A degenerate cylinder contains only the zero variation, so no linearly independent
admissible sequence exists there: `0 < r` and `τ₀ < τ₁` are not decoration. -/

/-- With `r = 0` the spatial ball is empty, so every admissible `b` vanishes. -/
example (c : Pt) (τ₀ τ₁ : ℝ) (b : Field)
    (hb : AffineSpec.specAffineAdmissible c 0 τ₀ τ₁ b) : b = 0 := by
  funext z
  show b z = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  have h := hb.2.2.1 hz
  simpa using h.2

/-- With `τ₁ ≤ τ₀` the time window is empty, so every admissible `b` vanishes. -/
example (c : Pt) (r τ₀ τ₁ : ℝ) (hle : τ₁ ≤ τ₀) (b : Field)
    (hb : AffineSpec.specAffineAdmissible c r τ₀ τ₁ b) : b = 0 := by
  funext z
  show b z = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  have h := hb.2.2.1 hz
  have h1 := h.1
  rw [Set.mem_Ioo] at h1
  linarith [h1.1, h1.2]

/-- Consequently the conclusion genuinely fails without `0 < r`. -/
example (c : Pt) (τ₀ τ₁ : ℝ) :
    ¬ ∃ b : ℕ → Field,
        (∀ n : ℕ, AffineSpec.specAffineAdmissible c 0 τ₀ τ₁ (b n)) ∧
          LinearIndependent ℝ b := by
  rintro ⟨b, hadm, hlin⟩
  have hzero : ∀ n : ℕ, b n = 0 := by
    intro n
    funext z
    show b n z = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    have h := (hadm n).2.2.1 hz
    simpa using h.2
  have : (0 : ℕ) = 1 := hlin.injective (by rw [hzero 0, hzero 1])
  exact absurd this (by norm_num)

#print axioms fam

end BlowupDensity.T24.ProbeUa7
