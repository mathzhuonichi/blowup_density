import NSFormalization.Source.PacketScaling
import NSFormalization.Source.ViscosityPacket

/-!
# The negative-time zero extensions of the packet

Lemma 2.2 ends with "Vanishing on an interval proves smoothness of both zero
extensions", `paper/sections/02-preliminaries.tex:152`, and
Proposition 3.3 uses those extensions together with the extended force,
`paper/sections/03-torus.tex:108-119, 141`.

The generic machinery already exists in
`formalization/NSFormalization/Source/PacketScaling.lean`
(`zeroPastField_smoothOn`, `zeroPastField_equation`); this file instantiates it
at a closed quiet interval `[0,τ]` and adds the missing un-rescaled
incompressibility statement for the extension, which previously only existed
inlined inside `PacketScaling.delayed_parabolic_divergence`.
-/

noncomputable section

namespace NSFormalization.Section4.I01

open Set
open scoped ContDiff
open NavierStokes.ProblemStatement
open NSFormalization.Source.PacketScaling (zeroPastField)

/-- A field smooth on `R³ × [0,1)` that vanishes on the closed interval `[0,τ]`
extends smoothly by zero to `(-∞,1) × R³`.  Velocity and pressure are both
covered, the statement being generic in the target normed space. -/
theorem extension_smoothOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} {τ : ℝ} (hτ : 0 < τ)
    (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (hq : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, g (t, x) = 0) :
    ContDiffOn ℝ ∞ (zeroPastField g) (Iio (1 : ℝ) ×ˢ (univ : Set Space)) :=
  Source.PacketScaling.zeroPastField_smoothOn hτ hg
    (fun t ht x => hq t ⟨ht.1.le, ht.2.le⟩ x)

/-- The zero-extended triple solves the momentum equation at every time below
the singular time, including the seam `t = 0` and the whole inactive past.
Stated with the canonical residual
`NavierStokesR3.ProblemStatement.navierStokesResidual`, which is definitionally
the `NSFormalization.Source.residual` of the underlying lemma. -/
theorem extension_navierStokes {ν τ : ℝ} {u f : VelocityField} {p : PressureField}
    (hτ : 0 < τ)
    (hu : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, u (t, x) = 0)
    (hp : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, p (t, x) = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    {t : ℝ} (ht : t < 1) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x) :=
  Source.PacketScaling.zeroPastField_equation hτ
    (fun s hs y => hu s ⟨hs.1.le, hs.2.le⟩ y)
    (fun s hs y => hp s ⟨hs.1.le, hs.2.le⟩ y) hNS ht x

/-- Incompressibility of the zero extension at every time below the singular
time.  At positive times the spatial slice is unchanged; at nonpositive times
the slice is constantly zero. -/
theorem extension_divergence_free {u : VelocityField}
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    {t : ℝ} (ht : t < 1) (x : Space) :
    spatialDivergence (zeroPastField u) t x = 0 := by
  by_cases hpos : 0 < t
  · have he : spatialDivergence (zeroPastField u) t x = spatialDivergence u t x := by
      simp only [spatialDivergence, spatialDerivative,
        Source.PacketScaling.zeroPastField_of_pos u hpos]
    rw [he, hd t ⟨hpos.le, ht⟩ x]
  · have hn : t ≤ 0 := le_of_not_gt hpos
    simp [spatialDivergence, spatialDerivative,
      Source.PacketScaling.zeroPastField_of_nonpos u hn]

end NSFormalization.Section4.I01
