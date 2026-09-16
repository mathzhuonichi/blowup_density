import Contracts.V1.Data
import Contracts.V1.HomogeneousNorm

/-!
# Contract: Proposition 4.3 critical regularity

Version one registers Proposition 4.3 (`prop:Rcritical1`) exactly in the shape
of `research/R43/Spec.lean:165-247`.  The only source-level substitution is the
canonical registered definition
`Contracts.V1.HomogeneousNorm.dotHomogeneousENorm` for the definitionally equal
Spec-local homogeneous norm.  No implementation module is imported here.

The universal constant is stored in the record before every viscosity, datum,
and force.  Both manuscript conclusions use that same positive constant: the
general homogeneous-smallness theorem at
`paper/sections/04-whole-space.tex:82-87`, and its zero-datum inhomogeneous
consequence at `paper/sections/04-whole-space.tex:88-89`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.CriticalRegularity

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

/-- **Proposition 4.3** (`prop:Rcritical1`),
`paper/sections/04-whole-space.tex:82-89`: global regularity for small critical
data and `L¹` force, including the stated inhomogeneous zero-datum consequence.

This is `research/R43/Spec.lean`'s `RCritical1API` token-for-token apart from
the registry-conventional structure name and the replacement of its local
`dotHomogeneousENorm` by the registered definition of the same name. -/
structure CriticalRegularityAPI where
  /-- `04-whole-space.tex:83`, "There is a universal `c > 0`": the smallness
  radius, in units of `ν`.  A single real, `ν`-free, shared by both conclusion
  clauses below. -/
  c : ℝ
  /-- `04-whole-space.tex:83`, "`c > 0`".  Load-bearing: without it `c ≤ 0` makes
  `ENNReal.ofReal (c * ν) = 0`, both smallness hypotheses become unsatisfiable,
  and the structure is inhabited by a statement with no content. -/
  hc : 0 < c
  /-- **The theorem** (`04-whole-space.tex:84-87`):

    `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹(0,∞;Ḣ^{1/2})} < cν  ⟹  T^ν_{max,ℝ}(a,f) = ∞`,

  for every `ν > 0`, every `a ∈ 𝒳_ℝ` and every `f ∈ 𝓕_ℝ`.  The homogeneous
  datum norm is the registered datum-infimum norm, the force norm is the
  measurable-datum-path Bochner norm, and the conclusion is genuine infinite
  maximal lifespan. -/
  universal :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (c * ν) →
            maximalLifespanR ν a f = ⊤
  /-- **The "in particular" clause** (`04-whole-space.tex:88-89`), with
  `a = 0`, the inhomogeneous force norm, and the same `c`:

    `‖f‖_{L¹(0,∞;H^{1/2})} < cν  ⟹  T^ν_{max,ℝ}(0,f) = ∞`,

  for every `ν > 0` and every `f ∈ 𝓕_ℝ`. -/
  inhomogeneousAtZero :
    ∀ ν : ℝ, 0 < ν →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (c * ν) →
          maximalLifespanR ν (fun _ => 0) f = ⊤

end BlowupDensity.Contracts.V1.CriticalRegularity
