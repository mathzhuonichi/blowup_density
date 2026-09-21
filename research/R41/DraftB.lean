import Contracts.V1.Data
import Contracts.V1.Thresholds

/-!
Independent statement-only draft B of Theorem 4.1.
Sources: paper/sections/04-whole-space.tex:7-16,31-42,176-181;
02-preliminaries.tex:12-43; 01-introduction.tex:125-145.
No implementation or competing statement is imported. No new vocabulary needs
registration: the family below uses only registered fields, solutions and norms.
-/

noncomputable section
namespace BlowupDensity.Contracts.V1.DraftB

open Data Filter Set
open scoped ENNReal Topology

/-- `04-whole-space.tex:7-14`, Theorem 4.1. Each mathematical assertion is
an explicit field; this record does not supply a proof or assume an axiom.
The implicit order parameter `s` in the prose is universally quantified here.
The regular-reference sentence is kept together to preserve its shared witnesses. -/
structure RMainAPI where
  /-- `04-whole-space.tex:8-10`, clause (i).
  Order: fix ν > 0, T > 0, q ∈ {1,2}, s ∈ ℝ; for every fixed a ∈ X_R,
  if s < 2/q - 3/2 then B^R_{ν,a,T} is relatively dense in F_R.
  `BreakdownDenseR` expands to ∀ g ∈ F_R, ∀ r > 0, ∃ f ∈ B, ‖f-g‖ < r. -/
  fixedInitialDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassR →
          s < 2 / q - 3 / 2 → BreakdownDenseR ν a T (ENNReal.ofReal q) s

  /-- `04-whole-space.tex:8,11`, clause (ii).
  Order: fix ν > 0, T > 0, q ∈ {1,2}, s ∈ ℝ; density at zero iff
  s < 2/q - 3/2. One iff field retains the manuscript's two directions,
  including non-density at equality, without inventing a converse for nonzero a. -/
  zeroInitialDensityIff :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        RelativelyDense (ENNReal.ofReal q) s forceClassR (breakdownSetRZero ν T) ↔
          s < 2 / q - 3 / 2

  /-- `04-whole-space.tex:13`, "Thus the thresholds are 1/2 ... and -1/2".
  No quantifiers: these are the two real values of the threshold in line 8.
  This repeats arithmetic already specified by `ThresholdAPI.formula/l1/l2`. -/
  thresholdValues :
    (2 / (1 : ℝ) - 3 / 2 = 1 / 2) ∧ (2 / (2 : ℝ) - 3 / 2 = -1 / 2)

  /-- `04-whole-space.tex:13`, the entire regular-reference rider, with its
  earlier-history meaning made explicit by :32-35 and its energy conclusion
  by :37-42; :181 identifies these assertions as coming from Theorem 4.2.
  Order: ν > 0, T > 0, q ∈ {1,2}, s < s_q; every a ∈ X_R, g ∈ F_R,
  every δ > 0 and reference v on [0,T+δ); there exist ε₀ > 0 and ONE family
  (f_ε,u_ε); for every 0 < ε < ε₀ there is a classical solution with datum a,
  velocity u_ε, lifespan exactly T, and u_ε = v on [0,T-2ε²]; both the force
  difference and the E_T velocity difference tend to zero as ε ↓ 0.
  Quantifying the extension v explicitly unpacks `RegularThrough ν a g T`
  and names the velocity whose history must be retained. The harmless bound
  2ε₀² < T ensures that the displayed history interval contains zero.
  The existential solution includes the unchanged initial value in its type.
  Separate existential fields would fail to assert simultaneous conclusions. -/
  regularReferenceApproximation :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < 2 / q - 3 / 2 →
        ∀ a : SpatialField, a ∈ initialClassR →
          ∀ g : SpaceTimeField, MemForceR g →
            ∀ δ : ℝ, 0 < δ → ∀ v : ClassicalSolutionR ν a g (T + δ),
              ∃ ε₀ : ℝ, 0 < ε₀ ∧ 2 * ε₀ ^ 2 < T ∧
                ∃ f u : ℝ → SpaceTimeField,
                  (∀ ε ∈ Ioo 0 ε₀,
                    MemForceR (f ε) ∧
                    maximalLifespanR ν a (f ε) = ENNReal.ofReal T ∧
                    ∃ U : ClassicalSolutionR ν a (f ε) T,
                      U.velocity = u ε ∧
                      ∀ t ∈ Icc 0 (T - 2 * ε ^ 2), ∀ x,
                        u ε (t, x) = v.velocity (t, x)) ∧
                  Tendsto (fun ε => forceSobolevENorm (ENNReal.ofReal q) s (f ε - g))
                    (nhdsWithin 0 (Ioi 0)) (𝓝 0) ∧
                  Tendsto (fun ε => energyENorm T (u ε - v.velocity))
                    (nhdsWithin 0 (Ioi 0)) (𝓝 0)

end BlowupDensity.Contracts.V1.DraftB
