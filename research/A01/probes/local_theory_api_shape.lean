import NSFormalization.Section4.A01.LocalTheoryBundle

noncomputable section
namespace NSFormalization.Section4.A01.BundleProbe
open Set
open A02 (SpatialField SpaceTimeField ClassicalSolutionR initialClassR)
open D01 (MemForceR sobolevENorm)
open A04 (forceSobolevENormL1)
open scoped ENNReal

structure LocalTheoryAPI where
  /-- `T₀ = T₀(ν,a,f) > 0`, the common existence horizon of
  `02-preliminaries.tex:117` "with one common existence interval for all
  Sobolev orders".  Total as a function so that no choice principle is needed
  to name it; its positivity is `(solution …).horizon_pos` and is not repeated
  as a field. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ
  /-- The classical solution itself, on `[0,T₀)`, for every manuscript datum:
  `ν > 0`, `a ∈ X_R = H^∞ ∩ L²_σ` (`02-preliminaries.tex:12` eq:Rinitial) and
  `f ∈ F_R` (`02-preliminaries.tex:17` eq:Rclasses).  Exposed as data, so that
  `velocity` and `pressure` below are functions of the datum.

  *Narrowing, recorded deliberately.*  `prop:local` itself asks only for "each
  force smooth into every `H^m` on compact time intervals"
  (`02-preliminaries.tex:107-108`); `MemForceR` additionally demands the
  `L¹_t`/`L²_t` finiteness of eq:Rclasses.  This contract is therefore stated
  on a strictly smaller force class than the proposition.  That is exactly the
  class Section 4 quantifies over — `F_c ⊆ F_rd ⊆ F_R`
  (`04-whole-space.tex:183-192`) — so nothing downstream is lost; a consumer
  needing the wider hypothesis must widen this field. -/
  solution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ClassicalSolutionR ν a f (horizon ν a f)
  /-- `paper/sections/appendix-a-local-theory.tex:66-77` together with
  `02-preliminaries.tex:81,90,96`: the four clauses of `prop:local` that go
  beyond `ClassicalSolutionR`, for that same solution on that same horizon —
  all-order Sobolev time smoothness, eq:Rpressure, eq:projected and the radial
  potential. -/
  regularity : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f),
      ManuscriptLocalRegularity ν a f (horizon ν a f) (solution ν a f hν ha hf)
  /-- `appendix-a-local-theory.tex:147-150`: "The `H¹` local existence bounds of
  the cited Theorems 5.1(ii) and 5.4(ii) then give **a common positive
  existence duration** when restarting at `t₀ ↑ S`: the initial `H¹` norms stay
  bounded, and `f` is bounded into `H¹` on `[0,S+1]`."

  The horizon is uniform over any `H¹` ball: for each `ν > 0` and each finite
  bound `K` on `‖a‖_{H¹}` and `‖f‖_{L¹_tH¹}` there is one `δ > 0` below every
  horizon in that ball.  Quantifier order is the operative content — `δ` is
  chosen *before* the datum, so a restart family with bounded `H¹` data gets one
  step length.

  *Why a field and not a remark.*  Without it `horizon` is an arbitrary total
  function and **A04 cannot state its restart from this contract**
  (`research/A01/REVIEW.md` M5): the continuation proof needs precisely the
  displayed uniformity, applied at `t₀ ↑ S`.  A01 is the only owner of a
  property of the local existence theorem.

  *Why qualitative and not a formula.*  Neither `prop:local`
  (`02-preliminaries.tex:105-115`) nor the appendix displays a lower bound for
  `T₀` in terms of `ν` and the norms; the quantitative source behind the
  appendix's sentence is Tao 2013 Theorem 5.4(ii), whose smallness condition is
  `(‖u₀‖_{H¹} + ‖f‖_{L¹_tH¹})⁴ T ≤ c` at viscosity one (published p. 52,
  eq. (46)), rescaled to `ν` by `appendix-a-local-theory.tex:79-87`.  This field
  states only what the manuscript asserts.  If A04 turns out to need the
  explicit `c`-form — for a quantitative restart rather than a merely uniform
  one — that is a strengthening of this field, not a new one.

  The `H¹` norms are the D01 quantities `sobolevENorm 1` (`Data.lean:189`) and
  `forceSobolevENormL1 1` (`Data.lean:231`), both `ℝ≥0∞`-valued and fail-safe to
  `⊤`, so `K ≠ ⊤` is the manuscript's "stay bounded". -/
  horizon_lower_bound : ∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField),
        a ∈ initialClassR → MemForceR f →
          sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K →
            δ ≤ horizon ν a f


-- Every field except the open H¹ field has precisely the required type.
example : ℝ → SpatialField → SpaceTimeField → ℝ := localTheoryData.horizon

example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ClassicalSolutionR ν a f (localTheoryData.horizon ν a f) := localTheoryData.solution

example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f),
      ManuscriptLocalRegularity ν a f (localTheoryData.horizon ν a f)
        (localTheoryData.solution ν a f hν ha hf) := localTheoryData.regularity

example : HorizonLowerBoundH1 localTheoryData.horizon =
    (∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (a : SpatialField) (f : SpaceTimeField),
        a ∈ initialClassR → MemForceR f →
          sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K →
            δ ≤ localTheoryData.horizon ν a f) := rfl

example : ManuscriptHorizonLowerBoundH1 = HorizonLowerBoundH1 localHorizon' := rfl

end NSFormalization.Section4.A01.BundleProbe
