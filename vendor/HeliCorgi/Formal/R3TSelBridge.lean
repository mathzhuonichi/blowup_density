import Formal.GronwallIntegralInequality
import Formal.R3TSelDecodedGradient
import Formal.R3SchwartzInitialData
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# The T-SEL bridge: formal statement layer and conditional assembly (SEL-1 … SEL-10)

This file formalizes the ten-lemma paper bridge of the selected theorem **T-SEL = L_a**
(`docs/gates/STAGE9_REVERSE_GAP_AUDIT_2026-09-02.md`, SS-5/SS-6): the time-integrated
velocity-gradient bound

`Q(u, T′) = ∫ s in 0..T′, ‖∇U(s)‖_{L∞} ≤ G(T; ν, ‖u0‖)`  (head `N0`, **OPEN**)

implies, through 1984-known mathematics, global continuation of the certified class
(`N0 → N1 → N2 → N3`).  Executed on the user's commission of 2026-09-02 (second
session): **bridge formalization only — the head `N0` is deliberately NOT proved, NOT
assumed as an axiom, and no proof search for it is performed.**  `N0` enters exactly as
an explicit hypothesis (`R3TSelGradientBound`) of the conditional theorems, per the
repository discipline that assumptions live in theorem statements.

## SEL-lemma ↔ Lean artifact map

* **SEL-1** (norm transport).  Consumed parts are existing theorems:
  `besselPotential_r3HsToTempered_eq_coordinate`, `r3HsToTempered_memSobolev`
  (`Formal/R3SobolevCarrier.lean`), `r3H3ToL2Operator_r3SchwartzToHsCLM`
  (`Formal/R3SchwartzInitialData.lean`); the initial-time carrier-norm identity is
  `r3TSel_initial_carrierNorm` below.  The classical two-sided `Σ‖D^α·‖²`-vs-Bessel
  comparability `R3TSelClassicalSobolevComparability` is **PROVED**
  (`r3TSel_classicalSobolevComparability`, `Formal/R3TSelClassicalComparability.lean`,
  third session), with explicit constants.
* **SEL-2** (embedding): **closed** — `r3TSel_decoded_embedding`
  (`Formal/R3TSelDecodedGradient.lean`), quantitative, explicit constant.
* **SEL-3** (identification + interior smoothing).  The identification/NS-semantics half
  is the existing capstone `r3EndpointSafeProjectedMild_navierStokes`
  (`Formal/R3NavierStokesEquation.lean`).  The interior smoothing upgrade is the open
  statement `R3TSelInteriorSobolevSmoothing` (consumed only by the future proof of
  SEL-5, not by the assembly).
* **SEL-4** (BKM/Kato–Ponce commutator): `R3TSelKatoPonceCommutator`, stated on the
  Schwartz core in the derivative-tuple form of the audit's own SS-6 statement (BKM
  ineq. (13)); see the definition's docstring for the relation to the sharp fractional
  Kato–Ponce, which is consumed by nothing in the chain.
* **SEL-5** (H³ ladder) + the `t₀ ↓ 0` endpoint limit of **SEL-7**: open statement
  `R3TSelH3Ladder` — the ladder in **integrated** form on `[0, t]` along certified
  solutions, `‖u t‖² ≤ ‖u0‖² + ∫₀ᵗ 2C‖∇U(s)‖_{L∞}‖u s‖² ds`.  (The paper derivation
  tests the `D^α`-equation, discards the viscous term by sign, kills transport by
  `div U = 0`, drops the projector — then integrates from `t₀ ↓ 0`; the integral form
  is chosen so the assembly needs no differentiability of `t ↦ ‖u t‖`.)
* **SEL-6** (Grönwall): **closed** — `le_mul_exp_of_le_add_intervalIntegral`
  (`Formal/GronwallIntegralInequality.lean`).
* **SEL-7** (endpoint bookkeeping): **closed in the parts the assembly consumes** —
  trajectory-norm continuity `r3TSel_carrierNorm_continuousOn`, integrand continuity
  and interval integrability (`Formal/R3TSelDecodedGradient.lean`), `Q` monotonicity;
  the `t₀ ↓ 0` limit is folded into `R3TSelH3Ladder` as noted above.
* **SEL-8** (realness): **closed** — `r3TSel_decodedReal_of_admissible` below,
  instantiating the existing unconditional realness theorems.
* **SEL-9** (bridge assembly `L_bridge(Q_a, R_a)`): **closed conditionally on SEL-5** —
  `r3TSel_carrierBound_of_ladder`: given the ladder, every certified solution obeys
  `‖u t‖ ≤ ‖u0‖ · exp(C·Q(u,t))`; `ν`-free exactly as the audit records.
* **SEL-10** (plug discharge): **closed** — uniqueness transfer
  `r3TSel_uniform_bound_transfer` (via `r3EndpointSafeProjectedMildSolution_unique`),
  and the sSup/BddAbove instantiation inside `r3TSel_horizons_unbounded`, feeding
  `r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound` (`N1 → N2`) and the
  dichotomy's left branch (`N2 → N3`).

## The conditional chain

`r3TSel_horizons_unbounded` : SEL-5-hypothesis + `N0`-hypothesis ⟹ the certified
horizon set of the datum is unbounded (`N2`).  `r3TSel_admissibleSchwartz_globalContinuation`
and `r3TSel_conditional_globalContinuation` package `N3` for admissible real
divergence-free Schwartz data.  Both are honest implications: **no unproved statement
is asserted**; the two open analytic inputs are the named hypotheses.

## Claim boundary

The head `N0` (`R3TSelGradientBound` / `R3TSelHead`) is OPEN and unclaimed —
Clay-equivalent-or-harder per the audit; nothing here approaches the Millennium problem
in either direction.  `VIOLATED`/park semantics of the frozen research map are
untouched.  The open statement definitions (`R3TSelClassicalSobolevComparability`,
`R3TSelInteriorSobolevSmoothing`, `R3TSelKatoPonceCommutator`, `R3TSelH3Ladder`) are
`Prop`-valued **definitions**, never asserted, never axiomatized; proving them is
future work (standard mathematics per the audit's classification, but real work —
Kato–Ponce and parabolic smoothing have no mathlib analogue today).  `Q` is *a*
continuation-controlling quantity, not "the" (C0 discipline).  The certified-class
terminal node `N3` is the repository's formal proxy for global continuation, not
classical global smoothness (maximal-trajectory gluing and the parabolic smoothness
upgrade remain outside scope guards, as recorded in the audit).
-/

namespace MNS2

open MeasureTheory Set LineDeriv
open scoped FourierTransform SchwartzMap ENNReal NNReal

noncomputable section

/-! ## SEL-1 — consumed part (existing anchors) and the deferred comparability -/

/-- SEL-1, initial-time norm transport along a certified solution: the trajectory starts
at the datum, so the initial carrier norm is the datum norm.  (The decoded `H³` reading
of the carrier norm is fixed by `besselPotential_r3HsToTempered_eq_coordinate` and
`r3HsToTempered_memSobolev`; `decode ∘ encode = id` on the Schwartz core is
`r3H3ToL2Operator_r3SchwartzToHsCLM`.) -/
theorem r3TSel_initial_carrierNorm {nu T : ℝ} {hnu : 0 < nu} {u0 : R3HsVelocity 3}
    {u : ℝ → R3HsVelocity 3}
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u) :
    ‖u 0‖ = ‖u0‖ := by
  rw [hu.2.2.1]

/-- **SEL-1, comparability clause**: two-sided comparability, on the Schwartz core,
between the classical squared Sobolev norm `Σ_{n ≤ 3} ‖D^n φ‖²_{L²}` and the squared
Bessel carrier norm.  It measures the reformulation distance of SEL-4 from its
literature `D^α` form.  **PROVED** in `Formal/R3TSelClassicalComparability.lean`
(`r3TSel_classicalSobolevComparability`, explicit constants `c₁ = 1/81`,
`c₂ = 27(2π)⁶`). -/
def R3TSelClassicalSobolevComparability : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ φ : R3SchwartzVelocity,
      (∀ n ∈ Finset.range 4, MemLp (iteratedFDeriv ℝ n (⇑φ)) 2 volume) ∧
      c₁ * ‖r3SchwartzToHsCLM 3 φ‖ ^ 2 ≤
          (∑ n ∈ Finset.range 4,
            ((eLpNorm (iteratedFDeriv ℝ n (⇑φ)) 2 volume).toReal) ^ 2) ∧
        (∑ n ∈ Finset.range 4,
            ((eLpNorm (iteratedFDeriv ℝ n (⇑φ)) 2 volume).toReal) ^ 2) ≤
          c₂ * ‖r3SchwartzToHsCLM 3 φ‖ ^ 2

/-! ## SEL-3 — the open interior-smoothing statement

The identification half (mild solution ⇒ strong `L²` time derivative + componentwise
`𝓢'` Navier–Stokes with the explicit Helmholtz pressure at interior times) is the
existing capstone `r3EndpointSafeProjectedMild_navierStokes` and is not restated. -/

/-- **SEL-3, smoothing clause (OPEN, stated only)**: at interior times of a certified
horizon, the decoded distribution of a certified solution with solenoidal datum lies in
every Sobolev order.  Consumed only by the future proof of `R3TSelH3Ladder`; the
assembly below does not use it.  KNOWN-MATH-TO-FORMALIZE (parabolic smoothing). -/
def R3TSelInteriorSobolevSmoothing : Prop :=
  ∀ (nu T : ℝ) (hnu : 0 < nu) (u0 : R3HsVelocity 3) (u : ℝ → R3HsVelocity 3),
    IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u →
    u0 ∈ r3L2SolenoidalSubmodule →
    ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ k : ℕ,
      TemperedDistribution.MemSobolev (k : ℝ) 2 (r3HsToTemperedCLM 3 (u t))

/-! ## SEL-4 — the BKM/Kato–Ponce commutator statement (derivative-tuple form) -/

/-- **SEL-4**: the BKM commutator estimate at order three, on the Schwartz core, in the
derivative-tuple form of the audit record's own SS-6 statement (BKM, CMP 94 (1984),
ineq. (13)): for every direction tuple `v` of length `n ≤ 3`,

`‖∂^v((φ·∇)φ) − (φ·∇)(∂^v φ)‖_{L²} ≤ C ‖∇φ‖_{L∞} ‖J³φ‖_{L²}`.

This is exactly the commutator consumed by the `D^α` energy derivation of the `H³`
ladder (SEL-5); the divergence-free hypothesis of the paper statement is not needed for
the commutator itself and is dropped (it is spent on the transport cancellation inside
SEL-5).  The distance to the carrier's `J³` reading is the **proved** SEL-1
comparability `r3TSel_classicalSobolevComparability`.  The sharp *fractional* Kato–Ponce
commutator (`J³` in place of `∂^v`, CPAM 41 (1988)) is strictly stronger, needs
Littlewood–Paley machinery absent from mathlib, and is consumed by nothing in the T-SEL
chain; it is deliberately NOT restated here.  Discharged in
`Formal/R3TSelLeibnizCommutator.lean`. -/
def R3TSelKatoPonceCommutator (C : ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ 3 → ∀ (v : Fin n → Fin 3) (φ : R3SchwartzVelocity),
    ‖((∂^{fun i => r3StdBasis (v i)} (r3SchwartzConvection φ φ) -
        r3SchwartzConvection φ (∂^{fun i => r3StdBasis (v i)} φ)).toLp 2 :
          R3L2Velocity)‖ ≤
      C * (r3SchwartzGradSup φ * ‖r3SchwartzToHsCLM 3 φ‖)

/-! ## SEL-5 — the open integrated H³ ladder -/

/-- **SEL-5 + SEL-7 endpoint limit (OPEN, stated only)**: the integrated `H³` energy
ladder along certified solutions with **real** solenoidal datum,

`‖u t‖² ≤ ‖u0‖² + ∫ s in 0..t, 2C ‖∇U(s)‖_{L∞} ‖u s‖² ds` on `[0, T]`,

with `‖∇U(s)‖_{L∞}` carried by `r3DecodedGradSup` (a.e.-pinned to the decoded velocity
by `r3DecodedRepresentative_ae_r3H3ToL2Operator`).  The paper derivation is BKM
ineq. (14) + the NS remark: test the `D^α`-equation with `D^α U`, discard the viscous
term by sign (`C` is `ν`-free), kill transport by `div U = 0` **and realness of `U`**
(the transport cancellation `re⟨V,(U·∇)V⟩ = −½∫(div U)|V|²` consumes a real transport
field, which is why the realness hypothesis is part of the statement: SEL-8 supplies it
for every admissible datum, and the head/N3 quantify only over admissible data), drop
the projector, use SEL-4, integrate from `t₀ ↓ 0` by SEL-3 + SEL-7.
KNOWN-MATH-TO-FORMALIZE. -/
def R3TSelH3Ladder (C : ℝ) : Prop :=
  ∀ (nu T : ℝ) (hnu : 0 < nu) (u0 : R3HsVelocity 3) (u : ℝ → R3HsVelocity 3),
    IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u →
    u0 ∈ r3L2SolenoidalSubmodule →
    IsR3RealVelocity u0 →
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖u t‖ ^ 2 ≤ ‖u0‖ ^ 2 +
        ∫ s in (0 : ℝ)..t, 2 * C * r3DecodedGradSup (u s) * ‖u s‖ ^ 2

/-! ## SEL-7 — consumed bookkeeping (closed) -/

/-- SEL-7: the carrier norm is continuous along every certified solution. -/
theorem r3TSel_carrierNorm_continuousOn {nu T : ℝ} {hnu : 0 < nu}
    {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u) :
    ContinuousOn (fun t => ‖u t‖) (Set.Icc 0 T) :=
  hu.2.1.norm

/-- SEL-7: the T-SEL integrand is interval integrable along every certified solution up
to every certified time — `Q(u, t)` is well defined and finite per horizon. -/
theorem r3TSel_gradIntegrand_intervalIntegrable {nu T t : ℝ} {hnu : 0 < nu}
    {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => r3DecodedGradSup (u s)) volume 0 t :=
  intervalIntegrable_r3DecodedGradSup_comp hu.2.1 ht

/-! ## SEL-8 — realness (closed) -/

/-- SEL-8: for admissible (real, divergence-free Schwartz) data, the decoded physical
velocity of every certified solution is physically real at every certified time — the
gradient-sup measures a real-field quantity while every estimate runs on the complex
carrier. -/
theorem r3TSel_decodedReal_of_admissible {nu T : ℝ} {hnu : 0 < nu}
    {φ : R3SchwartzVelocity} (hφ : IsR3AdmissibleSchwartzDatum φ)
    {u : ℝ → R3HsVelocity 3}
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T (r3SchwartzToHsCLM 3 φ) u) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, IsR3RealVelocity (r3H3ToL2Operator (u t)) :=
  r3EndpointSafeProjectedMild_isR3RealVelocity_decoded hu hφ.isR3RealVelocity_encode

/-! ## The head N0 — OPEN, hypothesis-only -/

/-- **The T-SEL head `N0` at one datum (OPEN — never asserted, never axiomatized).**
For every finite reference horizon `T` there is a bound `G` (allowed to depend on
`T, ν, u0`) dominating `Q(u, T′) = ∫ s in 0..T′, ‖∇U(s)‖_{L∞}` over **all** certified
solutions on **all** certified horizons `T′ ≤ T`.  Proving this for admissible data is
Clay-equivalent-or-harder (audit SS-5); a certified family driving `Q → ∞` on a bounded
horizon is exactly the falsification signature the lab's singularity program must
produce.  Both directions are open. -/
def R3TSelGradientBound {nu : ℝ} (hnu : 0 < nu) (u0 : R3HsVelocity 3) : Prop :=
  ∀ T : ℝ, ∃ G : ℝ, ∀ T' : ℝ, T' ≤ T →
    ∀ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T' u0 u →
      r3TSelGradIntegral u T' ≤ G

/-- **The T-SEL head `N0`, full form (OPEN)**: the gradient bound for every viscosity
and every admissible Schwartz datum. -/
def R3TSelHead : Prop :=
  ∀ (nu : ℝ) (hnu : 0 < nu) (φ : R3SchwartzVelocity),
    IsR3AdmissibleSchwartzDatum φ →
    R3TSelGradientBound hnu (r3SchwartzToHsCLM 3 φ)

/-! ## SEL-9 — bridge assembly (closed conditionally on SEL-5) -/

/-- **SEL-9, `L_bridge(Q_a, R_a)`**: given the integrated ladder (SEL-5 hypothesis),
every certified solution with solenoidal datum obeys the exponential carrier bound

`‖u t‖ ≤ ‖u0‖ · exp (C · Q(u, t))` on `[0, T]`

— Grönwall (SEL-6) applied to `y = ‖u ·‖²` with coefficient `2C‖∇U‖_{L∞}` (SEL-7
supplies continuity and integrability).  The bound is `ν`-free: dissipation was
discarded inside the ladder, exactly as the audit records. -/
theorem r3TSel_carrierBound_of_ladder {C : ℝ} (hC : 0 ≤ C) (hlad : R3TSelH3Ladder C)
    {nu T : ℝ} (hnu : 0 < nu) {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u)
    (hsol : u0 ∈ r3L2SolenoidalSubmodule) (hreal : IsR3RealVelocity u0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖u t‖ ≤ ‖u0‖ * Real.exp (C * r3TSelGradIntegral u t) := by
  intro t ht
  have hT0 : (0 : ℝ) ≤ T := hu.1
  have hcont : ContinuousOn u (Set.Icc 0 T) := hu.2.1
  have hy : ContinuousOn (fun t => ‖u t‖ ^ 2) (Set.Icc 0 T) := (hcont.norm).pow 2
  have hm : ContinuousOn (fun s => 2 * C * r3DecodedGradSup (u s)) (Set.Icc 0 T) :=
    continuousOn_const.mul (continuousOn_r3DecodedGradSup_comp hcont)
  have hm0 : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ 2 * C * r3DecodedGradSup (u s) := fun s _ =>
    mul_nonneg (by linarith) (r3DecodedGradSup_nonneg (u s))
  have hle : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖u s‖ ^ 2 ≤ ‖u0‖ ^ 2 +
        ∫ r in (0 : ℝ)..s, 2 * C * r3DecodedGradSup (u r) * ‖u r‖ ^ 2 :=
    hlad nu T hnu u0 u hu hsol hreal
  have hgron := le_mul_exp_of_le_add_intervalIntegral (T := T) (a := ‖u0‖ ^ 2)
    (y := fun t => ‖u t‖ ^ 2) (m := fun s => 2 * C * r3DecodedGradSup (u s))
    hT0 hy hm hm0 hle t ht
  have hQ : (∫ s in (0 : ℝ)..t, 2 * C * r3DecodedGradSup (u s)) =
      2 * C * r3TSelGradIntegral u t := by
    unfold r3TSelGradIntegral
    rw [← intervalIntegral.integral_const_mul]
  rw [hQ] at hgron
  have hsqrt := Real.sqrt_le_sqrt hgron
  rw [Real.sqrt_sq (norm_nonneg (u t))] at hsqrt
  have hprod : Real.sqrt (‖u0‖ ^ 2 * Real.exp (2 * C * r3TSelGradIntegral u t)) =
      ‖u0‖ * Real.exp (C * r3TSelGradIntegral u t) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg u0)]
    congr 1
    rw [show 2 * C * r3TSelGradIntegral u t =
        C * r3TSelGradIntegral u t + C * r3TSelGradIntegral u t by ring,
      Real.exp_add, Real.sqrt_mul_self (Real.exp_nonneg _)]
  rw [hprod] at hsqrt
  exact hsqrt

/-! ## SEL-10 — plug discharge (closed) -/

/-- SEL-10(a), uniqueness transfer: a carrier bound along one certified solution on a
horizon transfers to every certified solution on that horizon (unrestricted uniqueness
pins them together). -/
theorem r3TSel_uniform_bound_transfer {nu T : ℝ} {hnu : 0 < nu}
    {u0 : R3HsVelocity 3} {u v : ℝ → R3HsVelocity 3} {R : ℝ}
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u)
    (hv : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 v)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u t‖ ≤ R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖v t‖ ≤ R := by
  intro t ht
  rw [r3EndpointSafeProjectedMildSolution_unique hv hu t ht]
  exact hbound t ht

/-- **`N0 → N1` (Arrow A composed)**: the ladder hypothesis (SEL-5) and the head
hypothesis (`N0`, at this datum) give, for every finite reference horizon `T`, a single
nonnegative carrier bound `R(T) = ‖u0‖·exp(C·G(T))` valid for every certified solution
on every certified horizon `T′ ≤ T` at every certified time — node `N1` of the audit's
dependency chain, `ν`-free through the bridge. -/
theorem r3TSel_uniform_carrierBound_of_head {C : ℝ} (hC : 0 ≤ C)
    (hlad : R3TSelH3Ladder C) {nu : ℝ} (hnu : 0 < nu) {u0 : R3HsVelocity 3}
    (hsol : u0 ∈ r3L2SolenoidalSubmodule) (hreal : IsR3RealVelocity u0)
    (hhead : R3TSelGradientBound hnu u0) (T : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ T' : ℝ, T' ≤ T →
      ∀ u : ℝ → R3HsVelocity 3,
        IsR3EndpointSafeProjectedMildSolutionOn hnu T' u0 u →
        ∀ t ∈ Set.Icc (0 : ℝ) T', ‖u t‖ ≤ R := by
  obtain ⟨G, hG⟩ := hhead T
  refine ⟨‖u0‖ * Real.exp (C * G),
    mul_nonneg (norm_nonneg u0) (Real.exp_nonneg _), ?_⟩
  intro T' hT' u hu t ht
  have hQT : r3TSelGradIntegral u T' ≤ G := hG T' hT' u hu
  have hQt : r3TSelGradIntegral u t ≤ r3TSelGradIntegral u T' :=
    r3TSelGradIntegral_mono hu.2.1 ht.1 ht.2 le_rfl
  have hcarrier := r3TSel_carrierBound_of_ladder hC hlad hnu hu hsol hreal t ht
  refine hcarrier.trans ?_
  have hCQ : C * r3TSelGradIntegral u t ≤ C * G :=
    mul_le_mul_of_nonneg_left (hQt.trans hQT) hC
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hCQ) (norm_nonneg u0)

/-- **SEL-10(b) + `N1 → N2`**: the ladder hypothesis (SEL-5) and the head hypothesis
(`N0`, at this datum) force the certified horizon set to be unbounded.  The proof is the
audit's sSup/BddAbove two-liner: were the horizon set bounded above, instantiating the
head at `T = sSup + 1` yields through `N1` a single uniform carrier bound for all
certified solutions on all certified horizons, and
`r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound` refutes boundedness. -/
theorem r3TSel_horizons_unbounded {C : ℝ} (hC : 0 ≤ C) (hlad : R3TSelH3Ladder C)
    {nu : ℝ} (hnu : 0 < nu) {u0 : R3HsVelocity 3}
    (hsol : u0 ∈ r3L2SolenoidalSubmodule) (hreal : IsR3RealVelocity u0)
    (hhead : R3TSelGradientBound hnu u0) :
    ¬ BddAbove (r3MildHorizons hnu u0) := by
  intro hbdd
  obtain ⟨R, hR0, hR⟩ := r3TSel_uniform_carrierBound_of_head hC hlad hnu hsol hreal
    hhead (sSup (r3MildHorizons hnu u0) + 1)
  have hbound : ∀ T ∈ r3MildHorizons hnu u0, ∀ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u t‖ ≤ R := by
    intro T hT u hu t ht
    have hTle : T ≤ sSup (r3MildHorizons hnu u0) + 1 := by
      have := le_csSup hbdd hT
      linarith
    exact hR T hTle u hu t ht
  exact r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound hnu hR0 hbound hbdd

/-! ## N2 → N3 — packaging for admissible Schwartz data -/

/-- **`N3` at one admissible datum**: given the ladder (SEL-5 hypothesis) and the head
(`N0` hypothesis at the encoded datum), arbitrarily long certified horizons carry mild
solutions from every admissible real divergence-free Schwartz datum — the left branch of
the certified blow-up dichotomy, i.e. global continuation of the certified class at this
datum. -/
theorem r3TSel_admissibleSchwartz_globalContinuation {C : ℝ} (hC : 0 ≤ C)
    (hlad : R3TSelH3Ladder C) {nu : ℝ} (hnu : 0 < nu) {φ : R3SchwartzVelocity}
    (hφ : IsR3AdmissibleSchwartzDatum φ)
    (hhead : R3TSelGradientBound hnu (r3SchwartzToHsCLM 3 φ)) :
    ∀ M : ℝ, ∃ T ∈ r3MildHorizons hnu (r3SchwartzToHsCLM 3 φ), M ≤ T := by
  have hub := r3TSel_horizons_unbounded hC hlad hnu hφ.encode_mem_solenoidal
    hφ.isR3RealVelocity_encode hhead
  intro M
  obtain ⟨T, hT, hMT⟩ := not_bddAbove_iff.mp hub M
  exact ⟨T, hT, hMT.le⟩

/-- **The conditional T-SEL chain `N0 → N1 → N2 → N3`, full form.**  If the integrated
`H³` ladder (SEL-5, known 1984 mathematics, unformalized) holds with some nonnegative
constant, and the OPEN head `N0` holds, then the certified class continues globally from
every admissible real divergence-free Schwartz datum at every viscosity.  Every
hypothesis is explicit; nothing open is asserted. -/
theorem r3TSel_conditional_globalContinuation {C : ℝ} (hC : 0 ≤ C)
    (hlad : R3TSelH3Ladder C) (hhead : R3TSelHead) :
    ∀ (nu : ℝ) (hnu : 0 < nu) (φ : R3SchwartzVelocity),
      IsR3AdmissibleSchwartzDatum φ →
      ∀ M : ℝ, ∃ T ∈ r3MildHorizons hnu (r3SchwartzToHsCLM 3 φ), M ≤ T :=
  fun nu hnu φ hφ =>
    r3TSel_admissibleSchwartz_globalContinuation hC hlad hnu hφ (hhead nu hnu φ hφ)

end

end MNS2
