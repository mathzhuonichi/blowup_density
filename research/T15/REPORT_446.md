# REPORT 446 — T15 U8 periodized PDE transport

## 1. Theorems with exact statements

Namespace `NSFormalization.Section3.T15`; the viscosity remains `ν`.
All premises below are raw `scalingStatement` clauses or `PlacementData`.
The extra raw smoothness clauses are not needed by the transport identities.

```lean
theorem periodized_momentum
    {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hfzero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
    (heq : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (periodizedScaledVelocity u place.x₀ place.T ε)
        (normalizedScaledPressure p place.x₀ place.T ε) t x =
        periodizedScaledForce f place.x₀ place.T ε (t, x)

theorem periodized_divergence
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hdiv : ∀ t : ℝ, t < 1 → ∀ x : Space, spatialDivergence (zeroPastField u) t x = 0)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDivergence (periodizedScaledVelocity u place.x₀ place.T ε) t x = 0

theorem periodized_initial {u f : VelocityField} {p : PressureField} {K : Set Space}
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ x : Space,
      periodizedScaledVelocity u place.x₀ place.T ε (0, x) = 0
```

The mechanism is a fixed local single copy at every point. For the compact
affine carrier inside the cube, the vendor locally finite lattice family and
closedness exclude all nonzero translates on a neighbourhood, including on
cube faces. Coordinate-floor reduction chooses a lattice shift at the base
point and holds it fixed on that neighbourhood. Local Fréchet derivative
congruence then transports the time derivative, both spatial derivatives in
the Laplacian, advection, and the pressure gradient. The Section 4 parabolic
identity preserves viscosity, and subtracting the Haar pressure mean does
not alter its spatial gradient. Initial vanishing follows from `eps_time`.

## 2. Files

- `formalization/NSFormalization/Section3/T15/Equation.lean`: 18 proved
  declarations, including all three requested field conclusions and reusable
  local-congruence / lattice-translation lemmas. No existing module edited.
- `research/T15/probes/equation_closes.lean`: constructs a placement for the
  registered packet `Bindings.packet 1`, applies all three field theorems,
  proves the source packet nonzero, and proves a nonzero periodized velocity
  occurs at an admissible scale and an interior evolution time.
- `research/T15/axioms_u8.lean`: audits all 18 module declarations; every
  declaration prints exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T15/ATTEMPTS_U8.md`: all failed elaborations with exact diagnostics,
  the successful proof route, and the probe choice.
- `research/T15/T15_SPLIT.md`: U8 completion status.
- `logs/LESSONS.md`: one typed-`EventuallyEq` / simplifier lesson.
- `research/T15/REPORT_446.md`: this report.

Lane 439's report was read from its branch, not imported: the chart has its
representative in the closed cube, yielding pointwise single-copy equality
of torus lifts. This module additionally establishes neighbourhood equality,
which is what the differential operators require.

## 3. Gaps and error text

No gap remains in momentum, divergence, initial data, or their raw-hypothesis
conformance. This module does not assemble the other `ClassicalSolutionT`
fields, which belong to other units.

Probe deviation: `energy_mixed_closes.lean` is not in this checkout. The
fallback placement bump is not supplied with NS momentum/divergence clauses.
Its geometry alone cannot instantiate those hypotheses. The delivered probe
therefore uses the actual registered nonzero PDE packet, with the same cube
centre and radius `3/8`, constructing all 17 placement fields and a positive
threshold from its compact supports. It assumes no PDE or placement input.

Final error text: none. The principal resolved failures were:

```text
Tactic `apply` failed: could not unify the type of `periodize_eventuallyEq_translate ...`
```

Fixed by explicitly supplying the field `(v := scaledVelocity ...)` or
`(v := scaledPressure ...)` rather than asking unification to infer it through
the periodizer. Inferred slice germs had the form `u ∘ fun y => (t, id y)`;
using explicit lambda types makes `.fderiv_eq` rewrite the derivative goals.
The full verbatim diagnostics, including floor/dilation/positivity errors,
are retained in `ATTEMPTS_U8.md`.

## 4. Commands and results

All commands ran in this worktree after `. scripts/lean-env.sh`; all Lake
commands ran from `verification/` with `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T15.SingleCopy` | dependency closure built; 0 errors |
| `lake build NSFormalization.Section3.T15.Equation Bindings.Packet` | module and probe dependency closure built; 0 errors |
| `lake build NSFormalization.Section3.T15.Equation` | final build: 10004 jobs, module 2.7 s, 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T15/Equation.lean` | exit 0, zero output |
| `lake env lean ../research/T15/probes/equation_closes.lean` | exit 0, zero output |
| `lake env lean ../research/T15/axioms_u8.lean` | exit 0; all 18 declarations exactly the three standard axioms |
| `make check` (worktree root) | pass; 13 policy tests and 45-item work queue consistent |
| `lake test` | exit 0; registered test closure passed |
| `python3 experiments/test_contract_mutations.py` (worktree root) | exit 0; refactor accepted, all three bad mutations rejected |

No heartbeat override, forbidden proof primitive, push, merge, or rebase.
Committed locally on `erenup/446-T15-U8-periodized-pde`.
