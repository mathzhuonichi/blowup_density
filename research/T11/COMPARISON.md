# T11 reconciled comparison — periodic local theory and continuation

This merges the blind comparisons from lanes 288 (Draft A) and 289 (Draft B)
under the binding rulings in `research/T11/RECONCILIATION.md`. The provenance
files are retained verbatim beside this document.

## Paper clause → reconciled Lean field

| Paper clause | Draft A provenance | Draft B provenance | Reconciled declaration / ruling |
|---|---|---|---|
| Periodic inputs `X_T`, `F_T` (`02-preliminaries.tex:7-26`) | `PeriodicLocalTheoryAPI.solution`; viscosity, datum, force order | Same | `solution` keeps literal order `∀ν, 0<ν → ∀a, a∈initialClassT → ∀f, f∈forceClassT`; no mean-zero premise. |
| One common interval for all Sobolev orders (`02-preliminaries.tex:116-120`; `appendix-a-local-theory.tex:62-76`) | `horizon`, `solution`, `regularity`, `sobolev_smooth` | Same | Keep the single real `horizon ν a f`; use B's pointwise `IsPeriodicSobolevPathOn s I u G`, avoiding A's global-extension constraint. |
| Projected equation (`02-preliminaries.tex:80-83`; `appendix-a-local-theory.tex:76-77`) | `PeriodicLocalRegularity.projected` | Same | Keep the pointwise physical equality `(f-div(u⊗u))-∇p`, mirroring Section 4. |
| Torus pressure prescription (`02-preliminaries.tex:84-88`) | `pressure_poisson` plus redundant periodic/gauge field | Leray-complement recovery plus redundant periodic/gauge fields | Keep A's displayed Poisson equation. Drop every periodic/gauge repetition because `ClassicalSolutionT` already carries them. |
| Finiteness of Sobolev norms (`02-preliminaries.tex:107-114`) | Implicit in `sobolev_smooth` | Extra `sobolev_enorm_finite` | Drop B's redundant field: a representing datum already prevents the extended norm from being `⊤`. |
| Local existence (`02-preliminaries.tex:105-109`; `appendix-a-local-theory.tex:60-70`) | Type-valued API with selected horizon | Same, with `Type` implicit | Use A's explicit `PeriodicLocalTheoryAPI : Type`; all constant-free APIs are `Prop`. |
| Velocity uniqueness (`appendix-a-local-theory.tex:117-124`) | Pointwise on `Ico 0 (min T₁ T₂)` | Same | Keep unchanged. |
| Normalized pressure uniqueness (`02-preliminaries.tex:28,84-109`) | Literal pointwise equality | Same | Keep literal equality; the zero-mean gauge removes the whole-space time-dependent constant. |
| Maximal solution (`02-preliminaries.tex:32-34,105-109`; `appendix-a-local-theory.tex:123-125`) | Type-valued `PeriodicMaximalSolution` using `SolvesBelowT` | `IsMaximalPeriodicSolution` predicate, but with regularity conjunct | Use B's predicate shape and drop its extra regularity conjunct, exactly mirroring registered `IsMaximalSolution`. |
| Maximal uniqueness (`02-preliminaries.tex:105-109`) | Auxiliary positive horizon with `≤` | Auxiliary horizon with `<` | Use neither literal shape: quantify directly over `t≥0` with `ofReal t < maximalLifespanT`, then pointwise velocity and pressure equality. |
| Selected horizon below lifespan (`02-preliminaries.tex:32-34`) | `horizon_le_maximal` | `horizon_le_lifespan` | Keep B's registered spelling `horizon_le_lifespan`. |
| Common fields below a possibly unattained endpoint (`appendix-a-local-theory.tex:117-125`) | `SolvesBelowT` | A full `ClassicalSolutionT ... S` | Keep A decisively: the criterion is applied at the supremal lifespan, which need not be attained. |
| Squared-H² criterion (`02-preliminaries.tex:109-114`) | Wrapper norm and real `rpow` exponent | Inlined periodic norm and natural square | Keep B's inlined `ℝ≥0∞` lintegral with `^ (2 : ℕ)` / `^ 2`, matching the registered spelling and avoiding real-integral junk zero. |
| Fixed-force H¹ restart (`appendix-a-local-theory.tex:146-151`) | Inline field, force and finite ball before uniform `∃δ>0` | Separate predicate, same fixed-force order | Inline the field and keep the manuscript H¹ ball. The shifted force is passed directly to `ClassicalSolutionT`; it need not lie in `forceClassT`. |
| Higher-order bound (`appendix-a-local-theory.tex:127-147`) | `SolvesBelowT` fields | Full-horizon solution | Keep A's common-field hypothesis and B's inlined periodic norms. |
| Endpoint restart (`appendix-a-local-theory.tex:146-153`) | Uniform `∃δ>0` before datum and fields | δ chosen after one solution | Keep A's δ-first order and exact overlap equality of velocity and normalized pressure. |
| Concrete extension (`02-preliminaries.tex:109-114`; `appendix-a-local-theory.tex:149-155`) | Inlined larger solution | Named relation with redundant `RegularThroughT` | Keep named `ExtendsBeyondT` over `(u,p)` and delete the redundant conjunct; its witness already implies regular-through. |
| Maximal lifespan consequence (`03-torus.tex:490-502`) | Present with endpoint condition `≤` | Omitted | Keep A. The non-strict `ofReal S ≤ lifespan` is load-bearing at a finite maximal endpoint. |
| Mean identity (`appendix-a-local-theory.tex:89-93`; `03-torus.tex:395-403`) | Actual solution mean equals prescribed data mean | Same | Keep `mean_formula` with the known data-defined `galileanMeanT a f t = meanT a + ∫₀ᵗ meanT(f r)`. |
| Mean derivative (`appendix-a-local-theory.tex:92-98`; `03-torus.tex:397-403`) | `HasDerivAt` for the solution mean | Same | Keep on `Ioo 0 T`, with derivative `forceMeanT f t`; no derivative is embedded in a force definition. |
| Galilean reduction (`appendix-a-local-theory.tex:95-106`) | Transform used a solution-derived mean and `fderiv` in force | Transform used a solution-derived mean but subtracted `meanT f` | Use neither mean parameter: every transform is built from the known data `(a,f)`, and the force subtracts `forceMeanT f`. Carry `PeriodicLocalRegularity` in the transformed solution. |
| Transformed classes (`appendix-a-local-theory.tex:89-104`) | Absent | Present but false with arbitrary off-lifespan solution values | Keep B's field after switching to the data-defined mean; use registered `meanZeroPartT` rather than a duplicate centered-datum name. |
| Mean-zero conclusions (`appendix-a-local-theory.tex:97-103`) | Separate velocity/force fields | One three-conjunct field | Keep B's `transformed_mean_zero` for datum, velocity, and force. |
| Translation invariance (`appendix-a-local-theory.tex:102-103`) | General periodic field and arbitrary shift | Solution-specific special case | Keep A's general extended-norm equality. |
| Viscosity scaling (`appendix-a-local-theory.tex:79-87`) | Forward/backward solution conversion | Also class preservation and inverse identities | Keep B's four-field package, `(ν^2)⁻¹` spelling, `T ↦ ν*T`, and original-horizon parametrization of `from_unit`. |
| Critical-order density vocabulary | Absent | Absent | Out of T11 scope. The binding reconciliation says nothing absent from both drafts is added; `q : ℝ≥0∞`, `q=1∨q=2`, and `criticalOrder q.toReal` belong to later density specifications, not these five APIs. |

## Reconciled representation choices

- `PeriodicLocalRegularity` has exactly three nonredundant fields:
  `sobolev_smooth`, `pressure_poisson`, and `projected`.
- `PeriodicLocalTheoryAPI : Type` has exactly eight fields; the other three
  top-level APIs and `PeriodicLocalRegularity` are `Prop`.
- `IsMaximalPeriodicSolution` and `SolvesBelowT` follow the registered
  Section 4 predicate shapes without pretending that an `ℝ≥0∞` endpoint is
  an attained real solution horizon.
- `ExtendsBeyondT` returns a concrete longer normalized solution; continuation
  conclusions are stronger and more useful than a bare lifespan inequality.
- Every criterion norm is `ℝ≥0∞`-valued and finiteness is `≠ ⊤`.
- The mean and displacement are determined from `(a,f)` on all times. This
  makes the transformed class assertion meaningful for total Lean functions
  and avoids applying `fderiv` to an arbitrary mean curve.
- The manuscript's H¹ restart statement is retained. The Section 4 H⁷
  narrowing is implementation guidance only and is not silently substituted.

## Blind-draft ambiguities and their resolution

1. Pressure recovery at `t=0` remains on `Ico 0 T`, following the displayed
   torus prescription and one-sided smooth endpoint regularity.
2. Restart times range over all `Icc 0 S`, with one δ uniform over that compact
   interval and the H¹ datum ball.
3. The original force is fixed before δ. No cross-force uniformity is claimed.
4. The H¹ restart ball is manuscript fidelity; an H⁷ contract would require an
   explicit versioned narrowing.
5. Total maximal fields are constrained only at presingular times, never after
   a finite lifespan.
6. `mean_derivative` uses ordinary `HasDerivAt` only on `Ioo 0 T`; no unneeded
   one-sided derivative at zero is added.
7. Public local theory is narrowed to the Section 3 consumer class `F_T`;
   shifted restart forces are accepted directly by the solution structure.
8. Interval-local Sobolev paths are pointwise on the requested time set and
   impose no artificial global extension.
9. `S : ℝ` already expresses finiteness of the endpoint; the separate
   hypothesis retained is `0<S`.
10. Exact pressure overlap is sound because each `ClassicalSolutionT` carries
    the zero-mean gauge.

## Proof dependencies

The following text is copied from the binding reconciliation.

① register `T01.torus_data`, delete tier-(a) copies. ② unique weighted Fourier data for smooth periodic slices at every integer order; upgrade `ContinuousOn`→`ContDiffOn`. ③ `convectionDivergenceT = (u·∇)u` under solenoidality. ④ periodic pressure recovery: Poisson solvability, periodicity, zero mean, smoothness, uniqueness, **and** its equivalence to the order-0 Leray-complement form. ⑤ field-by-field conversion `ClassicalSolutionT ↔ Paper1/PeriodicLifespan.Flow` + round-trip lemmas (structure exception: no `rfl` bridge). ⑥ restriction/patching/order theory of `maximalLifespanT`, maximal gluing and uniqueness. ⑦ measurability of `t ↦ periodicSobolevENorm 2 (u t)` and the bridge `squaredHTwoIntegralT ≠ ⊤ ↔ PeriodicLocalLifespan.FiniteH2Energy`. ⑧ periodic high-order energy inequality `eq:Rhigh`, regularized-norm division, Grönwall `eq:highcontinuation`. ⑨ quantitative `H¹` local existence for forces merely smooth at time zero (T10's `F_T` is not closed under positive time shift). ⑩ restart patching with exact normalized-pressure agreement. ⑪ mean identity by integrating the equation over `T³` (Laplacian/pressure-gradient/nonlinear means vanish) + FTC for `prescribedMeanT`. ⑫ time-dependent translation preserves smoothness, divergence, gauge and every `H^s`; the `X'=m` cancellation. ⑬ viscosity chain rules, horizon scaling, class preservation.

**Implementation candidates** (both COMPARISONs, deduped; none imported by the spec): `Paper1/PeriodicLocalLifespan.lean` (`ClassicalPeriodicLocalTheory`, `IsSmoothPeriodicForce`, `MaximalSolution`, `exists_maximal_periodic_solution`, `maximal_solutions_agree`, `normalized_flows_agree`, `exists_periodic_extension_of_finite_h2`, `extension_agrees_on_common_interval`, `maximal_endpoint_gt_of_finite_h2`, `h2SquaredProfile`/`FiniteH2Energy`) — the closest conditional interface, and the target structure named in `SECTION3_PLAN.md` §3; `Paper1/PeriodicLifespan.lean` (`Flow`, `lifespan`, `horizon_le_lifespan`, `lifespan_le_iff`, `lifespan_le_iff_no_extension`); `Paper1/PeriodicFlowRestriction.lean` (`Flow.restrict`, `Flow.nonempty_restrict`); `Paper1/PeriodicUniqueness.lean` (`classical_uniqueness_on_Icc`, `normalized_residual`); `Paper1/PeriodicPressureNormalization.lean` (`pressureMean`, `normalizedPressure*`, `normalizedFlow`, `normalizedFlow_mean_zero`); `Paper1/PeriodicInitialData.lean` (`IsAdmissibleInitialData`, `Flow.initial_*`). **Not** a candidate: `Paper1/PeriodicOrdinaryLocal.lean` — its `OrdinaryRepresentative` needs genuine `L²(ℝ³)` data, impossible for a nonzero periodic field (both drafts flag this independently). **No** `PeriodicMeanReduction*` / `Galilean*` module exists: the whole mean-reduction package is new work.

## Open questions for the owner

1. The registered Section 4 implementation proves only a fixed-force H⁷
   restart, while this specification deliberately retains Appendix A's H¹
   restart ball (`appendix-a-local-theory.tex:147-150`). If the proof lane
   meets the same obstruction, should T11 receive an explicit V2 H⁷ narrowing?
2. `T01.torus_data` exists on lane 293 but is not present in this lane's base
   commit. On integration, should the registered data-tier copies through
   `IsPeriodicReweight` be deleted immediately and replaced by the import,
   leaving only T11's deferred solution-class copy?
3. The lane instruction names the data-defined trajectory `galileanMeanT`,
   while the reconciliation prose and proof-dependency text sometimes call
   the same formula `prescribedMeanT`. The spec follows the lane instruction;
   should registration retain an alias for the older draft name?
