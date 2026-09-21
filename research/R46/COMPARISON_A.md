# Proposition 4.6 — Draft A comparison

This draft was prepared only from the permitted manuscript passages and the
registered V1 vocabulary. It does not consult another R46/Renergy/RMain draft.

## Paper clause to Lean field

| Paper clause | Lean field | Encoding |
|---|---|---|
| `04-whole-space.tex:218-219`: fix `a ∈ 𝒳_ℝ` and `ν,T>0`; compact-smooth forces with `T^ν_max,ℝ(a,f) ≤ T` are dense in every `L^q(0,∞;H^s)` for `q∈{1,2}`, `s<s_q` | `REnergyAPI.completedSobolevDensity` | The outer binders are `a`, membership, `ν`, positivity, `T`, positivity, then `q`, membership in `{1,2}`, then `s<s_q`. The dense subset is `breakdownSetIn forceClassCompact ν a T`; the ambient completion and approximation relation are `CompletedDense q s`, hence `IsSobolevPath s`. |
| `04-whole-space.tex:219`: the same compact-smooth singular forces are dense in `L²(0,∞;Ḣ⁻¹)` | `REnergyAPI.completedHomogeneousDensity` | Uses `CompletedDenseHomogeneous 2 (-1)` on the same `breakdownSetIn forceClassCompact ν a T`. Its realization is `IsHomogeneousPath (-1)`, matching `02-preliminaries.tex:57-73`. |
| `04-whole-space.tex:221-223`: for every Theorem 4.2 reference, arrange `‖uε-v‖_{E_T}→0` | `REnergyAPI.strongTrajectoryClosure`, first conjunct of `StrongTrajectoryClosure` | A single existential `InsertionFamilyAPI` is quantified after the registered Theorem 4.2 reference binders. The norm is `energyENorm A.T (A.velocityDifference ε)` and the limit is along `ε→0+`. |
| `04-whole-space.tex:224-226`: simultaneously arrange convergence of the sum of the `L¹_tL²_x`, `L²_tH⁻¹_x`, and `L²_tḢ⁻¹_x` force-difference norms | Same field, second conjunct of `StrongTrajectoryClosure` | The literal ENNReal-valued sum uses `forceSobolevENorm 1 0`, `forceSobolevENorm 2 (-1)`, and `forceHomogeneousENorm 2 (-1)` on the same `A.forceDifference ε`, with one `Tendsto` to zero. |
| `04-whole-space.tex:228`: only the compact difference is measured homogeneously | Definition of `StrongTrajectoryClosure` | `forceHomogeneousENorm` receives `A.forceDifference ε = gε-g`; it is never applied to `A.g`. |

## Representation choices

The completed Bochner space is represented by the registered path model:
`b : ℝ → RealVectorSobolev s` with `MemBochnerDatum q s b`. This carries strong
measurability and finite norm. `CompletedDenseVia` measures the approximating
datum path against `b`; its norm is insensitive to a.e. changes, so it presents
the same completed `Lp` object without adding a second local quotient type.

The two completion clauses deliberately use different physical realizations:

- `CompletedDense` uses `IsSobolevPath s`, corresponding to
  `h ↦ ⟨ξ⟩^s ĥ`.
- `CompletedDenseHomogeneous` uses `IsHomogeneousPath (-1)`, corresponding to
  `h ↦ |ξ|⁻¹ ĥ` in `02-preliminaries.tex:57-73`.

The common datum carrier and `bochnerDatumENorm` do not identify these physical
realizations; the `path` argument of `CompletedDenseVia` is what distinguishes
them.

The threshold `s_q` is `criticalOrder q.toReal = 2/q-3/2`. The time exponent is
the registered `ℝ≥0∞` exponent, constrained by `q = 1 ∨ q = 2` before the order
is quantified.

“Strong closure of trajectories” is rendered as a one-sided filter limit in
the registered extended energy norm. “Simultaneously” is structural: one
existential family `A` must satisfy both the energy limit and the single summed
force limit. It is not three independently chosen approximation families.

## Local definition needing registration

`StrongTrajectoryClosure` is the only local definition. It is a concrete
conjunction of the two displayed limits, not a placeholder proposition. All
other notions—force classes, maximal lifespan, completed density, both path
realizations, norms, and the insertion family—come from registered contracts.

## Ambiguities and decisions

1. The phrase “for every reference in Theorem 4.2” does not repeat those
   binders at `04-whole-space.tex:221`. Draft A copies the exact binder order of
   the registered `insertionFamilyStatement`: `ν`, packet, scaling record,
   datum, classical reference, then the velocity and pressure identifications.
   It does not invent a second reference type.
2. The proposition has fixed `a,ν,T` in its density paragraph, while its second
   paragraph points back to the full reference quantification of Theorem 4.2.
   Accordingly the density fields expose the fixed outer binders, whereas the
   closure field follows the registered Theorem 4.2 reference interface, whose
   scaling record already carries its positive `T` and whose packet carries
   positive `ν`.
3. `InsertionFamilyAPI` is the registered family interface and deliberately
   omits Theorem 4.2's maximal-lifespan equality. Proposition 4.6 does not
   restate that equality in lines 221-228, so Draft A does not add it to the
   closure field. The density fields independently use the genuine registered
   `maximalLifespanR` through `breakdownSetIn`.
4. The manuscript writes convergence of a sum of three force norms. Draft A
   states that exact summed limit rather than three separate limits. This both
   preserves the displayed assertion and enforces use of the same family.
5. The local closure predicate does not require the background force to possess
   a homogeneous path. This is intentional and required by line 228.
