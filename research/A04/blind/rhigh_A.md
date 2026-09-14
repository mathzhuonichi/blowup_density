# Blind statement A — `eq:Rhigh` (high-order energy inequality)

Lane 130-SPEC-A04-rhigh-blind, blind writer **A**. Independent transcription of
the display `eq:Rhigh` from the paper alone plus the frozen contract vocabulary
(`Contracts/V1/Data.lean`, `Contracts/V1/TameProduct.lean`). Deliverable Lean
file: `research/A04/blind/rhigh_A.lean`, single statement `BlindRhighA.eqRhigh_A`.

## 1. Paper lines used

- `paper/sections/appendix-a-local-theory.tex:127-140`, the paragraph "The
  stated continuation criterion", inside the proof of `prop:local`.
  - `:129` — "For every integer `m ≥ 3`, pairing the equation with `u` in `H^m`,
    integrating by parts, and using `eq:Rproduct` gives" — fixes the **order
    range `m ≥ 3`** (integer).
  - `:132-137` — the display **`eq:Rhigh`** itself:
    `½ d/dt‖u‖²_{H^m} + ν‖∇u‖²_{H^m} ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}`.
  - `:138` — "The pressure term vanishes by solenoidality." (Why no pressure
    term appears; provided by `ClassicalSolutionR.divergence`.)
  - `:139` — "These identities are justified by Fourier approximation on compact
    intervals of smooth existence." (Source of the time-regularity that lets one
    write `d/dt‖u‖²_{H^m}`.)
  - `:134` — the token `‖∇u‖_{H^m}`, and the contract `gradientSobolevENorm`
    docstring (`TameProduct.lean:189-193`) cites exactly this line for its meaning.
- `paper/sections/02-preliminaries.tex`:
  - `:12` eq:Rinitial — `X_R = H^∞(R³;R³) ∩ L²_σ(R³)`, the initial class
    (`Data.initialClassR`).
  - `:17-21` eq:Rclasses — `F_R`, the force class (`Data.MemForceR`).
  - `:29` — "a classical velocity belongs to `C([0,S];H^m)` for every integer
    `m ≥ 0` on each compact interval of its lifespan" (why the velocity slices
    have finite `H^m` norms; carried by `ClassicalSolutionR.sobolev`).
  - `:105-115` prop:local — the classical-solution existence statement realized
    by `Data.ClassicalSolutionR`.
- `paper/sections/01-introduction.tex:80-103` — the `H^s(R³)` norm
  `‖z‖²_{H^s} = ∫(1+|ξ|²)^s|ẑ|²` (angular unitary transform, `:91`) and, `:103`,
  "For vectors and tensors we sum the squared component norms" (why the vector
  `H^m` norm and the nine-entry gradient-tensor norm are the right carriers).

## 2. Objects taken from the frozen contracts (no re-definition)

- `Data.SpatialField`, `Data.SpaceTimeField` — field types (time first).
- `Data.sobolevENorm (s : ℝ) : SpatialField → ℝ≥0∞` — `‖·‖_{H^s(R³)}` for a real
  vector slice. Used at `s = m` (order `m`) and `s = 2` (the `‖u‖_{H²}` factor).
- `Data.initialClassR`, `Data.MemForceR`, `Data.ClassicalSolutionR` — the
  hypothesis classes exactly as the task prescribes.
- `TameProduct.gradientSobolevENorm (s : ℝ) : SpatialField → ℝ≥0∞` — `‖∇v‖_{H^s}`
  (the object at `appendix-a-local-theory.tex:134`).

## 3. Auxiliary definitions I added (with the vocabulary the contracts do NOT provide)

The two contract files supply only `ℝ≥0∞`-valued spatial norms. `eq:Rhigh` is an
inequality between *real* numbers involving a *real time-derivative*, so I had to
build real-valued norms-at-a-time and the squared-norm time-path. All four are
thin wrappers on the frozen norms:

- `hmNorm m u t := (Data.sobolevENorm (m:ℝ) (fun x => u (t,x))).toReal` — real
  `‖u(t)‖_{H^m}`.
- `h2Norm u t := (Data.sobolevENorm (2:ℝ) (fun x => u (t,x))).toReal` — real
  `‖u(t)‖_{H²}`.
- `gradHmNorm m u t := (TameProduct.gradientSobolevENorm (m:ℝ) (fun x => u (t,x))).toReal`
  — real `‖∇u(t)‖_{H^m}`.
- `hmNormSq m u t := (hmNorm m u t)^2` — the real time-path `t ↦ ‖u(t)‖²_{H^m}`
  that is differentiated on the LHS.

## 4. Modelling decisions, and the alternative rejected in each case

1. **Time derivative — `deriv` under an explicit differentiability hypothesis.**
   Chosen: hypothesis `DifferentiableAt ℝ (hmNormSq m w.velocity) t`, then use
   `deriv (hmNormSq m w.velocity) t` in the inequality.
   - *Why:* `d/dt‖u‖²_{H^m}` presupposes the path is differentiable at `t`; the
     paper justifies this from smooth existence (`:139`). Under the hypothesis,
     `deriv` returns the genuine derivative (no junk value), so the LHS is exactly
     the paper's `½ d/dt‖u‖²_{H^m}`.
   - *Rejected A:* bare `deriv` with **no** hypothesis. `deriv` totalizes to `0`
     off the differentiability set, which would make the inequality assert a bound
     on a fictitious `0` derivative — unfaithful where the path is not
     differentiable.
   - *Rejected B:* bundle existence into the conclusion,
     `∃ d, HasDerivAt (hmNormSq …) d t ∧ [bound with d]`. Faithful too, and it also
     *asserts* the derivative exists. I preferred the hypothesis form because the
     task asked to "add whatever time-regularity hypothesis … needs, stated
     explicitly", i.e. put the regularity in the hypotheses rather than claim it as
     output. (This is the one place the two forms genuinely differ; flagged for the
     comparer.)

2. **Time-regularity hypothesis — differentiability of the squared `H^m` norm,
   pointwise at the interior `t`.** Chosen:
   `DifferentiableAt ℝ (hmNormSq m w.velocity) t`.
   - *Why:* it is the exact minimum needed to write the LHS at `t`. The frozen
     `ClassicalSolutionR` only guarantees *continuity* of the order-`m` datum path
     (`sobolev` field) and joint spacetime smoothness (`velocity_smooth`), neither
     of which is literally "the real function `t ↦ ‖u(t)‖²_{H^m}` is differentiable
     at `t`", so I state it rather than pretend it is free.
   - *Rejected:* a stronger `DifferentiableOn`/`C¹`-into-`H^m` hypothesis on the
     whole `(0,T)`. Unnecessary for a pointwise conclusion; the pointwise form is
     the weakest faithful choice.

3. **Real-valued norms via `.toReal`, with the `⊤ ↦ 0` caveat stated.** Chosen:
   every norm is `ENNReal.toReal` of the frozen `ℝ≥0∞` norm.
   - *Why:* forced — the inequality lives in `ℝ` (a signed derivative appears).
   - *Caveat:* `ENNReal.toReal ⊤ = 0`. Harmless on the quantified class: the
     `ClassicalSolutionR` velocity is in `C([0,S];H^m)` for every `m`
     (`02-preliminaries.tex:29`, field `sobolev`); its gradient is a partial
     derivative of a smooth field, also in every `H^m`; and `f ∈ F_R` has a genuine
     order-`m` datum at every `t ≥ 0` (`Data.MemForceR`). So no slice here is `⊤`
     and `.toReal` is faithful. Documented in each definition's docstring.

4. **`‖∇u‖_{H^m}` = gradient-tensor Sobolev norm, NOT `‖u‖_{H^{m+1}}`.** Chosen:
   `TameProduct.gradientSobolevENorm`.
   - *Why:* the frozen contract already contains this object and its docstring ties
     it to `appendix-a-local-theory.tex:134` — the display line of `eq:Rhigh` — as
     `(∑_j ‖∂_j u‖²_{H^m})^{1/2}` (nine-entry Frobenius). Using the project's own
     word for the paper's symbol is the faithful choice.
   - *Rejected:* `sobolevENorm (m+1) u` (the order-shift `‖∇u‖_{H^m} ≃ ‖u‖_{H^{m+1}}`).
     Only *equivalent up to constants*, not equal; and `TameProduct.lean:51-53`
     lists the order shift as explicitly out of scope, confirming the contract does
     not identify the two. Both the dissipation term `ν‖∇u‖²_{H^m}` and the RHS
     factor `‖∇u‖_{H^m}` use this same gradient-tensor norm at order `m`.

5. **Constant — one positive family `C : ℕ → ℝ`, quantified outside everything.**
   Chosen: `∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ ν a f T w m …`.
   - *Why:* the paper's `C_m` depends only on the order `m` and the fixed domain
     `R³` (`appendix-a-local-theory.tex:10`), never on `ν`, the data, or the
     solution. Quantifying `C` outside `ν, a, f, T, w` and `m` (as a family) is the
     strongest faithful reading and matches `TameProduct.C`. `C_m` is
     `ν`-independent because it comes from the `ν`-free `eq:Rproduct`.
   - *Rejected:* `∀ m, ∃ C > 0, …` (constant chosen after `m`). Equivalent in
     strength once `C` is a function of `m`, but the family form makes
     `m`-uniformity explicit and mirrors the sibling A03 contract.

6. **Time set — the open interval `Ioo (0,T)` (interior times).** Chosen:
   `t ∈ Ioo (0:ℝ) T`.
   - *Why:* the momentum equation in `ClassicalSolutionR` holds precisely on
     `Ioo 0 T` (interior), a two-sided `d/dt` is meaningful only at interior
     points, and the task says "every interior time". `T` is the solution horizon
     (`ClassicalSolutionR … T`, `[0,T)`).
   - *Rejected:* `Ico 0 T` (include `t = 0`). The endpoint would force a one-sided
     derivative and the paper's identity is an interior statement.

7. **`u = w.velocity`; `f` is the momentum-equation force; full `f`, not `ℙf`.**
   The bound's last term uses `‖f‖_{H^m}` (`:136`), the unprojected force. The
   pairing `⟨ℙf, u⟩_{H^m} = ⟨f, u⟩_{H^m}` because `u` is divergence-free, so
   `‖f‖_{H^m}‖u‖_{H^m}` is what is displayed. Used `sobolevENorm` of `f`'s slice.

## 5. Ambiguities in the paper

- **Differentiability of `t ↦ ‖u(t)‖²_{H^m}`** is asserted implicitly by writing
  `d/dt` and justified only in prose ("Fourier approximation on compact intervals
  of smooth existence", `:139`); no explicit regularity statement is displayed.
  Resolved by making it an explicit hypothesis (decision 2).
- **`‖∇u‖_{H^m}`** is notation the paper never expands. The gradient-vs-order-shift
  ambiguity (decision 4) is resolved by the frozen contract's own object.
- **`C_m` vs `C`** — the paper writes `C_m`, `C_k`, `C` with overlapping meaning
  across `lem:calculus`; here only the order dependence matters, taken as a family.
- **Endpoint / interior** — the paper does not spell out the time set of
  `eq:Rhigh`; the surrounding `prop:local` structure and "interior time" fix
  `Ioo 0 T` (decision 6).

## 6. Commands run and results

```
$ . scripts/lean-env.sh && cd verification \
    && LEAN_NUM_THREADS=6 lake build Contracts.V1.Data Contracts.V1.TameProduct
Build completed successfully (8817 jobs).

$ . scripts/lean-env.sh && cd verification \
    && lake env lean ../research/A04/blind/rhigh_A.lean
BlindRhighA.eqRhigh_A : Prop        # the only output (from #check); exit 0

$ grep -nE 'sorry|admit|native_decide|axiom' research/A04/blind/rhigh_A.lean
NO forbidden tokens
```

The file compiles silently except for the `#check eqRhigh_A` line, which prints
`BlindRhighA.eqRhigh_A : Prop`. No `sorry`, `admit`, `axiom`, `native_decide`, and
no placeholder `Prop` field.
