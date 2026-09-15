# eq:Rhigh — blind writer B

Lane `130-SPEC-A04-rhigh-blind`, writer **B** (independent of writer A). Target:
the display `eq:Rhigh` in `paper/sections/appendix-a-local-theory.tex:132-137`,

```
½ d/dt ‖u‖²_{H^m} + ν ‖∇u‖²_{H^m}
    ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m} + ‖f‖_{H^m} ‖u‖_{H^m}.
```

Deliverable: `research/A04/blind/rhigh_B.lean`, the single `def eqRhigh_B : Prop`.

## Paper lines used

| lines | what I took |
|---|---|
| `appendix-a-local-theory.tex:127-137` | the display and its paragraph; "For every integer `m ≥ 3`, pairing the equation with `u` in `H^m`, integrating by parts, and using `eq:Rproduct` gives" `eq:Rhigh`; "The pressure term vanishes by solenoidality"; "justified by Fourier approximation on compact intervals of smooth existence" |
| `appendix-a-local-theory.tex:71-76` | `u ∈ C^1_tH^k` for all `k` ("repeated time differentiation gives `C^j_tH^k_x`") — the paper's justification for differentiating `‖u‖²_{H^m}` in time |
| `appendix-a-local-theory.tex:118-120` | the `L²` uniqueness identity `½(‖z‖₂²)' + ν‖∇z‖₂² ≤ …` — same `½(·)' + ν‖∇·‖²` shape as `eq:Rhigh`, orients the LHS |
| `02-preliminaries.tex:12,17` | `X_R = H^∞ ∩ L²_σ` (`eq:Rinitial`), `F_R` (`eq:Rclasses`) — the datum and force classes |
| `02-preliminaries.tex:29` | classical velocity in `C([0,S];H^m)` for every `m` — finiteness of every spatial `H^m` norm, hence `.toReal` faithful |
| `02-preliminaries.tex:105-120` | `prop:local`, the maximal smooth solution on `[0,S)` and the `H²` continuation criterion `eq:criterion` that `eq:Rhigh` feeds |
| `02-preliminaries.tex:138-139` | `lem:packetenergy`'s `L²` energy identity `½(‖U‖₂²)' + ν‖∇U‖₂² = ⟨F,U⟩`, the order-0 template of `eq:Rhigh` |
| `01-introduction.tex:81-114` | norm conventions: `‖z‖²_{H^s(R³)} = ∫(1+|ξ|²)^s|ẑ|²`; "for vectors and tensors we sum the squared component norms"; `H^0 = L²` |
| `01-introduction.tex:118-152` | `eq:time-norms`, `eq:Enorm`, "velocity norms before blowup use `(0,T)`" — for the interior-time reading |

Contract vocabulary (allowed): `Data.lean` — `SpatialField`, `SpaceTimeField`,
`sobolevENorm`, `ClassicalSolutionR`, `initialClassR`, `MemForceR`;
`TameProduct.lean:192` — `gradientSobolevENorm` (`= ‖∇v‖_{H^s}`).

## Modelling decisions and the alternative rejected

1. **Real-valued via `ENNReal.toReal`.** All contract norms are `ℝ≥0∞`; `eq:Rhigh`
   is a real inequality with a real `d/dt`. Each factor is `.toReal` of the
   contract norm. `⊤ ↦ 0` caveat stated; harmless here because every slice of a
   `ClassicalSolutionR` velocity and of `f ∈ F_R` has finite `H^m` (and gradient
   `H^m`) norm. *Rejected:* an `ℝ≥0∞` inequality — it cannot express the time
   derivative on the LHS.

2. **`½ d/dt ‖u‖²_{H^m}` = `½ · deriv (hmNormSq m u) t`, gated by an explicit
   `DifferentiableAt` antecedent.** `hmNormSq m u t := (sobolevENorm m (slice u t)).toReal ^ 2`.
   Because `deriv` is `0` on non-differentiable functions (which would make the
   bound vacuous), differentiability at the interior `t` is an explicit
   hypothesis `DifferentiableAt ℝ (hmNormSq m w.velocity) t`. This is the exact
   time-regularity the display needs; the frozen `ClassicalSolutionR` only
   carries a *continuous* `H^m` datum path (`.sobolev`), so it is not free and is
   surfaced as a hypothesis. *Rejected #1:* `∃ d, HasDerivAt g d t ∧ …` (folds
   differentiability into the conclusion; valid and slightly stronger, but the
   task wants the regularity explicit). *Rejected #2:* differentiating the
   Hilbert-space datum path `G : ℝ → RealVectorSobolev m` and using `‖G t‖²` —
   forces the norm through `‖G t‖`, only an upper bound for `sobolevENorm` until
   datum uniqueness (D01 L1) is proved, so it would not be the canonical norm.

3. **`‖∇u‖_{H^m}` = `gradientSobolevENorm` (gradient's Sobolev norm), not
   `‖u‖_{H^{m+1}}`.** The paper writes `‖∇u‖_{H^m}` literally; the contract has
   exactly this at `TameProduct.lean:192`. *Rejected:* `‖u‖_{H^{m+1}}` — equivalent
   but unequal, and `TameProduct.lean` lists the order shift `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}`
   as out of scope, i.e. a separate fact, so substituting it changes the theorem.

4. **`C_m` = one positive family `C : ℕ → ℝ`, `∃` outermost.** Descends from
   `eq:Rproduct`'s `C_m`, depending only on `m`/dimension, never on `ν,a,f,T,w`.
   `∃ C, (∀ m, 0 < C m) ∧ ∀ …` at the outside makes that explicit and matches
   `TameProductAPI.C`/`C_pos`. *Rejected:* an inner `∃ C > 0` under the `∀`s
   (constant re-chosen per solution/order) — strictly weaker, misrepresents `C_m`.

5. **Range `m ≥ 3`** (`:129` "For every integer `m ≥ 3`"). *Rejected:* `m ≥ 2`
   (that is `eq:Rproduct`'s range, not `eq:Rhigh`'s; the paragraph uses the
   `k ≥ 3` clauses `eq:tame`/`eq:algebra`).

6. **Time set `Set.Ioo 0 T` (interior).** Identity holds on compact intervals of
   smooth existence and uses the momentum equation, imposed by the contract only
   on `Ioo 0 T` (`ClassicalSolutionR.momentum`). *Rejected:* `Ico 0 T` — the
   two-sided `½(·)'` and the equation are not available at `t = 0`.

7. **`‖f‖_{H^m}` is the spatial `H^m` norm of the slice `f(t,·)` at the fixed
   `t`**, not a Bochner time norm — `eq:Rhigh` is a pointwise-in-time ODE
   inequality. Modelled by `sobolevENorm m (slice f t)`.

8. **Hypotheses carried:** `ν > 0`, `a ∈ initialClassR`, `MemForceR f`,
   `w : ClassicalSolutionR ν a f T`, exactly the objects the display quantifies.

## Ambiguities in the paper

* `‖·‖_{H^m}` inside `eq:Rhigh` is not re-defined at the display; it is the
  fixed-time spatial `H^m(R³)` norm of `01-introduction.tex:81`. `‖f‖_{H^m}` is
  read as the force slice's spatial norm, not a `L^q_tH^m_x` time norm, since the
  whole line is pointwise in `t`.
* The precise analytic hypothesis licensing `d/dt ‖u‖²_{H^m}` is deferred to
  "Fourier approximation on compact intervals of smooth existence" and the
  `C^1_tH^m` claim; I encode only its display-level consequence (differentiability
  of the scalar `t ↦ ‖u(t)‖²_{H^m}`) as an antecedent.
* Whether `eq:Rhigh`'s `C_m` is literally `eq:Rproduct`'s `C_m` is not asserted;
  I take a positive family, provenance-agnostic, which is all the display needs.

## Commands and results

```
. scripts/lean-env.sh
cd verification && lake env lean ../research/A04/blind/rhigh_B.lean
# output: `BlowupDensity.Research.A04.RhighB.eqRhigh_B : Prop`  (the #check), exit 0
```

Compiles silently apart from the `#check`. No `sorry`, no `axiom`.
