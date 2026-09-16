# Lane 197-A01-leray-bridge — the projector bridge `hprojected`: the cylinder projected residual, lowered to order 0, is the Fourier Leray projection of the physical residual's datum

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/197-A01-leray-bridge` (git branch `erenup/197-A01-leray-bridge`, based on `origin/erenup/integration`).
This lane supplies the single named input `hprojected` of lane 195's `interior_momentum_identity` (branch `erenup/195-A01-interior-momentum`,
`git show erenup/195-A01-interior-momentum:formalization/NSFormalization/Section4/A01/InteriorMomentum.lean | sed -n 195,245p` — copy the binders
`hq hm hm2 hν hS u₀ fc uc U hU hduh hpaths … B R hB hR … A hres` and the exact statement
`hprojected : ∀ (t : ℝ) (ht : t ∈ Ioo 0 S), lowerVectorL (m:ℝ) 0 _ (R ⟨t,…⟩) = A ⟨t,…⟩ - Leray.lerayComplement 0 (A ⟨t,…⟩)`
where `hR τ : IsSobolevDatum m (ordinaryResidualPath hq hm ν fc uc τ) (R τ)` (lane 169's ordinary projected residual path at order `m`) and
`hres τ : IsSobolevDatum 0 (fun x => momentumResidualOfVelocity ν f (jointRepresentative U hpaths) (τ, x)) (A τ)` (order-0 datum of the physical
residual of lane 190's joint representative)). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7/P9, `NEXT_SESSION.md` (entries "压力腿重设计",
"A01 管线现状"), `Section4/A01/DatumPathDeriv.lean` (169: `cylinderResidualPath`, `ordinaryResidualPath`, `ordinaryResidualPath_eq_ordinaryDerivative`,
`ordinaryLift_ordinaryResidualPath`, `projectedResidualPath`, `projectedResidualPath_eq`, `ordinaryLift_projectedResidualOrdinaryPath`,
`ordinaryLift_adjoint_of_invariant`), `Source/ForcedCylinderLocal.lean` (the cylinder `leray 1 q` = cylinder gradient projection; grep its definition and
its characterization: projection onto the divergence-free cylinder subspace orthogonal to gradients), `Section4/D01/LerayDatum.lean`,
`LerayLowering.lean`, `LeraySymbol.lean`, `Longitudinal.lean`, `OrderZeroCurl.lean` (datum-level `lerayComplement`: Fourier `ξ(ξ·Â)/|ξ|²`; `isSobolevDatum_lower`;
lowering commutes with the complement), `Section4/A01/ConstructorDivergence.lean` (owner's: `ordinaryLift_gradient_mem`, `solenoidal_of_ordinaryLift`,
`spatialDivergence_eq_zero_of_cylinder`), `Section4/A01/L2Descent.lean` (153: `word_descent_ae_top/full`), `Section4/A01/DatumPathContinuous.lean` (161),
`Section4/A01/JointRepresentative.lean` (190: `vectorRepresentative_ae`, `jointRepresentative_slice`), `Section4/A01/ConstructorPressure.lean:52-60`
(`momentumResidualOfVelocity`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing
  modules; new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on the zero pair.
- **Satisfiability rule:** named inputs must be restrictions of standard properties (one sentence each); nothing at `t = 0`.

## Mathematics
Two Leray projectors must be identified on the descended data: (i) the cylinder one, `leray 1 q` (orthogonal projection in the cylinder Sobolev space onto
the divergence-free subspace, i.e. removing cylinder gradients); (ii) the datum-level one on `R³`, `A ↦ A − lerayComplement 0 A` (Fourier multiplier
`I − ξξᵀ/|ξ|²`). For the residual of the cylinder solution: `ordinaryResidualPath` is the *unprojected* residual descended to the ordinary carrier and
`projectedResidualPath = ν•Δ + restrict(leray (F − advection))` (169). Route: (1) the lowered order-`m` datum of the cylinder-projected residual is the
datum of the ordinary-lifted projected residual (`ordinaryLift_projectedResidualOrdinaryPath`, `isSobolevDatum_lower`); (2) the difference
`unprojected − projected` at cylinder level is a cylinder gradient (`leray`'s defining property), whose ordinary lift is an `L²` gradient
(`ordinaryLift_gradient_mem`), hence its order-0 datum is longitudinal = fixed by `lerayComplement 0` (`Longitudinal.lean`, `OrderZeroCurl.lean`);
(3) the projected part's ordinary lift is solenoidal (`solenoidal_of_ordinaryLift`), hence its order-0 datum is killed by `lerayComplement 0`;
(4) uniqueness of the decomposition `A = (A − cA) + cA` at datum level gives `lowerVectorL m 0 R = A − lerayComplement 0 A` once `A` (the physical
residual's datum) is identified with the descended cylinder residual's datum — that identification is `hres` + the a.e. agreement of the physical
residual of the joint representative with the descended cylinder residual (`jointRepresentative_slice`, `vectorRepresentative_ae`, and the datum-level
formulas for `Δ`, advection and force: `D01/DerivativeDatum.lean`, `A04/NonlinearDatum.lean`, `A04/LaplacianDatum.lean`, `C01/JetPaths.lean`). Prove
that agreement as a separate theorem (`physicalResidual_datum_eq`) — it is what lane 194 also needs; if one identity is genuinely missing (say which),
isolate it as ONE named hypothesis with the exact statement.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/LerayBridge.lean` (namespace `NSFormalization.Section4.A01`): `physicalResidual_datum_eq`,
   the gradient/solenoidal datum lemmas, and `hprojected_of_cylinder` with the conclusion token-for-token lane 195's `hprojected` (write a probe that
   applies 195's `interior_momentum_identity` with it — copy 195's statement if the branch cannot be imported).
2. Records `research/A01/ATTEMPTS_LERAY_BRIDGE.md`, `research/A01/A3_SPLIT.md` row "P4c projector bridge", conformance `research/A01/axioms_leray_bridge.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.LerayBridge` (silent), `lake env lean` on the module (0 output), the
axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and named inputs / files / gaps with error text / commands). Also write it
to `research/A01/REPORT_197.md`.
