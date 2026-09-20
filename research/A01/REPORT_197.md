# Lane 197 — second review fix

The canonical cylinder-to-Fourier bridge is proved. `hprojected_of_cylinder''`
derives the projected-datum equality without Helmholtz, physical-agreement, or
independent residual-datum hypotheses. The positive consumer probe imports the
landed `InteriorMomentum` module and closes
`interior_momentum_identity_of_complement_paths`, supplying both its projector
identity and its physical residual agreement internally.

## Base and scope

Rebased onto `origin/erenup/integration` at `2536a9d`, after fetching. The rebase
dropped the lane-194 merge and skipped its already-landed content commit.
Conflicts in `A3_SPLIT.md` retained integration's version. The net diff contains
only `Section4/A01/LerayBridge.lean` and this lane's research records/probes;
there are no deletions or lane-194 files relative to integration. No pre-existing
module was edited. The former lane-local `LerayBridgeTime.lean` is removed from
the patch: its helpers are now imported from landed `InteriorMomentum`.

## Proof and supplier account

Lane 194's `residualCarrier` fixes the full unprojected ordinary residual,
`residualCarrier_paths` supplies all-order paths, and `residualCarrier_physical`
and `residualDatum_physicalSlice` identify the physical residual including the
prescribed force. The earlier report's missing-supplier claim was incorrect.

The cylinder Leray projection has solenoidal range and its complement has
cylinder-gradient range. Second derivative words preserve solenoidality, so the
viscous Laplacian is included in `cylinderResidual_solenoidal`. The unprojected
and projected residuals have the same Laplacian; restriction compatibility of
advection leaves precisely the gradient projection of the source.

The elaboration is split into `value_residual_linear` (linear evaluation before
large terms are substituted), `unprojectedResidual_value` (Laplacian/advection
value transport), and `residual_difference_gradient` (cancellation and gradient
membership). Typed intermediate identities and `congrArg₂` avoid rewriting the
expanded residual path. The latter two declarations each have a commented local
`maxHeartbeats 400000` limit; other declarations pass at Lean's default limit.

`ordinaryLift_unprojectedResidual` and `ordinaryResidual_helmholtz` descend the
memberships using angular invariance. The datum-level lemmas use smooth
representatives, cylinder weak curl, and the order-zero Fourier results.
`hprojected_of_canonical_pairs` uses lane 194's order-seven pair and compares any
consumer order through the same joint time derivative. Datum uniqueness covers
`q = 6` without requiring an additional cross-order agreement assumption.

## Export and landed consumer

The export prefix is the fix6 `PressureSupply` prefix at `cca4af7`:
`hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3`.
`A02.SpaceTimeField` is qualified to avoid namespace ambiguity. The all-order
`hpairs` has lane 194's family shape. There is no redundant selected-order
`u/hU/hdiv/hduh` block: the export selects `Classical.choose (hpairs q hq)` and
obtains its properties from `Classical.choose_spec`. The remaining inputs are
`m`, `hm`, `hm2`, `B`, `R`, `hB`, and `hR`, with `hR` using that selected pair.
The initial divergence and velocity representative binders remain interface
inputs; the projected-datum conclusion concerns the fixed carrier `U`.

`probes/leray_bridge_195.lean` uses the same prefix and calls the landed
`interior_momentum_identity_of_complement_paths` directly. It builds the
canonical complement-path conjunction from lane 194's paths and datum identity,
proves physical agreement using `residualCarrier_physical`, and identifies the
adapter's chosen datum with `residualDatum` by uniqueness. It then applies the
new export. No consumer theorem is copied, and neither `hprojected` nor
`hresidualAgreement` is a caller input. The smooth complement field and its
slice agreement are the outputs of lane 194's
`exists_complement_joint_representative`.

## Verification

Module build, direct module elaboration, the axiom audit, all four probes, and
`make check` pass. Every explicit heartbeat limit is locally scoped at 400000.
The heartbeat probe replays the refactored membership proof body. The sign probe
uses `fail_if_success` to require rejection of the original wrong-sign rewrite,
then proves the correct identity; the file now exits successfully as a negative
test. The zero-carrier checks remain nonvacuous. All audited declarations and
the landed consumer composition use exactly the three standard axioms.

The second review is retained unchanged as the rejection record. See
`ATTEMPTS_LERAY_BRIDGE.md` for commands and results. No push was performed.
