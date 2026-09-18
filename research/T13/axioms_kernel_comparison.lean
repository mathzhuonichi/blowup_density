import NSFormalization.Section3.T13.KernelComparison

open NSFormalization.Section3.T13

-- Every public declaration of lane 354 must print exactly
-- `[propext, Classical.choice, Quot.sound]`.

-- §0-1 helpers
#print axioms latticeVector_norm_ge_one
#print axioms latticeTail_neg
#print axioms ball_coord_bounds
#print axioms separationRadius
#print axioms separationRadius_le
#print axioms separationRadius_pos
#print axioms closedBall_coord_sep

-- Item 1
#print axioms exists_separation

-- §2 geometry
#print axioms norm_sub_le_sqrt3
#print axioms tailGeomC0
#print axioms tailGeomC0_pos
#print axioms geom_norm_lower

-- Item 2
#print axioms tailGeomConst
#print axioms tailGeomConst_lt_top
#print axioms latticeTail_le_tailGeomConst

-- Item 3
#print axioms iTorus_singular_le

-- §4-5 helpers
#print axioms measurable_latticeTail
#print axioms measurable_prod_frac
#print axioms measurable_prod_tail
#print axioms measurable_inner_frac
#print axioms periodicKernel_split
#print axioms volume_fundamentalCube
#print axioms sq_eLpNorm_two

-- Item 4
#print axioms iTorus_periodize_le
