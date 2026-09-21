# B4 attempts

- Read the COMMON rules, assessment, split and B0/B1/B3 reports and target.
- Normalization correction: `Source.angular_partial_norm_sq` explicitly cancels
  `2π`; the correct B1 parameter is κ=1. B0's force cap is a norm, so its square
  bounds the physical squared force energy.
- Direct support-free route: `D01.FiniteOrderNorm.norm_raise_sq_eq`, using
  `weakDerivs_smooth`, `smoothField_weakDeriv_pairing`, and datum uniqueness.
  `sobolevEnergy_succ_smooth` compiled without any support hypothesis.
- Initial direct compilation failed because B0's .olean was not installed;
  building the dependency closure resolved this.
- Existing-file edit authorized by brief: entrypoints.json registers new modules.
  No lane 503/504/506 source has been edited.
