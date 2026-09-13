import NSFormalization.Paper1.PeriodicH2Embedding
open NSFormalization.Paper1 NavierStokes.ProblemStatement
set_option pp.all true in
#check fun (k : PeriodicFrequency) => ‖(fun i => (k i : ℝ))‖
set_option pp.all true in
#check (fun i => (0:ℝ))
#check EuclideanSpace.equiv
#check EuclideanSpace.basisFun
#check PiLp.toLp
#check WithLp.toLp
