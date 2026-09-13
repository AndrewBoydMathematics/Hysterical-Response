/-
TeX: `6_cosmological_constant/paper_6_late_universe.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Finite-amplitude crossing                         → Paper6.Crossing
2. Dilution / eventual criticality / w_H0            → Paper6.EventualCriticality
3. Nonlinear cosmological attractor                  → Paper6.NonlinearAttractor
4. Critical density and covariant positivity         → Paper6.CovariantAttractor
5. Slow-pole nonlinear closure                       → Paper6.SlowPoleClosure

Background Planck residuals in TeX are phenomenological numerics, not Lean theorems.
-/

import HystericalResponse.Paper6.Crossing
import HystericalResponse.Paper6.EventualCriticality
import HystericalResponse.Paper6.NonlinearAttractor
import HystericalResponse.Paper6.CovariantAttractor
import HystericalResponse.Paper6.SlowPoleClosure
