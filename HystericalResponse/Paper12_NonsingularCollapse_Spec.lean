/-
TeX: `12_nonsingular_gravitational_collapse/paper_12_nonsingular_collapse.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Inherited HRT + horizon wake                         → Paper12.WakeDynamics
2. Existence of a remnant equilibrium                   → Paper12.RemnantExistence
3. Linear stability and dissipative attraction          → Paper12.RemnantStability
4. Nonsingular Gravitational Collapse Theorem           → Paper12.StableRemnant

`thm_wake`: Ass.horizon supplies uncanceled residual magnitude μ>0; outward
orientation identifies H; concludes nonzero outward wake.
`cor_nofocus` / `thm_nonsingular`: all three standard linear modes → R_*.
Prior HRT survival/instability: `literature_*` propositional tags (Paper 1).
-/

import HystericalResponse.Paper12.WakeDynamics
import HystericalResponse.Paper12.RemnantExistence
import HystericalResponse.Paper12.RemnantStability
import HystericalResponse.Paper12.StableRemnant
