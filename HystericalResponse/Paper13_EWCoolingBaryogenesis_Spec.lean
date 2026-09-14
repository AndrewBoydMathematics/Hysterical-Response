/-
TeX: `13_ew_cooling_baryogenesis/paper_13_ew_cooling_baryogenesis.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Inherited electroweak residual (Debye model)
     → Paper13.InheritedResidual
2. Forced cooling criticality
     → Paper13.CoolingCriticality
3. Open-g placement (dual of cooling criticality)
     → Paper13.OpenPlacement
4. Full Higgs-band restabilization witness
     → Paper13.HiggsRestabilization
5. Condensate-coupled activity / analytic overlap
     → Paper13.ActivityWindow
6. Concurrency ⇒ branch asymmetry
     → Paper13.CoolingAsymmetry
7. Radiation-era time estimate (literature GeV plug-in only here)
     → Paper13.RadiationTime

Coefficients (α_X, α_Y, g) fixing which T_♦ occurs, and the observed |η_B|,
are physical inputs — not imported here as theorems.
Lattice GeV edges are literature hypotheses used only in RadiationTime.
-/

import HystericalResponse.Paper13.InheritedResidual
import HystericalResponse.Paper13.CoolingCriticality
import HystericalResponse.Paper13.OpenPlacement
import HystericalResponse.Paper13.HiggsRestabilization
import HystericalResponse.Paper13.ActivityWindow
import HystericalResponse.Paper13.CoolingAsymmetry
import HystericalResponse.Paper13.RadiationTime
