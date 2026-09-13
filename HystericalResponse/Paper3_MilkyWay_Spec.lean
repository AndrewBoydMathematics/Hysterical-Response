/-
TeX: `3_milky_way_fit/paper_3_milky_way_response_model.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Axisymmetric radial response     → Paper3.AxisymmetricRadial
2. Normalization and the Solar circle → Paper3.BTFRNormalization
3. Analytic vertical geometry (+ algebraic ρ_eff) → Paper3.VerticalGeometry

Observational Gaia radial/vertical fits, MOND/RAR numerical comparisons, and
baryonic mass-model tables are physics / numerical inputs — not imported here
as theorems. See `.cursor/rules/lean-tex-alignment.mdc` and `paper-series-standard.mdc`.
-/

import HystericalResponse.Paper3.AxisymmetricRadial
import HystericalResponse.Paper3.BTFRNormalization
import HystericalResponse.Paper3.VerticalGeometry
