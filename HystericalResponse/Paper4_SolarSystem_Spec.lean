/-
TeX: `4_solar_system/paper_4_solar_system_null_test.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Subcritical point-source response → Paper4.PointSourceResponse
2. Secular perihelion signature     → Paper4.PerihelionSignature

Observational Saturn/Cassini translations, enclosed-mass consistency scales, and
illustrative numerical benchmarks are physics / observational inputs — not imported
here as theorems. See `.cursor/rules/lean-tex-alignment.mdc` and
`paper-series-standard.mdc`.
-/

import HystericalResponse.Paper4.PointSourceResponse
import HystericalResponse.Paper4.PerihelionSignature
