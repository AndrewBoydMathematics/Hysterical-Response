/-
TeX: `11_hawking_radiation/paper_11_horizon_hysterical_response.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. Horizon regularity → T_H                         → Paper11.HorizonTemperature
2. Detailed balance → Hawking occupation             → Paper11.HawkingOccupation
3. Tolman exterior temperature                       → Paper11.TolmanTemperature
4. Backreaction / evaporation feedback               → Paper11.Evaporation

Interpretive Section “Why Hawking and Tolman touched HRT” is not Lean.
Membrane embedding, Euclidean period, FDR, and Tolman's law are `literature_*`.
Geometry-free KMS from a Hysterical action alone is not claimed.
-/

import HystericalResponse.Paper11.HorizonTemperature
import HystericalResponse.Paper11.HawkingOccupation
import HystericalResponse.Paper11.TolmanTemperature
import HystericalResponse.Paper11.Evaporation
