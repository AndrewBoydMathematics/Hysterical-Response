/-
TeX: `15_btfr_zero_point/paper_15_btfr_zero_point.tex`

Umbrella imports follow TeX section order — this file *is* the module map:

1. IR memory acceleration          → Paper15.MemoryScale
2. Zero-point matching / main thm  → Paper15.ZeroPoint

Named theorems use TeX labels (`thm_…`) where ported.
Literature hypotheses and physical inputs are tagged axioms.
See `.cursor/rules/lean-tex-alignment.mdc` and `paper-series-standard.mdc`.
-/

import HystericalResponse.Paper15.MemoryScale
import HystericalResponse.Paper15.ZeroPoint
