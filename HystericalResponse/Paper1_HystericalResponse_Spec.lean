/-
TeX: `1_hysterical_response/paper_1_hysterical_response.tex` (unified Paper 1)

Umbrella imports follow TeX section order — this file *is* the module map:

1. Setup + constructive core     → Paper1_ResponseTheory_Spec
2. Basis covariance              → BasisCovariance
3. Unentangled incoming / Everett toy → UnentangledIncoming
4. Constructive response (rest)  → ConstructiveResponse
5. Neutrality + survival         → Paper1_1_TypicalBranchNeutrality_Spec
                                   Paper1_1_GravitationalSurvival_Spec
6. Critical instability          → Paper1_2_NeutralityInstability_Spec_v2
7. Infrared equivalence          → Paper1_3_InfraredEquivalence_Spec

Named theorems use TeX labels (`thm_…`, `lem_…`, `cor_…`, `prop_…`) where ported.
See `.cursor/rules/lean-tex-alignment.mdc`.
-/

import HystericalResponse.Paper1.Paper1_ResponseTheory_Spec
import HystericalResponse.Paper1.BasisCovariance
import HystericalResponse.Paper1.UnentangledIncoming
import HystericalResponse.Paper1.ConstructiveResponse
import HystericalResponse.Paper1.Paper1_1_TypicalBranchNeutrality_Spec
import HystericalResponse.Paper1.Paper1_1_GravitationalSurvival_Spec
import HystericalResponse.Paper1.Paper1_2_NeutralityInstability_Spec_v2
import HystericalResponse.Paper1.Paper1_3_InfraredEquivalence_Spec
