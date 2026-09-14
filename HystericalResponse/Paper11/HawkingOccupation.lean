import Mathlib

/-!
TeX: `11_hawking_radiation/paper_11_horizon_hysterical_response.tex`,
Section “Detailed balance produces the Hawking factor”.

Algebraic layer of thm:hawking-occupation (lemmas + Bose factor).
KMS/FDR and membrane embedding are literature hypotheses.
-/

set_option autoImplicit false

namespace Paper11

/-- TeX: lit:membrane — membrane / open-system embedding (literature). -/
axiom literature_membrane_embedding : True

/-- TeX: lit:fdr — quantum FDR / KMS noise at β_H (literature). -/
axiom literature_quantum_fdr : True

/-- TeX: lem:occupation — detailed-balance occupation. -/
theorem lem_occupation {r pPlus pMinus : ℝ}
    (hr : r ≠ 1) (hp : pPlus ≠ 0) (hbal : pMinus = r * pPlus) :
    pMinus / (pPlus - pMinus) = r / (1 - r) := by
  rw [hbal]
  field_simp

/-- TeX: lem:bose — exponential ratio is Bose–Einstein. -/
theorem lem_bose {x : ℝ} (hx : Real.exp x ≠ 1) :
    Real.exp (-x) / (1 - Real.exp (-x)) = 1 / (Real.exp x - 1) := by
  rw [Real.exp_neg]
  field_simp

/-- TeX: thm:hawking-occupation — packaging of the Bose factor from r = e^{-βω}. -/
theorem thm_hawking_occupation {beta omega : ℝ}
    (hx : Real.exp (beta * omega) ≠ 1) :
    Real.exp (-(beta * omega)) / (1 - Real.exp (-(beta * omega))) =
      1 / (Real.exp (beta * omega) - 1) :=
  lem_bose hx

end Paper11
