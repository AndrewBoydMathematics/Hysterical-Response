import Mathlib

/-!
TeX: `11_hawking_radiation/paper_11_horizon_hysterical_response.tex`,
Section “Tolman exterior temperature”.

`thm_tolman`: algebraic redshift identity for r > 2M.
Tolman's equilibrium law is a literature hypothesis.
-/

set_option autoImplicit false

namespace Paper11

noncomputable section

/-- TeX: lit:tolman — Tolman equilibrium law (literature). -/
axiom literature_tolman_law : True

/-- Redshift factor √(1 - 2M/r) for exterior static observers. -/
def redshiftFactor (M r : ℝ) : ℝ :=
  Real.sqrt (1 - 2 * M / r)

/-- TeX: thm:tolman — local temperature from asymptotic T_H. -/
theorem thm_tolman {T_H T_loc M r : ℝ}
    (hfac : redshiftFactor M r ≠ 0)
    (htol : T_loc * redshiftFactor M r = T_H) :
    T_loc = T_H / redshiftFactor M r :=
  (eq_div_iff hfac).2 htol

/-- Domain witness: for M > 0 and r > 2M one has 1 - 2M/r > 0. -/
theorem exterior_redshift_pos {M r : ℝ}
    (hM : 0 < M) (hr : 2 * M < r) :
    0 < 1 - 2 * M / r := by
  have hr0 : 0 < r := lt_trans (mul_pos (by norm_num : (0:ℝ) < 2) hM) hr
  have hdiv : 2 * M / r < 1 := (div_lt_one hr0).2 hr
  linarith

/-- Interior: r < 2M makes 1 - 2M/r negative (no static Tolman factor). -/
theorem interior_redshift_neg {M r : ℝ}
    (_hM : 0 < M) (hr : 0 < r) (hin : r < 2 * M) :
    1 - 2 * M / r < 0 := by
  have hdiv : 1 < 2 * M / r := (one_lt_div hr).2 hin
  linarith

end

end Paper11
