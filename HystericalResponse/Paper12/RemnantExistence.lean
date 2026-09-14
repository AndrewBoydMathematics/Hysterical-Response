import Mathlib
import HystericalResponse.Paper12.WakeDynamics

/-!
TeX: `12_nonsingular_gravitational_collapse/paper_12_nonsingular_collapse.tex`,
Section “Existence of a remnant equilibrium”.
-/

set_option autoImplicit false

namespace Paper12

noncomputable section

/-- TeX: lem:ivt — intermediate-value zero on a compact interval. -/
theorem lem_ivt {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (ha : 0 < f a) (hb : f b < 0) :
    ∃ c, c ∈ Set.Ioo a b ∧ f c = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f b) (f a) := ⟨le_of_lt hb, le_of_lt ha⟩
  have himg := intermediate_value_Icc' hab hf
  have hex : ∃ c ∈ Set.Icc a b, f c = 0 := by
    have : 0 ∈ f '' Set.Icc a b := himg hmem
    obtain ⟨c, hc, hfc⟩ := this
    exact ⟨c, hc, hfc⟩
  obtain ⟨c, hc, hfc⟩ := hex
  refine ⟨c, ⟨?_, ?_⟩, hfc⟩
  · exact lt_of_le_of_ne hc.1 (by
      intro h
      subst h
      exact absurd hfc (ne_of_gt ha))
  · exact lt_of_le_of_ne hc.2 (by
      intro h
      have : c = b := h
      subst this
      exact absurd hfc (ne_of_lt hb))

/-- TeX: thm:existence — finite-radius remnant with F(R_*) = 0. -/
theorem thm_existence (W : WakeHypotheses) :
    ∃ Rstar, W.R_in < Rstar ∧ Rstar < W.R_out ∧
      netForce W.G Rstar = 0 ∧ 0 < Rstar := by
  have hab : W.R_in ≤ W.R_out := le_of_lt W.hOrd
  obtain ⟨Rstar, hIoo, hF⟩ :=
    lem_ivt hab (continuousOn_netForce_interval W) W.hPos W.hNeg
  refine ⟨Rstar, hIoo.1, hIoo.2, hF, lt_trans W.hIn hIoo.1⟩

/-- Steady-state reading: balance H(R_*) = GM/R_*^2. -/
theorem thm_existence_balance (W : WakeHypotheses) :
    ∃ Rstar, 0 < Rstar ∧ W.G.H Rstar = W.G.GM / Rstar ^ 2 := by
  obtain ⟨Rstar, _, _, hF, hpos⟩ := thm_existence W
  refine ⟨Rstar, hpos, ?_⟩
  simpa [netForce, sub_eq_zero] using hF

end

end Paper12
