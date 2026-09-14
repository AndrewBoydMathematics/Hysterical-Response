/-
TeX: `13_ew_cooling_baryogenesis/paper_13_ew_cooling_baryogenesis.tex`
Section “Condensate-coupled activity and analytic overlap” —
ass:condensate, def:concurrent, thm:overlap (sharp C = (T_*, T_♦)),
cor:open-half (Td > T_* ↔ |g| large).

No independent Td > Tc hypothesis: nonempty concurrency ↔ Td > T_*.
-/

import Mathlib
import HystericalResponse.Paper13.CoolingCriticality

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Paper13

noncomputable section

/-- Physical input: freeze-out below crossover (TeX ass:condensate). -/
structure CondensateScale where
  Tc : ℝ
  Tstar : ℝ
  hTc : 0 < Tc
  hord : Tstar < Tc
  hTstar : 0 < Tstar

/-- Topology active for all T > T_* (SM input; includes the whole symmetric phase). -/
def topologicallyActive (S : CondensateScale) (T : ℝ) : Prop :=
  S.Tstar < T

/-- Concurrent set C = {T > 0 : Δ(T) < 0 ∧ T > T_*}. -/
def concurrent (αX αY g : ℝ) (S : CondensateScale) (T : ℝ) : Prop :=
  0 < T ∧ Delta αX αY g T < 0 ∧ topologicallyActive S T

/-- TeX: thm:overlap / eq:C-iff — T ∈ C ↔ T_* < T < T_♦ (for T > 0). -/
theorem thm_overlap_iff {αX αY g : ℝ} (S : CondensateScale)
    (hαX : 0 < αX) (hαY : 0 < αY) {T : ℝ} (hT : 0 < T) :
    concurrent αX αY g S T ↔ S.Tstar < T ∧ T < Tdiamond αX αY g := by
  constructor
  · intro ⟨_, hΔ, hact⟩
    refine ⟨hact, ?_⟩
    have hΔ' : αX * αY * (T ^ 4 - Tdiamond αX αY g ^ 4) < 0 := by
      rw [← Delta_Tdiamond hαX hαY]; exact hΔ
    have hα : 0 < αX * αY := mul_pos hαX hαY
    have hdiff : T ^ 4 < Tdiamond αX αY g ^ 4 := by
      have : T ^ 4 - Tdiamond αX αY g ^ 4 < 0 := by
        nlinarith
      exact sub_neg.mp this
    exact (pow_lt_pow_iff_left₀ hT.le (Tdiamond_nonneg αX αY g)
      (by norm_num : (4:ℕ) ≠ 0)).1 hdiff
  · intro ⟨hact, hhi⟩
    have hp4 : T ^ 4 < Tdiamond αX αY g ^ 4 :=
      pow_lt_pow_left₀ hhi hT.le (by norm_num : (4:ℕ) ≠ 0)
    have hΔ := thm_cooling_supercritical_pow hαX hαY hp4
    exact ⟨hT, hΔ, hact⟩

/-- TeX: eq:nonempty — C nonempty ↔ T_♦ > T_*. -/
theorem thm_overlap_nonempty_iff {αX αY g : ℝ} (S : CondensateScale)
    (hαX : 0 < αX) (hαY : 0 < αY) :
    (∃ T, concurrent αX αY g S T) ↔ S.Tstar < Tdiamond αX αY g := by
  constructor
  · intro ⟨T, hC⟩
    have hT : 0 < T := hC.1
    have hiff := (thm_overlap_iff S hαX hαY hT).mp hC
    exact lt_trans hiff.1 hiff.2
  · intro hhalf
    -- midpoint between T_* and T_♦
    let T : ℝ := (S.Tstar + Tdiamond αX αY g) / 2
    have hTpos : 0 < T := by
      have : 0 < S.Tstar + Tdiamond αX αY g :=
        add_pos S.hTstar (lt_trans S.hTstar hhalf)
      positivity
    have hlo : S.Tstar < T := by
      have h2 : (0:ℝ) < 2 := by norm_num
      rw [lt_div_iff₀ h2]; linarith
    have hhi : T < Tdiamond αX αY g := by
      have h2 : (0:ℝ) < 2 := by norm_num
      rw [div_lt_iff₀ h2]; linarith
    exact ⟨T, (thm_overlap_iff S hαX hαY hTpos).mpr ⟨hlo, hhi⟩⟩

/-- Convenience: T_♦ > T_* ⇒ nonempty C. -/
theorem thm_overlap_nonempty {αX αY g : ℝ} (S : CondensateScale)
    (hαX : 0 < αX) (hαY : 0 < αY)
    (hhalf : S.Tstar < Tdiamond αX αY g) :
    ∃ T, concurrent αX αY g S T :=
  (thm_overlap_nonempty_iff S hαX hαY).mpr hhalf

/-- TeX: cor:open-half — g > √(αX αY) T_*² ⇒ T_♦ > T_* (g > 0 case). -/
theorem cor_open_half {αX αY g Tstar : ℝ}
    (hαX : 0 < αX) (hαY : 0 < αY) (hTstar : 0 < Tstar) (hg : 0 < g)
    (hcoup : Real.sqrt (αX * αY) * Tstar ^ 2 < g) :
    Tstar < Tdiamond αX αY g := by
  have hden : 0 < αX * αY := mul_pos hαX hαY
  have hsq : (Real.sqrt (αX * αY)) ^ 2 = αX * αY :=
    Real.sq_sqrt hden.le
  have hs : 0 ≤ Real.sqrt (αX * αY) * Tstar ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have h3 : (Real.sqrt (αX * αY) * Tstar ^ 2) ^ 2 < g ^ 2 :=
    pow_lt_pow_left₀ hcoup hs (by norm_num : (2:ℕ) ≠ 0)
  have hg2 : αX * αY * Tstar ^ 4 < g ^ 2 := by
    calc
      αX * αY * Tstar ^ 4
          = (Real.sqrt (αX * αY)) ^ 2 * (Tstar ^ 2) ^ 2 := by rw [hsq]; ring
      _ = (Real.sqrt (αX * αY) * Tstar ^ 2) ^ 2 := by ring
      _ < g ^ 2 := h3
  have hTd4 : Tdiamond αX αY g ^ 4 = g ^ 2 / (αX * αY) :=
    Tdiamond_pow4 hαX hαY
  have hT4_lt : Tstar ^ 4 < Tdiamond αX αY g ^ 4 := by
    rw [hTd4]
    have hg2' : Tstar ^ 4 * (αX * αY) < g ^ 2 := by
      convert hg2 using 1; ring
    exact (lt_div_iff₀ hden).mpr hg2'
  exact (pow_lt_pow_iff_left₀ hTstar.le (Tdiamond_nonneg αX αY g)
    (by norm_num : (4:ℕ) ≠ 0)).1 hT4_lt

end

end Paper13
