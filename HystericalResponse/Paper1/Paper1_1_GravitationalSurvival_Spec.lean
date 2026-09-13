import Mathlib

/-!
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Section: **Hysterical neutrality and gravitational survival**
(`cor:gravity-survival`, finite-system inequalities).

Route: branchwise neutrality + weight bound → nongravitational vanishing;
positive weights + monopole lower bound → gravitational survival *permission*
(not a macroscopic amplitude derivation).
-/

open scoped BigOperators

namespace Paper1_1

variable {α : Type*} [DecidableEq α]

/-- Finite coarse-grained Hysterical response in one interaction channel. -/
def HResponse (s : Finset α) (w f : α → ℝ) : ℝ :=
  ∑ i ∈ s, w i * f i

/-- Branchwise neutrality plus bounded total response weight forces a finite
Hysterical response to be small. -/
theorem neutral_response_bound
    (s : Finset α) (w f : α → ℝ) (W ε : ℝ)
    (hW : 0 ≤ W) (hε : 0 ≤ ε)
    (hweight : ∑ i ∈ s, |w i| ≤ W)
    (hneutral : ∀ i ∈ s, |f i| ≤ ε) :
    |HResponse s w f| ≤ W * ε := by
  unfold HResponse
  calc
    |∑ i ∈ s, w i * f i|
        ≤ ∑ i ∈ s, |w i * f i| := by
            simpa using Finset.abs_sum_le_sum_abs (s := s) (f := fun i => w i * f i)
    _ = ∑ i ∈ s, |w i| * |f i| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul]
    _ ≤ ∑ i ∈ s, |w i| * ε := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hneutral i hi) (abs_nonneg (w i))
    _ = (∑ i ∈ s, |w i|) * ε := by
          rw [Finset.sum_mul]
    _ ≤ W * ε := by
          exact mul_le_mul_of_nonneg_right hweight hε

/-- Quantitative epsilon form: if branch neutrality is at most δ/W, then the
Hysterical response is at most δ. This is the finite-N core of the N->∞ limit. -/
theorem neutral_response_epsilon
    (s : Finset α) (w f : α → ℝ) (W δ : ℝ)
    (hW : 0 < W) (hδ : 0 ≤ δ)
    (hweight : ∑ i ∈ s, |w i| ≤ W)
    (hneutral : ∀ i ∈ s, |f i| ≤ δ / W) :
    |HResponse s w f| ≤ δ := by
  have hbound := neutral_response_bound s w f W (δ / W)
      (le_of_lt hW) (div_nonneg hδ (le_of_lt hW)) hweight hneutral
  have hWne : W ≠ 0 := ne_of_gt hW
  calc
    |HResponse s w f| ≤ W * (δ / W) := hbound
    _ = δ := by field_simp

/-- Positive branch weights and a positive branchwise gravitational monopole
force a positive Hysterical gravitational response *under these hypotheses*.
This is an algebraic lower bound, not a derivation of macroscopic galactic amplitude. -/
theorem positive_gravity_bound
    (s : Finset α) (w g : α → ℝ) (w0 g0 : ℝ)
    (hw0 : 0 < w0) (hg0 : 0 < g0)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hg_lower : ∀ i ∈ s, g0 ≤ g i)
    (hweight_lower : w0 ≤ ∑ i ∈ s, w i) :
    w0 * g0 ≤ HResponse s w g := by
  unfold HResponse
  calc
    w0 * g0 ≤ (∑ i ∈ s, w i) * g0 := by
      exact mul_le_mul_of_nonneg_right hweight_lower (le_of_lt hg0)
    _ = ∑ i ∈ s, w i * g0 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ i ∈ s, w i * g i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hg_lower i hi) (hw_nonneg i hi)

/-- Hence, under the same hypotheses, the gravitational Hysterical response is
strictly positive. Relative to the Neutrality Theorem this is a *permission*
witness: vanishing is not forced when a positive channel is present. -/
theorem positive_gravity_survives
    (s : Finset α) (w g : α → ℝ) (w0 g0 : ℝ)
    (hw0 : 0 < w0) (hg0 : 0 < g0)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hg_lower : ∀ i ∈ s, g0 ≤ g i)
    (hweight_lower : w0 ≤ ∑ i ∈ s, w i) :
    0 < HResponse s w g := by
  have hbound := positive_gravity_bound s w g w0 g0 hw0 hg0
      hw_nonneg hg_lower hweight_lower
  have hprod : 0 < w0 * g0 := mul_pos hw0 hg0
  exact lt_of_lt_of_le hprod hbound

/-- Abstract channel-selection corollary: one neutral channel is uniformly small
while a positive gravitational channel is bounded away from zero. -/
theorem channel_separation
    (s : Finset α)
    (w f g : α → ℝ)
    (W ε w0 g0 : ℝ)
    (hW : 0 ≤ W) (hε : 0 ≤ ε)
    (hw0 : 0 < w0) (hg0 : 0 < g0)
    (hweight_abs : ∑ i ∈ s, |w i| ≤ W)
    (hneutral : ∀ i ∈ s, |f i| ≤ ε)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hg_lower : ∀ i ∈ s, g0 ≤ g i)
    (hweight_lower : w0 ≤ ∑ i ∈ s, w i) :
    |HResponse s w f| ≤ W * ε ∧ w0 * g0 ≤ HResponse s w g := by
  constructor
  · exact neutral_response_bound s w f W ε hW hε hweight_abs hneutral
  · exact positive_gravity_bound s w g w0 g0 hw0 hg0
      hw_nonneg hg_lower hweight_lower

/-- TeX: cor:gravity-survival — permission under positive channel hypotheses. -/
theorem cor_gravity_survival
    (s : Finset α) (w g : α → ℝ) (w0 g0 : ℝ)
    (hw0 : 0 < w0) (hg0 : 0 < g0)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hg_lower : ∀ i ∈ s, g0 ≤ g i)
    (hweight_lower : w0 ≤ ∑ i ∈ s, w i) :
    0 < HResponse s w g :=
  positive_gravity_survives s w g w0 g0 hw0 hg0 hw_nonneg hg_lower hweight_lower

/-- TeX: cor:gravity-failure — same permission stated from failure of neutrality. -/
theorem cor_gravity_failure
    (s : Finset α) (w g : α → ℝ) (w0 g0 : ℝ)
    (hw0 : 0 < w0) (hg0 : 0 < g0)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hg_lower : ∀ i ∈ s, g0 ≤ g i)
    (hweight_lower : w0 ≤ ∑ i ∈ s, w i) :
    0 < HResponse s w g :=
  cor_gravity_survival s w g w0 g0 hw0 hg0 hw_nonneg hg_lower hweight_lower

end Paper1_1
