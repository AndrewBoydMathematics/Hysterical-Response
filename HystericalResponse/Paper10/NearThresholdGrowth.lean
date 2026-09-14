import Mathlib
import HystericalResponse.Paper10.LinearEMSpectrum

/-!
TeX: `10_cyclic_cosmology/paper_10_hysterical_ccc.tex`,
Section “Near-threshold growth”.

TeX Prop.~onset is explicitly the *frozen-denominator algebraic form* of the
near-threshold dispersion. Lean ports that algebraic claim faithfully (not the
Taylor expansion derivation of the formula itself).
-/

set_option autoImplicit false

namespace Paper10

noncomputable section

/-- Leading near-threshold growth rate (frozen-denominator approximation of TeX). -/
def lambdaNear (H gamma epsilon q : ℝ) : ℝ :=
  (gamma / (2 * H * (2 * H + gamma))) * (4 * H ^ 2 * epsilon - q ^ 2)

/-- TeX: prop:onset — unstable precisely on the infrared band q² < 4 H² ε. -/
theorem prop_onset {H gamma epsilon q : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) :
    0 < lambdaNear H gamma epsilon q ↔ q ^ 2 < 4 * H ^ 2 * epsilon := by
  unfold lambdaNear
  have hpre : 0 < gamma / (2 * H * (2 * H + gamma)) := by positivity
  constructor
  · intro h
    have hΔ : 0 < 4 * H ^ 2 * epsilon - q ^ 2 :=
      pos_of_mul_pos_right h (le_of_lt hpre)
    linarith
  · intro h
    exact mul_pos hpre (sub_pos.mpr h)

/-- Maximal growth among real q occurs at q = 0. -/
theorem prop_onset_max_at_zero {H gamma epsilon q : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) (_hε : 0 ≤ epsilon) :
    lambdaNear H gamma epsilon q ≤ lambdaNear H gamma epsilon 0 := by
  unfold lambdaNear
  have hpre : 0 ≤ gamma / (2 * H * (2 * H + gamma)) := by positivity
  have hΔ : 4 * H ^ 2 * epsilon - q ^ 2 ≤ 4 * H ^ 2 * epsilon - (0 : ℝ) ^ 2 := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    nlinarith [sq_nonneg q]
  exact mul_le_mul_of_nonneg_left hΔ hpre

/-- Strict maximum at q = 0 when ε > 0 and q ≠ 0. -/
theorem prop_onset_strict_max {H gamma epsilon q : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) (_hε : 0 < epsilon) (hq : q ≠ 0) :
    lambdaNear H gamma epsilon q < lambdaNear H gamma epsilon 0 := by
  unfold lambdaNear
  have hpre : 0 < gamma / (2 * H * (2 * H + gamma)) := by positivity
  have hΔ : 4 * H ^ 2 * epsilon - q ^ 2 < 4 * H ^ 2 * epsilon - (0 : ℝ) ^ 2 := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    nlinarith [sq_pos_of_ne_zero hq]
  exact mul_lt_mul_of_pos_left hΔ hpre

end

end Paper10
