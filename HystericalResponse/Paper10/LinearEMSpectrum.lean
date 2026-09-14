import Mathlib

/-!
TeX: `10_cyclic_cosmology/paper_10_hysterical_ccc.tex`,
Section “Linear infrared electromagnetic instability”.

Faithful ports:
* Jacobian `J` and `det(λI − J)` → characteristic polynomial (helicity cancels)
* zero-mode threshold, IR-first criticality (strict), infrared band + positive root via IVT

Compiler certification: `lake build HystericalResponse.Paper10_HystericalCCC_Spec`.
-/

set_option autoImplicit false

open Matrix

namespace Paper10

noncomputable section

/-- Helical EM–response Jacobian of TeX~(eq:J), ordered `(E, B, h)`. -/
def jacobian (H alpha sigma gamma q s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-2 * H, s * q, alpha;
     -s * q, -2 * H, 0;
     sigma, 0, -gamma]

/-- Explicit matrix `λI − J` (TeX expansion target). -/
def charMatrix (H alpha sigma gamma q s lambda : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![lambda + 2 * H, -(s * q), -alpha;
     s * q, lambda + 2 * H, 0;
     -sigma, 0, lambda + gamma]

/-- Closed-form characteristic polynomial of TeX~(eq:char), with `A = α σ`. -/
def charPoly (H gamma A q lambda : ℝ) : ℝ :=
  (lambda + gamma) * ((lambda + 2 * H)^2 + q^2) - A * (lambda + 2 * H)

theorem charMatrix_eq_sub
    (H alpha sigma gamma q s lambda : ℝ) :
    charMatrix H alpha sigma gamma q s lambda =
      lambda • (1 : Matrix (Fin 3) (Fin 3) ℝ) - jacobian H alpha sigma gamma q s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [charMatrix, jacobian, Matrix.sub_apply, Matrix.smul_apply]

/-- Expanded monic cubic form (used for `λ → +∞`). -/
theorem charPoly_expand (H gamma A q lambda : ℝ) :
    charPoly H gamma A q lambda =
      lambda^3
        + (4 * H + gamma) * lambda^2
        + (4 * H^2 + q^2 + 4 * H * gamma - A) * lambda
        + (gamma * (4 * H^2 + q^2) - 2 * H * A) := by
  unfold charPoly
  ring

/-- Determinant of the explicit characteristic matrix.
For general helicity the formula carries `s² q²`; TeX takes `s ∈ {±1}` so `s² = 1`. -/
theorem det_charMatrix_general
    (H alpha sigma gamma q s lambda : ℝ) :
    (charMatrix H alpha sigma gamma q s lambda).det =
      (lambda + gamma) * ((lambda + 2 * H)^2 + s^2 * q^2)
        - (alpha * sigma) * (lambda + 2 * H) := by
  simp [charMatrix, det_fin_three]
  ring

/-- TeX: prop:char — with helicity `s² = 1`, `det(λI − J) = charPoly`. -/
theorem prop_char
    (H alpha sigma gamma q s lambda : ℝ) (hs : s^2 = 1) :
    (lambda • (1 : Matrix (Fin 3) (Fin 3) ℝ) - jacobian H alpha sigma gamma q s).det =
      charPoly H gamma (alpha * sigma) q lambda := by
  rw [← charMatrix_eq_sub, det_charMatrix_general, hs]
  unfold charPoly
  ring

/-- Convenience: both physical helicities. -/
theorem prop_char_pos (H alpha sigma gamma q lambda : ℝ) :
    (lambda • (1 : Matrix (Fin 3) (Fin 3) ℝ) - jacobian H alpha sigma gamma q 1).det =
      charPoly H gamma (alpha * sigma) q lambda :=
  prop_char H alpha sigma gamma q 1 lambda (by norm_num)

theorem prop_char_neg (H alpha sigma gamma q lambda : ℝ) :
    (lambda • (1 : Matrix (Fin 3) (Fin 3) ℝ) - jacobian H alpha sigma gamma q (-1)).det =
      charPoly H gamma (alpha * sigma) q lambda :=
  prop_char H alpha sigma gamma q (-1) lambda (by norm_num)

/-- Helicity cancels in the spectrum for `s = ±1`. -/
theorem prop_char_helicity_indep (H alpha sigma gamma q lambda : ℝ) :
    (lambda • (1 : Matrix (Fin 3) (Fin 3) ℝ) - jacobian H alpha sigma gamma q (1 : ℝ)).det =
      (lambda • (1 : Matrix (Fin 3) (Fin 3) ℝ) - jacobian H alpha sigma gamma q (-1 : ℝ)).det := by
  rw [prop_char_pos, prop_char_neg]

/-- TeX: prop:char — evaluation at λ = 0. -/
theorem prop_char_at_zero (H gamma A q : ℝ) :
    charPoly H gamma A q 0 = gamma * (4 * H^2 + q^2) - 2 * H * A := by
  unfold charPoly
  ring

/-- TeX: thm:zero-mode. -/
theorem thm_zero_mode {H gamma A : ℝ} (hH : H ≠ 0) :
    charPoly H gamma A 0 0 = 0 ↔ A = 2 * H * gamma := by
  rw [prop_char_at_zero]
  constructor
  · intro h
    apply mul_left_cancel₀ hH
    nlinarith
  · intro h
    rw [h]
    ring

/-- Stationary critical relaxation rate. -/
def gammaCrit (H A x : ℝ) : ℝ := 2 * H * A / (4 * H^2 + x)

theorem gammaCrit_zero (H A : ℝ) (hH : H ≠ 0) :
    gammaCrit H A 0 = A / (2 * H) := by
  unfold gammaCrit
  field_simp [hH]
  ring

theorem gammaCrit_antitone {H A x y : ℝ}
    (hH : 0 < H) (hA : 0 < A) (hx : 0 ≤ x) (hxy : x ≤ y) :
    gammaCrit H A y ≤ gammaCrit H A x := by
  unfold gammaCrit
  have hdx : 0 < 4 * H^2 + x := by nlinarith
  have hdy : 0 < 4 * H^2 + y := by nlinarith
  have hnum : 0 ≤ 2 * H * A := by positivity
  rw [div_le_div_iff₀ hdy hdx]
  exact mul_le_mul_of_nonneg_left (by nlinarith) hnum

theorem gammaCrit_strict_antitone {H A x y : ℝ}
    (hH : 0 < H) (hA : 0 < A) (hx : 0 ≤ x) (hxy : x < y) :
    gammaCrit H A y < gammaCrit H A x := by
  unfold gammaCrit
  have hdx : 0 < 4 * H^2 + x := by nlinarith
  have hdy : 0 < 4 * H^2 + y := by nlinarith
  have hnum : 0 < 2 * H * A := by positivity
  rw [div_lt_div_iff₀ hdy hdx]
  nlinarith

/-- TeX: thm:IR-first — γ_c maximised at q = 0. -/
theorem thm_IR_first {H A q : ℝ}
    (hH : 0 < H) (hA : 0 < A) :
    gammaCrit H A (q^2) ≤ gammaCrit H A 0 :=
  gammaCrit_antitone hH hA (by norm_num) (sq_nonneg q)

theorem thm_IR_first_eq_iff {H A q : ℝ}
    (hH : 0 < H) (hA : 0 < A) :
    gammaCrit H A (q^2) = gammaCrit H A 0 ↔ q = 0 := by
  constructor
  · intro h
    by_contra hq
    have hsq : 0 < q^2 := sq_pos_of_ne_zero hq
    have hlt : gammaCrit H A (q^2) < gammaCrit H A 0 :=
      gammaCrit_strict_antitone hH hA (by norm_num) hsq
    exact (ne_of_lt hlt) h
  · intro hq
    simp [hq]

/-- Stationary electromagnetic gain in the squared-momentum variable. -/
def gainEM_sq (H gamma A x : ℝ) : ℝ :=
  A / (gamma * (2 * H + x / (2 * H)))

theorem gainEM_sq_antitone {H gamma A x y : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) (hA : 0 < A) (hx : 0 ≤ x) (hxy : x ≤ y) :
    gainEM_sq H gamma A y ≤ gainEM_sq H gamma A x := by
  unfold gainEM_sq
  have hxden : 0 < 2 * H + x / (2 * H) := by
    have : 0 ≤ x / (2 * H) := div_nonneg hx (by positivity)
    nlinarith
  have hyden : 0 < 2 * H + y / (2 * H) := by
    have : 0 ≤ y / (2 * H) := div_nonneg (le_trans hx hxy) (by positivity)
    nlinarith
  have hdenx : 0 < gamma * (2 * H + x / (2 * H)) := mul_pos hg hxden
  have hdeny : 0 < gamma * (2 * H + y / (2 * H)) := mul_pos hg hyden
  have hden_le :
      gamma * (2 * H + x / (2 * H)) ≤ gamma * (2 * H + y / (2 * H)) := by
    have : x / (2 * H) ≤ y / (2 * H) :=
      div_le_div_of_nonneg_right hxy (by positivity)
    nlinarith
  rw [div_le_div_iff₀ hdeny hdenx]
  exact mul_le_mul_of_nonneg_left hden_le (le_of_lt hA)

theorem gainEM_sq_strict_antitone {H gamma A x y : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) (hA : 0 < A) (hx : 0 ≤ x) (hxy : x < y) :
    gainEM_sq H gamma A y < gainEM_sq H gamma A x := by
  unfold gainEM_sq
  have hxden : 0 < 2 * H + x / (2 * H) := by
    have : 0 ≤ x / (2 * H) := div_nonneg hx (by positivity)
    nlinarith
  have hyden : 0 < 2 * H + y / (2 * H) := by
    have : 0 ≤ y / (2 * H) :=
      div_nonneg (le_of_lt (lt_of_le_of_lt hx hxy)) (by positivity)
    nlinarith
  have hdenx : 0 < gamma * (2 * H + x / (2 * H)) := mul_pos hg hxden
  have hdeny : 0 < gamma * (2 * H + y / (2 * H)) := mul_pos hg hyden
  have hden_lt :
      gamma * (2 * H + x / (2 * H)) < gamma * (2 * H + y / (2 * H)) := by
    have : x / (2 * H) < y / (2 * H) :=
      (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * H) (by positivity)).2
        (by nlinarith)
    nlinarith
  rw [div_lt_div_iff₀ hdeny hdenx]
  nlinarith

/-- Packaged TeX: thm:IR-first. -/
theorem thm_IR_first_full {H gamma A q : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) (hA : 0 < A) :
    gainEM_sq H gamma A (q^2) ≤ gainEM_sq H gamma A 0 ∧
      gammaCrit H A (q^2) ≤ gammaCrit H A 0 ∧
      gammaCrit H A 0 = A / (2 * H) :=
  ⟨gainEM_sq_antitone hH hg hA (by norm_num) (sq_nonneg q),
    thm_IR_first hH hA,
    gammaCrit_zero H A (ne_of_gt hH)⟩

/-- TeX: thm:band — sign test. -/
theorem thm_band {H gamma A q : ℝ}
    (_hH : 0 < H) (hg : 0 < gamma) :
    charPoly H gamma A q 0 < 0 ↔
      q^2 < 2 * H * A / gamma - 4 * H^2 := by
  rw [prop_char_at_zero]
  constructor <;> intro h
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hg]
    nlinarith
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hg] at h
    nlinarith

theorem thm_band_nonempty {H gamma A : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) (hsup : 2 * H * gamma < A) :
    0 < 2 * H * A / gamma - 4 * H^2 := by
  have heq : 2 * H * A / gamma - 4 * H^2 = 2 * H * (A / gamma - 2 * H) := by ring
  rw [heq]
  have hpos : 0 < A / gamma - 2 * H := by
    have : 2 * H < A / gamma := (lt_div_iff₀ hg).2 (by nlinarith)
    linarith
  exact mul_pos (by positivity) hpos

theorem continuous_charPoly (H gamma A q : ℝ) :
    Continuous fun lambda : ℝ => charPoly H gamma A q lambda := by
  unfold charPoly
  continuity

/-- Monic cubic is eventually positive. -/
theorem charPoly_pos_of_large (H gamma A q : ℝ) :
    ∃ Bound : ℝ, ∀ lam, Bound ≤ lam → 0 < charPoly H gamma A q lam := by
  set b : ℝ := 4 * H + gamma
  set c : ℝ := 4 * H ^ 2 + q ^ 2 + 4 * H * gamma - A
  set d : ℝ := gamma * (4 * H ^ 2 + q ^ 2) - 2 * H * A
  refine ⟨1 + abs b + abs c + abs d, ?_⟩
  intro lam hlam
  have h1 : (1 : ℝ) ≤ lam := by
    have : (1 : ℝ) ≤ 1 + abs b + abs c + abs d := by
      nlinarith [abs_nonneg b, abs_nonneg c, abs_nonneg d]
    exact le_trans this hlam
  have hlower :
      lam ^ 3 - abs b * lam ^ 2 - abs c * lam - abs d ≤ charPoly H gamma A q lam := by
    rw [charPoly_expand]
    nlinarith [neg_le_abs b, neg_le_abs c, neg_le_abs d, abs_nonneg b, abs_nonneg c, abs_nonneg d,
      sq_nonneg lam]
  have hpos0 : 0 < lam ^ 3 - abs b * lam ^ 2 - abs c * lam - abs d := by
    have hlampos : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one h1
    have hlam2 : (0 : ℝ) < lam ^ 2 := sq_pos_of_pos hlampos
    have hgap : abs b + abs c + abs d < lam := by nlinarith [abs_nonneg b, abs_nonneg c, abs_nonneg d]
    have hc' : abs c * lam ≤ abs c * lam ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg c)
    have hd' : abs d ≤ abs d * lam ^ 2 := by
      nlinarith [abs_nonneg d, sq_nonneg (lam - 1), h1]
    have hge :
        lam ^ 2 * (lam - (abs b + abs c + abs d)) ≤
          lam ^ 3 - abs b * lam ^ 2 - abs c * lam - abs d := by
      nlinarith [abs_nonneg b, hc', hd']
    have hfac : 0 < lam - (abs b + abs c + abs d) := sub_pos.mpr hgap
    exact lt_of_lt_of_le (mul_pos hlam2 hfac) hge
  exact lt_of_lt_of_le hpos0 hlower

/-- TeX: thm:band — `p_q(0) < 0` ⇒ positive real root (IVT). -/
theorem thm_band_positive_root {H gamma A q : ℝ}
    (hp0 : charPoly H gamma A q 0 < 0) :
    ∃ lam : ℝ, 0 < lam ∧ charPoly H gamma A q lam = 0 := by
  rcases charPoly_pos_of_large H gamma A q with ⟨Bound, hBound⟩
  let lam0 : ℝ := max Bound 1
  have hpos : 0 < charPoly H gamma A q lam0 := hBound lam0 (le_max_left _ _)
  have h0le : (0 : ℝ) ≤ lam0 := le_trans zero_le_one (le_max_right _ _)
  have hcont :
      ContinuousOn (fun lam => charPoly H gamma A q lam) (Set.Icc 0 lam0) :=
    (continuous_charPoly H gamma A q).continuousOn
  have hIcc : (0 : ℝ) ∈ Set.Icc (charPoly H gamma A q 0) (charPoly H gamma A q lam0) :=
    ⟨le_of_lt hp0, le_of_lt hpos⟩
  rcases intermediate_value_Icc h0le hcont hIcc with ⟨lam, hmem, hroot⟩
  have hge : 0 ≤ lam := hmem.1
  have hne : lam ≠ 0 := by
    intro hz
    subst hz
    have : charPoly H gamma A q 0 = 0 := by simpa using hroot
    exact (ne_of_lt hp0) this
  exact ⟨lam, lt_of_le_of_ne hge hne.symm, by simpa using hroot⟩

/-- Full TeX: thm:band package. -/
theorem thm_band_full {H gamma A q : ℝ}
    (hH : 0 < H) (hg : 0 < gamma) (hsup : 2 * H * gamma < A)
    (hq : q^2 < 2 * H * A / gamma - 4 * H^2) :
    charPoly H gamma A q 0 < 0 ∧
      0 < 2 * H * A / gamma - 4 * H^2 ∧
      ∃ lambda : ℝ, 0 < lambda ∧ charPoly H gamma A q lambda = 0 := by
  have hp0 : charPoly H gamma A q 0 < 0 := (thm_band hH hg).2 hq
  exact ⟨hp0, thm_band_nonempty hH hg hsup, thm_band_positive_root hp0⟩

end

end Paper10
