import Mathlib

/-!
TeX: `5_early_galactic_formation/paper_5_early_universe.tex`,
Sections “Cosmological response closure” and
“Frozen Jacobian and inherited instability”.

Ports the frozen characteristic polynomial, Lemma [Supercritical offset],
and the positive-root step of Proposition [Cosmological instance].
The master instability / threshold-time package is inherited from Paper 1
and is not re-proved here.
-/

set_option autoImplicit false

namespace Paper5

noncomputable section

/-- TeX Eq. poly: frozen characteristic polynomial with coupling `C = βσ`. -/
def charPoly (H A gamma C lam : ℝ) : ℝ :=
  (lam + gamma) * (lam ^ 2 + 2 * H * lam - A) - A * C

/-- Coupling product `C = β σ`. -/
def coupling (beta sigma : ℝ) : ℝ :=
  beta * sigma

theorem charPoly_zero (H A gamma C : ℝ) :
    charPoly H A gamma C 0 = -A * gamma - A * C := by
  unfold charPoly
  ring

/--
TeX: lem:P0 — Supercritical offset.
-/
theorem lem_P0
    {H A gamma beta sigma : ℝ}
    (_hH : 0 ≤ H) (hA : 0 < A) (hgamma : 0 ≤ gamma)
    (hbeta : 0 < beta) (hsigma : 0 < sigma) :
    charPoly H A gamma (coupling beta sigma) 0 < 0 := by
  rw [charPoly_zero]
  have hC : 0 < coupling beta sigma := mul_pos hbeta hsigma
  nlinarith

/-- Explicit positive bracket used for the monic-cubic IVT step. -/
def instabilityBracket (A C : ℝ) : ℝ :=
  1 + A + A * C

theorem instabilityBracket_pos {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    0 < instabilityBracket A C := by
  unfold instabilityBracket
  nlinarith

theorem continuous_charPoly (H A gamma C : ℝ) :
    Continuous (charPoly H A gamma C) := by
  unfold charPoly
  continuity

theorem charPoly_bracket_pos
    {H A gamma C : ℝ}
    (hH : 0 ≤ H) (hA : 0 < A) (hgamma : 0 ≤ gamma) (hC : 0 < C) :
    0 < charPoly H A gamma C (instabilityBracket A C) := by
  let L : ℝ := 1 + A + A * C
  have hLdef : instabilityBracket A C = L := rfl
  rw [hLdef]
  have hLpos : 0 < L := by dsimp [L]; nlinarith
  have hLA : 1 + A ≤ L := by dsimp [L]; nlinarith [hC]
  have hL2Age1 : 1 ≤ L ^ 2 - A := by
    have hsq : (1 + A) ^ 2 ≤ L ^ 2 :=
      sq_le_sq' (by nlinarith [hLpos]) hLA
    nlinarith
  have hlower :
      L * (L ^ 2 - A) ≤ (L + gamma) * (L ^ 2 + 2 * H * L - A) := by
    have h1 : L ≤ L + gamma := by nlinarith [hgamma]
    have h2 : L ^ 2 - A ≤ L ^ 2 + 2 * H * L - A := by nlinarith [hH, hLpos]
    exact mul_le_mul h1 h2 (by nlinarith [hL2Age1]) (by nlinarith [hLpos])
  have hbig : A * C < L * (L ^ 2 - A) := by
    have hLge : A * C < L := by dsimp [L]; nlinarith [hA]
    have : L ≤ L * (L ^ 2 - A) := by nlinarith [hLpos, hL2Age1]
    exact lt_of_lt_of_le hLge this
  unfold charPoly
  have : A * C < (L + gamma) * (L ^ 2 + 2 * H * L - A) :=
    lt_of_lt_of_le hbig hlower
  linarith

/-- IVT: negative at `a`, positive at `b > a` yields a root in `(a,b]`. -/
theorem exists_root_of_neg_pos
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : Continuous f)
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c, a < c ∧ c ≤ b ∧ f c = 0 := by
  have hI : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt hfa, le_of_lt hfb⟩
  have himg : (0 : ℝ) ∈ f '' Set.Icc a b :=
    intermediate_value_Icc (le_of_lt hab) hf.continuousOn hI
  rcases himg with ⟨c, hc, hfc⟩
  have hc' : a ≤ c ∧ c ≤ b := by
    simpa [Set.mem_Icc] using hc
  have hne : c ≠ a := by
    intro h
    rw [h] at hfc
    linarith [hfa, show f a = 0 from hfc]
  exact ⟨c, lt_of_le_of_ne hc'.1 (Ne.symm hne), hc'.2, hfc⟩

/--
TeX: prop:instance — positive-root step only.
Reduced abstraction: establishes `∃ λ > 0, P(λ)=0` (hence `α(J)>0`);
the inherited master theorem / threshold corollary are cited in TeX, not ported.
-/
theorem prop_instance_positive_root
    {H A gamma beta sigma : ℝ}
    (hH : 0 ≤ H) (hA : 0 < A) (hgamma : 0 ≤ gamma)
    (hbeta : 0 < beta) (hsigma : 0 < sigma) :
    ∃ lam, 0 < lam ∧ charPoly H A gamma (coupling beta sigma) lam = 0 := by
  set C := coupling beta sigma
  have hC : 0 < C := mul_pos hbeta hsigma
  have hLpos : 0 < instabilityBracket A C := instabilityBracket_pos hA hC
  have hneg := lem_P0 hH hA hgamma hbeta hsigma
  have hpos := charPoly_bracket_pos hH hA hgamma hC
  obtain ⟨lam, h0, _, hP⟩ :=
    exists_root_of_neg_pos hLpos (continuous_charPoly H A gamma C) hneg hpos
  exact ⟨lam, h0, hP⟩

end

end Paper5
