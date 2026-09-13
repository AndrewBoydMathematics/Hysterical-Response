import Mathlib

/-!
TeX: `4_solar_system/paper_4_solar_system_null_test.tex`,
Section “Secular perihelion signature”.

Ports Proposition [Perihelion shift of a logarithmic response] and the circular
limit corollary. The Gauss planetary reduction to the true-anomaly integrand is
tagged as a literature hypothesis; the remaining integral/algebraic reduction is
checked here.
-/

set_option autoImplicit false

namespace Paper4

noncomputable section

/-- Keplerian radial distance as a function of true anomaly. -/
def orbitalRadius (a e f : ℝ) : ℝ :=
  a * (1 - e ^ 2) / (1 + e * Real.cos f)

/--
TeX Eq. gauss (after literature Gauss reduction): periapsis true-anomaly density
`dϖ/df = (V² / (GM e)) r(f) cos f`.
-/
def periapsisDensity (V2 GM a e f : ℝ) : ℝ :=
  V2 / (GM * e) * orbitalRadius a e f * Real.cos f

/-- Eccentricity factor appearing in the closed perihelion formula. -/
def eccFactor (e : ℝ) : ℝ :=
  Real.sqrt (1 - e ^ 2) / (1 + Real.sqrt (1 - e ^ 2))

/-- TeX Eq. Delta-varpi closed form (retrograde). -/
def deltaVarpi (V2 GM a e : ℝ) : ℝ :=
  - (2 * Real.pi * V2 * a / GM) * eccFactor e

/-- Circular-limit closed form `-π V² a / GM`. -/
def deltaVarpiCircular (V2 GM a : ℝ) : ℝ :=
  - Real.pi * V2 * a / GM

/--
LITERATURE: classical definite integrals on the Keplerian ellipse for `0 < e < 1`,
\[
\int_0^{2\pi}\frac{\cos f}{1+e\cos f}\,df
=\frac{2\pi}{e}\Bigl(1-\frac{1}{\sqrt{1-e^2}}\Bigr).
\]
Used by TeX after the Gauss reduction; not re-proved here.
-/
axiom literature_kepler_cos_integral :
  ∀ (e : ℝ), 0 < e → e < 1 →
    (∫ f in (0 : ℝ)..(2 * Real.pi), Real.cos f / (1 + e * Real.cos f)) =
      (2 * Real.pi / e) * (1 - 1 / Real.sqrt (1 - e ^ 2))

/--
Algebraic identity underlying TeX Eq. Delta-varpi:
\[
\frac{1-e^2}{e^2}\Bigl(1-\frac{1}{\sqrt{1-e^2}}\Bigr)
= -\frac{\sqrt{1-e^2}}{1+\sqrt{1-e^2}}.
\]
-/
theorem ecc_factor_identity
    (e : ℝ) (he0 : 0 < e) (he1 : e < 1) :
    (1 - e ^ 2) / e ^ 2 * (1 - 1 / Real.sqrt (1 - e ^ 2)) =
      - eccFactor e := by
  have hsq : 0 < 1 - e ^ 2 := by nlinarith [mul_self_nonneg e]
  have hspos : 0 < Real.sqrt (1 - e ^ 2) := Real.sqrt_pos.mpr hsq
  have hs1 : Real.sqrt (1 - e ^ 2) ≠ 0 := ne_of_gt hspos
  have he : e ≠ 0 := ne_of_gt he0
  set s := Real.sqrt (1 - e ^ 2) with hs_eq
  have hs_def : s ^ 2 = 1 - e ^ 2 := by
    rw [hs_eq]; exact Real.sq_sqrt (le_of_lt hsq)
  have hne : (1 + s) ≠ 0 := by
    intro h; nlinarith [hspos]
  have h1s : (1 - s) ≠ 0 := by
    intro h
    have hs1' : s = 1 := by linarith
    have : e ^ 2 = 0 := by nlinarith [hs_def, hs1']
    exact (pow_ne_zero 2 he) this
  unfold eccFactor
  change (1 - e ^ 2) / e ^ 2 * (1 - 1 / s) = - (s / (1 + s))
  have hnum : 1 - 1 / s = (s - 1) / s := by field_simp [hs1]
  rw [hnum, ← hs_def]
  have : e ^ 2 = 1 - s ^ 2 := by nlinarith [hs_def]
  rw [this]
  have : 1 - s ^ 2 = (1 - s) * (1 + s) := by ring
  rw [this]
  field_simp [h1s, hne, hs1]
  ring

/-- Pointwise rewriting of the Gauss integrand into the classical angular form. -/
theorem periapsisDensity_rewrite
    (V2 GM a e f : ℝ) (he : e ≠ 0) (hGM : GM ≠ 0)
    (hden : 1 + e * Real.cos f ≠ 0) :
    periapsisDensity V2 GM a e f =
      (V2 / (GM * e) * a * (1 - e ^ 2)) *
        (Real.cos f / (1 + e * Real.cos f)) := by
  unfold periapsisDensity orbitalRadius
  field_simp [he, hGM, hden]

/-- On `0 < e < 1`, the Kepler denominator never vanishes. -/
theorem kepler_denom_ne
    (e f : ℝ) (he0 : 0 < e) (he1 : e < 1) :
    1 + e * Real.cos f ≠ 0 := by
  have hc : |Real.cos f| ≤ 1 := Real.abs_cos_le_one f
  have hbound : |e * Real.cos f| ≤ e := by
    calc
      |e * Real.cos f| = |e| * |Real.cos f| := abs_mul _ _
      _ ≤ |e| * 1 := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ = |e| := by ring
      _ = e := abs_of_pos he0
  have : 1 + e * Real.cos f ≥ 1 - e := by
    have := neg_le_of_abs_le hbound
    linarith
  linarith

/--
TeX: prop:perihelion — Perihelion shift of a logarithmic response.

Given the literature Kepler integral and the Gauss integrand, one orbit yields
`Δϖ = - (2π V² a / GM) · eccFactor e`.
-/
theorem prop_perihelion_shift
    (V2 GM a e : ℝ)
    (hGM : GM ≠ 0) (he0 : 0 < e) (he1 : e < 1) :
    (∫ f in (0 : ℝ)..(2 * Real.pi), periapsisDensity V2 GM a e f) =
      deltaVarpi V2 GM a e := by
  have he : e ≠ 0 := ne_of_gt he0
  have hcos := literature_kepler_cos_integral e he0 he1
  have hfun :
      (fun f : ℝ => periapsisDensity V2 GM a e f) =
        fun f =>
          (V2 / (GM * e) * a * (1 - e ^ 2)) *
            (Real.cos f / (1 + e * Real.cos f)) := by
    funext f
    exact periapsisDensity_rewrite V2 GM a e f he hGM (kepler_denom_ne e f he0 he1)
  rw [hfun, intervalIntegral.integral_const_mul, hcos]
  unfold deltaVarpi
  have hid := ecc_factor_identity e he0 he1
  have hrewrite :
      V2 / (GM * e) * a * (1 - e ^ 2) *
          ((2 * Real.pi / e) * (1 - 1 / Real.sqrt (1 - e ^ 2))) =
        (2 * Real.pi * V2 * a / GM) *
          ((1 - e ^ 2) / e ^ 2 * (1 - 1 / Real.sqrt (1 - e ^ 2))) := by
    field_simp [he, hGM]
  rw [hrewrite, hid]
  ring

/--
TeX: cor:circular — Circular perihelion limit.

At `e = 0` the eccentricity factor equals `1/2`, so
`Δϖ = -π V² a / GM`.
-/
theorem cor_circular_perihelion
    (V2 GM a : ℝ) :
    eccFactor 0 = (1 : ℝ) / 2 ∧
      deltaVarpi V2 GM a 0 = deltaVarpiCircular V2 GM a := by
  have hfac : eccFactor 0 = (1 : ℝ) / 2 := by
    unfold eccFactor
    norm_num
  refine ⟨hfac, ?_⟩
  unfold deltaVarpi deltaVarpiCircular
  rw [hfac]
  ring

end

end Paper4
