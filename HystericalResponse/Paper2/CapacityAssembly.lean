import Mathlib

/-
TeX: `2_galactic_modelling/paper_2_galactic_modelling.tex`,
Section “Capacity setup, assembly attractor, and formation conjecture”.

IF/THEN (theorem/corollary): given the capacity inequality / filling dynamics setup,
there is a stable attractor with Q² = (A²/y*) M (cor:sqrt-sat).

CONJECTURE (TeX conj:capacity): formation/retention requires
  Q ≳ O(√M) — not that the attractor itself is conjectural,
and not proved from transport.
-/

set_option autoImplicit false

namespace Paper2

noncomputable section

/--
PHYSICS CONJECTURE marker (TeX conj:capacity).
Formation / mature retention is proposed to require response capacity
`Q ≳ O(√M)` (equivalently a capacity ceiling `M ≲ Q²/A²`).
This is an opaque tagged conjecture — **not** a mathematical assertion that
`∀ A M Q, Q ≥ A √M`, and not the square-root attractor (`cor:sqrt-sat`).
-/
axiom physics_capacity_conjecture : Prop

def maxSupportedMass (A Q : ℝ) : ℝ :=
  Q^2 / A^2

def fillingFraction (A M Q : ℝ) : ℝ :=
  A^2 * M / Q^2

/-- Capacity inequality `y ≤ 1` rearranges to `Q ≥ A √M` for `A, M, Q ≥ 0`. -/
theorem capacity_inequality_iff_Q_ge
    (A M Q : ℝ)
    (hA : 0 ≤ A)
    (hM : 0 ≤ M)
    (hQ : 0 ≤ Q)
    (hQ0 : Q ≠ 0) :
    fillingFraction A M Q ≤ 1 ↔ A * Real.sqrt M ≤ Q := by
  have hQ2 : 0 < Q ^ 2 := sq_pos_of_ne_zero hQ0
  have hAsqrt : 0 ≤ A * Real.sqrt M := mul_nonneg hA (Real.sqrt_nonneg M)
  unfold fillingFraction
  rw [div_le_one hQ2]
  constructor
  · intro hAM
    have hsq : (A * Real.sqrt M) ^ 2 ≤ Q ^ 2 := by
      calc
        (A * Real.sqrt M) ^ 2 = A ^ 2 * (Real.sqrt M) ^ 2 := by ring
        _ = A ^ 2 * M := by rw [Real.sq_sqrt hM]
        _ ≤ Q ^ 2 := hAM
    exact (sq_le_sq₀ hAsqrt hQ).1 hsq
  · intro h
    have hsq : (A * Real.sqrt M) ^ 2 ≤ Q ^ 2 := (sq_le_sq₀ hAsqrt hQ).2 h
    calc
      A ^ 2 * M = A ^ 2 * (Real.sqrt M) ^ 2 := by rw [Real.sq_sqrt hM]
      _ = (A * Real.sqrt M) ^ 2 := by ring
      _ ≤ Q ^ 2 := hsq

def fillingRHS (μ ν y : ℝ) : ℝ :=
  y * (μ * (1 - y) - 2 * ν)

def fillingFixedPoint (μ ν : ℝ) : ℝ :=
  1 - 2 * ν / μ

theorem fillingFixedPoint_is_fixed
    (μ ν : ℝ)
    (hμ : μ ≠ 0) :
    fillingRHS μ ν (fillingFixedPoint μ ν) = 0 := by
  unfold fillingRHS fillingFixedPoint
  field_simp [hμ]
  ring

theorem fillingRHS_factorization
    (μ ν y : ℝ)
    (hμ : μ ≠ 0) :
    fillingRHS μ ν y =
      μ * y * (fillingFixedPoint μ ν - y) := by
  unfold fillingRHS fillingFixedPoint
  field_simp [hμ]
  ring

/--
TeX: thm:filling-stable — positive fixed point under μ > 0 and 2ν < μ.
Reduced abstraction: local exponential attraction is recorded algebraically via
linearization coefficient `-μ y*` (negative when μ y* > 0); full ODE flow theory
is not re-developed here.
-/
theorem thm_filling_stable
    (μ ν : ℝ)
    (hμ : 0 < μ)
    (hsub : 2 * ν < μ) :
    0 < fillingFixedPoint μ ν ∧
      fillingRHS μ ν =
        fun y => μ * y * (fillingFixedPoint μ ν - y) := by
  refine ⟨?pos, ?fac⟩
  · unfold fillingFixedPoint
    have : 2 * ν / μ < 1 := (div_lt_one hμ).2 hsub
    linarith
  · funext y
    exact fillingRHS_factorization μ ν y (ne_of_gt hμ)

theorem fillingFixedPoint_stable
    (μ ν : ℝ)
    (hμ : 0 < μ)
    (hsub : 2 * ν < μ) :
    0 < fillingFixedPoint μ ν :=
  (thm_filling_stable μ ν hμ hsub).1

/-- Linearization coefficient at the fixed point is strictly negative. -/
theorem filling_linearization_coeff_neg
    (μ ν : ℝ)
    (hμ : 0 < μ)
    (hsub : 2 * ν < μ) :
    μ * fillingFixedPoint μ ν > 0 :=
  mul_pos hμ (fillingFixedPoint_stable μ ν hμ hsub)

/--
TeX: cor:sqrt-sat — Square-root *attractor* (theorem/corollary, not conjecture):
given capacity filling y* = A² M / Q² with y* ≠ 0, one has Q² = (A²/y*) M.
-/
theorem cor_sqrt_sat
    (A M Q ystar : ℝ)
    (hQ : Q ≠ 0)
    (hy : ystar ≠ 0)
    (hfill : ystar = fillingFraction A M Q) :
    Q^2 = (A^2 / ystar) * M := by
  unfold fillingFraction at hfill
  field_simp [hQ, hy] at hfill ⊢
  nlinarith

theorem source_mass_relation_at_fixed_filling
    (A M Q ystar : ℝ)
    (hQ : Q ≠ 0)
    (hy : ystar ≠ 0)
    (hfill : ystar = fillingFraction A M Q) :
    Q^2 = (A^2 / ystar) * M :=
  cor_sqrt_sat A M Q ystar hQ hy hfill

end

end Paper2
