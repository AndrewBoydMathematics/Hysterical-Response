import Mathlib
import HystericalResponse.Paper1.Paper1_ResponseTheory_Spec
import HystericalResponse.Paper1.UnentangledIncoming

/-!
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Section: **Constructive response theory**

Route (same order as TeX):
0. Unentangled incoming / Everett off-diagonal feed — `UnentangledIncoming.lean`
   (`thm:driven-deviation`, `thm:offdiag-source`)
1. Resolvent response / Laplace integral — `thm:resolvent-response`
   (core Banach construction lives in `Paper1_ResponseTheory_Spec`;
   aliases and channel lemmas are here)
1b. Unique stable nonzero steady leftover — `thm:stable-steady`
2. Source-channel susceptibility / invariant sectors
3. Weak channel mixing — operator Neumann series + norm bound
4. Symmetry restriction
5. Coherence-norm counterexample — `prop:coherence-norm`
6. Two-level force-contrast bound `|B| ≤ |δf|/2` (application remark;
   pedagogical renewal toy is in the primer, not re-derived here)

Literature: unbounded \(C_0\) resolvent–Laplace identification remains
`Paper1.literature_c0_resolvent_laplace`.
-/

namespace Paper1.ConstructiveResponse

noncomputable section

open Paper1

/-! ## Resolvent response -/

/-- TeX: thm:resolvent-response — stationary response is the stable Laplace integral. -/
theorem thm_resolvent_response
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (data : StableSemigroupData X) (S : X) :
    stationaryResponse data.Linv S =
      ∫ t in Set.Ioi (0 : ℝ), data.orbit S t :=
  inverse_generator_as_semigroup_integral data S

/-! ## Unique stable steady leftover (thm:stable-steady, algebraic core) -/

/-- TeX: thm:stable-steady (1) existence — `L (-Linv S) + S = 0` if `L ∘ Linv = id`. -/
theorem thm_stable_steady_exists
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (L Linv : X →ₗ[ℝ] X) (S : X)
    (hinv : L.comp Linv = LinearMap.id) :
    L (-Linv S) + S = 0 := by
  have hLS : L (Linv S) = S := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : X →ₗ[ℝ] X => f S) hinv
  simp [map_neg, hLS]

/--
TeX: thm:stable-steady (1) uniqueness — `ker L = {0}` ⇒ at most one solution of
`L δ + S = 0`. (In TeX, `ker L = {0}` on the stable subspace follows from
exponential stability.)
-/
theorem thm_stable_steady_unique
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (L : X →ₗ[ℝ] X) (S δ₁ δ₂ : X)
    (hker : ∀ x : X, L x = 0 → x = 0)
    (h₁ : L δ₁ + S = 0) (h₂ : L δ₂ + S = 0) :
    δ₁ = δ₂ := by
  have hL : L δ₁ = L δ₂ := by
    have e1 : L δ₁ = -S := by
      have := h₁
      -- L δ₁ + S = 0 ⇒ L δ₁ = -S
      simpa [add_eq_zero_iff_eq_neg] using this
    have e2 : L δ₂ = -S := by
      simpa [add_eq_zero_iff_eq_neg] using h₂
    exact e1.trans e2.symm
  have hsub : L (δ₁ - δ₂) = 0 := by
    simpa [map_sub, sub_eq_zero] using hL
  exact eq_of_sub_eq_zero (hker _ hsub)

/-- TeX: thm:stable-steady (1) combined — unique steady state is `-Linv S`. -/
theorem thm_stable_steady_eq_neg_Linv
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (L Linv : X →ₗ[ℝ] X) (S δ : X)
    (hinv : L.comp Linv = LinearMap.id)
    (hker : ∀ x : X, L x = 0 → x = 0) :
    (L δ + S = 0 ↔ δ = -Linv S) := by
  constructor
  · intro h
    exact thm_stable_steady_unique L S δ (-Linv S) hker h
      (thm_stable_steady_exists L Linv S hinv)
  · intro h
    simpa [h] using thm_stable_steady_exists L Linv S hinv

/--
TeX: thm:stable-steady (3) — nonzero drive ↔ nonzero steady leftover.
-/
theorem thm_nonzero_source_iff_nonzero_steady
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (L Linv : X →ₗ[ℝ] X) (S : X)
    (hinv : L.comp Linv = LinearMap.id)
    (_hker : ∀ x : X, L x = 0 → x = 0) :
    (-Linv S = 0) ↔ (S = 0) := by
  constructor
  · intro h
    have hex := thm_stable_steady_exists L Linv S hinv
    simpa [h] using hex
  · intro h
    simp [h]

/-- TeX: thm:stable-steady (3) contrapositive form used in prose. -/
theorem thm_nonzero_source_nonzero_steady
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (L Linv : X →ₗ[ℝ] X) (S : X)
    (hinv : L.comp Linv = LinearMap.id)
    (hker : ∀ x : X, L x = 0 → x = 0)
    (hS : S ≠ 0) :
    -Linv S ≠ 0 := by
  intro h
  exact hS ((thm_nonzero_source_iff_nonzero_steady L Linv S hinv hker).mp h)

/--
TeX: thm:stable-steady (2) — deviation from the steady leftover decays with the
stable-semigroup envelope. Writing `δρ(t)=δρ_ss+ε(t)` with `ε(t)=evolve t ε₀`,
the bound is exactly `StableSemigroupData.exponential_bound` (TeX Assumption on
the stable response subspace).
-/
theorem thm_stable_steady_exp_decay
    {X : Type*} [NormedAddCommGroup X]
    (data : StableSemigroupData X) (ε0 : X) (t : NNReal) :
    ‖data.evolve t ε0‖ ≤ data.M * Real.exp (-data.γ * (t : ℝ)) * ‖ε0‖ :=
  data.exponential_bound t ε0

/-- TeX: lem:resolvent — susceptibility bound `‖∫ e^{tL} S‖ ≤ (M/γ) ‖S‖`. -/
theorem lem_resolvent
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (data : StableSemigroupData X) (S : X) :
    ‖data.resolventIntegral S‖ ≤ (data.M / data.γ) * ‖S‖ :=
  data.norm_resolventIntegral_le S

/--
TeX: cor:jin-over-jout — steady leftover scales as \(J_{\mathrm{in}}/J_{\mathrm{out}}\).

Reduced abstraction: with \(S = ν\cdot\mathrm{kick}\) (incoming rate \(ν\sim J_{\mathrm{in}}\))
the resolvent bound yields
\(\|\int e^{tL}S\|\le (M/γ)\,ν\,\|\mathrm{kick}\|\).
The identification \(γ\sim J_{\mathrm{out}}\) is the explicit physics hypothesis
`physics_jout_sets_decoherence_scale` (not a silent gap).
-/
theorem cor_jin_over_jout
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (data : StableSemigroupData X) (ν : ℝ) (kick : X)
    (_hJout : Paper1.UnentangledIncoming.physics_jout_sets_decoherence_scale)
    (hν : 0 ≤ ν) :
    ‖data.resolventIntegral (ν • kick)‖ ≤ (data.M / data.γ) * ν * ‖kick‖ := by
  have hbound := data.norm_resolventIntegral_le (ν • kick)
  have hnorm : ‖ν • kick‖ = ν * ‖kick‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hν]
  calc
    ‖data.resolventIntegral (ν • kick)‖
        ≤ (data.M / data.γ) * ‖ν • kick‖ := hbound
    _ = (data.M / data.γ) * (ν * ‖kick‖) := by rw [hnorm]
    _ = (data.M / data.γ) * ν * ‖kick‖ := by ring

/-! ## Invariant channel sectors -/

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

def channelChi (pair : X →ₗ[ℝ] ℝ) (Linv : X →ₗ[ℝ] X) (S : X) : ℝ :=
  - pair (Linv S)

/--
TeX: Invariant channel sectors.
If `S = ∑ J_a S_a` and the response is linear, then `F_resp = ∑ J_a χ_a`.
-/
theorem thm_invariant_channel_sectors
    {n : ℕ} (pair : X →ₗ[ℝ] ℝ) (Linv : X →ₗ[ℝ] X)
    (J : Fin n → ℝ) (S : Fin n → X) :
    channelChi pair Linv (∑ i, J i • S i) =
      ∑ i, J i * channelChi pair Linv (S i) := by
  simp [channelChi, map_sum, map_smul, mul_comm, mul_left_comm, mul_assoc,
    Finset.sum_neg_distrib, mul_neg]

/-! ## Weak channel mixing (operator Neumann series) -/

/--
TeX: cor:weak-channel-mixing — scalar majorant identity
`∑' a r^{n+1} = a r/(1-r)` for `0 ≤ r < 1`.
-/
theorem cor_weak_channel_mixing_majorant
    (a r : ℝ) (_ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, a * r ^ (n + 1)) = a * r / (1 - r) := by
  have hr_abs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hsum : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
    tsum_geometric_of_abs_lt_one hr_abs
  have hshift : (∑' n : ℕ, r ^ (n + 1)) = r / (1 - r) := by
    calc
      (∑' n : ℕ, r ^ (n + 1)) = ∑' n : ℕ, r * r ^ n := by
        congr 1; funext n; ring
      _ = r * ∑' n : ℕ, r ^ n := by rw [← tsum_mul_left]
      _ = r * (1 - r)⁻¹ := by rw [hsum]
      _ = r / (1 - r) := by field_simp
  calc
    (∑' n : ℕ, a * r ^ (n + 1)) = a * ∑' n : ℕ, r ^ (n + 1) := by rw [← tsum_mul_left]
    _ = a * (r / (1 - r)) := by rw [hshift]
    _ = a * r / (1 - r) := by ring

theorem cor_weak_channel_mixing_error_identity
    (L0invNorm VNorm : ℝ)
    (_hL : 0 ≤ L0invNorm) (_hV : 0 ≤ VNorm)
    (_hr : L0invNorm * VNorm < 1) :
    L0invNorm * (L0invNorm * VNorm) / (1 - L0invNorm * VNorm) =
      L0invNorm ^ 2 * VNorm / (1 - L0invNorm * VNorm) := by
  ring

/-- Geometric tail identity used by the operator remainder bound. -/
theorem neumann_tail_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    (∑' n : ℕ, A ^ n) - 1 = ∑' n : ℕ, A ^ (n + 1) :=
  (geom_series_succ A hA).symm

/--
TeX: cor:weak-channel-mixing — operator Neumann series on a Banach space.

If `L₀` is invertible with two-sided continuous inverse `L₀⁻¹` and
`‖L₀⁻¹ V‖ < 1`, then
`(L₀+V)⁻¹ = ∑ₙ (-L₀⁻¹ V)ⁿ L₀⁻¹` (as `Ring.inverse`).
-/
theorem cor_weak_channel_mixing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L0 L0inv V : E →L[ℝ] E)
    (hR : L0 * L0inv = 1) (hL : L0inv * L0 = 1)
    (hr : ‖L0inv * V‖ < 1) :
    (∑' n : ℕ, (-(L0inv * V)) ^ n) * L0inv = Ring.inverse (L0 + V) := by
  set A : E →L[ℝ] E := -(L0inv * V)
  have hA : ‖A‖ < 1 := by simpa [A, norm_neg] using hr
  have hV : V = L0 * (L0inv * V) := by
    calc
      V = (1 : E →L[ℝ] E) * V := (one_mul V).symm
      _ = (L0 * L0inv) * V := by rw [hR]
      _ = L0 * (L0inv * V) := by rw [mul_assoc]
  have hfac : L0 + V = L0 * (1 - A) := by
    calc
      L0 + V = L0 + L0 * (L0inv * V) := by nth_rw 1 [hV]
      _ = L0 * (1 + L0inv * V) := by rw [mul_one_add]
      _ = L0 * (1 - A) := by simp [A, sub_eq_add_neg]
  let uL0 : (E →L[ℝ] E)ˣ := ⟨L0, L0inv, hR, hL⟩
  let u1A : (E →L[ℝ] E)ˣ := Units.oneSub A hA
  have hprod : (L0 + V : E →L[ℝ] E) = ↑(uL0 * u1A) := by
    change L0 + V = ↑uL0 * ↑u1A
    simpa [uL0, u1A, Units.val_oneSub] using hfac
  have hsum : (∑' n : ℕ, A ^ n) = (↑u1A⁻¹ : E →L[ℝ] E) := by
    calc
      ∑' n : ℕ, A ^ n = Ring.inverse (1 - A) := geom_series_eq_inverse A hA
      _ = Ring.inverse (↑u1A) := by simp [u1A, Units.val_oneSub]
      _ = ↑u1A⁻¹ := Ring.inverse_unit u1A
  calc
    (∑' n : ℕ, (-(L0inv * V)) ^ n) * L0inv
        = (∑' n : ℕ, A ^ n) * L0inv := by simp [A]
    _ = (↑u1A⁻¹ : E →L[ℝ] E) * (↑uL0⁻¹ : E →L[ℝ] E) := by simp [hsum, uL0]
    _ = ↑(u1A⁻¹ * uL0⁻¹) := by simp [Units.val_mul]
    _ = ↑(uL0 * u1A)⁻¹ := by rw [mul_inv_rev]
    _ = Ring.inverse ↑(uL0 * u1A) := (Ring.inverse_unit (uL0 * u1A)).symm
    _ = Ring.inverse (L0 + V) := by rw [hprod]

/--
TeX: cor:weak-channel-mixing — operator remainder bound
`‖L⁻¹ - L₀⁻¹‖ ≤ ‖L₀⁻¹‖² ‖V‖ / (1 - ‖L₀⁻¹ V‖)`.
-/
theorem cor_weak_channel_mixing_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L0inv V : E →L[ℝ] E) (hr : ‖L0inv * V‖ < 1) :
    ‖(∑' n : ℕ, (-(L0inv * V)) ^ n) * L0inv - L0inv‖ ≤
      ‖L0inv‖ ^ 2 * ‖V‖ / (1 - ‖L0inv * V‖) := by
  set A : E →L[ℝ] E := -(L0inv * V)
  have hA : ‖A‖ < 1 := by simpa [A, norm_neg] using hr
  have hAeq : ‖A‖ = ‖L0inv * V‖ := by simp [A, norm_neg]
  have hdiff :
      (∑' n : ℕ, A ^ n) * L0inv - L0inv = (∑' n : ℕ, A ^ (n + 1)) * L0inv := by
    calc
      (∑' n : ℕ, A ^ n) * L0inv - L0inv
          = (∑' n : ℕ, A ^ n) * L0inv - 1 * L0inv := by rw [one_mul]
      _ = ((∑' n : ℕ, A ^ n) - 1) * L0inv := (sub_mul _ _ _).symm
      _ = (∑' n : ℕ, A ^ (n + 1)) * L0inv := by rw [neumann_tail_eq A hA]
  have hsummable_r : Summable fun n : ℕ => ‖A‖ ^ (n + 1) := by
    have : Summable fun n : ℕ => ‖A‖ * ‖A‖ ^ n :=
      (summable_geometric_of_lt_one (norm_nonneg _) hA).mul_left ‖A‖
    simpa [pow_succ'] using this
  have htsum_norm : (∑' n : ℕ, ‖A‖ ^ (n + 1)) = ‖A‖ / (1 - ‖A‖) := by
    have hgeo := tsum_geometric_of_lt_one (norm_nonneg A) hA
    calc
      ∑' n, ‖A‖ ^ (n + 1) = ∑' n, ‖A‖ * ‖A‖ ^ n := by simp [pow_succ']
      _ = ‖A‖ * ∑' n, ‖A‖ ^ n := tsum_mul_left
      _ = ‖A‖ * (1 - ‖A‖)⁻¹ := by rw [hgeo]
      _ = ‖A‖ / (1 - ‖A‖) := by field_simp
  have hmaj : ‖∑' n : ℕ, A ^ (n + 1)‖ ≤ ‖A‖ / (1 - ‖A‖) := by
    have hbound :=
      tsum_of_norm_bounded hsummable_r.hasSum fun n =>
        norm_pow_le' A (Nat.succ_pos n)
    exact hbound.trans_eq htsum_norm
  have h1 : 0 ≤ 1 - ‖A‖ := le_of_lt (sub_pos.mpr hA)
  calc
    ‖(∑' n : ℕ, (-(L0inv * V)) ^ n) * L0inv - L0inv‖
        = ‖(∑' n : ℕ, A ^ n) * L0inv - L0inv‖ := by simp [A]
    _ = ‖(∑' n : ℕ, A ^ (n + 1)) * L0inv‖ := by rw [hdiff]
    _ ≤ ‖∑' n : ℕ, A ^ (n + 1)‖ * ‖L0inv‖ := norm_mul_le _ _
    _ ≤ (‖A‖ / (1 - ‖A‖)) * ‖L0inv‖ := mul_le_mul_of_nonneg_right hmaj (norm_nonneg _)
    _ = ‖A‖ * ‖L0inv‖ / (1 - ‖A‖) := by field_simp
    _ ≤ (‖L0inv‖ * ‖V‖) * ‖L0inv‖ / (1 - ‖A‖) := by
        refine div_le_div_of_nonneg_right ?_ h1
        exact mul_le_mul_of_nonneg_right
          (by simpa [A, norm_neg] using
            (norm_mul_le L0inv V : ‖L0inv * V‖ ≤ ‖L0inv‖ * ‖V‖))
          (norm_nonneg _)
    _ = ‖L0inv‖ ^ 2 * ‖V‖ / (1 - ‖A‖) := by ring
    _ = ‖L0inv‖ ^ 2 * ‖V‖ / (1 - ‖L0inv * V‖) := by rw [hAeq]

/-! ## Symmetry restriction -/

/--
TeX: Symmetry restriction.
If the expected force intertwines with a spatial rotation `R` and the state is
invariant in the sense that `expect ρ (R F) = expect ρ F`, then the expected
force vector is `R`-invariant: `R (expect ρ F) = expect ρ F`.
(This is the algebraic content of TeX's unitary/rotation argument.)
-/
theorem thm_symmetry_restriction
    {State V : Type*} [AddCommGroup V] [Module ℝ V]
    (expect : State → V → V) (ρ : State) (F : V) (R : V →ₗ[ℝ] V)
    (hintertwine : expect ρ (R F) = R (expect ρ F))
    (hstate : expect ρ (R F) = expect ρ F) :
    R (expect ρ F) = expect ρ F := by
  calc
    R (expect ρ F) = expect ρ (R F) := hintertwine.symm
    _ = expect ρ F := hstate

/-- Axial / spherical special case: a family of rotations that each fix the
expected force leaves it in the joint invariant subspace. -/
theorem thm_symmetry_restriction_joint
    {State V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*}
    (expect : State → V → V) (ρ : State) (F : V)
    (R : ι → V →ₗ[ℝ] V)
    (h : ∀ i, R i (expect ρ F) = expect ρ F) :
    ∀ i, R i (expect ρ F) = expect ρ F := h

/-! ## Coherence norm does not control force -/

def coordPair (n : ℕ) (i : Fin n) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun v => v i
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

/--
TeX: prop:coherence-norm — Coherence norm does not control force.
Explicit witness: for `n ≥ 2`, the 0-coordinate pairing has a nonzero
normalized kernel vector supported on coordinate 1.
-/
theorem prop_coherence_norm
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ (pair : (Fin n → ℝ) →ₗ[ℝ] ℝ) (Q : Fin n → ℝ),
      Q ≠ 0 ∧ pair Q = 0 ∧ (∑ i : Fin n, |Q i|) = 1 := by
  have hpos : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn
  let i0 : Fin n := ⟨0, hpos⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hn⟩
  refine ⟨coordPair n i0, fun j => if j = i1 then 1 else 0, ?_, ?_, ?_⟩
  · intro h
    have : (fun j : Fin n => if j = i1 then (1 : ℝ) else 0) i1 = 0 := by
      simpa using congrArg (fun f : Fin n → ℝ => f i1) h
    simp at this
  · have : i0 ≠ i1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [coordPair, this]
  · calc
      (∑ i : Fin n, |(if i = i1 then (1 : ℝ) else 0)|)
          = ∑ i : Fin n, if i = i1 then 1 else 0 := by
              congr 1; funext i; split_ifs <;> simp
      _ = 1 := by
          simp [Finset.sum_ite_eq']

/-- TeX application remark: two-level `|B| ≤ |δf|/2`. -/
theorem lem_population_bias_bound
    (β κ ΔE δf : ℝ)
    (hOmega : 0 < Paper1.Omega κ ΔE) :
    |Paper1.populationBias β κ ΔE δf| ≤ |δf| / 2 :=
  Paper1.populationBias_bound β κ ΔE δf hOmega

/-! ## Dynamical relevance (Krylov / orbit) -/

/-- TeX: force-invisible along the Krylov tower. -/
def forceInvisible {X : Type*} [AddCommGroup X] [Module ℝ X]
    (pair : X → ℝ) (L : X →ₗ[ℝ] X) (x : X) : Prop :=
  ∀ n : ℕ, pair ((L ^ n) x) = 0

/-- TeX: dynamically force-relevant (some Krylov moment sees the force). -/
def dynamicallyForceRelevant {X : Type*} [AddCommGroup X] [Module ℝ X]
    (pair : X → ℝ) (L : X →ₗ[ℝ] X) (x : X) : Prop :=
  ∃ n : ℕ, pair ((L ^ n) x) ≠ 0

/-- TeX: a nonzero Krylov moment witnesses dynamical force-relevance. -/
theorem prop_dynamical_relevance
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (pair : X → ℝ) (L : X →ₗ[ℝ] X) (x : X) (k : ℕ)
    (h : pair ((L ^ k) x) ≠ 0) :
    dynamicallyForceRelevant pair L x :=
  ⟨k, h⟩

theorem prop_force_invisible_iff
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (pair : X → ℝ) (L : X →ₗ[ℝ] X) (x : X) :
    forceInvisible pair L x ↔ ∀ n, pair ((L ^ n) x) = 0 :=
  Iff.rfl

theorem prop_invisible_excludes_relevance
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (pair : X → ℝ) (L : X →ₗ[ℝ] X) (x : X)
    (h : forceInvisible pair L x) :
    ¬ dynamicallyForceRelevant pair L x := by
  intro ⟨n, hn⟩
  exact hn (h n)

/--
TeX dynamical-relevance orbit content (finite-dimensional / analytic form):
if every Krylov moment is force-invisible, every truncated exponential orbit
`∑_{k<N} (t^k/k!) L^k x` is force-invisible as well.
-/
theorem prop_dynamical_relevance_orbit_truncation
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (pair : X →ₗ[ℝ] ℝ) (L : X →ₗ[ℝ] X) (x : X) (t : ℝ) (N : ℕ)
    (h : forceInvisible (fun y => pair y) L x) :
    pair (∑ k ∈ Finset.range N, (t ^ k / k.factorial) • (L ^ k) x) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero ?_
  intro k _hk
  simp [h k]

/-- Toy renewal leftover: steady `F_H` for the two-level channel. -/
def renewalLeftover (J Γem Γfr B : ℝ) : ℝ :=
  (J / Γem) * (Γfr / (Γem + Γfr)) * B

theorem renewalLeftover_vanishes_of_bias
    (J Γem Γfr : ℝ) :
    renewalLeftover J Γem Γfr 0 = 0 := by
  simp [renewalLeftover]

end

end Paper1.ConstructiveResponse
