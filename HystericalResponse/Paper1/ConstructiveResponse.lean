import Mathlib
import HystericalResponse.Paper1.Paper1_ResponseTheory_Spec

/-!
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Section: **Constructive response theory**

Route (same order as TeX):
1. Resolvent response / Laplace integral — `thm:resolvent-response`
   (core Banach construction lives in `Paper1_ResponseTheory_Spec`;
   aliases and channel lemmas are here)
2. Source-channel susceptibility / invariant sectors
3. Weak channel mixing (Neumann remainder)
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

/-- TeX: lem:resolvent — susceptibility bound `‖∫ e^{tL} S‖ ≤ (M/γ) ‖S‖`. -/
theorem lem_resolvent
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (data : StableSemigroupData X) (S : X) :
    ‖data.resolventIntegral S‖ ≤ (data.M / data.γ) * ‖S‖ :=
  data.norm_resolventIntegral_le S

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

/-! ## Weak channel mixing -/

/--
TeX: Weak channel mixing — Neumann remainder coefficients.
If `0 ≤ r < 1` and `a ≥ 0`, then `∑'_{n≥0} a r^{n+1} = a r/(1-r)`,
which is the majorant used for
`‖L⁻¹ - L₀⁻¹‖ ≤ ‖L₀⁻¹‖² ‖V‖ / (1-r)` under `r = ‖L₀⁻¹ V‖ ≤ ‖L₀⁻¹‖ ‖V‖`.
-/
theorem cor_weak_channel_mixing
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
