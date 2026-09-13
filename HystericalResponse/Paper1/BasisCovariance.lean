import Mathlib

/-!
TeX: `1_hysterical_response/paper_1_hysterical_response.tex`
Section: **Basis covariance**

Route (same order as TeX):
1. Classicalization / off-classical sector
2. Passive unitary change of representation
3. Inverse-generator covariance
4. `thm:basis-covariance` — Basis Covariance Theorem
5. No arbitrary basis ambiguity / pointer-map distinction (corollaries)
6. Odd-observable cancellation (used again under neutrality)

Constructive-response material (resolvent, sectors, mixing, …) lives in
`ConstructiveResponse.lean`, matching the next TeX section.
-/

namespace Paper1.BasisCovariance

noncomputable section

structure Classicalization (X : Type*) where
  Δ : X → X
  idempotent : ∀ x, Δ (Δ x) = Δ x

structure UnitChange (X : Type*) [AddCommGroup X] [Module ℝ X] where
  Ad : X →ₗ[ℝ] X
  Ad_inv : X →ₗ[ℝ] X
  left_inv : ∀ x, Ad_inv (Ad x) = x
  right_inv : ∀ x, Ad (Ad_inv x) = x

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- Off-classical sector `Q_cl = I - Δ_cl`. -/
def offClassical (C : Classicalization X) (x : X) : X :=
  x - C.Δ x

theorem offClassical_covariant
    (C : Classicalization X) (U : UnitChange X)
    (hΔ : ∀ x, C.Δ (U.Ad x) = U.Ad (C.Δ x)) (x : X) :
    offClassical C (U.Ad x) = U.Ad (offClassical C x) := by
  simp [offClassical, hΔ, map_sub]

/-- Transformed inverse generator: `Linv' = Ad ∘ Linv ∘ Ad⁻¹`. -/
def conjugateInverse (Linv : X →ₗ[ℝ] X) (U : UnitChange X) : X →ₗ[ℝ] X :=
  U.Ad ∘ₗ Linv ∘ₗ U.Ad_inv

/-- TeX lemma: covariance of the inverse generator. -/
theorem lem_inverse_generator_covariant
    (Linv : X →ₗ[ℝ] X) (U : UnitChange X) (x : X) :
    conjugateInverse Linv U (U.Ad x) = U.Ad (Linv x) := by
  simp [conjugateInverse, U.left_inv]

def hystericalForce (pair : X → ℝ) (Linv : X → X) (S : X) : ℝ :=
  - pair (Linv S)

/--
TeX: thm:basis-covariance — Basis Covariance Theorem for Hysterical Response.
Passive simultaneous conjugation of pairing, inverse generator, and source
leaves `F_H` invariant.
-/
theorem thm_basis_covariance
    (pair : X →ₗ[ℝ] ℝ) (Linv : X →ₗ[ℝ] X) (U : UnitChange X) (S : X)
    (hpair : ∀ x, pair (U.Ad x) = pair x) :
    hystericalForce (fun x => pair x) (fun x => conjugateInverse Linv U x) (U.Ad S) =
      hystericalForce (fun x => pair x) (fun x => Linv x) S := by
  simp [hystericalForce, conjugateInverse, U.left_inv, hpair]

/--
TeX corollary [No arbitrary basis ambiguity]: a passive basis change cannot
create, destroy, or alter `F_H`. Any two pairing-preserving passive renamings
give the same force as each other (and as the original description).
-/
theorem cor_no_arbitrary_basis_ambiguity
    (pair : X →ₗ[ℝ] ℝ) (Linv : X →ₗ[ℝ] X) (U V : UnitChange X) (S : X)
    (hU : ∀ x, pair (U.Ad x) = pair x)
    (hV : ∀ x, pair (V.Ad x) = pair x) :
    hystericalForce (fun x => pair x) (fun x => conjugateInverse Linv U x) (U.Ad S) =
      hystericalForce (fun x => pair x) (fun x => conjugateInverse Linv V x) (V.Ad S) := by
  calc
    hystericalForce (fun x => pair x) (fun x => conjugateInverse Linv U x) (U.Ad S)
        = hystericalForce (fun x => pair x) (fun x => Linv x) S :=
          thm_basis_covariance pair Linv U S hU
    _ = hystericalForce (fun x => pair x) (fun x => conjugateInverse Linv V x) (V.Ad S) :=
          (thm_basis_covariance pair Linv V S hV).symm

/-- TeX: active / pointer-map changes may change the prediction. -/
theorem prop_pointer_map_may_change_force
    (pair : X → ℝ) (Linv : X → X) (S S_new : X)
    (h : pair (Linv S_new) ≠ pair (Linv S)) :
    hystericalForce pair Linv S_new ≠ hystericalForce pair Linv S := by
  simpa [hystericalForce] using neg_injective.ne h

/-! ## Odd cancellation (TeX neutrality section also uses this) -/

structure Involution (Y : Type*) where
  ι : Y → Y
  involutive : ∀ y, ι (ι y) = y

def OddMap {Y Z : Type*} [Neg Z] (ι : Involution Y) (f : Y → Z) : Prop :=
  ∀ y, f (ι.ι y) = - f y

theorem lem_odd_observable_cancellation
    {Y : Type*} [AddCommGroup Y]
    (ι : Involution Y) (f : Y → ℝ)
    (hodd : OddMap ι f) (y : Y) (hsys : ι.ι y = y) :
    f y = 0 := by
  have h := hodd y
  have : f y = - f y := by rwa [hsys] at h
  linarith

end

end Paper1.BasisCovariance
