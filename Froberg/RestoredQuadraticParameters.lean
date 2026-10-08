import Froberg.RestoredBaseProjection

/-! All scalar tails and the true biform outer columns are independent
coordinates of the full restored parameter space. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

abbrev QuadraticParameters (K : Type) [Field K] (h m d r f : ℕ) :=
  (Fin r → Forms K m d) × (Fin f → FullBiform K (Fin h) m 1 (d-1))

def restoredC2Projection (idx : Fin r ≃ Label q J counts) :
    RestoredOuterSpace m d q f J counts O →ₗ[K] QuadraticParameters K h m d r f where
  toFun p := (fun i => p.1.1.1 (idx i),p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restoredC2Point (idx : Fin r ≃ Label q J counts)
    (p : QuadraticParameters K h m d r f) : RestoredOuterSpace m d q f J counts O :=
  (((fun i => p.1 (idx.symm i),0),0),p.2)

@[simp] theorem restoredC2Projection_point (idx : Fin r ≃ Label q J counts)
    (p : QuadraticParameters K h m d r f) :
    restoredC2Projection (O := O) idx (restoredC2Point idx p)=p := by
  apply Prod.ext
  · funext i
    exact congrArg p.1 (idx.symm_apply_apply i)
  · rfl

theorem restoredC2Projection_surjective (idx : Fin r ≃ Label q J counts) :
    Function.Surjective (restoredC2Projection (m := m) (d := d) (f := f) (O := O) idx) :=
  fun p => ⟨restoredC2Point idx p,restoredC2Projection_point idx p⟩

theorem restored_c2_principal_pullback
    (hO : ∀ j∈J,O j≤Forms K h j) (idx : Fin r ≃ Label q J counts)
    (D : MvPolynomial (Fin (finrank K (QuadraticParameters K h m d r f))) K)
    (hD : ∃ p : QuadraticParameters K h m d r f,
      eval ((Module.finBasis K _).equivFun p) D≠0)
    (Good : QuadraticParameters K h m d r f → Prop)
    (hGood : ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 → Good p) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ P : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) P≠0) ∧
      ∀ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) P≠0 → Good (restoredC2Projection idx p) := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  exact principal_open_linear_pullback (restoredC2Projection idx)
    (restoredC2Projection_surjective idx) D hD Good hGood

end Froberg.PreparedParameters
