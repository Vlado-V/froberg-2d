import Froberg.ProjectedPrefix
import Froberg.OuterMultiplication
import Froberg.BilinearScalarFamily

/-! Scalar injection extends to arbitrary finite output coefficients. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K J : Type*} [Field K] [Fintype J] {n d s q : ℕ}

theorem prefix_injective_of_projected
    (P : (Fin n →₀ ℕ) → Prop) [DecidablePred P] (Q : Fin q → Forms K n d)
    (hQ : Function.Injective (ProjectedPrefix.multiplication P Q s)) :
    Function.Injective (prefixMultiplication Q s) := by
  intro a b hab
  apply hQ
  apply Subtype.ext
  simpa only [ProjectedPrefix.multiplication_val,hab]

theorem vector_scalar_injective_of_prefix (Q : Fin q → Forms K n d)
    (hQ : Function.Injective (prefixMultiplication Q s)) :
    Function.Injective (BilinearScalarFamily.multiplication
      (AttachedMultiplication.vectorMultiply (J := J) (s := s)) Q) := by
  intro a b hab
  funext i j
  have hj : prefixMultiplication Q s (fun i => a i j)=
      prefixMultiplication Q s (fun i => b i j) := by
    apply Subtype.ext
    have h := congrArg (fun p : J → Forms K n (s+d) => (p j).val) hab
    simpa only [BilinearScalarFamily.multiplication_apply,Finset.sum_apply,
      Submodule.coe_sum,AttachedMultiplication.vectorMultiply_val,prefixMultiplication_val] using h
  exact congrFun (hQ hj) i

theorem vector_scalar_injective_of_projected
    (P : (Fin n →₀ ℕ) → Prop) [DecidablePred P] (Q : Fin q → Forms K n d)
    (hQ : Function.Injective (ProjectedPrefix.multiplication P Q s)) :
    Function.Injective (BilinearScalarFamily.multiplication
      (AttachedMultiplication.vectorMultiply (J := J) (s := s)) Q) :=
  vector_scalar_injective_of_prefix Q (prefix_injective_of_projected P Q hQ)

end Froberg
