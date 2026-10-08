import Froberg.PreparedCountRestriction
import Froberg.PreparedBiformFamilies
import Froberg.RestoredScalarCompatibility

/-! Restricting the parameter family is literally restriction of its
generators, including the restored pure parts in their retained slots. -/
noncomputable section
set_option maxHeartbeats 250000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K]

theorem pureShift_injective_index {U V : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {u r r' : ℕ} (embed : U →ₗ[K] V) (slot : Fin u → Fin r)
    (j : Fin r → Fin r') (hj : Function.Injective j) (v : Fin u → U) (i : Fin r) :
    PolynomialRestoration.pureShift embed (j ∘ slot) v (j i)=
      PolynomialRestoration.pureShift embed slot v i := by
  classical
  simp only [PolynomialRestoration.pureShift,LinearMap.sum_apply,Finset.sum_apply,
    LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.single_apply,Pi.single_apply,
    Function.comp_apply,hj.eq_iff]

namespace PreparedParameters
variable [Infinite K] {h m d q f r r' : ℕ}
variable {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def countIndexMap (hc : ∀ j∈J,c j≤c' j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c') : Fin r → Fin r' :=
  fun i => idx'.symm (countLabelMap hc (idx i))

theorem countIndexMap_injective (hc : ∀ j∈J,c j≤c' j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c') :
    Function.Injective (countIndexMap hc idx idx') :=
  idx'.symm.injective.comp ((countLabelMap_injective hc).comp idx.injective)

theorem restoredFamilyLinear_restrictCounts (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J c' O) (i : Fin r) :
    restoredFamilyLinear hd hO hJ heven idx slot (restrictCounts hc p.1,p.2) i=
      restoredFamilyLinear hd hO hJ heven idx' (countIndexMap hc idx idx' ∘ slot) p
        (countIndexMap hc idx idx' i) := by
  apply Subtype.ext
  change generator (restrictCounts hc p.1) (idx i)+
      (PolynomialRestoration.pureShift (pureEvenEmbed hd) slot p.2 i).val=
    generator p.1 (idx' (idx'.symm (countLabelMap hc (idx i))))+
      (PolynomialRestoration.pureShift (pureEvenEmbed hd)
        (countIndexMap hc idx idx' ∘ slot) p.2 (countIndexMap hc idx idx' i)).val
  rw [restrictCounts_generator,Equiv.apply_symm_apply,
    pureShift_injective_index _ _ _ (countIndexMap_injective hc idx idx')]

theorem restoredEndpointFamily_restrictCounts (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J c' O) (i : Fin r) :
    restoredEndpointFamily hd hO hJ heven idx slot (restrictCounts hc p.1,p.2) i=
      restoredEndpointFamily hd hO hJ heven idx' (countIndexMap hc idx idx' ∘ slot) p
        (countIndexMap hc idx idx' i) := by
  apply Subtype.ext
  change rename finSumFinEquiv (restoredFamilyLinear hd hO hJ heven idx slot
    (restrictCounts hc p.1,p.2) i).val=_
  rw [restoredFamilyLinear_restrictCounts]
  rfl

end PreparedParameters

namespace PreparedTarget
variable [Infinite K] {h m d q : ℕ}
variable {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem preparedEvenBiform_restrictCounts
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j) (p : PreparedParameters.Space m d q J c' O)
    (i : PreparedParameters.Label q J c) :
    preparedEvenBiform hO hJ heven (PreparedParameters.restrictCounts hc p) i=
      preparedEvenBiform hO hJ heven p (PreparedParameters.countLabelMap hc i) := by
  apply Subtype.ext
  exact PreparedParameters.restrictCounts_generator hc p i

end PreparedTarget
end Froberg
