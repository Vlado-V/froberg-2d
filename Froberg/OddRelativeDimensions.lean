import Froberg.OddEvenTargetExtension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Froberg.HigherRelationCost
import Froberg.LayeredTargetDimension

/-! The actual odd quotient dimension and the exact common-even-family
contribution to the C.4 dimension budget. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem quotient_finrank_eq_annihilator {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Submodule K V) :
    finrank K (V ⧸ A)=finrank K A.dualAnnihilator := by
  have h1 := Submodule.finrank_quotient_add_finrank A
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq A
  omega

theorem odd_ambient_quotient_dimension (hh : 0 < h) (hm : 0 < m) (hd : Odd d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    finrank K (biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G)≤
      finrank K (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G)+
        higherRelationCost d h u m := by
  rw [quotient_finrank_eq_annihilator,quotient_finrank_eq_annihilator]
  exact odd_ambient_covector_dimension hh hm hd Q F G

theorem injective_pi_quotient_finrank {V W : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : (Fin e → V) →ₗ[K] W) (hf : Function.Injective f) :
    finrank K W=finrank K (W ⧸ f.range)+e*finrank K V := by
  have hq := Submodule.finrank_quotient_add_finrank f.range
  rw [LinearMap.finrank_range_of_inj hf,Module.finrank_pi_fintype] at hq
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hq.symm

theorem odd_even_relative_dimension
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (hE : Function.Injective (oddEvenRelativeMap Q F G E)) :
    finrank K (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G)=
      finrank K (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations (Fin.append Q E) F G)+
        e*finrank K (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) := by
  have hq := injective_pi_quotient_finrank (oddEvenRelativeMap Q F G E) hE
  rw [(oddEvenTargetExtensionEquiv Q F G E).finrank_eq] at hq
  exact hq

theorem odd_ambient_relative_dimension (hh : 0 < h) (hm : 0 < m) (hd : Odd d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (hE : Function.Injective (oddEvenRelativeMap Q F G E)) :
    finrank K (biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G)≤
      finrank K (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations (Fin.append Q E) F G)+
        e*finrank K (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G)+
          higherRelationCost d h u m := by
  rw [←odd_even_relative_dimension Q F G E hE]
  exact odd_ambient_quotient_dimension hh hm hd Q F G

end Froberg
