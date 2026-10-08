import Froberg.SingleProfileScalarProduct
import Froberg.IntrinsicBiformRow

/-! With no generators in the new layer, a scalar/product injection is
exactly the required intrinsic prepared-row exactness. -/
noncomputable section
set_option maxHeartbeats 900000
namespace Froberg
open Module MvPolynomial AttachedMultiplication MonomialExpansion
variable {K : Type} [Field K] [Infinite K]
variable {σ J : Type*} [Fintype σ] [Fintype J] [IsEmpty J]
variable {n R s d r j : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem intrinsic_empty_single_profile_exact
    (S : Finset (Fin n)) (P : V →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hP : Function.Injective P)
    (hPY : ∀ p,(P p).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) j)
    (Q : Fin r → Forms K n d)
    (hQ : Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠j) Q s))
    (E : J → FullBiform K σ n R s) :
    (bilinearKoszulRow fullBiformScalarProduct Q E P).ker=
      (bilinearKoszulConstants (K := K) (W := V) Q E).range := by
  classical
  letI : Module.Finite K (homogeneousSubmodule σ K R) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ R)
  let b := Module.finBasis K (homogeneousSubmodule σ K R)
  let o := fun i => (b i).val
  have ho : LinearIndependent K o := b.linearIndependent.map'
    (homogeneousSubmodule σ K R).subtype (Submodule.ker_subtype _)
  have hdeg : ∀ i,(o i).IsHomogeneous R := fun i => (b i).property
  let c : (Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s) ≃ₗ[K]
      FullBiform K σ n R s := fullBiformCoordinates o ho hdeg
  have hi := single_profile_scalar_product_row_injective o ho hdeg S P hP hPY Q hQ
  have hscalar (a : Fin r → FullBiform K σ n R s) :
      polynomialScalarRow o Q (fun i => c.symm (a i))=
        ∑ i,fullBiformScalarProduct (Q i) (a i) := by
    unfold polynomialScalarRow
    rw [LinearMap.comp_apply,BilinearScalarFamily.multiplication_apply,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change coordinateScalarProduct o (Q i) (c.symm (a i))=_
    rw [coordinateScalarProduct_apply,fullBiformScalarProduct_apply]
    congr 1
    exact congrArg Subtype.val (c.apply_symm_apply (a i))
  have hker : (bilinearKoszulRow fullBiformScalarProduct Q E P).ker=⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hh : addRow (polynomialScalarRow o Q) P ((fun i => c.symm (x.1.1 i)),x.2)=0 := by
      rw [addRow_apply,hscalar]
      change (∑ i,fullBiformScalarProduct (Q i) (x.1.1 i))+
        (∑ k,fullBiformScalarProduct (x.1.2 k) (E k))+P x.2=0 at hx
      simpa only [Finset.sum_empty,Finset.univ_eq_empty,add_zero] using hx
    have hz := hi (hh.trans (map_zero _).symm)
    apply Prod.ext
    · apply Prod.ext
      · funext i
        have hz' := congrArg (fun y : (Fin r → Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s) × V => y.1 i) hz
        change c.symm (x.1.1 i) = 0 at hz'
        change x.1.1 i = 0
        apply c.symm.injective
        simpa only [map_zero] using hz'
      · exact Subsingleton.elim _ _
    · have hh := congrArg (fun y : (Fin r → Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s) × V => y.2) hz
      change x.2 = 0
      exact hh
  rw [hker]
  refine le_antisymm bot_le ?_
  rintro _ ⟨a,rfl⟩
  have hh := LinearMap.congr_fun (bilinearKoszulRow_constants fullBiformScalarProduct Q E P) a
  rw [←hker]
  exact hh

end Froberg
