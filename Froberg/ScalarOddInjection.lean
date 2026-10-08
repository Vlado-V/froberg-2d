import Froberg.PrefixLowerInjection
import Froberg.IntrinsicBiformRow
import Froberg.ScalarVectorInjection
import Froberg.OddBiformDecomposition
import Froberg.WeightedTriangularProducts
import Froberg.MixedAmbientCorrection

/-! A scalar tuple injective through the strict prefix has no relation with
odd homogeneous biform coefficients. Every odd output layer has smaller
scalar degree, so the same tuple controls all layers. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial AttachedMultiplication TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d t s r : ℕ}

def fullBiformScalarRow (Q : Fin r → Forms K m d) :
    (Fin r → FullBiform K (Fin h) m t s) →ₗ[K] MvPolynomial (Fin h ⊕ Fin m) K :=
  ∑ i,(fullBiformScalarProduct (Q i)).comp (LinearMap.proj i)

theorem fullBiform_scalar_injective (Q : Fin r → Forms K m d)
    (hQ : Function.Injective (prefixMultiplication Q s)) :
    Function.Injective (fullBiformScalarRow (h := h) (t := t) (s := s) Q) := by
  classical
  let b := Module.finBasis K (Forms K h t)
  let o := fun i => (b i).val
  have ho : LinearIndependent K o := b.linearIndependent.map'
    (Forms K h t).subtype (Submodule.ker_subtype _)
  have hdeg : ∀ i,(o i).IsHomogeneous t := fun i => (b i).property
  let c : (Fin (finrank K (Forms K h t)) → Forms K m s) ≃ₗ[K]
      FullBiform K (Fin h) m t s := fullBiformCoordinates o ho hdeg
  have hi := (polynomialFormVector_injective o ho).comp
    (vector_scalar_injective_of_prefix (J := Fin (finrank K (Forms K h t))) Q hQ)
  have hscalar (a : Fin r → FullBiform K (Fin h) m t s) :
      polynomialScalarRow o Q (fun i => c.symm (a i))=
        fullBiformScalarRow Q a := by
    unfold polynomialScalarRow
    rw [LinearMap.comp_apply,BilinearScalarFamily.multiplication_apply,map_sum]
    simp only [fullBiformScalarRow,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro i _
    change coordinateScalarProduct o (Q i) (c.symm (a i))=_
    rw [coordinateScalarProduct_apply,fullBiformScalarProduct_apply]
    congr 1
    exact congrArg Subtype.val (c.apply_symm_apply (a i))
  intro a a' haa
  have hh : polynomialScalarRow o Q (fun i => c.symm (a i))=
      polynomialScalarRow o Q (fun i => c.symm (a' i)) := by rw [hscalar,hscalar,haa]
  have hz := hi hh
  funext i
  exact c.symm.injective (congrFun hz i)

theorem scalar_odd_relation_zero (hm : 0 < m) (Q : Fin r → Forms K m d)
    (hQ : Function.Injective (prefixMultiplication Q (d-1)))
    (v : Fin r → biformParitySpace K h m d 1)
    (hv : (∑ i,rename Sum.inr (Q i).val*(v i).val)=0) : v=0 := by
  have hcomponent (a : Fin ((d+1)/2)) (i : Fin r) :
      oddBiformCoordinatesEquiv (v i) a=0 := by
    let t := 2*a.val+1
    let s := d-t
    have ht : t ≤ d := by dsimp [t];omega
    have hsmall : s ≤ d-1 := by dsimp [s,t];omega
    let c : Fin r → FullBiform K (Fin h) m t s := fun i =>
      ⟨sumBiformMap (oddBiformCoordinatesEquiv (v i) a),sumBiformMap_range.le ⟨_,rfl⟩⟩
    have hc : fullBiformScalarRow Q c=0 := by
      have he := congrArg (weightedHomogeneousComponent (blockWeight h m) t) hv
      simp only [map_sum,map_zero] at he
      simp only [fullBiformScalarRow,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,fullBiformScalarProduct_apply]
      change (∑ i,rename Sum.inr (Q i).val*sumBiformMap (oddBiformCoordinatesEquiv (v i) a))=0
      convert he using 1
      apply Finset.sum_congr rfl
      intro j _
      rw [oddBiformCoordinatesEquiv_component]
      have hq : (rename Sum.inr (Q j).val).IsWeightedHomogeneous (blockWeight h m) 0 :=
        by simpa only [scalarEvenBiform_val] using scalarEvenBiform_weighted (h := h) (Q j)
      have hx := weighted_component_mul_homogeneous (blockWeight h m) (v j).val
        (rename Sum.inr (Q j).val) t 0 hq
      simpa only [Nat.add_zero,mul_comm,t,Nat.mul_comm] using hx.symm
    have hc0 := fullBiform_scalar_injective (t := t) Q (prefix_lower_injective hm hsmall Q hQ)
      (hc.trans (map_zero _).symm)
    apply sumBiformMap_injective
    have hi := congrArg (fun f : Fin r → FullBiform K (Fin h) m t s => (f i).val) hc0
    change sumBiformMap (oddBiformCoordinatesEquiv (v i) a)=0 at hi
    simpa only [map_zero] using hi
  funext i
  let e := oddBiformCoordinatesEquiv (K := K) (h := h) (m := m) (d := d)
  have hvi : e (v i)=0 := funext (fun a => hcomponent a i)
  exact e.injective (hvi.trans e.map_zero.symm)

end Froberg
