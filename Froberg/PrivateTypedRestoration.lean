import Froberg.PreparedPrivateWitnessOpen
import Froberg.PreparedRestorationOpen
import Froberg.SplitRestorationOpen

/-! The literal private reduction in fixed even and odd homogeneous
coefficient spaces, ready for polynomial-complex openness. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {σ : Type*} [Fintype σ]

def oddRestorationSpace (w : σ → ℕ) (d : ℕ) : Submodule K (MvPolynomial σ K) :=
  homogeneousSubmodule σ K d⊓weightedParitySpace w 1

instance oddRestorationSpace_finite (w : σ → ℕ) (d : ℕ) :
    Module.Finite K (oddRestorationSpace (K := K) w d) := by
  letI : Module.Finite K (homogeneousSubmodule σ K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ d)
  exact Submodule.finiteDimensional_of_le inf_le_left

namespace PreparedParameters
variable {n d q r b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def privateOddEmbed (hd : 0<d) : FullBiform K σ n 1 (d-1) →ₗ[K]
    oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d where
  toFun P := ⟨P.val,by
    have hh := biformImage_homogeneous _ _ le_rfl le_rfl P.property
    change P.val.IsHomogeneous (1+(d-1)) at hh
    change P.val.IsHomogeneous d
    simpa only [show 1+(d-1)=d by omega] using hh,
    IsWeightedHomogeneous.mem_parity (biformImage_output_weight _ _ le_rfl P.property) rfl⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def pureOddEmbed (hd : d%2=1) : homogeneousSubmodule σ K d →ₗ[K]
    oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d where
  toFun U := ⟨rename Sum.inl U.val,U.property.rename_isHomogeneous,by
    apply IsWeightedHomogeneous.mem_parity (j := d) _ hd
    exact rename_weightedHomogeneous
      (⟨Sum.inl,Sum.inl_injective⟩ : σ ↪ σ ⊕ Fin n)
      (fun _ => 1) outputWeight (fun _ => rfl) U.property⟩
  map_add' U V := Subtype.ext (map_add (rename Sum.inl) U.val V.val)
  map_smul' c U := Subtype.ext (map_smul (rename Sum.inl) c U.val)

def privateOddFamily (hd : 0<d) (ho : d%2=1)
    (P : Fin b → FullBiform K σ n 1 (d-1))
    (U : Fin b → homogeneousSubmodule σ K d) :
    Fin b → oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d :=
  fun i => privateOddEmbed hd (P i)+pureOddEmbed ho (U i)

@[simp] theorem privateOddFamily_val (hd : 0<d) (ho : d%2=1)
    (P : Fin b → FullBiform K σ n 1 (d-1))
    (U : Fin b → homogeneousSubmodule σ K d) (i : Fin b) :
    (privateOddFamily hd ho P U i).val=(P i).val+rename Sum.inl (U i).val := rfl

theorem private_typed_reduction
    (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : Space n d q J counts O) (P : Fin b → FullBiform K σ n 1 (d-1))
    (hp : PrivatePositiveReduction p P)
    (U : Fin b → homogeneousSubmodule σ K d) (e : Fin r ≃ Label q J counts)
    (c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d)
    (v : Fin b → oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d)
    (hc : SplitRestoration.row (evenRestorationSpace outputWeight d).subtype
      (oddRestorationSpace outputWeight d).subtype (positiveWeightProjection outputWeight d)
      (fun i => evenGenerator hO hJ heven p (e i)) (privateOddFamily hd ho P U) (c,v)=0) :
    ∃ (M : Fin r → Fin r → K) (C : Fin b → Fin b → K)
      (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (e i))),
      c-coefficientBoundary (fun i => evenGenerator hO hJ heven p (e i)) M=z.val ∧
      v=coefficientBoundary (privateOddFamily hd ho P U) C := by
  classical
  let c' : Label q J counts → MvPolynomial (σ ⊕ Fin n) K := fun i => (c (e.symm i)).val
  have hsum : (∑ i,generator p i*c' i)=∑ i,generator p (e i)*(c i).val := by
    simpa only [c',Equiv.symm_apply_apply] using
      (e.sum_comp (fun i => generator p i*c' i)).symm
  obtain ⟨C,M,z,hv,hc',hzpos,hzweight⟩ := hp (fun i => rename Sum.inl (U i).val)
    (by
      intro i
      refine ⟨(U i).property.rename_isHomogeneous,?_⟩
      exact rename_weightedHomogeneous
        (⟨Sum.inl,Sum.inl_injective⟩ : σ ↪ σ ⊕ Fin n)
        (fun _ => 1) outputWeight (fun _ => rfl) (U i).property)
    c' (fun i => (v i).val) (fun i => (c (e.symm i)).property.1)
    (fun i => (v i).property.1)
    (fun i => (mem_weightedParitySpace_iff _ _ _).mp (c (e.symm i)).property.2)
    (fun i => (mem_weightedParitySpace_iff _ _ _).mp (v i).property.2) (by
      intro t ht htmax
      have hh := congrFun hc ⟨t,ht,htmax⟩
      change weightedHomogeneousComponent outputWeight t
        (∑ i,generator p (e i)*(c i).val)+weightedHomogeneousComponent outputWeight t
          (∑ i,((P i).val+rename Sum.inl (U i).val)*(v i).val)=0 at hh
      rw [map_add,hsum]
      exact hh)
  let z' : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d :=
    fun i => ⟨z (e i),(hzweight (e i)).1,
      IsWeightedHomogeneous.mem_parity (hzweight (e i)).2 rfl⟩
  refine ⟨fun i k => M (e i) (e k),C,⟨z',?_,?_⟩,?_,?_⟩
  · intro i hi
    apply Subtype.ext
    exact hzpos (e i) hi
  · intro i
    exact (hzweight (e i)).2
  · funext i
    apply Subtype.ext
    have hh := congrFun hc' (e i)
    simp only [Pi.sub_apply,c',Equiv.symm_apply_apply,matrixBoundary,matrixCombination] at hh
    simp only [Pi.sub_apply,coefficientBoundary,Submodule.coe_sub,Submodule.coe_sum,
      Submodule.coe_smul,evenGenerator,z']
    rw [e.sum_comp (fun k => M (e i) k • generator p k),
      e.sum_comp (fun k => M k (e i) • generator p k)]
    exact hh
  · funext i
    apply Subtype.ext
    have hh := congrFun hv i
    simpa only [coefficientBoundary,Submodule.coe_sub,Submodule.coe_sum,Submodule.coe_smul,
      privateOddFamily_val,matrixBoundary,matrixCombination,Pi.sub_apply] using hh

end PreparedParameters
end Froberg
