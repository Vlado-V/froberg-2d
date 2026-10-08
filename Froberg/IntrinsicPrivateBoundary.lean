import Froberg.PreparedPrivateRowOpen
import Froberg.PrivateBoundaryRemoval

/-! Constant private-private boundaries in the actual intrinsic coefficient
space, with an explicit finite matrix parameterization in every characteristic. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {σ : Type*} [Fintype σ]
variable {n d b : ℕ}

def intrinsicPrivateBoundary (P : Fin b → FullBiform K σ n 1 (d-1)) :
    (Fin b → Fin b → K) →ₗ[K] (Fin b → FullBiform K σ n 1 (d-1)) where
  toFun C i := (∑ j,C i j • P j)-(∑ j,C j i • P j)
  map_add' C D := by
    funext i
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
    abel
  map_smul' c C := by
    funext i
    simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,smul_sub,RingHom.id_apply,smul_eq_mul]

@[simp] theorem intrinsicPrivateBoundary_val (P : Fin b → FullBiform K σ n 1 (d-1))
    (C : Fin b → Fin b → K) (i : Fin b) :
    (intrinsicPrivateBoundary P C i).val=matrixBoundary (fun j => (P j).val) C i := by
  simp only [intrinsicPrivateBoundary,LinearMap.coe_mk,AddHom.coe_mk,
    matrixBoundary,matrixCombination,Pi.sub_apply,Submodule.coe_sub,Submodule.coe_sum,Submodule.coe_smul]

 theorem intrinsicPrivateBoundary_cycle (P : Fin b → FullBiform K σ n 1 (d-1)) :
    (PreparedParameters.privateRowMap (d := d) (fun i => (P i).val) 2).comp
      (intrinsicPrivateBoundary P)=0 := by
  apply LinearMap.ext
  intro C
  change (∑ i,(P i).val*(intrinsicPrivateBoundary P C i).val)=0
  simp only [intrinsicPrivateBoundary_val]
  exact matrixBoundary_cycle (fun i => (P i).val) C

 theorem intrinsicPrivateBoundary_mem_of_polynomial
    (P : Fin b → FullBiform K σ n 1 (d-1))
    (u : Fin b → FullBiform K σ n 1 (d-1))
    (hu : (fun i => (u i).val)∈Submodule.span K (Set.range (koszulVector (fun i => (P i).val)))) :
    u∈(intrinsicPrivateBoundary P).range := by
  obtain ⟨C,hC⟩ := exists_matrixBoundary_of_mem_koszul (fun i => (P i).val) (fun i => (u i).val) hu
  refine ⟨C,?_⟩
  funext i
  apply Subtype.ext
  rw [intrinsicPrivateBoundary_val]
  exact congrFun hC i

 theorem addRow_exact_of_boundary_separation
    {A B U Z V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] [AddCommGroup Z] [Module K Z] [AddCommGroup V] [Module K V]
    (F : A →ₗ[K] V) (P : B →ₗ[K] V) (C : U →ₗ[K] A) (D : Z →ₗ[K] B)
    (hF : F.ker=C.range) (hPD : P.comp D=0)
    (hsep : ∀ a b,F a+P b=0 → b∈D.range) :
    (addRow F P).ker=(C.prodMap D).range := by
  apply le_antisymm
  · rintro ⟨a,b⟩ hab
    obtain ⟨z,rfl⟩ := hsep a b hab
    have hz : P (D z)=0 := LinearMap.congr_fun hPD z
    have ha : a∈F.ker := by
      change F a=0
      change F a+P (D z)=0 at hab
      simpa only [hz,add_zero] using hab
    rw [hF] at ha
    obtain ⟨c,rfl⟩ := ha
    exact ⟨(c,z),rfl⟩
  · rintro _ ⟨⟨c,z⟩,rfl⟩
    have hc : F (C c)=0 := hF.ge ⟨c,rfl⟩
    have hz : P (D z)=0 := LinearMap.congr_fun hPD z
    change F (C c)+P (D z)=0
    rw [hc,hz,add_zero]

end Froberg
