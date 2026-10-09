module

public import Froberg.DetectedTensorProducts
public import Froberg.IntrinsicBiformRow
public import Froberg.BiformOutputConstraint

@[expose] public section

/-! Detected tensor products give actual biforms of the prescribed output
and scalar degrees, retaining both gradings in the separation witness. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h n j t m : ℕ}

theorem exists_detected_biform_family
    (o : ι → Forms K h j) (T : Poly K h →ₗ[K] X)
    (ho : LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)))
    (C P Q : Submodule K (Poly K n)) (hCt : C ≤ Forms K n t)
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCP : C*C ≤ P) (hPQ : Disjoint P Q)
    (hm : m ≤ Fintype.card ι * (finrank K C / 2)) :
    ∃ F : Fin m → FullBiform K (Fin h) n j t,
      LinearIndependent K (fun p =>
        TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ
          (biformOutputMap T (pairProducts (fun i => (F i).val) p))) := by
  classical
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hCt
  let o' : ι → Poly K h := fun i => (o i).val
  obtain ⟨q,hq,hp⟩ := exists_detected_separated_family o' T ho C P Q hC hCP hPQ hm
  let e := tensorEquivSum K (Fin h) (Fin n) K
  have hOh : Submodule.span K (Set.range o') ≤ Forms K h j :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact (o i).property)
  have hbiform (i : Fin m) : e (q i) ∈ FullBiform K (Fin h) n j t := by
    have hi : e (q i) ∈ biformImage (Submodule.span K (Set.range o')) C :=
      ⟨q i,hq i,rfl⟩
    exact mem_biformImage_of_homogeneous
      (biformImage_homogeneous _ _ hOh hCt hi)
      (biformImage_output_weight _ _ hOh hi)
  let F : Fin m → FullBiform K (Fin h) n j t := fun i => ⟨e (q i),hbiform i⟩
  refine ⟨F,?_⟩
  convert hp using 1
  funext p
  induction p using Sym2.inductionOn with
  | _ i k =>
    simp only [pairProducts_mk]
    change TensorProduct.map (LinearMap.id : X →ₗ[K] X) Q.mkQ
      (biformOutputMap T (e (q i)*e (q k)))=TensorProduct.map T Q.mkQ (q i*q k)
    rw [←map_mul]
    simp only [biformOutputMap,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
      e,AlgEquiv.symm_apply_apply,TensorProduct.map_map,LinearMap.id_comp,LinearMap.comp_id]

end Froberg
