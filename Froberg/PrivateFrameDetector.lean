import Froberg.PrivateFrameModel
import Froberg.BiformVectorDetector
import Froberg.FramedPreparedParameters

/-! The private-frame quotient detector acts on the literal polynomial ring.
Its action on quadratic products agrees with the finite coordinate maps. -/
noncomputable section
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K] {h H c : ℕ}

def quadraticPolynomialDetector (L : Forms K h 2 →ₗ[K] (Fin c → K)) :
    Poly K h →ₗ[K] (Fin c → K) :=
  L.comp ((homogeneousComponent 2).codRestrict (Forms K h 2)
    (fun p => homogeneousComponent_isHomogeneous 2 p))

@[simp] theorem quadraticPolynomialDetector_form
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) (f : Forms K h 2) :
    quadraticPolynomialDetector L f.val=L f := by
  change L ⟨homogeneousComponent 2 f.val,_⟩=L f
  congr 1
  exact Subtype.ext (homogeneousComponent_eq_self f.property)

theorem outputCombination_equiv_basis
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (v : Fin h → K) :
    outputCombination (fun j => (e (Pi.single j 1)).val) v=(e v).val := by
  classical
  have hv : v=∑ j,v j • Pi.single j 1 := by
    funext j
    simp [Pi.single_apply]
  calc
    _ = (e (∑ j,v j • Pi.single j 1)).val := by
      simp only [map_sum,map_smul,Submodule.coe_sum,Submodule.coe_smul,
        outputCombination,LinearMap.coe_mk,AddHom.coe_mk]
    _ = (e v).val := by rw [←hv]

 theorem quadraticPolynomialDetector_private_column
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1)
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) (w : Fin h → K) (j : Fin h) :
    quadraticPolynomialDetector L
      (outputCombination (fun k => (e (Pi.single k 1)).val) w*(e (Pi.single j 1)).val)=
      ((L.comp (mulForm (e w))).comp e.toLinearMap) (Pi.single j 1) := by
  rw [outputCombination_equiv_basis]
  exact quadraticPolynomialDetector_form L (mulForm (e w) (e (Pi.single j 1)))

 theorem quadraticPolynomialDetector_frame
    (frame : Fin H → Forms K h 2)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL : L.ker=Submodule.span K (Set.range frame)) :
    outputFrameSpace frame≤(quadraticPolynomialDetector L).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change quadraticPolynomialDetector L (frame i).val=0
  rw [quadraticPolynomialDetector_form]
  apply LinearMap.mem_ker.mp
  rw [hL]
  exact Submodule.subset_span ⟨i,rfl⟩

 theorem quadraticPolynomialDetector_biform_frame {n s : ℕ}
    (frame : Fin H → Forms K h 2)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL : L.ker=Submodule.span K (Set.range frame))
    {f : MvPolynomial (Fin h ⊕ Fin n) K}
    (hf : f∈biformImage (outputFrameSpace frame) (Forms K n s)) :
    biformVectorDetector (quadraticPolynomialDetector L) f=0 :=
  biformVectorDetector_eq_zero _ _ _ (quadraticPolynomialDetector_frame frame L hL) hf

end Froberg
