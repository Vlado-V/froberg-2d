import Froberg.PreparedProductBiform
import Froberg.FirstPrivateIntrinsicRow
import Froberg.IntrinsicPrivateBoundary

/-! The first private row has precisely the ordinary scalar-layer constants
and the genuine private-private constants, in the literal prepared family. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z d q b h c : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_first_core_row_exact
    (hd : 3≤d) (h2J : 2∈J)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (bo : Basis (Fin h) K (homogeneousSubmodule σ K 1))
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (w : Fin b → Fin h → K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=A i (Pi.single j 1))
    (hker : (privatePolynomialMap (a := a) (s := d-1) ι A).ker=
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := d-1) ι w))))
    (P : Fin b → FullBiform K σ (a+z) 1 (d-1))
    (hP : ∀ i,(P i).val=rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))
    (p₀ : Space a d q J counts O)
    (hE : ∀ i,biformVectorDetector T (layers (coreExtension z p₀) 2 i)=0)
    (hprod : ProductRows.multiplication counts (layers (coreExtension z p₀)) J 2=0)
    (hrow : (row hO ⟨2,h2J⟩ (coreExtension z p₀)).ker=
      (rowConstants hO ⟨2,h2J⟩ (coreExtension z p₀)).range) :
    (privateAugmentedRow hO ⟨2,h2J⟩ (coreExtension z p₀) (fun i => (P i).val)).ker=
      ((rowConstants hO ⟨2,h2J⟩ (coreExtension z p₀)).prodMap (intrinsicPrivateBoundary P)).range := by
  classical
  apply addRow_exact_of_boundary_separation _ _ _ _ hrow (intrinsicPrivateBoundary_cycle P)
  intro x u hrel
  let f := Fintype.equivFin (Label q J counts)
  have hscalar :
      (∑ i : Fin (Fintype.card (Label q J counts)),
        rename Sum.inr (rename (Fin.castAdd z) (p₀.1 (f.symm i)).val)*
          (x.1.1 (f.symm i)).val)=
      ∑ i : Label q J counts,rename Sum.inr (rename (Fin.castAdd z) (p₀.1 i).val)*(x.1.1 i).val := by
    exact Fintype.sum_equiv f.symm _ _ (fun i => rfl)
  have hraw := first_private_intrinsic_row hd bo T w ι A hA hker
    (fun i => p₀.1 (f.symm i)) (layers (coreExtension z p₀) 2) hE
    (fun i => x.1.1 (f.symm i)) x.1.2 u
  have hz :
      (∑ i,rename Sum.inr (rename (Fin.castAdd z) (p₀.1 (f.symm i)).val)*(x.1.1 (f.symm i)).val)+
      (∑ i,layers (coreExtension z p₀) 2 i*rename Sum.inr (x.1.2 i).val)+
      (∑ i,(rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
        rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))*(u i).val)=0 := by
    rw [hscalar]
    have hQ (i : Label q J counts) : (scalarMap i (coreExtension z p₀)).val=
      rename (Fin.castAdd z) (p₀.1 i).val := rfl
    simp only [row,bilinearKoszulRow,LinearMap.coe_mk,AddHom.coe_mk,
      fullBiformScalarProduct_apply,privateRowMap] at hrel
    have hnew (i) : (intrinsicLayerMap hO ⟨2,h2J⟩ i (coreExtension z p₀)).val=
        layers (coreExtension z p₀) 2 i := layerMap_apply _ _ _
    simp only [hnew] at hrel
    simpa only [hQ,hP,hprod,LinearMap.zero_apply,add_zero,mul_comm] using hrel
  have hu := (hraw hz).1
  apply intrinsicPrivateBoundary_mem_of_polynomial P u
  simpa only [hP] using hu

end Froberg.PreparedParameters
