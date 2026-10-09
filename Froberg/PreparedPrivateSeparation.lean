module

public import Froberg.PreparedProductBiform
public import Froberg.PreparedPrivateRowOpen
public import Froberg.PrivateIntrinsicSeparation

@[expose] public section

/-! The literal sparse witness, after adjoining private variables, separates
the private coefficient block in the common prepared parameter space. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z d q b R hi ho : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_core_row_separation
    (hd : 3≤d) (hR : 2≤R) (hRd : R+1≤d) (hRJ : R+1∈J)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d)
    (bi : Basis (Fin hi) K (homogeneousSubmodule σ K R))
    (bo : Basis (Fin ho) K (homogeneousSubmodule σ K (R+1)))
    (w : Fin b → homogeneousSubmodule σ K 1) (hw : ∀ i,w i≠0)
    (ι : Fin b ↪ Fin z)
    (e : Fin (counts (R+1)) → Fin a →₀ ℕ)
    (v : Fin (counts (R+1)) → Fin ho → K)
    (hproj : ∀ l c,c≤1 → ∀ p : Fin (counts (R+1)) → Forms K a c,
      (∀ α,sparseOutputCoefficient e v p α∈(privateOutputMatrix bi bo (w l)).range) → p=0)
    (p₀ : Space a d q J counts O)
    (hE : ∀ i,layers p₀ (R+1) i=attachedPolynomialFamily (fun j => (bo j).val) e v i) :
    let p := coreExtension z p₀
    let P := fun i => rename Sum.inl (w i).val*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K))
    ∀ x u,row hO ⟨R+1,hRJ⟩ p x+privateRowMap (d := d) P (R+1) u=0 → u=0 := by
  classical
  dsimp only
  intro x u hrel
  let f := Fintype.equivFin (Label q J counts)
  let C := ProductRows.multiplication counts (layers p₀) J (R+1) x.2
  have hC : C∈FullBiform K σ a (R+1) (2*d-(R+1)) := by
    apply ProductRows.multiplication_range_full_biform (layers p₀) (by omega)
      (fun j hj i => (homogeneousLayerMap hO hJ j i p₀).property)
      (fun j hj i => biformImage_output_weight _ _ (hO j hj) (by
        change layers p₀ j i∈biformImage (O j) (Forms K a (d-j))
        simpa only [layers,dif_pos hj] using (p₀.2 ⟨j,hj⟩ i).property))
    exact ⟨x.2,rfl⟩
  have hraw := private_intrinsic_row_zero hd hR hRd bi bo w hw ι e v hproj
    (fun i => p₀.1 (f.symm i)) (fun i => x.1.1 (f.symm i)) x.1.2
    (⟨C,hC⟩ : FullBiform K σ a (R+1) (2*d-(R+1))) u
  apply hraw
  have hscalar :
      (∑ i : Fin (Fintype.card (Label q J counts)),
        rename Sum.inr (rename (Fin.castAdd z) (p₀.1 (f.symm i)).val)*
          (x.1.1 (f.symm i)).val)=
      ∑ i : Label q J counts,rename Sum.inr (rename (Fin.castAdd z) (p₀.1 i).val)*(x.1.1 i).val := by
    exact Fintype.sum_equiv f.symm _ _ (fun i => rfl)
  have hnew : ∀ i,(intrinsicLayerMap hO ⟨R+1,hRJ⟩ i (coreExtension z p₀)).val=
      rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily (fun j => (bo j).val) e v i) := by
    intro i
    change layers (coreExtension z p₀) (R+1) i=_
    rw [coreExtension_layers]
    dsimp only
    rw [hE]
  have hprod := LinearMap.congr_fun (coreExtension_products (z := z) p₀ (R+1)) x.2
  change ProductRows.multiplication counts (layers (coreExtension z p₀)) J (R+1) x.2=
    rename (Sum.map id (Fin.castAdd z)) C at hprod
  have hQ (i : Label q J counts) : (scalarMap i (coreExtension z p₀)).val=
    rename (Fin.castAdd z) (p₀.1 i).val := rfl
  simp only [row,bilinearKoszulRow,LinearMap.coe_mk,AddHom.coe_mk,
    fullBiformScalarProduct_apply,privateRowMap] at hrel
  simp only [hQ,hnew,hprod] at hrel
  rw [hscalar]
  simpa only [mul_comm] using hrel

end Froberg.PreparedParameters
