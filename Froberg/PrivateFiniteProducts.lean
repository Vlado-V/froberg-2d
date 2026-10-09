module

public import Froberg.PreparedPrivateFinite

@[expose] public section

noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem private_finite_reduction_open_of_core_products {w v z d q t c b₂ H : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X}
    [Module.Finite K (Space (v+v+z) d q J counts (constrainedOutputs T))]
    [LinearOrder (Label q J counts)]
    (hd : 3≤d) (hodd : d%2=1) (hv : 0<v)
    (hJ : ∀ j∈J,2≤j) (hdegree : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hcover : ∀ r,0<r → r≤d → r%2=0 → r∈J)
    (b : ℕ → ℕ)
    (hquad : QuadraticRowCapacity (v+v) d q b₂ J counts (constrainedOutputs T))
    (hhigher : ∀ R : J,R.val≠2 → HigherRowCapacity w v d q (b R.val) J counts T R)
    (hprojected : ∀ R : J,R.val≠2 →
      b R.val*(d-R.val+1).choose (d-R.val)≤oddOutputDimension w R.val-
        finrank K (homogeneousSubmodule (Fin w × Bool) K (R.val-1)))
    (hprod : ∀ R,d<R → R≤2*d → R%2=0 →
      ∃ p : Space (v+v) d q J counts (constrainedOutputs T),
        Function.Injective (ProductRows.multiplication counts (layers p) J R))
    (bo : Basis (Fin H) K (homogeneousSubmodule (Fin w × Bool) K 1))
    (l : Fin t → homogeneousSubmodule (Fin w × Bool) K 1) (hl : ∀ i,l i≠0)
    (ι : Fin t ↪ Fin z)
    (L : MvPolynomial (Fin w × Bool) K →ₗ[K] (Fin c → K))
    (hOL : constrainedOutputs T 2≤L.ker)
    (A : Fin t → (Fin H → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,L ((l i).val*(bo j).val)=A i (Pi.single j 1))
    (hprivate : (privatePolynomialMap (a := v+v) (s := d-1) ι A).ker=
      Submodule.span K (Set.range (koszulVector
        (privateGenerator (a := v+v) (s := d-1) ι (fun i => bo.equivFun (l i)))))) :
    ∃ D : MvPolynomial (Fin (finrank K (Space (v+v+z) d q J counts (constrainedOutputs T)))) K,
      (∃ p : Space (v+v+z) d q J counts (constrainedOutputs T),
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        PrivatePositiveReduction p (privatePowerBiform (a := v+v) (d := d) l ι) := by
  classical
  let hO : ∀ j∈J,constrainedOutputs T j≤homogeneousSubmodule (Fin w × Bool) K j :=
    fun _ _ => inf_le_left
  obtain ⟨ell,hell⟩ := exists_two_core_linear_forms (K := K) (by omega : 2≤v+v)
  apply private_reduction_open_of_witnesses hd hodd hO hJ hdegree heven hcover
    (privatePowerBiform (a := v+v) (d := d) l ι)
  · obtain ⟨p,_,hp⟩ := exists_quadratic_private_row_parameter hd hO hJ hdegree
      (hcover 2 (by omega) (by omega) rfl) hquad bo L hOL
      (fun i => bo.equivFun (l i)) ι A (by simpa only [outputCombination_basis] using hA)
      hprivate (privatePowerBiform (a := v+v) (d := d) l ι)
      (by intro i; simp only [privatePowerBiform_val,outputCombination_basis]) ell hell
    exact ⟨p,hp⟩
  · rintro ⟨r,hr⟩ hne
    cases r with
    | zero => have := hJ 0 hr; omega
    | succ R =>
      change R+1≠2 at hne
      have hR : 2≤R := by have := hJ (R+1) hr; omega
      have hRd : R+1<d := by have := hdegree (R+1) hr; have := heven (R+1) hr; omega
      have hrel : ∀ i,b (R+1)*(d-(R+1)+1).choose (d-(R+1))≤oddOutputDimension w (R+1)-
          finrank K (privateOutputMatrix (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K R))
            (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K (R+1))) (l i)).range := by
        intro i
        apply (hprojected ⟨R+1,hr⟩ hne).trans
        apply Nat.sub_le_sub_left
        change _ ≤ finrank K (homogeneousSubmodule (Fin w × Bool) K (R+1-1))
        rw [Nat.add_sub_cancel]
        simpa only [Nat.add_sub_cancel,Module.finrank_pi,Fintype.card_fin,Module.finrank_self,
          mul_one] using LinearMap.finrank_range_le
            (privateOutputMatrix (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K R))
              (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K (R+1))) (l i))
      simpa only [privatePowerBiform_val] using exists_higher_private_row_parameter R hr hd hR hRd
        (hhigher ⟨R+1,hr⟩ hne) (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K R))
        (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K (R+1))) l hl ι hrel ell hell
  · intro R hRd hR2d hRe
    obtain ⟨p,hp⟩ := hprod R hRd hR2d hRe
    exact ⟨coreExtension z p,private_product_extension p hp⟩
  · obtain ⟨p,hp⟩ := hprod (d+1) (by omega) (by omega) (by omega)
    refine ⟨coreExtension z p,?_⟩
    exact private_top_core_injective hd hO hdegree
      (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K d))
      (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K (d+1))) l hl ι p hp

end Froberg.PreparedParameters
