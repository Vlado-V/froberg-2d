import Froberg.PreparedPrivateFourthWitness
import Froberg.EmptyPrivateRow
import Froberg.PreparedPrivateFinite

noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem private_small_reduction_open_of_core_witnesses {w v z d q t c b₂ H : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X}
    [Module.Finite K (Space (v+v+z) d q J counts (constrainedOutputs T))]
    [LinearOrder (Label q J counts)]
    (hd : 3≤d) (hodd : d%2=1) (hv : 0<v)
    (hJ : ∀ j∈J,2≤j) (hdegree : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hcover : ∀ r,0<r → r≤d → r%2=0 → r∈J)
    (b₄ : ℕ)
    (hquad : QuadraticRowCapacity (v+v) d q b₂ J counts (constrainedOutputs T))
    (hfourth : 4∈J → FourthRowCapacity w v d q b₄ J counts T)
    (hprojected : b₄*(d-4+1).choose (d-4)≤oddOutputDimension w 4-
      finrank K (homogeneousSubmodule (Fin w × Bool) K 3))
    (hempty : ∀ R : J,R.val≠2 → R.val≠4 → counts R.val=0)
    (hemptyRow : ∀ R : J,R.val≠2 → R.val≠4 →
      ∃ p : Space (v+v) d q J counts (constrainedOutputs T),
        (row (fun _ _ => inf_le_left) R p).ker=(rowConstants (fun _ _ => inf_le_left) R p).range)
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
    by_cases hfour : r=4
    · subst r
      have hRd : 4<d := by have := hdegree 4 hr; have := heven 4 hr; omega
      have hrel : ∀ i,b₄*(d-4+1).choose (d-4)≤oddOutputDimension w 4-
          finrank K (privateOutputMatrix (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K 3))
            (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K 4)) (l i)).range := by
        intro i
        apply hprojected.trans
        apply Nat.sub_le_sub_left
        simpa only [Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] using
          LinearMap.finrank_range_le
            (privateOutputMatrix (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K 3))
              (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K 4)) (l i))
      simpa only [privatePowerBiform_val] using exists_fourth_private_row_parameter hr hd hRd
        (hfourth hr) (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K 3))
        (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K 4)) l hl ι hrel ell hell
    · cases r with
      | zero => have := hJ 0 hr; omega
      | succ R =>
        change R+1≠2 at hne
        have hR : 2≤R := by have := hJ (R+1) hr; omega
        have hRd : R+1<d := by have := hdegree (R+1) hr; have := heven (R+1) hr; omega
        obtain ⟨p,hp⟩ := hemptyRow ⟨R+1,hr⟩ hne hfour
        refine ⟨coreExtension z p,?_⟩
        simpa only [privatePowerBiform_val] using empty_private_row_exact hd hR hRd hr hO hdegree
          (hempty ⟨R+1,hr⟩ hne hfour)
          (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K R))
          (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K (R+1))) l hl ι p hp ell hell
  · intro R hRd hR2d hRe
    obtain ⟨p,hp⟩ := hprod R hRd hR2d hRe
    exact ⟨coreExtension z p,private_product_extension p hp⟩
  · obtain ⟨p,hp⟩ := hprod (d+1) (by omega) (by omega) (by omega)
    refine ⟨coreExtension z p,?_⟩
    exact private_top_core_injective hd hO hdegree
      (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K d))
      (Module.finBasis K (homogeneousSubmodule (Fin w × Bool) K (d+1))) l hl ι p hp

end Froberg.PreparedParameters
