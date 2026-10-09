module

public import Froberg.PrivateSmallFinite
public import Froberg.PreparedLateMiddleSmallReduction
public import Froberg.PreparedPrivateProjectedCapacity
public import Froberg.LatePreparedQuadraticCapacity

@[expose] public section

/-! Actual private opens in odd degrees five and seven, with the detector
and private model chosen after the scalar threshold. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter PrivateColumns
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_middle_private_reduction_open_uniform {d : ℕ}
    (hd : 5≤d) (hd8 : d≤8) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w →
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      T 4=0 →
        ∀ (t c H : ℕ)
          (bo : Basis (Fin H) K (homogeneousSubmodule (Fin w × Bool) K 1))
          (l : Fin t → homogeneousSubmodule (Fin w × Bool) K 1),
        (∀ i,l i≠0) →
        ∀ (ι : Fin t ↪ Fin z)
          (L : MvPolynomial (Fin w × Bool) K →ₗ[K] (Fin c → K)),
        constrainedOutputs T 2≤L.ker →
        ∀ A : Fin t → (Fin H → K) →ₗ[K] (Fin c → K),
        (∀ i j,L ((l i).val*(bo j).val)=A i (Pi.single j 1)) →
        (privatePolynomialMap (a := v+v) (s := d-1) ι A).ker=
          Submodule.span K (Set.range (koszulVector
            (privateGenerator (a := v+v) (s := d-1) ι (fun i => bo.equivFun (l i))))) →
        let S := Space (v+v+z) d (upperCount (v+v+z) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
        ∃ D : MvPolynomial (Fin (finrank K S)) K,
          (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
          ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
            PrivatePositiveReduction p (privatePowerBiform (a := v+v) (d := d) l ι) := by
  classical
  have h4 : 4∈allEvenIndices d := mem_allEvenIndices.mpr ⟨by omega,by omega,by decide⟩
  have h4a : 4∈activeEvenIndices d := by
    simp [activeEvenIndices,hd8,show 4<d by omega]
  filter_upwards [eventually_actual_middle_small_witnesses_shift_late_output (K := K) hd hd8,
    eventually_counted_fourth_row_capacity_shift_late_output (K := K) hd hd8,
    eventually_actual_quadratic_capacity_shift_late (K := K) (by omega : 3≤d),
    eventually_all_private_projected_capacity (K := K) (by omega : 3≤d)]
      with w hmiddle hfourth hquadratic hprojected
  intro hdiv z extra e he
  have hproj := hprojected ⟨4,h4⟩ (by change (4 : ℕ)≠2; omega)
  simp only [if_pos h4a] at hproj
  filter_upwards [hmiddle hdiv z extra e he,
    hfourth z extra e he,hquadratic z extra e he,
    eventually_gt_atTop (0 : ℕ)] with v hmv hfv hqv hv
  intro X _ _ _ T hX hO hT t c H bo l hl ι L hOL A hA hprivate
  have hmv := hmv X T hX hO hT
  have hfv := hfv X T hX hT
  have hqv := hqv X T hO
  let counts := allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)
  let I := Label (upperCount (v+v+z) d) (allEvenIndices d) counts
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  exact private_small_reduction_open_of_core_witnesses (by omega) hodd hv
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun r hr hrd hre => mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩)
    (sparseBlockCount ((101/100 : ℝ)*higherCountGamma d 4) 4 (d-4) w)
    hqv (fun _ => hfv) hproj
    (fun R h2 h4 => allEvenCount_off_two_four_small hd8 _ _ _ h2 h4)
    (fun R _ _ => by obtain ⟨p,_,hp⟩ := hmv.1 R; exact ⟨p,hp⟩)
    hmv.2 bo l hl ι L hOL A hA hprivate

end Froberg.PreparedParameters
