module

public import Froberg.PreparedPrivateFinite
public import Froberg.PreparedPrivateProjectedCapacity
public import Froberg.UniformShiftedPreparedCapacities

@[expose] public section

/-! The literal rounded counts at the full scalar dimension admit a common
private positive-row reduction open. The remaining hypotheses specify the
private quadratic model; all numerical row capacities are discharged. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter PrivateColumns
variable {K : Type} [Field K] [Infinite K]

local instance privateConstrainedSpaceFinite {X : Type*} [AddCommGroup X] [Module K X]
    {w n d q : ℕ} {J : Finset ℕ}
    {counts : ℕ → ℕ} (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) :
    Module.Finite K (Space n d q J counts (constrainedOutputs T)) :=
  finite_space (fun _ _ => inf_le_left)

theorem eventually_actual_private_reduction_open {d : ℕ} (hd : 9≤d) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
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
  filter_upwards [eventually_actual_even_capacities_shift_uniform (K := K) hd,
    eventually_all_private_projected_capacity (K := K) (by omega : 3≤d)] with w hw hprojected
  intro X _ _ _ T hX hO hT z extra e he
  filter_upwards [hw X T hX hO hT z extra e he,eventually_gt_atTop 0] with v hv hvpos
  intro t c H bo l hl ι L hOL A hA hprivate
  let counts := allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)
  let I := Label (upperCount (v+v+z) d) (allEvenIndices d) counts
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  exact private_finite_reduction_open (by omega) hodd hvpos
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun r hr hrd hre => mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩)
    (fun R => if R∈activeEvenIndices d then
      sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R) R (d-R) w else 0)
    hv.1 hv.2.1 hprojected (fun R _ _ _ => hv.2.2 R) bo l hl ι L hOL A hA hprivate

end Froberg.PreparedParameters
