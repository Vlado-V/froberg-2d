module

public import Froberg.PrivateFiniteProducts
public import Froberg.PreparedActualSmallReduction
public import Froberg.SmallRenamedProducts
public import Froberg.LatePreparedQuadraticCapacity

@[expose] public section

/-! Actual cubic counts produce the private reduction open with the detector
and private model chosen after the scalar threshold. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter PrivateColumns
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_cubic_private_reduction_open_uniform :
    ∀ᶠ w : ℕ in atTop,
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 3*(2*(w : ℝ))^2*(n : ℝ)^(3-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount 3 (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension 3 (2*w) →
        ∀ (t c H : ℕ)
          (bo : Basis (Fin H) K (homogeneousSubmodule (Fin w × Bool) K 1))
          (l : Fin t → homogeneousSubmodule (Fin w × Bool) K 1),
        (∀ i,l i≠0) →
        ∀ (ι : Fin t ↪ Fin z)
          (L : MvPolynomial (Fin w × Bool) K →ₗ[K] (Fin c → K)),
        constrainedOutputs T 2≤L.ker →
        ∀ A : Fin t → (Fin H → K) →ₗ[K] (Fin c → K),
        (∀ i j,L ((l i).val*(bo j).val)=A i (Pi.single j 1)) →
        (privatePolynomialMap (a := v+v) (s := 3-1) ι A).ker=
          Submodule.span K (Set.range (koszulVector
            (privateGenerator (a := v+v) (s := 3-1) ι (fun i => bo.equivFun (l i))))) →
        let S := Space (v+v+z) 3 (upperCount (v+v+z) 3) (allEvenIndices 3)
          (allEvenCount 3 (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
        ∃ D : MvPolynomial (Fin (finrank K S)) K,
          (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
          ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
            PrivatePositiveReduction p (privatePowerBiform (a := v+v) (d := 3) l ι) := by
  classical
  filter_upwards [eventually_actual_quadratic_capacity_shift_late (K := K) (d := 3) (by omega),
    tendsto_twice_nat.eventually eventually_strong_cubic_diagonal_capacity_shift] with w hq hs
  intro z extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,
      (e n : ℝ)<countBeta 3*((2*w : ℕ):ℝ)^2*(n : ℝ)^(3-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  filter_upwards [hq z extra e he,
    tendsto_twice_nat.eventually (hs z extra),
    tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually hecast),
    eventually_gt_atTop (0 : ℕ)] with v hqv hsv hev hv
  intro X _ _ _ T hX hO t c H bo l hl ι L hOL A hA hprivate
  let counts := allEvenCount 3 (2*w) (v+v+z) (e (v+v+z)+extra)
  let I := Label (upperCount (v+v+z) 3) (allEvenIndices 3) counts
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hb : e (2*v+z)≤⌈countBeta 3*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)⌉₊ := by
    have he' : (e (2*v+z) : ℝ)<countBeta 3*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ) := by
      simpa only [show 3-2=1 by omega,pow_one] using hev
    exact_mod_cast he'.le.trans (Nat.le_ceil _)
  have hm : counts 2≤(2*((w+w)/2).choose 2-finrank K X)*((v+v)/2) := by
    have hc := (Nat.add_le_add_right hb extra).trans hsv
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices (d := 3) (by omega)),
      targetLayerCount,ite_true,two_mul,hX] using hc
  have hz : ∀ j∈allEvenIndices 3,j≠2 → counts j=0 :=
    fun j _ hj => allEvenCount_off_two_small (Or.inl rfl) _ _ _ hj
  obtain ⟨p,hp⟩ := exists_strong_cubic_product_parameter_equiv
    (q := upperCount (v+v+z) 3) (pairedScalarEquiv w).symm T hz hm
  have hrow : ∀ R : allEvenIndices 3,R.val=2 := by
    intro R
    have hr := mem_allEvenIndices.mp R.property
    omega
  exact private_finite_reduction_open_of_core_products (by omega) (by decide) hv
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun r hr hrd hre => mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩)
    (fun _ => 0) (hqv X T hO) (fun R hR => False.elim (hR (hrow R)))
    (fun R hR => False.elim (hR (hrow R))) (fun R _ _ _ => ⟨p,hp R⟩)
    bo l hl ι L hOL A hA hprivate

end Froberg.PreparedParameters
