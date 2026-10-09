module

public import Froberg.PositiveIntrinsicLayeredSlices
public import Froberg.OddAffineBottomDetection
public import Froberg.LayeredTargetDimension

@[expose] public section

/-! The actual common even-scalar family: C.15 and relative exactness
supply the dimension budget, and B.7 supplies the zero-bottom exclusion. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily QuotientCovectorKernel
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K] {h m d q f u e : ℕ}
variable {V₀ W₀ H : Type}
  [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
  [AddCommGroup W₀] [Module K W₀] [FiniteDimensional K W₀]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable
  (Q : Fin q → biformParitySpace K h m d 0)
  (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
  (E : Fin e → biformParitySpace K h m d 0)
local notation "V" => biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G
local notation "W" => biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G
local notation "WA" => biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G
local notation "μ" => oddBackgroundScalarProduct Q F G
local notation "μA" => LinearMap.comp (oddAmbientScalarProduct Q F G) (LinearEquiv.toLinearMap (scalarBiformEquiv (K := K) (h := h) (n := m) (d := d)))
local notation "π" => oddAmbientToFull Q F G
local notation "j" => finrank K W-e*finrank K V

theorem actual_odd_affine_slices (hh : 0  <  h) (hm : 0  <  m) (hd : Odd d)
    (ec : WA ≃ₗ[K] W₀ × H)
    (hw : ∀ v : biformParitySpace K h m (2*d) 1,
      v.val.IsWeightedHomogeneous (blockWeight h m) 1 →
        (ec ((ambientOddRelations Q F G).mkQ v)).2=0)
    (nu : Forms K m d →ₗ[K] V₀ →ₗ[K] W₀)
    (s₀ : ℕ → ℕ) (hs₀ : HasClosedKernelSlices nu s₀) (M : ℕ)
    (hmono : ∀ ell : W →ₗ[K] K,quotientSplitBottom ec π ell ≠ 0 →
      finrank K (relation nu (quotientSplitBottom ec π ell)).ker ≤ finrank K (relation μ ell).ker)
    (hgrowth : ∀ ell : W →ₗ[K] K,quotientSplitBottom ec π ell ≠ 0 →
      M*(finrank K (relation μ ell).ker-finrank K (relation nu (quotientSplitBottom ec π ell)).ker) ≤ 
        finrank K (BilinearImage.image (splitTargetHigherAction ec μA) (relation μ ell).ker))
    (P₀ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K)
    (hP₀ : ∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0)
    (hinj : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Injective (oddEvenRelativeMap Q F G (oddEvenAffineFamily E a)))
    (hupper : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Surjective (upperTargetMap (backgroundEnumeratedForms (Fin.append Q (oddEvenAffineFamily E a)) F G)))
    (slices : ℕ → ℕ) (hslices0 : j ≤ slices 0)
    (C L : ℕ) (loss : ℕ → ℕ)
    (hbase : ∀ k₀ : Fin (finrank K V₀+1),0 < s₀ k₀.val → s₀ k₀.val+C*k₀.val ≤ finrank K W₀)
    (hslices : ∀ r : Fin (finrank K V+1),0 < r.val → j ≤ slices r.val+loss r.val)
    (hC : L ≤ C) (hM : L ≤ M)
    (hloss : ∀ r : Fin (finrank K V+1),0 < r.val → loss r.val ≤ L*r.val/2)
    (hsmall : 2*(higherRelationCost d h u m+finrank K V+e)+1 ≤ L) :
    ∃ P₁ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K,
      (∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0) ∧
      ∀ a,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0 →
        eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 ∧
        HasClosedKernelSlices (targetPostcompose μ (oddEvenAffineRelations Q F G E a).mkQ) slices := by
  have hprod : ∀ p v,π (μA p v)=μ p v := by
    intro p v
    exact oddAmbientScalarProduct_toFull Q F G (scalarBiformEquiv p) v
  have hdim : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      finrank K (W ⧸ oddEvenAffineRelations Q F G E a) ≤ slices 0 := by
    intro a ha
    rw [oddEvenAffineRelations_finrank Q F G E a (hinj a ha)]
    exact hslices0
  have hb : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      ∀ ell : W →ₗ[K] K,oddEvenAffineRelations Q F G E a ≤ ell.ker →
        quotientSplitBottom ec π ell=0 → ell=0 := by
    intro a ha ell hA he
    exact odd_affine_bottom_detects Q F G E a ec hw (hupper a ha) ell hA he
  obtain ⟨a₀,ha₀⟩ := hP₀
  have hdim₀ := oddEvenAffineRelations_finrank Q F G E a₀ (hinj a₀ ha₀)
  have hambient := layered_target_dimension ec (odd_ambient_quotient_dimension hh hm hd Q F G)
    (oddEvenRelativeMap Q F G (oddEvenAffineFamily E a₀)) (hinj a₀ ha₀) hdim₀
  exact intrinsic_uniform_quotient_slices_positive μ nu
    (splitTargetBottomAction ec μA) (splitTargetHigherAction ec μA)
    (quotientSplitBottom ec π) (quotientSplitHigher ec π) (quotientSplitReconstruct ec π)
    (quotientSplit_reconstruct ec π (oddAmbientToFull_surjective Q F G))
    (quotientSplit_action_compat ec π μA μ hprod) s₀ hs₀ hmono hgrowth
    (fun i => oddBackgroundQuotientProduct Q F G (E i)) (oddEvenAffineRelations Q F G E)
    (oddEvenAffineRelations_generator_mem Q F G E) slices P₀ ⟨a₀,ha₀⟩ hdim hb
    C L j (higherRelationCost d h u m) loss hbase hambient hslices hC hM hloss hsmall

end Froberg
