module

public import Froberg.EvenAffineRelations
public import Froberg.PositiveIntrinsicLayeredSlices
public import Froberg.LayeredTargetDimension

@[expose] public section

/-! The finite C.4 scalar-open statement for the even-degree background.
All kernel and higher-image hypotheses are derived from actual graded actions. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates BilinearScalarFamily
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K] {h m d q f e : ℕ}
variable (hd3 : 3 ≤ d) (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
local notation "hdp" => Nat.le_trans (by decide : 1 ≤ 3) hd3
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "V" => EvenBackgroundSource hdp F
local notation "W" => EvenBackgroundTarget hdp Q F
local notation "ec" => oddTargetBaseEquiv hdp Q₀ F₁
  (fun i => scalarEvenBiform_weighted (h := h) (Q i))
  (fun i => oddLinearBiform_weighted hdp (F i))
local notation "mu" => evenBackgroundScalar hdp Q F
local notation "nu" => bottomCoordinateScalarAction hdp Q g
local notation "j" => finrank K W-e*finrank K V

theorem even_actual_affine_slices
    (s₀ : ℕ → ℕ) (hs₀ : HasClosedKernelSlices nu s₀) (M : ℕ)
    (hmid : ∀ (k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d), k%2=1 →
      OddScalarLayerProperty M (by omega : 1 ≤ k) hkd
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (E : Fin e → biformParitySpace K h m d 0)
    (P₀ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K)
    (hP₀ : ∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0)
    (hinj : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Injective (oddEvenRelativeMap Q₀ F₁ emptyOddFamily (oddEvenAffineFamily E a)))
    (hupper : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      Function.Surjective (upperTargetMap (backgroundEnumeratedForms
        (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ emptyOddFamily)))
    (slices : ℕ → ℕ) (hslices0 : j ≤ slices 0)
    (C L : ℕ) (loss : ℕ → ℕ)
    (hbase : ∀ k₀ : Fin (finrank K (OddBottomQuotient F)+1),0 < s₀ k₀.val →
      s₀ k₀.val+C*k₀.val ≤ finrank K (OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp)))
    (hslices : ∀ r : Fin (finrank K V+1),0 < r.val → j ≤ slices r.val+loss r.val)
    (hC : L ≤ C) (hM : L ≤ M)
    (hloss : ∀ r : Fin (finrank K V+1),0 < r.val → loss r.val ≤ L*r.val/2)
    (hsmall : 2*(finrank K V+e)+1 ≤ L) :
    ∃ P₁ : MvPolynomial (Fin (finrank K (Fin e → Forms K m d))) K,
      (∃ a : Fin e → Forms K m d,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0) ∧
      ∀ a,eval ((Module.finBasis K _).equivFun a) P₁ ≠ 0 →
        eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 ∧
        HasClosedKernelSlices
          (targetPostcompose mu (evenAffineRelations hdp Q F E a).mkQ) slices := by
  have hdim : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      finrank K (W ⧸ evenAffineRelations hdp Q F E a) ≤ slices 0 := by
    intro a ha
    rw [evenAffineRelations_finrank hdp Q F E a (hinj a ha)]
    exact hslices0
  have hb : ∀ a,eval ((Module.finBasis K _).equivFun a) P₀ ≠ 0 →
      ∀ ell : W →ₗ[K] K,evenAffineRelations hdp Q F E a ≤ ell.ker →
        splitTargetBottom ec ell=0 → ell=0 := by
    intro a ha ell hA hz
    exact even_affine_bottom_detects hdp Q F E a (hupper a ha) ell hA hz
  obtain ⟨a₀,ha₀⟩ := hP₀
  have hdim₀ := evenAffineRelations_finrank hdp Q F E a₀ (hinj a₀ ha₀)
  have hambient := layered_target_dimension (loss := 0) ec (Nat.le_refl (finrank K W))
    (evenRelativeFamily hdp Q F (oddEvenAffineFamily E a₀))
    (evenRelativeFamily_injective hdp Q F _ (hinj a₀ ha₀)) hdim₀
  exact intrinsic_uniform_quotient_slices_positive mu nu
    (splitTargetBottomAction ec mu) (splitTargetHigherAction ec mu)
    (splitTargetBottom ec) (splitTargetHigher ec) (splitTargetReconstruct ec)
    (splitTarget_reconstruct ec) (splitTarget_action_compat ec mu) s₀ hs₀
    (fun ell _ => even_full_bottom_kernel_finrank_le hd3 Q g ell)
    (fun ell _ => even_full_higher_kernel_growth hd3 Q g M hmid ell)
    (fun i => evenBackgroundProduct hdp Q F (E i)) (evenAffineRelations hdp Q F E)
    (evenAffineRelations_generator_mem hdp Q F E) slices P₀ ⟨a₀,ha₀⟩ hdim hb
    C L j 0 loss hbase hambient hslices hC hM hloss (by simpa only [zero_add] using hsmall)

end Froberg
