import Froberg.OddOutputSpace
import Froberg.ProductRowProfiles
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact coordinates for passing between the paired-variable witnesses and
the balanced finite-variable scalar projection. -/
noncomputable section
namespace Froberg
open MvPolynomial Finset

def pairedScalarEquiv (v : ℕ) : (Fin v × Bool) ≃ Fin (v+v) :=
  (halfVariableEquiv (Fin v)).symm.trans finSumFinEquiv

def balancedScalarHalf (v : ℕ) : Finset (Fin (v+v)) :=
  univ.image (fun i : Fin v => pairedScalarEquiv v (i,true))

theorem pairedScalarEquiv_mem_half (v : ℕ) (i : Fin v) (b : Bool) :
    pairedScalarEquiv v (i,b)∈balancedScalarHalf v ↔ b=true := by
  classical
  simp only [balancedScalarHalf,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have h := (pairedScalarEquiv v).injective hj
    exact (congrArg Prod.snd h).symm
  · rintro rfl
    exact ⟨i,rfl⟩

theorem balancedScalarHalf_card (v : ℕ) : (balancedScalarHalf v).card=v := by
  rw [balancedScalarHalf,card_image_of_injective]
  · simp
  · intro i j hij
    exact congrArg Prod.fst ((pairedScalarEquiv v).injective hij)

theorem balancedScalarHalf_compl_card (v : ℕ) : (balancedScalarHalf v)ᶜ.card=v := by
  rw [card_compl,balancedScalarHalf_card,Fintype.card_fin]
  omega

theorem pairedScalarEquiv_halfWeight (v : ℕ) (x : Fin v × Bool) :
    ProductRows.halfWeight (balancedScalarHalf v) (pairedScalarEquiv v x) = pairedHalfWeight x := by
  rcases x with ⟨i,b⟩
  cases b <;> simp [ProductRows.halfWeight,splitWeight,pairedScalarEquiv_mem_half,pairedHalfWeight]

variable {K : Type} [Field K] [Infinite K]

/-- Scalar renaming identifies the product witness's scalar half-degree with
the exact half-set used in the scalar quotient theorem. -/
theorem fourBlock_scalar_weight_transport {w v r : ℕ}
    {f : MvPolynomial ((Fin w × Bool) ⊕ (Fin v × Bool)) K}
    (hf : f.IsWeightedHomogeneous FourBlocks.yHalfWeight r) :
    (rename (Sum.map id (pairedScalarEquiv v)) f).IsWeightedHomogeneous
      (Sum.elim (fun _ : Fin w × Bool => 0) (ProductRows.halfWeight (balancedScalarHalf v))) r := by
  apply rename_weightedHomogeneous
    ((Equiv.refl (Fin w × Bool)).sumCongr (pairedScalarEquiv v)).toEmbedding
    FourBlocks.yHalfWeight _ _ hf
  rintro (x|y)
  · rfl
  · exact pairedScalarEquiv_halfWeight v y

theorem fourBlock_output_weight_transport {w v r : ℕ}
    {f : MvPolynomial ((Fin w × Bool) ⊕ (Fin v × Bool)) K}
    (hf : f.IsWeightedHomogeneous FourBlocks.xHalfWeight r) :
    (rename (Sum.map id (pairedScalarEquiv v)) f).IsWeightedHomogeneous
      (Sum.elim pairedHalfWeight (fun _ : Fin (v+v) => 0)) r := by
  apply rename_weightedHomogeneous
    ((Equiv.refl (Fin w × Bool)).sumCongr (pairedScalarEquiv v)).toEmbedding
    FourBlocks.xHalfWeight _ _ hf
  rintro (x|y) <;> rfl

end Froberg
