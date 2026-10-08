import Froberg.HigherOddVectorOpen
import Froberg.OddSplitComplex
import Froberg.OddSplitElimination
import Froberg.StrictScalarJointSelection

/-! The strict first row and the higher-row incidence opens give exactness
of the complete odd polynomial coefficient complex at one common tuple. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f t : ℕ}

def scalarEvenForm (p : Forms K m d) : biformParitySpace K h m d 0 :=
  evenBiformEmbedding (t := 0) (Nat.zero_le d) (by decide) (scalarBiformEquiv p)

def linearOddForm (hd : 1≤d) (g : Rows K h m (d-1)) : biformParitySpace K h m d 1 :=
  oddBiformEmbedding hd (by decide) (linearOutputTensorEquiv g)

@[simp] theorem scalarEvenForm_val (p : Forms K m d) :
    (scalarEvenForm (h := h) p).val=rename Sum.inr p.val := sumBiformMap_scalarBiform p

@[simp] theorem linearOddForm_val (hd : 1≤d) (g : Rows K h m (d-1)) :
    (linearOddForm hd g).val=sumBiformMap (linearOutputTensorEquiv g) := rfl

theorem scalar_vector_odd_exact (hd : 1≤d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (hg : Function.Injective (BilinearImage.tupleMap (multiplication (d := d)) g))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication
      (VectorExpansionOpen.quotientMultiplication g d) Q))
    (hhigher : HigherOddRows Q g) :
    OddSplitExact (fun i => scalarEvenForm (h := h) (Q i)) (fun j => linearOddForm hd (g j)) := by
  intro u v hr
  have hS (i) : (rename Sum.inr (Q i).val).IsWeightedHomogeneous (blockWeight h m) 0 := by
    rw [←sumBiformMap_scalarBiform (h := h) (Q i)]
    exact biformImage_output_weight (Forms K h 0) (Forms K m d) le_rfl
      (sumBiformMap_range.le ⟨scalarBiformEquiv (Q i),rfl⟩)
  have hO (j) : (sumBiformMap (linearOutputTensorEquiv (g j))).IsWeightedHomogeneous
      (blockWeight h m) 1 :=
    biformImage_output_weight (Forms K h 1) (Forms K m (d-1)) le_rfl
      (sumBiformMap_range.le ⟨linearOutputTensorEquiv (g j),rfl⟩)
  obtain ⟨C,hC,hC'⟩ := scalar_linear_odd_cycles (blockWeight h m)
    (by intro x; cases x <;> simp [blockWeight]) d
    (fun i => rename Sum.inr (Q i).val) (fun j => sumBiformMap (linearOutputTensorEquiv (g j)))
    hS hO (bottom_polynomial_constants hd Q g hg hQ) hhigher
    (fun i => (u i).val) (fun j => (v j).val)
    (fun i => (u i).property.1) (fun j => (v j).property.1)
    (fun i => (parity_homogeneous_iff (blockWeight h m) (u i).val 1 (by decide)).mp (u i).property.2)
    (fun j => (parity_homogeneous_iff (blockWeight h m) (v j).val 0 (by decide)).mp (v j).property.2)
    (by simpa only [scalarEvenForm_val,linearOddForm_val] using hr)
  exact ⟨C,by simpa only [linearOddForm_val] using hC,by simpa only [scalarEvenForm_val] using hC'⟩

theorem exists_scalar_vector_odd_exact (hh : 0<h) (hm : 0 < m) (hd : 1≤d) {G : ℝ}
    (D : MvPolynomial (Fin (finrank K (Fin f → Rows K h m (d-1)))) K)
    (hD : ∃ g : Fin f → Rows K h m (d-1),eval ((Module.finBasis K _).equivFun g) D≠0)
    (hmodel : ∀ g : Fin f → Rows K h m (d-1),eval ((Module.finBasis K _).equivFun g) D≠0 →
      VectorExpansionOpen.StrictModel g d G ∧
      q*finrank K (VectorExpansionOpen.Source g)≤finrank K (VectorExpansionOpen.Target g d))
    (hscalar : HasOddScalarLayersOpen K h m d f q t)
    (hupper : (f+(h+d-1).choose d)*(h+d-1).choose d≤
      (h+(d+1)-1).choose (d+1)*(m+(d-1)-1).choose (d-1)) :
    ∃ (g : Fin f → Rows K h m (d-1)) (Q : Fin q → Forms K m d),
      VectorExpansionOpen.StrictModel g d G ∧
      OddSplitExact (fun i => scalarEvenForm (h := h) (Q i)) (fun j => linearOddForm hd (g j)) := by
  obtain ⟨P,hP,hgood⟩ := higher_odd_vector_open hh hm hd hscalar hupper
  obtain ⟨g,Q,hg,hQ,hjoint⟩ := VectorExpansionOpen.strict_scalar_joint_selection D hD hmodel P hP
  exact ⟨g,Q,hg,scalar_vector_odd_exact hd Q g hg.product_injective hQ (hgood (g,Q) hjoint)⟩

end Froberg
