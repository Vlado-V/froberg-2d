module

public import Froberg.PreparedEndpointParity
public import Froberg.OddSplitRelativeInjection

@[expose] public section

/-! The actual prepared coefficients split into the Q/E/F/G biform
families used by the relative quotient and covector construction. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def preparedEvenBiform (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : PreparedParameters.Space m d q J counts O) (i : PreparedParameters.Label q J counts) :
    biformParitySpace K h m d 0 :=
  ⟨PreparedParameters.generator p i,PreparedParameters.generator_homogeneous hO hJ p i,
    (parity_homogeneous_iff (blockWeight h m) _ 0 (by decide)).mpr
      ((mem_weightedParitySpace_iff _ _ _).mp (PreparedParameters.generator_even hO heven p i))⟩

theorem oddGenerator_homogeneous (hd : 0<d) (U : Fin u → Forms K h d)
    (P : OuterSpace K (Fin h) m d u) (F : OuterSpace K (Fin h) m d f) (k : Fin f ⊕ Fin u) :
    (oddGenerator U P F k).IsHomogeneous d := by
  apply IsHomogeneous.add
  · cases k with
    | inl i => exact FullPreparedParameters.private_homogeneous hd F i
    | inr i => exact FullPreparedParameters.private_homogeneous hd P i
  · cases k with
    | inl i => exact isHomogeneous_zero _ _ _
    | inr i => exact (U i).property.rename_isHomogeneous

def preparedOddBiform (hd : 0<d) (hdodd : d%2=1) (U : Fin u → Forms K h d)
    (P : OuterSpace K (Fin h) m d u) (F : OuterSpace K (Fin h) m d f) (k : Fin f ⊕ Fin u) :
    biformParitySpace K h m d 1 :=
  ⟨oddGenerator U P F k,oddGenerator_homogeneous hd U P F k,
    (parity_homogeneous_iff (blockWeight h m) _ 1 (by decide)).mpr
      ((mem_weightedParitySpace_iff _ _ _).mp (oddGenerator_parity hdodd U P F k))⟩

def preparedBaseBiform (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : PreparedParameters.Space m d q J counts O) : Fin q → biformParitySpace K h m d 0 :=
  fun i => preparedEvenBiform hO hJ heven p (Sum.inl i)

def preparedPositiveBiform (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : PreparedParameters.Space m d q J counts O) :
    Fin (Fintype.card (ProductRows.LayerLabel J counts)) → biformParitySpace K h m d 0 :=
  fun i => preparedEvenBiform hO hJ heven p (Sum.inr ((Fintype.equivFin _).symm i))

theorem prepared_odd_split_exact (hd : 0<d) (hdodd : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (H : OddCyclesExact U P p) :
    OddSplitExact
      (Fin.append (preparedBaseBiform hO hJ heven p.1) (preparedPositiveBiform hO hJ heven p.1))
      (Fin.append (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inl i))
        (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inr i))) := by
  let idx : PreparedParameters.Label q J counts ≃
      Fin (q+Fintype.card (ProductRows.LayerLabel J counts)) :=
    (Equiv.sumCongr (Equiv.refl (Fin q)) (Fintype.equivFin _)).trans finSumFinEquiv
  let S := Fin.append (preparedBaseBiform hO hJ heven p.1) (preparedPositiveBiform hO hJ heven p.1)
  let T := Fin.append (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inl i))
    (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inr i))
  have hS (i) : (S (idx i)).val=PreparedParameters.generator p.1 i := by
    cases i <;> simp [S,idx,preparedBaseBiform,preparedPositiveBiform,preparedEvenBiform]
  have hT (k) : (T (finSumFinEquiv k)).val=oddGenerator U P p.2 k := by
    cases k <;> simp [T,preparedOddBiform]
  intro c v hr
  apply constant_pair_kernel_reindex idx.symm finSumFinEquiv.symm
    (fun i => (S i).val) (fun k => (T k).val)
    (biformParitySpace K h m d 1) (biformParitySpace K h m d 0) ?_
    (fun i => (c i).val) (fun k => (v k).val)
    (fun i => (c i).property) (fun k => (v k).property) hr
  intro x y hx hy hrel
  obtain ⟨B,hB,hB'⟩ := H x y (fun i => (hx i).1) (fun k => (hy k).1)
    (fun i => (parity_homogeneous_iff (blockWeight h m) (x i) 1 (by decide)).mp (hx i).2)
    (fun k => (parity_homogeneous_iff (blockWeight h m) (y k) 0 (by decide)).mp (hy k).2)
    (by simpa only [Equiv.symm_symm,hS,hT] using hrel)
  exact ⟨B,by simpa only [Equiv.symm_symm,hT] using hB,
    by simpa only [Equiv.symm_symm,hS] using hB'⟩

theorem prepared_odd_relative_injective (hd : 0<d) (hdodd : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (H : OddCyclesExact U P p) :
    Function.Injective (oddEvenRelativeMap (preparedBaseBiform hO hJ heven p.1)
      (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inl i))
      (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inr i))
      (preparedPositiveBiform hO hJ heven p.1)) :=
  odd_split_relative_injective _ _ _ _ (prepared_odd_split_exact hd hdodd hO hJ heven U P p H)

end Froberg.PreparedTarget
