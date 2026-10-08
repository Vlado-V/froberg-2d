import Froberg.ProductMinors
import Mathlib.Data.Fintype.EquivFin

/-! Finite families of vectors whose small subfamilies are all independent. -/
noncomputable section
namespace Froberg.GeneralPositionVectors
open MvPolynomial
variable {K α : Type*} [Field K] [Fintype α] [DecidableEq α]

/-- A generic coordinate minor is nonzero whenever its selected coordinates are distinct. -/
theorem coordinate_minor_ne_zero (h : ℕ) (S : Finset α) (row : S ↪ Fin h) :
    Matrix.det (fun i j : S => (X (j.val,row i) : MvPolynomial (α × Fin h) K)) ≠ 0 := by
  classical
  let coord : S × S → α × Fin h := fun p => (p.2.val,row p.1)
  have hinj : Function.Injective coord := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ he
    have hj : j = j' := Subtype.ext (congrArg Prod.fst he)
    have hi : i = i' := row.injective (congrArg Prod.snd he)
    exact Prod.ext hi hj
  let entry : S × S → K := fun p => if p.1 = p.2 then 1 else 0
  apply Matching.determinant_ne_zero_of_identity_specialization _
    (Function.extend coord entry (fun _ => 0))
  ext i j
  change MvPolynomial.eval (Function.extend coord entry (fun _ => 0)) (X (j.val,row i)) = _
  rw [MvPolynomial.eval_X]
  change Function.extend coord entry (fun _ => 0) (coord (i,j)) = _
  rw [hinj.extend_apply]
  rfl

/-- Over an infinite field one can attach vectors to arbitrarily many labels,
with every subfamily of size at most the ambient dimension independent. -/
theorem exists_small_subfamilies_independent [Infinite K] (h : ℕ) :
    ∃ v : α → Fin h → K, ∀ S : Finset α, S.card ≤ h →
      LinearIndependent K (fun i : S => v i.val) := by
  classical
  let Subsets := {S : Finset α // S.card ≤ h}
  letI : Fintype Subsets := inferInstance
  have hrow (S : Subsets) : Nonempty (S.val ↪ Fin h) :=
    Function.Embedding.nonempty_of_card_le (by simpa using S.property)
  let row (S : Subsets) : S.val ↪ Fin h := Classical.choice (hrow S)
  let minors (S : Subsets) : MvPolynomial (α × Fin h) K :=
    Matrix.det (fun i j : S.val => (X (j.val,row S i) : MvPolynomial (α × Fin h) K))
  obtain ⟨values,hvalues⟩ := ProductMinors.exists_common_specialization minors
    (fun S => coordinate_minor_ne_zero h S.val (row S))
  refine ⟨fun a i => values (a,i),?_⟩
  intro S hS
  let T : Subsets := ⟨S,hS⟩
  let coordinates : (Fin h → K) →ₗ[K] (S → K) :=
    LinearMap.pi (fun i => LinearMap.proj (row T i))
  apply LinearIndependent.of_comp coordinates
  let M : Matrix S S (MvPolynomial (α × Fin h) K) :=
    fun i j => X (j.val,row T i)
  have hv : MvPolynomial.eval values M.det ≠ 0 := hvalues T
  rw [RingHom.map_det] at hv
  convert Matrix.linearIndependent_cols_of_det_ne_zero hv using 1
  ext i j
  change values (i.val,row T j) = MvPolynomial.eval values (X (i.val,row T j))
  exact (MvPolynomial.eval_X _).symm

end Froberg.GeneralPositionVectors
