module

public import Froberg.UniversalMixedPosition

@[expose] public section

/-! The uniform mixed-position conditions hold on a genuine principal open. -/
noncomputable section
namespace Froberg.MixedExterior
open MvPolynomial Matrix
variable {K α C : Type*} [Field K] [Infinite K] [Fintype α] [DecidableEq α] [Fintype C]

/-- Simultaneous specialization for an arbitrary finite list of disjoint-label
mixed-minor certificates, possibly in different exterior degrees. -/
theorem common_mixed_vectors_principal_open (h : ℕ) (r l : C → ℕ) (hr : ∀ c, r c+l c=h)
    (t : (c : C) → Set.powersetCard (Fin (r c+l c)) (r c) → ℕ)
    (ht : ∀ c I, t c I ≤ l c)
    (label : (c : C) → (Σ I, Fin (t c I)) ↪ α) :
    ∃ P : MvPolynomial (α × Fin h) K, P≠0 ∧ ∀ values,eval values P≠0 →
      (∀ S : Finset α, S.card ≤ h → LinearIndependent K (fun i : S => fun j => values (i.val,j))) ∧
      ∀ c, Matrix.det (fun I J => mixedRow
        (paddedVectors (t c) (label c) (fun a j => values (a,Fin.cast (hr c) j)) I) J) ≠ 0 := by
  classical
  let coord (c : C) : α × Fin (r c+l c) → α × Fin h :=
    fun p => (p.1,Fin.cast (hr c) p.2)
  have hcoord (c : C) : Function.Injective (coord c) := by
    intro p q he
    apply Prod.ext
    · exact congrArg (fun p : α × Fin h => p.1) he
    · apply Fin.ext
      exact congrArg (fun p : α × Fin h => p.2.val) he
  let mixed (c : C) : MvPolynomial (α × Fin (r c+l c)) K :=
    Matrix.det (fun I J => mixedRow
      (paddedVectors (t c) (label c) (fun a j => (X (a,j) : MvPolynomial (α × Fin (r c+l c)) K)) I) J)
  let Subsets := {S : Finset α // S.card ≤ h}
  have hrow (S : Subsets) : Nonempty (S.val ↪ Fin h) :=
    Function.Embedding.nonempty_of_card_le (by simpa using S.property)
  let row (S : Subsets) : S.val ↪ Fin h := Classical.choice (hrow S)
  let polynomials : C ⊕ Subsets → MvPolynomial (α × Fin h) K := Sum.elim
    (fun c => MvPolynomial.rename (coord c) (mixed c))
    (fun S => Matrix.det (fun i j : S.val => (X (j.val,row S i) : MvPolynomial (α × Fin h) K)))
  have hpoly : ∀ x, polynomials x ≠ 0 := by
    intro x
    cases x with
    | inl c =>
      intro hz
      have hi := MvPolynomial.rename_injective (R := K) (coord c) (hcoord c)
      apply padded_constraint_minor_ne_zero (K := K) (t c) (ht c) (label c)
      apply hi
      change MvPolynomial.rename (coord c) (mixed c) = 0 at hz
      rw [map_zero]
      exact hz
    | inr S => exact GeneralPositionVectors.coordinate_minor_ne_zero h S.val (row S)
  refine ⟨∏ x,polynomials x,Finset.prod_ne_zero_iff.mpr (fun x _ => hpoly x),?_⟩
  intro values hvalues'
  have hvalues (x) : eval values (polynomials x)≠0 := by
    have hp : (∏ y,eval values (polynomials y))≠0 := by simpa only [map_prod] using hvalues'
    exact Finset.prod_ne_zero_iff.mp hp x (Finset.mem_univ x)
  refine ⟨?_,?_⟩
  · intro S hS
    let T : Subsets := ⟨S,hS⟩
    let coordinates : (Fin h → K) →ₗ[K] (S → K) :=
      LinearMap.pi (fun i => LinearMap.proj (row T i))
    apply LinearIndependent.of_comp coordinates
    let M : Matrix S S (MvPolynomial (α × Fin h) K) := fun i j => X (j.val,row T i)
    have hv : MvPolynomial.eval values M.det ≠ 0 := hvalues (Sum.inr T)
    rw [RingHom.map_det] at hv
    convert Matrix.linearIndependent_cols_of_det_ne_zero hv using 1
    ext i j
    change values (i.val,row T j) = MvPolynomial.eval values (X (i.val,row T j))
    exact (MvPolynomial.eval_X _).symm
  · intro c
    have hv : MvPolynomial.eval values (MvPolynomial.rename (coord c) (mixed c)) ≠ 0 :=
      hvalues (Sum.inl c)
    rw [MvPolynomial.eval_rename] at hv
    have he : MvPolynomial.eval (values ∘ coord c) (mixed c) =
        Matrix.det (fun I J => mixedRow
          (paddedVectors (t c) (label c) (fun a j => values (a,Fin.cast (hr c) j)) I) J) := by
      let M : Matrix (Set.powersetCard (Fin (r c+l c)) (r c))
          (Set.powersetCard (Fin (r c+l c)) (r c)) (MvPolynomial (α × Fin (r c+l c)) K) :=
        fun I J => mixedRow
          (paddedVectors (t c) (label c) (fun a j => X (a,j)) I) J
      change MvPolynomial.eval (values ∘ coord c) M.det = _
      rw [RingHom.map_det]
      congr 1
      ext I J
      change MvPolynomial.eval (values ∘ coord c) (mixedRow _ J) = _
      rw [← mixedRow_map, ← paddedVectors_map]
      simp only [MvPolynomial.eval_X]
      rfl
    rwa [he] at hv

/-- One principal open simultaneously enforces all full-spark and mixed
exterior conditions, and can therefore be intersected with other opens. -/
theorem universal_mixed_vectors_principal_open (h : ℕ) :
    ∃ P : MvPolynomial (α × Fin h) K, P≠0 ∧ ∀ values,eval values P≠0 →
      (∀ S : Finset α,S.card ≤ h → LinearIndependent K (fun i : S => fun j => values (i.val,j))) ∧
      UniversalMixedPosition (fun a j => values (a,j)) := by
  classical
  let r : MixedConfiguration h α → ℕ := fun c => c.1.val
  let l : MixedConfiguration h α → ℕ := fun c => h-c.1.val
  have hr : ∀ c,r c+l c=h := fun c => Nat.add_sub_of_le (Nat.le_of_lt_succ c.1.isLt)
  obtain ⟨P,hP,hgood⟩ := common_mixed_vectors_principal_open (K := K) h r l hr
    (fun c I => (c.2.1 I).val) (fun c I => Nat.le_of_lt_succ (c.2.1 I).isLt)
    (fun c => c.2.2)
  exact ⟨P,hP,hgood⟩

end Froberg.MixedExterior
