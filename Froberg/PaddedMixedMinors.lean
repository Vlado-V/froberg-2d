module

public import Froberg.ComplementMixed
public import Froberg.ProductMinors

@[expose] public section

/-! Polynomial mixed-minor certificates for disjoint sets of added vectors. -/
noncomputable section
namespace Froberg.MixedExterior
open Module MvPolynomial Matrix
variable {K α : Type*} [Field K] {r l : ℕ}

/-- Each mixed row uses its own first `t I` attached vectors, followed by fixed
complementary coordinate vectors. The labels used in different rows are disjoint. -/
def paddedVectors {R : Type*} [CommRing R]
    (t : Set.powersetCard (Fin (r+l)) r → ℕ)
    (label : (Σ I, Fin (t I)) → α) (v : α → Fin (r+l) → R)
    (I : Set.powersetCard (Fin (r+l)) r) : Fin l → Fin (r+l) → R :=
  fun j => if hj : j.val < t I then v (label ⟨I,⟨j.val,hj⟩⟩) else complementVectors I j

theorem paddedVectors_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Set.powersetCard (Fin (r+l)) r → ℕ)
    (label : (Σ I, Fin (t I)) → α) (v : α → Fin (r+l) → R)
    (I : Set.powersetCard (Fin (r+l)) r) :
    paddedVectors t label (fun a j => f (v a j)) I =
      fun i j => f (paddedVectors t label v I i j) := by
  classical
  funext i j
  unfold paddedVectors
  split_ifs <;> simp [complementVectors, Pi.basisFun_apply, Pi.single_apply]

/-- Independent labels let the added vectors be specialized separately to the
missing coordinate directions in each mixed determinant. -/
theorem paddedVectors_specialization
    (t : Set.powersetCard (Fin (r+l)) r → ℕ) (ht : ∀ I, t I ≤ l)
    (label : (Σ I, Fin (t I)) ↪ α) :
    ∃ v : α → Fin (r+l) → K, ∀ I,
      paddedVectors t label v I = complementVectors I := by
  classical
  let prescribed : (Σ I, Fin (t I)) → Fin (r+l) → K := fun p =>
    complementVectors p.1 ⟨p.2.val,lt_of_lt_of_le p.2.isLt (ht p.1)⟩
  let v := Function.extend label prescribed (fun _ => 0)
  refine ⟨v,?_⟩
  intro I
  funext j
  unfold paddedVectors
  split_ifs with hj
  · change Function.extend label prescribed (fun _ => 0) (label ⟨I,⟨j.val,hj⟩⟩) = _
    rw [label.injective.extend_apply]
  · rfl

/-- The finite linear system on Plücker coordinates has a genuinely nonzero
polynomial determinant. Its witness specializes it to a diagonal matrix of units. -/
theorem padded_constraint_minor_ne_zero
    (t : Set.powersetCard (Fin (r+l)) r → ℕ) (ht : ∀ I, t I ≤ l)
    (label : (Σ I, Fin (t I)) ↪ α) :
    Matrix.det (fun I J => mixedRow
      (paddedVectors t label (fun a j => (X (a,j) : MvPolynomial (α × Fin (r+l)) K)) I) J) ≠ 0 := by
  classical
  obtain ⟨v,hv⟩ := paddedVectors_specialization (K := K) t ht label
  let values : α × Fin (r+l) → K := fun p => v p.1 p.2
  let A : Matrix (Set.powersetCard (Fin (r+l)) r) (Set.powersetCard (Fin (r+l)) r)
      (MvPolynomial (α × Fin (r+l)) K) := fun I J => mixedRow
        (paddedVectors t label (fun a j => X (a,j)) I) J
  have hentry (I J : Set.powersetCard (Fin (r+l)) r) :
      MvPolynomial.eval values (A I J) = mixedRow (complementVectors (R := K) I) J := by
    change MvPolynomial.eval values (mixedRow _ J) = _
    rw [← mixedRow_map]
    rw [← paddedVectors_map]
    simp only [MvPolynomial.eval_X, values]
    rw [hv]
  have he : (A.map (MvPolynomial.eval values)) =
      Matrix.diagonal (fun I => mixedRow (complementVectors (R := K) I) I) := by
    ext I J
    change MvPolynomial.eval values (A I J) = _
    rw [hentry]
    by_cases hij : I = J
    · subst J
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact mixedRow_complement_offdiag I J hij
  have hd : MvPolynomial.eval values A.det ≠ 0 := by
    rw [RingHom.map_det]
    change (A.map (MvPolynomial.eval values)).det ≠ 0
    rw [he, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun I _ => (isUnit_mixedRow_complement I).ne_zero)
  intro hz
  exact hd (by rw [show A.det = 0 from hz, map_zero])

end Froberg.MixedExterior
