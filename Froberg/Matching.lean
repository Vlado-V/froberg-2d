module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Tactic

@[expose] public section

/-! Finite matching and polynomial minor tools for the independent-product construction. -/
noncomputable section
namespace Froberg.Matching

open Finset
variable {A B : Type*} [Fintype A] [DecidableEq B]

/-- A uniform positive lower degree on the left and upper degree on the right imply Hall. -/
theorem exists_matching_of_degree_bounds (t : A → Finset B) (k : ℕ) (hk : 0 < k)
    (hl : ∀ a, k ≤ (t a).card)
    (hr : ∀ b, (Finset.univ.filter (fun a => b ∈ t a)).card ≤ k) :
    ∃ f : A → B, Function.Injective f ∧ ∀ a, f a ∈ t a := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp
  intro s
  have hcount : s.card * k ≤ (s.biUnion t).card * k := by
    apply Finset.card_mul_le_card_mul (fun a b => b ∈ t a)
    · intro a ha
      have heq : (s.biUnion t).bipartiteAbove (fun a b => b ∈ t a) a = t a := by
        ext b
        simp only [Finset.mem_bipartiteAbove, Finset.mem_biUnion]
        exact ⟨fun h => h.2, fun h => ⟨⟨a, ha, h⟩, h⟩⟩
      rw [heq]
      exact hl a
    · intro b _
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))).trans (hr b)
  exact Nat.le_of_mul_le_mul_right hcount hk

/-- Every finite biregular bipartite graph with at least as many right vertices
and positive left degree has a matching covering all left vertices. -/
theorem exists_matching_of_biregular [Fintype B] (t : A → Finset B)
    (leftDegree rightDegree : ℕ) (hleft : 0 < leftDegree)
    (hl : ∀ a, (t a).card = leftDegree)
    (hr : ∀ b, (Finset.univ.filter (fun a => b ∈ t a)).card = rightDegree)
    (hcard : Fintype.card A ≤ Fintype.card B) :
    ∃ f : A → B, Function.Injective f ∧ ∀ a, f a ∈ t a := by
  by_cases hzero : Fintype.card A = 0
  · let : IsEmpty A := Fintype.card_eq_zero_iff.mp hzero
    exact ⟨isEmptyElim, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  have hpos : 0 < Fintype.card A := Nat.pos_of_ne_zero hzero
  have htotal : Fintype.card A * leftDegree = Fintype.card B * rightDegree := by
    have h := Finset.card_mul_eq_card_mul (fun a b => b ∈ t a)
      (s := Finset.univ) (t := Finset.univ) (m := leftDegree) (n := rightDegree)
      (fun a _ => by simpa [Finset.bipartiteAbove] using hl a)
      (fun b _ => by simpa [Finset.bipartiteBelow] using hr b)
    simpa using h
  have hdeg : rightDegree ≤ leftDegree := by
    have hm := Nat.mul_le_mul_right rightDegree hcard
    nlinarith
  exact exists_matching_of_degree_bounds t leftDegree hleft
    (fun a => (hl a).ge) (fun b => (hr b).le.trans hdeg)

/-- The symmetry criterion used in the product-monomial fibers: transitivity on
both sides makes the graph biregular, so one edge and the cardinality inequality suffice. -/
theorem exists_matching_of_two_sided_symmetry [Fintype B] (t : A → Finset B)
    (leftSymmetry : ∀ a a', ∃ e : B ≃ B, ∀ b, b ∈ t a ↔ e b ∈ t a')
    (rightSymmetry : ∀ b b', ∃ e : A ≃ A, ∀ a, b ∈ t a ↔ b' ∈ t (e a))
    (hedge : ∃ a b, b ∈ t a) (hcard : Fintype.card A ≤ Fintype.card B) :
    ∃ f : A → B, Function.Injective f ∧ ∀ a, f a ∈ t a := by
  classical
  obtain ⟨a₀, b₀, hab⟩ := hedge
  apply exists_matching_of_biregular t (t a₀).card
    (Finset.univ.filter (fun a => b₀ ∈ t a)).card
    (Finset.card_pos.mpr ⟨b₀, hab⟩) _ _ hcard
  · intro a
    obtain ⟨e, he⟩ := leftSymmetry a a₀
    have h := Fintype.card_congr (e.subtypeEquiv he)
    simpa only [Fintype.card_coe] using h
  · intro b
    obtain ⟨e, he⟩ := rightSymmetry b b₀
    have h := Fintype.card_congr (e.subtypeEquiv
      (p := fun a => b ∈ t a) (q := fun a => b₀ ∈ t a) he)
    simpa only [Fintype.card_subtype] using h

/-- A square polynomial minor admitting an identity specialization is nonzero. -/
theorem determinant_ne_zero_of_identity_specialization
    {K σ ι : Type*} [CommRing K] [Nontrivial K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) (values : σ → K)
    (hM : M.map (MvPolynomial.eval values) = 1) : M.det ≠ 0 := by
  intro hzero
  have h := congrArg Matrix.det hM
  rw [Matrix.det_one] at h
  change ((MvPolynomial.eval values).mapMatrix M).det = 1 at h
  rw [← RingHom.map_det, hzero, map_zero] at h
  exact zero_ne_one h

/-- Independent parameter sets for the columns allow columnwise specializations to be combined.
This is the precise polynomial-minor step used after matching each product to a monomial. -/
theorem determinant_ne_zero_of_disjoint_column_parameters
    {K σ ι : Type*} [CommRing K] [Nontrivial K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) (owner : σ → ι)
    (columnValues : ι → σ → K)
    (hvars : ∀ i j x, x ∈ (M i j).vars → owner x = j)
    (hcolumns : ∀ i j, MvPolynomial.eval (columnValues j) (M i j) =
      (1 : Matrix ι ι K) i j) : M.det ≠ 0 := by
  apply determinant_ne_zero_of_identity_specialization M
    (fun x => columnValues (owner x) x)
  ext i j
  change MvPolynomial.eval (fun x => columnValues (owner x) x) (M i j) = _
  rw [← hcolumns i j]
  apply MvPolynomial.eval₂Hom_congr' rfl ?_ rfl
  intro x hx _
  rw [hvars i j x hx]

end Froberg.Matching
