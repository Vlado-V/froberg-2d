import Froberg.ProductRows
import Quartic.PolynomialRankOpen

/-! The actual product row is polynomial in the coefficients of its generators.
Thus each concrete row witness gives a principal open in one common parameter
space, and finitely many row witnesses can be imposed simultaneously. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.ProductRows
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K]
variable {ι σ U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]

private def embeddedProduct (L : U →ₗ[K] MvPolynomial σ K) :
    U →ₗ[K] U →ₗ[K] MvPolynomial σ K where
  toFun x :=
    { toFun := fun y => L x * L y
      map_add' := by intros; simp only [map_add,mul_add]
      map_smul' := by intros; simp only [map_smul,mul_smul_comm,RingHom.id_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact (map_add L x y ▸ add_mul (L x) (L y) (L z))
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro z
    change L (c • x) * L z = c • (L x * L z)
    rw [map_smul,smul_mul_assoc]

theorem products_polynomial (e : ℕ → ℕ) (L : U →ₗ[K] MvPolynomial σ K)
    (q : (j : ℕ) → Fin (e j) → (ι → K) → U) {J R}
    (hq : ∀ j∈J, ∀ i, IsPolynomialFamily (q j i))
    (r : Row J R) (c : Columns e r) :
    IsPolynomialFamily (fun a => products e (fun j i => L (q j i a)) r c) := by
  classical
  by_cases h : r.val.val=R-r.val.val
  · unfold products
    simp only [dif_pos h]
    generalize hc : cast (if_pos h) c = p
    induction p using Sym2.inductionOn with
    | _ i j =>
      exact (hq _ r.property.1 i).bilinear (hq _ r.property.1 j) (embeddedProduct L)
  · unfold products
    simp only [dif_neg h]
    exact (hq _ r.property.1 _).bilinear (hq _ r.property.2.1 _) (embeddedProduct L)

private theorem polynomial_family_open_fintype
    {I V : Type*} [Fintype I] [AddCommGroup V] [Module K V]
    (f : I → (ι → K) → V) (hf : ∀ i,IsPolynomialFamily (f i))
    (a₀ : ι → K) (hli : LinearIndependent K (fun i => f i a₀)) :
    ∃ D : MvPolynomial ι K,eval a₀ D≠0 ∧
      ∀ a,eval a D≠0 → LinearIndependent K (fun i => f i a) := by
  classical
  let E := (Fintype.equivFin I).symm
  obtain ⟨D,hD,hopen⟩ := independent_polynomial_principal_open
    (fun i => f (E i)) (fun i => hf (E i)) a₀ (hli.comp E E.injective)
  exact ⟨D,hD,fun a ha => (linearIndependent_equiv E).mp (hopen a ha)⟩

/-- Every injective product row yields a determinant open in the given common
coefficient space; no new or independent coefficient variables are introduced. -/
theorem product_row_principal_open (e : ℕ → ℕ) (L : U →ₗ[K] MvPolynomial σ K)
    (q : (j : ℕ) → Fin (e j) → (ι → K) → U) (J : Finset ℕ) (R : ℕ)
    (hq : ∀ j∈J, ∀ i, IsPolynomialFamily (q j i)) (a₀ : ι → K)
    (ha₀ : Function.Injective (multiplication e (fun j i => L (q j i a₀)) J R)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 →
        Function.Injective (multiplication e (fun j i => L (q j i a)) J R) := by
  have hli : LinearIndependent K (fun i : Σ r : Row J R, Columns e r =>
      products e (fun j k => L (q j k a₀)) i.1 i.2) := ha₀
  obtain ⟨D,hD,hopen⟩ := polynomial_family_open_fintype
    (fun (i : Σ r : Row J R, Columns e r) a =>
      products e (fun j k => L (q j k a)) i.1 i.2)
    (fun i => products_polynomial e L q hq i.1 i.2) a₀ hli
  exact ⟨D,hD,fun a ha => hopen a ha⟩

/-- All finitely many row witnesses are compatible because they are opens in
the same actual coefficient space. -/
theorem simultaneous_product_rows [Infinite K]
    (e : ℕ → ℕ) (L : U →ₗ[K] MvPolynomial σ K)
    (q : (j : ℕ) → Fin (e j) → (ι → K) → U) (J T : Finset ℕ)
    (hq : ∀ j∈J, ∀ i, IsPolynomialFamily (q j i))
    (hwitness : ∀ R∈T, ∃ a : ι → K,
      Function.Injective (multiplication e (fun j i => L (q j i a)) J R)) :
    ∃ a : ι → K, ∀ R∈T,
      Function.Injective (multiplication e (fun j i => L (q j i a)) J R) := by
  classical
  obtain ⟨a,ha⟩ := simultaneous_principal_properties
    (fun R : T => fun a => Function.Injective
      (multiplication e (fun j i => L (q j i a)) J R.val)) (fun R => by
        obtain ⟨a₀,ha₀⟩ := hwitness R.val R.property
        obtain ⟨D,hD,hprop⟩ := product_row_principal_open e L q J R.val hq a₀ ha₀
        exact ⟨D,⟨a₀,hD⟩,hprop⟩)
  exact ⟨a,fun R hR => ha ⟨R,hR⟩⟩

end Froberg.ProductRows
