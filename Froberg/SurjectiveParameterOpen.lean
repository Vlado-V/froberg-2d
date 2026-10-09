module

public import Quartic.PolynomialRankOpen

@[expose] public section

/-! Finite intersection and base/fiber specialization of actual surjective
polynomial maps. Different row witnesses may use different base points. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K P J : Type*} [Field K] [Infinite K]
variable {E T : Type*} [AddCommGroup E] [Module K E] [Module.Finite K E]
  [AddCommGroup T] [Module K T] [Module.Finite K T]

theorem surjective_polynomial_principal_open (A : (P → K) → E →ₗ[K] T)
    (hA : IsPolynomialFamily A) (a₀ : P → K) (ha₀ : Function.Surjective (A a₀)) :
    ∃ D : MvPolynomial P K, eval a₀ D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (A a) := by
  obtain ⟨D,hD,hRank⟩ := rank_polynomial_principal_open A hA a₀
  refine ⟨D,hD,fun a ha => ?_⟩
  have hr := hRank a ha
  rw [LinearMap.range_eq_top.mpr ha₀,finrank_top] at hr
  apply LinearMap.range_eq_top.mp
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hr)

section FiniteRows
variable [Fintype J]
variable {E T : J → Type*}
  [∀ j,AddCommGroup (E j)] [∀ j,Module K (E j)] [∀ j,Module.Finite K (E j)]
  [∀ j,AddCommGroup (T j)] [∀ j,Module K (T j)] [∀ j,Module.Finite K (T j)]

/-- Each row may have a different successful specialization, but all rows
are simultaneously surjective on a single nonempty polynomial open. -/
theorem surjective_polynomial_common_open
    (A : (j : J) → (P → K) → E j →ₗ[K] T j)
    (hA : ∀ j,IsPolynomialFamily (A j))
    (hwit : ∀ j,∃ a,Function.Surjective (A j a)) :
    ∃ D : MvPolynomial P K, (∃ a,eval a D≠0) ∧
      ∀ a,eval a D≠0 → ∀ j,Function.Surjective (A j a) := by
  classical
  choose a ha using hwit
  choose D hD hgood using fun j => surjective_polynomial_principal_open (A j) (hA j) (a j) (ha j)
  have hnz (j : J) : D j≠0 := by
    intro hz
    exact hD j (by rw [hz,map_zero])
  obtain ⟨a₀,ha₀⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ j,D j,⟨a₀,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun j _ => ha₀ j)
  intro a ha j
  have hh : ∏ j,eval a (D j)≠0 := by simpa only [map_prod] using ha
  exact hgood j a (Finset.prod_ne_zero_iff.mp hh j (Finset.mem_univ _))

/-- Separate witnesses in a matrix-frame base descend to a common nonempty
base open. At every such base, all rows hold on a common nonempty coefficient
open. This makes the passage from separate output planes to one shared plane
explicit at the level of polynomials. -/
theorem surjective_polynomial_base_fiber_open {B : Type*}
    (A : (j : J) → (B → K) → (P → K) → E j →ₗ[K] T j)
    (hbase : ∀ j p,IsPolynomialFamily (fun b => A j b p))
    (hfiber : ∀ j b,IsPolynomialFamily (A j b))
    (hwit : ∀ j,∃ b p,Function.Surjective (A j b p)) :
    ∃ D : MvPolynomial B K, (∃ b,eval b D≠0) ∧
      ∀ b,eval b D≠0 → ∃ F : MvPolynomial P K, (∃ p,eval p F≠0) ∧
        ∀ p,eval p F≠0 → ∀ j,Function.Surjective (A j b p) := by
  classical
  choose b p hp using hwit
  obtain ⟨D,hD,hgood⟩ := surjective_polynomial_common_open
    (fun j b' => A j b' (p j)) (fun j => hbase j (p j)) (fun j => ⟨b j,hp j⟩)
  refine ⟨D,hD,fun b hb => ?_⟩
  exact surjective_polynomial_common_open (fun j => A j b) (fun j => hfiber j b)
    (fun j => ⟨p j,hgood b hb j⟩)

end FiniteRows
end Froberg
