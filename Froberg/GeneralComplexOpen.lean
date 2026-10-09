module

public import Froberg.ExactKernelGeneral

@[expose] public section

/-! Exact polynomial complexes with finite source spaces are open even when
the target is the full polynomial ring and the boundary is not injective. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K I U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

theorem complex_general_exact_principal_open
    (A : (I → K) → V →ₗ[K] W) (B : (I → K) → U →ₗ[K] V)
    (hA : IsPolynomialFamily A) (hB : IsPolynomialFamily B)
    (hAB : ∀ p,(A p).comp (B p)=0)
    (p₀ : I → K) (hexact : (A p₀).ker=(B p₀).range) :
    ∃ P : MvPolynomial I K,eval p₀ P≠0 ∧
      ∀ p,eval p P≠0 → (A p).ker=(B p).range := by
  obtain ⟨PA,hPA,hArank⟩ := rank_polynomial_general_open A hA p₀
  obtain ⟨PB,hPB,hBrank⟩ := rank_polynomial_general_open B hB p₀
  refine ⟨PA*PB,by simpa only [map_mul] using mul_ne_zero hPA hPB,?_⟩
  intro p hp
  obtain ⟨ha,hb⟩ := mul_ne_zero_iff.mp (show eval p PA*eval p PB≠0 by simpa only [map_mul] using hp)
  have hle : (B p).range≤(A p).ker := by
    rintro x ⟨u,rfl⟩
    exact LinearMap.congr_fun (hAB p) u
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have hdim₀ := (A p₀).finrank_range_add_finrank_ker
  rw [hexact] at hdim₀
  have hdim := (A p).finrank_range_add_finrank_ker
  have h1 := hArank p ha
  have h2 := hBrank p hb
  omega

end Froberg
