module

public import Froberg.ExactKernelOpen

@[expose] public section

/-! Exactness of a polynomial complex persists on a principal open through
every exact specialization. Neither boundary injectivity nor a separately
assumed constant boundary rank is required. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K I U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem complex_exact_principal_open
    (A : (I → K) → V →ₗ[K] W) (B : (I → K) → U →ₗ[K] V)
    (hA : IsPolynomialFamily A) (hB : IsPolynomialFamily B)
    (hAB : ∀ p,(A p).comp (B p)=0)
    (p₀ : I → K) (hexact : (A p₀).ker=(B p₀).range) :
    ∃ P : MvPolynomial I K,eval p₀ P ≠ 0 ∧
      ∀ p,eval p P ≠ 0 → (A p).ker=(B p).range := by
  obtain ⟨PA,hPA,hArank⟩ := rank_polynomial_principal_open A hA p₀
  obtain ⟨PB,hPB,hBrank⟩ := rank_polynomial_principal_open B hB p₀
  refine ⟨PA*PB,by simpa only [map_mul] using mul_ne_zero hPA hPB,?_⟩
  intro p hp
  obtain ⟨ha,hb⟩ := mul_ne_zero_iff.mp (show eval p PA*eval p PB ≠ 0 by simpa only [map_mul] using hp)
  have hle : (B p).range ≤ (A p).ker := by
    rintro x ⟨u,rfl⟩
    exact LinearMap.congr_fun (hAB p) u
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have hdim₀ := (A p₀).finrank_range_add_finrank_ker
  rw [hexact] at hdim₀
  have hdim := (A p).finrank_range_add_finrank_ker
  have h1 := hArank p ha
  have h2 := hBrank p hb
  omega

theorem complex_pencil_exact_principal_open
    (A₀ A₁ : V →ₗ[K] W) (B₀ B₁ : U →ₗ[K] V)
    (hAB : ∀ e : K,(A₀+e • A₁).comp (B₀+e • B₁)=0)
    (hexact : A₀.ker=B₀.range) :
    ∃ P : MvPolynomial (Fin 1) K,eval 0 P ≠ 0 ∧
      ∀ e : K,eval (fun _ => e) P ≠ 0 → (A₀+e • A₁).ker=(B₀+e • B₁).range := by
  let A : (Fin 1 → K) → V →ₗ[K] W := fun p => A₀+p 0 • A₁
  let B : (Fin 1 → K) → U →ₗ[K] V := fun p => B₀+p 0 • B₁
  have hA : IsPolynomialFamily A := (isPolynomialFamily_const A₀).add
    ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul (isPolynomialFamily_const A₁))
  have hB : IsPolynomialFamily B := (isPolynomialFamily_const B₀).add
    ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul (isPolynomialFamily_const B₁))
  obtain ⟨P,hP,hgood⟩ := complex_exact_principal_open A B hA hB (fun p => hAB (p 0)) 0
    (by simpa only [A,B,Pi.zero_apply,zero_smul,add_zero] using hexact)
  exact ⟨P,hP,fun e he => hgood (fun _ => e) he⟩

end Froberg
