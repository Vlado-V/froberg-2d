module

public import Froberg.GeneralComplexOpen
public import Froberg.PreparedPrivateRowOpen

@[expose] public section

/-! A product block remains independent modulo a varying relation block on
a principal open, when the complete relation block has its expected kernel.
The boundary is allowed to have redundant generators. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type} {I U V Z W : Type*} [Field K] [Infinite K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
  [AddCommGroup W] [Module K W]

theorem separated_complex_principal_open
    (A : (I → K) → V →ₗ[K] W) (B : (I → K) → U →ₗ[K] V)
    (C : (I → K) → Z →ₗ[K] W)
    (hA : IsPolynomialFamily A) (hB : IsPolynomialFamily B)
    (hC : IsPolynomialFamily C) (hAB : ∀ p,(A p).comp (B p)=0)
    (p₀ : I → K) (hexact : (A p₀).ker=(B p₀).range)
    (hsep : ∀ v z,A p₀ v+C p₀ z=0 → z=0) :
    ∃ P : MvPolynomial I K,eval p₀ P≠0 ∧
      ∀ p,eval p P≠0 → ∀ v z,A p v+C p z=0 → z=0 := by
  let D (p : I → K) := addRow (A p) (C p)
  let E (p : I → K) := (LinearMap.inl K V Z).comp (B p)
  have hD : IsPolynomialFamily D := by
    apply isPolynomialFamily_linearMap
    intro x
    exact (hA.linear_comp (LinearMap.applyₗ (R := K) x.1)).add
      (hC.linear_comp (LinearMap.applyₗ (R := K) x.2))
  have hE : IsPolynomialFamily E := by
    apply isPolynomialFamily_linearMap
    intro x
    exact (hB.linear_comp (LinearMap.applyₗ (R := K) x)).prod_mk
      (isPolynomialFamily_const (0 : Z))
  have hDE (p : I → K) : (D p).comp (E p)=0 := by
    apply LinearMap.ext
    intro x
    change A p (B p x)+C p 0=0
    rw [map_zero,add_zero]
    exact LinearMap.congr_fun (hAB p) x
  have hex : (D p₀).ker=(E p₀).range :=
    addRow_exact_of_separated (A p₀) (C p₀) (B p₀) hexact hsep
  obtain ⟨P,hP,hgood⟩ := complex_general_exact_principal_open D E hD hE hDE p₀ hex
  refine ⟨P,hP,?_⟩
  intro p hp v z hz
  have hmem : (v,z)∈(D p).ker := hz
  rw [hgood p hp] at hmem
  obtain ⟨x,hx⟩ := hmem
  exact (congrArg Prod.snd hx).symm

end Froberg
