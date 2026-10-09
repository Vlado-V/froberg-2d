module

public import Froberg.CycleReductionFormal
public import Froberg.PolynomialComplexOpen
public import Froberg.GeneralComplexOpen
public import Froberg.GenericDimensions

@[expose] public section

/-! Restoring pure components preserves the exact literal polynomial
coefficient reduction. The incoming boundary may have arbitrary kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic

namespace PolynomialRestoration
variable {K : Type} {σ V Z B I : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Z] [Module K Z]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]
variable {r : ℕ}

/-- The actual projected sum of products, with any homogeneous coefficient
space embedded in the polynomial ring. -/
def row (j : V →ₗ[K] MvPolynomial σ K) (pi : MvPolynomial σ K →ₗ[K] Z)
    (q : Fin r → V) : (Fin r → V) →ₗ[K] Z where
  toFun c := pi (∑ i,j (q i)*j (c i))
  map_add' c c' := by simp only [Pi.add_apply,map_add,mul_add,Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply,map_smul,mul_smul_comm,←Finset.smul_sum,RingHom.id_apply]

/-- Constant coefficient matrices give the literal incoming Koszul boundary. -/
def boundary (q : Fin r → V) : (Fin r → Fin r → K) →ₗ[K] (Fin r → V) where
  toFun M := coefficientBoundary q M
  map_add' M N := by
    funext i
    simp only [coefficientBoundary,Pi.add_apply,add_smul,Finset.sum_add_distrib]
    abel
  map_smul' a M := by
    funext i
    simp only [coefficientBoundary,Pi.smul_apply,smul_eq_mul,mul_smul,
      ←Finset.smul_sum,smul_sub,RingHom.id_apply]

def boundaryInFamily (M : Fin r → Fin r → K) : (Fin r → V) →ₗ[K] (Fin r → V) where
  toFun q := coefficientBoundary q M
  map_add' q q' := by
    funext i
    simp only [coefficientBoundary,Pi.add_apply,smul_add,Finset.sum_add_distrib]
    abel
  map_smul' a q := by
    funext i
    simp only [coefficientBoundary,Pi.smul_apply,smul_smul,smul_sub,
      Finset.smul_sum,mul_comm,RingHom.id_apply]

lemma row_boundary (j : V →ₗ[K] MvPolynomial σ K) (pi : MvPolynomial σ K →ₗ[K] Z)
    (q : Fin r → V) (M : Fin r → Fin r → K) : row j pi q (boundary q M)=0 := by
  change pi (∑ i,j (q i)*j (coefficientBoundary q M i))=0
  simp only [coefficientBoundary_map,matrixBoundary_cycle,map_zero]

lemma row_polynomial (j : V →ₗ[K] MvPolynomial σ K) (pi : MvPolynomial σ K →ₗ[K] Z)
    (q : (I → K) → Fin r → V) (hq : IsPolynomialFamily q) :
    IsPolynomialFamily (fun p => row j pi (q p)) := by
  apply isPolynomialFamily_linearMap
  intro c
  have hh := hq.linear_comp (row j pi c)
  simpa only [row,LinearMap.coe_mk,AddHom.coe_mk,mul_comm] using hh

lemma boundary_polynomial (q : (I → K) → Fin r → V) (hq : IsPolynomialFamily q)
    (S : B →ₗ[K] (Fin r → V)) :
    IsPolynomialFamily (fun p => (boundary (q p)).coprod S) := by
  apply isPolynomialFamily_linearMap
  intro x
  change IsPolynomialFamily (fun p => boundaryInFamily x.1 (q p)+S x.2)
  exact (hq.linear_comp (boundaryInFamily x.1)).add (isPolynomialFamily_const (S x.2))

/-- A checked coefficient reduction at one specialization persists on an
actual coefficient open after restoring the omitted pure components. -/
theorem restoration_open
    (j : V →ₗ[K] MvPolynomial σ K) (pi : MvPolynomial σ K →ₗ[K] Z)
    (q : (I → K) → Fin r → V) (hq : IsPolynomialFamily q)
    (S : B →ₗ[K] (Fin r → V))
    (hS : ∀ p z,row j pi (q p) (S z)=0)
    (p₀ : I → K)
    (hreduce : ∀ c,row j pi (q p₀) c=0 →
      ∃ (M : Fin r → Fin r → K) (z : B),c-coefficientBoundary (q p₀) M=S z) :
    ∃ P : MvPolynomial I K,eval p₀ P≠0 ∧
      ∀ p,eval p P≠0 → ∀ c,row j pi (q p) c=0 →
        ∃ (M : Fin r → Fin r → K) (z : B),c-coefficientBoundary (q p) M=S z := by
  let A := fun p => row j pi (q p)
  let C := fun p => (boundary (q p)).coprod S
  have hcomplex : ∀ p,(A p).comp (C p)=0 := by
    intro p
    apply LinearMap.ext
    intro x
    change row j pi (q p) (boundary (q p) x.1+S x.2)=0
    rw [map_add,row_boundary,hS,zero_add]
  have hexact : (A p₀).ker=(C p₀).range := by
    apply le_antisymm
    · intro c hc
      obtain ⟨M,z,hz⟩ := hreduce c hc
      refine ⟨(M,z),?_⟩
      change coefficientBoundary (q p₀) M+S z=c
      exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hz).symm
    · rintro c ⟨x,rfl⟩
      exact LinearMap.congr_fun (hcomplex p₀) x
  obtain ⟨P,hP,hgood⟩ := complex_general_exact_principal_open A C
    (row_polynomial j pi q hq) (boundary_polynomial q hq S) hcomplex p₀ hexact
  refine ⟨P,hP,?_⟩
  intro p hp c hc
  have hmem : c∈(C p).range := (hgood p hp) ▸ (show c∈(A p).ker from hc)
  obtain ⟨⟨M,z⟩,hMz⟩ := hmem
  refine ⟨M,z,?_⟩
  change coefficientBoundary (q p) M+S z=c at hMz
  rw [←hMz,add_sub_cancel_left]

/-- Insert the freely varying pure columns into their fixed generator slots. -/
def pureShift {U : Type*} [AddCommGroup U] [Module K U] {u : ℕ}
    (embed : U →ₗ[K] V) (slot : Fin u → Fin r) : (Fin u → U) →ₗ[K] (Fin r → V) :=
  ∑ k,(LinearMap.single K (fun _ : Fin r => V) (slot k)).comp
    (embed.comp (LinearMap.proj k))

/-- In even degree the restored pure columns may simultaneously form a full
basis. This uses their free coefficient space, never independence of their
symmetric products. -/
theorem restoration_with_pure_basis [Infinite K]
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (j : V →ₗ[K] MvPolynomial σ K) (pi : MvPolynomial σ K →ₗ[K] Z)
    (embed : U →ₗ[K] V) (slot : Fin (finrank K U) → Fin r)
    (q₀ : Fin r → V) (S : B →ₗ[K] (Fin r → V))
    (hS : ∀ v : Fin (finrank K U) → U,∀ z,
      row j pi (q₀+pureShift embed slot v) (S z)=0)
    (hreduce : ∀ c,row j pi q₀ c=0 →
      ∃ (M : Fin r → Fin r → K) (z : B),c-coefficientBoundary q₀ M=S z) :
    ∃ v : Fin (finrank K U) → U,LinearIndependent K v ∧
      ∀ c,row j pi (q₀+pureShift embed slot v) c=0 →
        ∃ (M : Fin r → Fin r → K) (z : B),
          c-coefficientBoundary (q₀+pureShift embed slot v) M=S z := by
  let e := (Module.finBasis K (Fin (finrank K U) → U)).equivFun
  let q := fun a => q₀+pureShift embed slot (e.symm a)
  have hq : IsPolynomialFamily q :=
    (isPolynomialFamily_const q₀).add (isPolynomialFamily_linear
      ((pureShift embed slot).comp e.symm.toLinearMap))
  obtain ⟨D,hD,hgood⟩ := restoration_open j pi q hq S
    (fun p z => hS (e.symm p) z) 0 (by
      simpa only [q,map_zero,add_zero] using hreduce)
  let basisTuple : Fin (finrank K U) → U := Module.finBasis K U
  obtain ⟨P,hP,hindep⟩ := independent_polynomial_principal_open
    (fun k a => e.symm a k)
    (fun k => isPolynomialFamily_linear ((LinearMap.proj k).comp e.symm.toLinearMap))
    (e basisTuple) (by simpa only [LinearEquiv.symm_apply_apply,basisTuple] using
      (Module.finBasis K U).linearIndependent)
  obtain ⟨a,haD,haP⟩ := principal_opens_intersect (show ∃ a,eval a D≠0 from ⟨0,hD⟩)
    (show ∃ a,eval a P≠0 from ⟨e basisTuple,hP⟩)
  exact ⟨e.symm a,hindep a haP,hgood a haD⟩

end PolynomialRestoration
end Froberg
