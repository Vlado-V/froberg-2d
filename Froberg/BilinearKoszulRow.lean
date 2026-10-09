module

public import Froberg.ExactKernelGeneral

@[expose] public section

/-! Coordinate-free finite scalar/new-layer/product rows. The mandatory
constant relations and all row entries vary polynomially in common parameters. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial Quartic
variable {K U V A W I J ι : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup A] [Module K A]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [Fintype I] [Fintype J]

/-- The actual scalar/new-layer row together with its product columns. -/
def bilinearKoszulRow (μ : V →ₗ[K] U →ₗ[K] A) (Q : I → V) (E : J → U)
    (P : W →ₗ[K] A) : (((I → U) × (J → V)) × W) →ₗ[K] A where
  toFun x := (∑ i,μ (Q i) (x.1.1 i))+(∑ j,μ (x.1.2 j) (E j))+P x.2
  map_add' x y := by
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add,LinearMap.add_apply,Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    change (∑ i,μ (Q i) (c • x.1.1 i))+(∑ j,μ (c • x.1.2 j) (E j))+P (c • x.2)=_
    simp only [map_smul,LinearMap.smul_apply,← Finset.smul_sum,smul_add,RingHom.id_apply]

/-- Literal constant scalar-layer Koszul relations. -/
def bilinearKoszulConstants (Q : I → V) (E : J → U) :
    (I → J → K) →ₗ[K] (((I → U) × (J → V)) × W) where
  toFun C := ((fun i => ∑ j,C i j • E j,fun j => -∑ i,C i j • Q i),0)
  map_add' C D := by
    apply Prod.ext
    · apply Prod.ext <;> funext i <;>
        simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,add_smul,Finset.sum_add_distrib,neg_add]
    · simp
  map_smul' c C := by
    apply Prod.ext
    · apply Prod.ext
      · funext i
        change (∑ j,(c*(C i j)) • E j)=c • (∑ j,C i j • E j)
        simp only [mul_smul,Finset.smul_sum]
      · funext j
        change -(∑ i,(c*(C i j)) • Q i)=c • (-∑ i,C i j • Q i)
        simp only [mul_smul,Finset.smul_sum,smul_neg]
    · simp

/-- The mandatory constants are relations without any independence assumption. -/
theorem bilinearKoszulRow_constants (μ : V →ₗ[K] U →ₗ[K] A)
    (Q : I → V) (E : J → U) (P : W →ₗ[K] A) :
    (bilinearKoszulRow μ Q E P).comp (bilinearKoszulConstants Q E)=0 := by
  ext C
  change (∑ i,μ (Q i) (∑ j,C i j • E j))+
    (∑ j,μ (-∑ i,C i j • Q i) (E j))+P 0=0
  simp only [map_sum,map_smul,map_neg,LinearMap.sum_apply,LinearMap.neg_apply,
    LinearMap.smul_apply,map_zero,add_zero,Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun j i => C i j • μ (Q i) (E j))]
  exact add_neg_cancel _

theorem bilinearKoszulConstants_injective (Q : I → V) (E : J → U)
    (hE : LinearIndependent K E) :
    Function.Injective (bilinearKoszulConstants (K := K) (W := W) Q E) := by
  intro C D hCD
  funext i
  apply (linearIndependent_iff_injective_fintypeLinearCombination.mp hE)
  exact congrArg (fun x : ((I → U) × (J → V)) × W => x.1.1 i) hCD

/-- Row maps are polynomial in the same parameters as their scalar, new-layer,
and product families. -/
theorem bilinearKoszulRow_polynomial
    (μ : V →ₗ[K] U →ₗ[K] A) (Q : I → (ι → K) → V) (E : J → (ι → K) → U)
    (P : (ι → K) → (W →ₗ[K] A))
    (hQ : ∀ i,IsPolynomialFamily (Q i)) (hE : ∀ j,IsPolynomialFamily (E j))
    (hP : IsPolynomialFamily P) :
    IsPolynomialFamily (fun a => bilinearKoszulRow μ (fun i => Q i a) (fun j => E j a) (P a)) := by
  apply isPolynomialFamily_linearMap
  intro x
  exact ((IsPolynomialFamily.sum (fun i => (hQ i).linear_comp (μ.flip (x.1.1 i)))).add
    (IsPolynomialFamily.sum (fun j => (hE j).linear_comp (μ (x.1.2 j))))).add
      (hP.linear_comp (LinearMap.applyₗ (R := K) (M₂ := A) x.2))

theorem bilinearKoszulConstants_polynomial
    (Q : I → (ι → K) → V) (E : J → (ι → K) → U)
    (hQ : ∀ i,IsPolynomialFamily (Q i)) (hE : ∀ j,IsPolynomialFamily (E j)) :
    IsPolynomialFamily (fun a => bilinearKoszulConstants (K := K) (W := W) (fun i => Q i a) (fun j => E j a)) := by
  classical
  apply isPolynomialFamily_linearMap
  intro C
  have hleft (i : I) : IsPolynomialFamily (fun a => ∑ j,C i j • E j a) :=
    IsPolynomialFamily.sum (fun j => (isPolynomialFamily_const (C i j)).smul (hE j))
  have hright (j : J) : IsPolynomialFamily (fun a => -∑ i,C i j • Q i a) :=
    (IsPolynomialFamily.sum (fun i => (isPolynomialFamily_const (C i j)).smul (hQ i))).linear_comp
      (-LinearMap.id)
  have hL : IsPolynomialFamily (fun a i => ∑ j,C i j • E j a) := by
    have hh := IsPolynomialFamily.sum (fun i => (hleft i).linear_comp (LinearMap.single K (fun _ : I => U) i))
    simpa only [LinearMap.single_apply,Finset.univ_sum_single] using hh
  have hR : IsPolynomialFamily (fun a j => -∑ i,C i j • Q i a) := by
    have hh := IsPolynomialFamily.sum (fun j => (hright j).linear_comp (LinearMap.single K (fun _ : J => V) j))
    simpa only [LinearMap.single_apply,Finset.univ_sum_single] using hh
  exact (hL.prod_mk hR).prod_mk (isPolynomialFamily_const (0 : W))

/-- One row witness yields a nonempty principal open in the full common
coefficient space; no independent row-wise parameters are introduced. -/
theorem bilinearKoszulRow_open
    (μ : V →ₗ[K] U →ₗ[K] A) (Q : I → (ι → K) → V) (E : J → (ι → K) → U)
    (P : (ι → K) → (W →ₗ[K] A))
    (hQ : ∀ i,IsPolynomialFamily (Q i)) (hE : ∀ j,IsPolynomialFamily (E j))
    (hP : IsPolynomialFamily P) (a₀ : ι → K)
    (hEI : LinearIndependent K (fun j => E j a₀))
    (hker : (bilinearKoszulRow μ (fun i => Q i a₀) (fun j => E j a₀) (P a₀)).ker=
      (bilinearKoszulConstants (K := K) (W := W) (fun i => Q i a₀) (fun j => E j a₀)).range) :
    ∃ D : MvPolynomial ι K,eval a₀ D≠0 ∧ ∀ a,eval a D≠0 →
      (bilinearKoszulRow μ (fun i => Q i a) (fun j => E j a) (P a)).ker=
        (bilinearKoszulConstants (K := K) (W := W) (fun i => Q i a) (fun j => E j a)).range := by
  obtain ⟨D,hD,hopen⟩ := exact_kernel_general_open _ _
    (bilinearKoszulRow_polynomial μ Q E P hQ hE hP)
    (bilinearKoszulConstants_polynomial Q E hQ hE)
    (fun a => bilinearKoszulRow_constants μ _ _ _) a₀
    (bilinearKoszulConstants_injective _ _ hEI) hker
  exact ⟨D,hD,fun a ha => (hopen a ha).2⟩

end Froberg
