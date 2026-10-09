module

public import Froberg.TensorVectorEmbedding
public import Froberg.IntermediateKernelDimension

@[expose] public section

/-! The exact scalar/new-layer row transported to genuine split polynomials. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K]
variable {I J σ : Type*} [Fintype I] [Fintype J]
variable {n s d q : ℕ}

/-- Homogeneous coefficient vectors become actual split polynomials. -/
def polynomialFormVector (o : J → MvPolynomial σ K) (s : ℕ) :
    (J → Forms K n s) →ₗ[K] MvPolynomial (σ ⊕ Fin n) K :=
  (polynomialVector o).comp (LinearMap.pi (fun j =>
    (Forms K n s).subtype.comp (LinearMap.proj j)))

@[simp] theorem polynomialFormVector_apply (o : J → MvPolynomial σ K)
    (p : J → Forms K n s) : polynomialFormVector o s p=polynomialVector o (fun j => (p j).val) := rfl

theorem polynomialFormVector_injective (o : J → MvPolynomial σ K) (ho : LinearIndependent K o) :
    Function.Injective (polynomialFormVector (n := n) o s) := by
  intro p p' hp
  have heq := polynomialVector_injective o ho hp
  funext j
  exact Subtype.ext (congrFun heq j)

theorem polynomialFormVector_homogeneous (o : J → MvPolynomial σ K) {R : ℕ}
    (ho : ∀ j,(o j).IsHomogeneous R) (p : J → Forms K n s) :
    (polynomialFormVector o s p).IsHomogeneous (R+s) :=
  polynomialVector_homogeneous o _ ho (fun j => (p j).property)

namespace AttachedMultiplication

def polynomialIntermediateRow (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K n d) :
    ((Fin q → J → Forms K n s) × (I → Forms K n d)) →ₗ[K] MvPolynomial (σ ⊕ Fin n) K :=
  (polynomialFormVector o (s+d)).comp (intermediateRow e v he Q)

/-- The scalar part is literal multiplication by the scalar forms after
embedding the output coefficients. -/
theorem polynomialFormVector_vectorMultiply (o : J → MvPolynomial σ K)
    (f : Forms K n d) (p : J → Forms K n s) :
    polynomialFormVector o (s+d) (vectorMultiply f p) =
      rename Sum.inr f.val * polynomialFormVector o s p :=
  polynomialVector_scalar_mul o (fun j => (p j).val) f.val

theorem polynomialIntermediateRow_ker (o : J → MvPolynomial σ K)
    (ho : LinearIndependent K o)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K n d)
    (hE : Function.Injective (multiplication (d := d) e v))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply e v he) Q)) :
    (polynomialIntermediateRow o e v he Q).ker=(intermediateKoszul e v he Q).range := by
  have hk : (polynomialIntermediateRow o e v he Q).ker=(intermediateRow e v he Q).ker := by
    ext x
    change polynomialFormVector o (s+d) (intermediateRow e v he Q x)=0 ↔
      intermediateRow e v he Q x=0
    exact (polynomialFormVector_injective o ho).eq_iff' (map_zero _)
  rw [hk]
  exact intermediateRow_ker_eq_koszul e v he Q hE hQ

/-- The split polynomial row has exactly the same mandatory kernel dimension. -/
theorem polynomialIntermediateRow_kernel_finrank (hn : 0<n)
    (o : J → MvPolynomial σ K) (ho : LinearIndependent K o)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K n d)
    (hE : Function.Injective (multiplication (d := d) e v))
    (hE₀ : Function.Injective (multiplication (d := 0) e v))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply e v he) Q)) :
    finrank K (polynomialIntermediateRow o e v he Q).ker=q*Fintype.card I := by
  rw [polynomialIntermediateRow_ker o ho e v he Q hE hQ,
    LinearMap.finrank_range_of_inj (intermediateKoszul_injective e v he Q hE₀)]
  simp only [Module.finrank_pi_fintype,finrank_forms K n 0 hn,Nat.choose_zero_right,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

end AttachedMultiplication
end Froberg
