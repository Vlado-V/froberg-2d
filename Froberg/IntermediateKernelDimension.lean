module

public import Froberg.IntermediateKoszul

@[expose] public section

/-! The exact dimension of the new-layer constant Koszul kernel. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module MvPolynomial
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
variable {n s d q : ℕ}

theorem intermediateRow_kernel_finrank (hn : 0<n)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i, (e i).degree=s)
    (Q : Fin q → Forms K n d)
    (hE : Function.Injective (multiplication (d := d) e v))
    (hE₀ : Function.Injective (multiplication (d := 0) e v))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply e v he) Q)) :
    finrank K (intermediateRow e v he Q).ker=q*Fintype.card I := by
  rw [intermediateRow_ker_eq_koszul e v he Q hE hQ,
    LinearMap.finrank_range_of_inj (intermediateKoszul_injective e v he Q hE₀)]
  simp only [Module.finrank_pi_fintype,finrank_forms K n 0 hn,Nat.choose_zero_right,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

end Froberg.AttachedMultiplication
