import Froberg.IntermediateKoszul

/-! Comparing the two endpoint relations obtained by multiplying a lower
relation by independent linear forms. The comparison is made in the actual
vector polynomial module, not a hypothetical graded complex. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] {n : ℕ}

/-- Actual multiplication of vector polynomial columns by linear coefficients. -/
def linearVectorCombination (E : I → J → Poly K n) :
    (I → Forms K n 1) →ₗ[K] (J → Poly K n) where
  toFun a j := ∑ i, E i j*(a i).val
  map_add' a b := by
    funext j
    simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
  map_smul' c a := by
    funext j
    simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]

/-- If both independent linear multiples of a vector polynomial lie in the
constant column space, linear-coefficient injectivity forces the vector and
both constant expressions to vanish. -/
theorem lower_relation_comparison (E : I → J → Poly K n)
    (hE : Function.Injective (linearVectorCombination E))
    (ell : Fin 2 → Forms K n 1) (hell : LinearIndependent K ell)
    (x : J → Poly K n) (c₀ c₁ : I → K)
    (h₀ : ∀ j, (ell 0).val*x j=∑ i, c₀ i • E i j)
    (h₁ : ∀ j, (ell 1).val*x j=∑ i, c₁ i • E i j) :
    x=0 ∧ c₀=0 ∧ c₁=0 := by
  classical
  let a : I → Forms K n 1 := fun i => c₀ i • ell 1-c₁ i • ell 0
  have ha : linearVectorCombination E a=0 := by
    funext j
    have hp : (ell 1).val*(∑ i, c₀ i • E i j) =
        (ell 0).val*(∑ i, c₁ i • E i j) := by
      rw [← h₀ j,← h₁ j]
      ring
    change (∑ i, E i j*(c₀ i • (ell 1).val-c₁ i • (ell 0).val))=0
    simp only [mul_sub,Finset.sum_sub_distrib,mul_smul_comm]
    have he₀ : (∑ i, c₀ i • (E i j*(ell 1).val)) = (ell 1).val*(∑ i, c₀ i • E i j) := by
      simp only [Finset.mul_sum,mul_smul_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    have he₁ : (∑ i, c₁ i • (E i j*(ell 0).val)) = (ell 0).val*(∑ i, c₁ i • E i j) := by
      simp only [Finset.mul_sum,mul_smul_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    rw [he₀,he₁,hp,sub_self]
  have haz : a=0 := hE (ha.trans (map_zero _).symm)
  have hc (i : I) : c₀ i=0 ∧ c₁ i=0 := by
    let c : Fin 2 → K := ![-c₁ i,c₀ i]
    have hz : ∑ j, c j • ell j=0 := by
      have h := congrFun haz i
      change c₀ i • ell 1-c₁ i • ell 0=0 at h
      simp only [Fin.sum_univ_two, c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      change (-(c₁ i)) • ell 0 + (c₀ i) • ell 1=0
      calc
        _ = c₀ i • ell 1-c₁ i • ell 0 := by module
        _ = 0 := h
    have h := Fintype.linearIndependent_iff.mp hell c hz
    constructor
    · simpa [c] using h 1
    · have hz₀ : -c₁ i=0 := by simpa [c] using h 0
      exact neg_eq_zero.mp hz₀
  have hc₀ : c₀=0 := funext (fun i => (hc i).1)
  have hc₁ : c₁=0 := funext (fun i => (hc i).2)
  refine ⟨?_,hc₀,hc₁⟩
  funext j
  have hz := h₀ j
  rw [hc₀] at hz
  simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero] at hz
  have hn : (ell 0).val ≠ 0 := by
    intro h
    exact hell.ne_zero 0 (Subtype.ext h)
  exact (mul_eq_zero.mp hz).resolve_left hn

end Froberg
