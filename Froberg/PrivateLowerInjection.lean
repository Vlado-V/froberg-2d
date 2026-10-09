module

public import Froberg.PrivatePolynomialMap

@[expose] public section

/-! Below the first pair overlap, distinct private powers give an actual
injective polynomial multiplication map, with arbitrary injective output maps. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PrivateColumns
open MvPolynomial
variable {K : Type*} [Field K] {a z s t b h c : ℕ}

/-- The private-column multiplication map with arbitrary coefficient degree. -/
def privatePolynomialMapAt (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K)) :
    (Fin b → Fin h → Forms K (a+z) t) →ₗ[K] (Fin c → Poly K (a+z)) where
  toFun v k := ∑ i, ∑ j, monomial (privateExponent a s ι i) (A i (Pi.single j 1) k)*(v i j).val
  map_add' v w := by
    funext k
    simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
  map_smul' u v := by
    funext k
    simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]

theorem privatePolynomialMapAt_coefficient (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (v : Fin b → Fin h → Forms K (a+z) t) (β : Fin (a+z) →₀ ℕ) (k : Fin c) :
    (privatePolynomialMapAt (s := s) ι A v k).coeff β =
      privateCoefficient (s := s) ι A (privateSourceCoefficient v) β k := by
  classical
  simp only [privatePolynomialMapAt,LinearMap.coe_mk,AddHom.coe_mk,MvPolynomial.coeff_sum,
    coeff_monomial_mul',privateCoefficient,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : privateExponent a s ι i ≤ β
  · simp only [hi,ite_true]
    rw [pi_linear_expansion]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · simp only [hi,ite_false,Finset.sum_const_zero,Pi.zero_apply]

/-- A coefficient of degree strictly below the private exponent cannot meet
another private column, so injectivity is unconditional in this range. -/
theorem privatePolynomialMapAt_injective (ht : t<s) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i, Function.Injective (A i)) :
    Function.Injective (privatePolynomialMapAt (a := a) (s := s) (t := t) ι A) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  funext i j
  apply Subtype.ext
  apply MvPolynomial.ext
  intro α
  by_cases hα : α.degree=t
  · let β := privateExponent a s ι i+α
    have hβ : β.degree=s+t := by simp only [β,map_add,privateExponent_degree,hα]
    have hunique (k : Fin b) (hki : k≠i) : ¬privateExponent a s ι k≤β := by
      intro hk
      have hsum := private_pair_le ι (Ne.symm hki)
        (show privateExponent a s ι i≤β from le_add_right le_rfl) hk
      have hd := Finsupp.degree_mono hsum
      simp only [map_add,privateExponent_degree,hβ] at hd
      omega
    have he : privateCoefficient (s := s) ι A (privateSourceCoefficient v) β =
        A i (privateSourceCoefficient v i α) := by
      unfold privateCoefficient
      rw [Finset.sum_eq_single i]
      · rw [if_pos (show privateExponent a s ι i≤β from le_add_right le_rfl)]
        simp only [β,add_tsub_cancel_left]
      · intro k _ hki
        exact if_neg (hunique k hki)
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    have hzero : privateCoefficient (s := s) ι A (privateSourceCoefficient v) β=0 := by
      funext k
      rw [← privatePolynomialMapAt_coefficient, hv]
      rfl
    rw [he] at hzero
    have hc := hA i (hzero.trans (map_zero _).symm)
    exact congrFun hc j
  · exact (v i j).property.coeff_eq_zero hα

theorem privatePolynomialMapAt_homogeneous (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (v : Fin b → Fin h → Forms K (a+z) t) (k : Fin c) :
    (privatePolynomialMapAt (s := s) ι A v k).IsHomogeneous (s+t) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (MvPolynomial.isHomogeneous_monomial (A i (Pi.single j 1) k)
    (privateExponent_degree ι i)).mul (v i j).property

end Froberg.PrivateColumns
