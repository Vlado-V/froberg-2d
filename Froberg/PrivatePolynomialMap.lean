module

public import Froberg.PrivateFiberRelations
public import Froberg.Graded

@[expose] public section

/-! Literal polynomial multiplication for the private-power columns and the
exact connection with the coefficientwise pair-overlap calculation. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PrivateColumns
open MvPolynomial
variable {K : Type*} [Field K] {a z s b h c : ℕ}

/-- A column output map is applied to the linear-form coefficient and its
scalar coefficient is multiplied by the prescribed private power. -/
def privatePolynomialMap (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K)) :
    (Fin b → Fin h → Forms K (a+z) s) →ₗ[K] (Fin c → Poly K (a+z)) where
  toFun v k := ∑ i, ∑ j, monomial (privateExponent a s ι i) (A i (Pi.single j 1) k)*(v i j).val
  map_add' v w := by
    funext k
    simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
  map_smul' t v := by
    funext k
    simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]

/-- The vector of actual polynomial coefficients at a scalar monomial. -/
def privateSourceCoefficient (v : Fin b → Fin h → Forms K (a+z) s)
    (i : Fin b) (α : Fin (a+z) →₀ ℕ) : Fin h → K := fun j => (v i j).val.coeff α

lemma pi_linear_expansion (A : (Fin h → K) →ₗ[K] (Fin c → K))
    (v : Fin h → K) (k : Fin c) :
    A v k = ∑ j, v j * A (Pi.single j 1) k := by
  classical
  have hv : v = ∑ j, v j • Pi.single j 1 := by
    funext i
    simp [Pi.single_apply]
  calc
    A v k = A (∑ j, v j • Pi.single j 1) k := congrArg (fun x => A x k) hv
    _ = ∑ j, v j * A (Pi.single j 1) k := by
      simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

/-- Exact monomial coefficient formula for the actual polynomial map. -/
theorem privatePolynomialMap_coefficient (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (v : Fin b → Fin h → Forms K (a+z) s) (β : Fin (a+z) →₀ ℕ) (k : Fin c) :
    (privatePolynomialMap ι A v k).coeff β =
      privateCoefficient (s := s) ι A (privateSourceCoefficient v) β k := by
  classical
  simp only [privatePolynomialMap,LinearMap.coe_mk,AddHom.coe_mk,MvPolynomial.coeff_sum,
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

/-- Polynomial relations give the literal coefficient equations used in the
private-overlap kernel calculation. -/
theorem privatePolynomialMap_relation (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (v : Fin b → Fin h → Forms K (a+z) s) (hv : privatePolynomialMap ι A v=0)
    (β : Fin (a+z) →₀ ℕ) : privateCoefficient (s := s) ι A (privateSourceCoefficient v) β=0 := by
  funext k
  rw [← privatePolynomialMap_coefficient]
  rw [hv]
  rfl


/-- The literal private polynomial output lies in the required endpoint degree. -/
theorem privatePolynomialMap_homogeneous (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (v : Fin b → Fin h → Forms K (a+z) s) (k : Fin c) :
    (privatePolynomialMap ι A v k).IsHomogeneous (2*s) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  simpa only [two_mul] using
    (MvPolynomial.isHomogeneous_monomial (A i (Pi.single j 1) k)
      (privateExponent_degree ι i)).mul (v i j).property

/-- Finite-dimensional form of the same private polynomial map. -/
def homogeneousPrivatePolynomialMap (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K)) :
    (Fin b → Fin h → Forms K (a+z) s) →ₗ[K] (Fin c → Forms K (a+z) (2*s)) :=
  LinearMap.pi fun k => (((LinearMap.proj k).comp (privatePolynomialMap ι A)).codRestrict
    (Forms K (a+z) (2*s)) (fun v => privatePolynomialMap_homogeneous ι A v k))

theorem homogeneousPrivatePolynomialMap_kernel (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K)) :
    (homogeneousPrivatePolynomialMap (a := a) (s := s) ι A).ker=(privatePolynomialMap (a := a) (s := s) ι A).ker := by
  ext v
  constructor
  · intro hv
    change privatePolynomialMap ι A v=0
    funext k
    exact congrArg Subtype.val (congrFun hv k)
  · intro hv
    change homogeneousPrivatePolynomialMap ι A v=0
    funext k
    apply Subtype.ext
    exact congrFun hv k

end Froberg.PrivateColumns
