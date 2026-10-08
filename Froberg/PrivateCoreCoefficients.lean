import Quartic.SplitBigrading
import Froberg.Graded

/-! Adding private variables to a core polynomial matrix. Every private
monomial coefficient is an actual lower-degree core relation. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open MvPolynomial Module Quartic.FreeCoefficients Quartic.FreeCoefficientProducts
open Quartic.ConvolutionLayers Quartic.ConvolutionFreeMultiplication
variable {K : Type*} [Field K] {a z t : ℕ}

lemma liftCoeff_zero_eq_rename (f : Poly K a) :
    liftCoeff (0 : Fin z →₀ ℕ) f=rename (Fin.castAdd z) f := by
  rw [liftCoeff_eq_mul]
  have hz : mergeExponent (0 : Fin a →₀ ℕ) (0 : Fin z →₀ ℕ)=0 := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  simp [hz]

/-- Extraction in private variables commutes with every core polynomial multiplier. -/
theorem freeCoeff_rename_mul (β : Fin z →₀ ℕ) (f : Poly K a) (p : Poly K (a+z)) :
    freeCoeff β (rename (Fin.castAdd z) f*p)=f*freeCoeff β p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
      rw [← merge_core_free α,← liftCoeff_monomial]
      rw [← liftCoeff_zero_eq_rename f,liftCoeff_mul,zero_add,
        freeCoeff_liftCoeff,freeCoeff_liftCoeff]
      split_ifs <;> simp
  | add p q hp hq => simp only [mul_add,map_add,hp,hq]

variable {I J : Type*} [Fintype I]

/-- Multiplication by a finite matrix whose entries use only core variables. -/
def corePolynomialMatrix (q : J → I → Poly K a) :
    (I → Forms K a t) →ₗ[K] (J → Poly K a) where
  toFun p j := ∑ i,q j i*(p i).val
  map_add' p p' := by ext j; simp [mul_add,Finset.sum_add_distrib]
  map_smul' c p := by ext j; simp [mul_smul_comm,Finset.smul_sum]

def extendedCorePolynomialMatrix (q : J → I → Poly K a) :
    (I → Forms K (a+z) t) →ₗ[K] (J → Poly K (a+z)) where
  toFun p j := ∑ i,rename (Fin.castAdd z) (q j i)*(p i).val
  map_add' p p' := by ext j; simp [mul_add,Finset.sum_add_distrib]
  map_smul' c p := by ext j; simp [mul_smul_comm,Finset.smul_sum]

/-- Actual lower-degree injectivity is preserved on adjoining any number
of private variables, without a new general-position assumption. -/
theorem extendedCorePolynomialMatrix_injective (q : J → I → Poly K a)
    (hq : ∀ c≤t,Function.Injective (corePolynomialMatrix (t := c) q)) :
    Function.Injective (extendedCorePolynomialMatrix (z := z) (t := t) q) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  funext i
  apply Subtype.ext
  apply eq_zero_of_freeCoeff
  intro β
  by_cases hβ : β.degree≤t
  · let pβ : I → Forms K a (t-β.degree) := fun i =>
      ⟨freeCoeff β (p i).val,freeCoeff_homogeneous _ (p i).property β⟩
    have hrel : corePolynomialMatrix q pβ=0 := by
      funext j
      have hh := congrArg (freeCoeff β) (congrFun hp j)
      simpa only [extendedCorePolynomialMatrix,corePolynomialMatrix,pβ,LinearMap.coe_mk,AddHom.coe_mk,
        map_sum,freeCoeff_rename_mul,Pi.zero_apply,map_zero] using hh
    have hz : pβ=0 := (hq (t-β.degree) (Nat.sub_le _ _)) (hrel.trans (map_zero _).symm)
    exact congrArg Subtype.val (congrFun hz i)
  · exact freeCoeff_eq_zero_of_degree_lt _ (p i).property β (by omega)

end Froberg
