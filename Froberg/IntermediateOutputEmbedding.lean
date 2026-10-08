import Froberg.VectorOutputMap
import Froberg.IntermediateKoszul
import Froberg.Prefix

/-! An exact sparse scalar/new-layer row remains exact after embedding its
output space into a larger output space. The extra scalar summands are free. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg.AttachedMultiplication
open Module MvPolynomial
variable {K I J H : Type*} [Field K] [Fintype I] [Fintype J] [Fintype H]
variable {n s d q : ℕ}

private def coefficientMultiply (f : Forms K n d) : Forms K n s →ₗ[K] Forms K n (s+d) where
  toFun p := ⟨f.val*p.val,by
    change (f.val*p.val).IsHomogeneous (s+d)
    simpa only [add_comm] using f.property.mul p.property⟩
  map_add' p p' := Subtype.ext (mul_add _ _ _)
  map_smul' c p := Subtype.ext (mul_smul_comm _ _ _)

private theorem vectorOutputMap_vectorMultiply
    (L : (J → K) →ₗ[K] (H → K)) (f : Forms K n d) (p : J → Forms K n s) :
    vectorOutputMap L (vectorMultiply f p) = vectorMultiply f (vectorOutputMap L p) :=
  vectorOutputMap_natural L (coefficientMultiply f) p

private theorem homogeneousMultiplication_sum
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (p : I → Forms K n d) :
    homogeneousMultiplication e v he p =
      ∑ i, fun j => v i j • gradedMultiplication
        (⟨monomial (e i) 1,isHomogeneous_monomial 1 (he i)⟩ : Forms K n s) (p i) := by
  funext j
  apply Subtype.ext
  simp only [homogeneousMultiplication_val,multiplication_apply,Finset.sum_apply,
    Submodule.coe_sum,Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i hi
  change monomial (e i) (v i j)*(p i).val = v i j • (monomial (e i) 1*(p i).val)
  rw [← smul_mul_assoc,smul_monomial,smul_eq_mul,mul_one]

theorem vectorOutputMap_homogeneousMultiplication
    (L : (J → K) →ₗ[K] (H → K))
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (p : I → Forms K n d) :
    vectorOutputMap L (homogeneousMultiplication e v he p) =
      homogeneousMultiplication e (fun i => L (v i)) he p := by
  rw [homogeneousMultiplication_sum,homogeneousMultiplication_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact vectorOutputMap_pure L (v i) _

theorem vectorOutputMap_scalarFamily
    (L : (J → K) →ₗ[K] (H → K)) (Q : Fin q → Forms K n d)
    (p : Fin q → J → Forms K n s) :
    vectorOutputMap L (BilinearScalarFamily.multiplication vectorMultiply Q p) =
      BilinearScalarFamily.multiplication vectorMultiply Q (fun i => vectorOutputMap L (p i)) := by
  simp only [BilinearScalarFamily.multiplication_apply,map_sum,vectorOutputMap_vectorMultiply]

/-- Embedding an output space adds only free scalar summands, so it creates no
new row relations whenever the scalar family itself is injective. -/
theorem intermediateRow_ker_output_embedding
    (L : (J → K) →ₗ[K] (H → K)) (hL : Function.Injective L)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K n d)
    (hE : Function.Injective (multiplication (d := d) e v))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply e v he) Q))
    (hfree : Function.Injective (BilinearScalarFamily.multiplication
      (vectorMultiply (J := H) (s := s)) Q)) :
    (intermediateRow e (fun i => L (v i)) he Q).ker =
      (intermediateKoszul e (fun i => L (v i)) he Q).range := by
  obtain ⟨N,hN⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hL)
  have hNv (i : I) : N (L (v i))=v i := LinearMap.congr_fun hN (v i)
  apply le_antisymm
  · rintro ⟨a,b⟩ hx
    have hlo : intermediateRow e v he Q (fun i => vectorOutputMap N (a i),b)=0 := by
      have ht := congrArg (vectorOutputMap (V := Forms K n (s+d)) N) hx
      change vectorOutputMap N (BilinearScalarFamily.multiplication vectorMultiply Q a +
        homogeneousMultiplication e (fun i => L (v i)) he b)=vectorOutputMap N 0 at ht
      rw [map_add,map_zero,vectorOutputMap_scalarFamily,
        vectorOutputMap_homogeneousMultiplication] at ht
      change BilinearScalarFamily.multiplication vectorMultiply Q (fun i => vectorOutputMap N (a i)) +
        homogeneousMultiplication e v he b=0
      simpa only [hNv] using ht
    have hc : (fun i => vectorOutputMap N (a i),b) ∈ (intermediateKoszul e v he Q).range := by
      rw [← intermediateRow_ker_eq_koszul e v he Q hE hQ]
      exact hlo
    obtain ⟨c,hc⟩ := hc
    have hcb : (intermediateKoszul e (fun i => L (v i)) he Q c).2=b :=
      congrArg Prod.snd hc
    refine ⟨c,Prod.ext ?_ hcb⟩
    have hz := intermediateRow_koszul e (fun i => L (v i)) he Q c
    change BilinearScalarFamily.multiplication vectorMultiply Q
      (intermediateKoszul e (fun i => L (v i)) he Q c).1 +
      homogeneousMultiplication e (fun i => L (v i)) he
        (intermediateKoszul e (fun i => L (v i)) he Q c).2=0 at hz
    rw [hcb] at hz
    change BilinearScalarFamily.multiplication vectorMultiply Q a +
      homogeneousMultiplication e (fun i => L (v i)) he b=0 at hx
    apply hfree
    exact add_right_cancel (hz.trans hx.symm)
  · rintro _ ⟨c,rfl⟩
    exact intermediateRow_koszul e (fun i => L (v i)) he Q c

end Froberg.AttachedMultiplication
