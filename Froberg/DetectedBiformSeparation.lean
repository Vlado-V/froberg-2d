import Froberg.DetectedBiformFamily
import Froberg.BiformVectorQuotient
import Froberg.QuadraticSeparationRow

/-! The detected biform witness separates outer symmetric products from
the full scalar coefficient row in the actual polynomial coordinates. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {h n d t c q f R s : ℕ}

theorem scalarCoefficientRow_injective (Q : Fin q → Forms K n d)
    (hQ : Function.Injective (prefixMultiplication Q t)) :
    Function.Injective (scalarCoefficientRow (c := c) (t := t) Q) := by
  intro x y hxy
  have hk (k : Fin c) : (fun i => x i k)=(fun i => y i k) := by
    apply hQ
    apply Subtype.ext
    rw [prefixMultiplication_val,prefixMultiplication_val]
    exact congrFun hxy k
  funext i k
  exact congrFun (hk k) i

theorem scalarCoefficientRow_mem (Q : Fin q → Forms K n d)
    (x : Fin q → Fin c → Forms K n t) (k : Fin c) :
    scalarCoefficientRow Q x k ∈ familySpace Q*Forms K n t := by
  change (∑ i,(Q i).val*(x i k).val)∈familySpace Q*Forms K n t
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i,rfl⟩) (x i k).property

theorem scalar_detected_biform_separation
    (Q : Fin q → Forms K n d) (T : Poly K h →ₗ[K] (Fin c → K))
    (F : Fin f → FullBiform K (Fin h) n R s)
    (hF : LinearIndependent K (fun p =>
      TensorProduct.map (LinearMap.id : (Fin c → K) →ₗ[K] _) (familySpace Q*Forms K n t).mkQ
        (biformOutputMap T (pairProducts (fun i => (F i).val) p))))
    (x : Fin q → Fin c → Forms K n t) (a : Sym2 (Fin f) → K)
    (hrel : scalarCoefficientRow Q x+
      detectedSymmetricProductRow (FullBiform K (Fin h) n R s).subtype
        (biformVectorDetector T) F a=0) : a=0 := by
  exact detected_biform_vector_relation_coefficients T (familySpace Q*Forms K n t)
    (pairProducts (fun i => (F i).val)) hF (scalarCoefficientRow Q x)
    (scalarCoefficientRow_mem Q x) a hrel

theorem exists_scalar_separated_biform_family
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Fin q → Forms K n d)
    (o : ι → Forms K h 1) (T : Poly K h →ₗ[K] (Fin c → K))
    (ho : LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)))
    (C : Submodule K (Poly K n)) (hCdeg : C≤Forms K n (d-1))
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCQ : Disjoint (C*C) (familySpace Q*Forms K n (d-2)))
    (hf : f≤Fintype.card ι*(finrank K C/2)) :
    ∃ F : Fin f → FullBiform K (Fin h) n 1 (d-1),
      LinearIndependent K F ∧
      ∀ (x : Fin q → Fin c → Forms K n (d-2)) (a : Sym2 (Fin f) → K),
        scalarCoefficientRow Q x+
          detectedSymmetricProductRow (FullBiform K (Fin h) n 1 (d-1)).subtype
            (biformVectorDetector T) F a=0 → a=0 := by
  obtain ⟨F,hF⟩ := exists_detected_biform_family o T ho C (C*C)
    (familySpace Q*Forms K n (d-2)) hCdeg hC le_rfl hCQ hf
  have hprod : LinearIndependent K (pairProducts (fun i => (F i).val)) := by
    exact LinearIndependent.of_comp
      ((TensorProduct.map (LinearMap.id : (Fin c → K) →ₗ[K] _)
        (familySpace Q*Forms K n (d-2)).mkQ).comp (biformOutputMap T)) hF
  have hi : LinearIndependent K F :=
    LinearIndependent.of_comp (FullBiform K (Fin h) n 1 (d-1)).subtype
      (linearIndependent_of_pairProducts (fun i => (F i).val) hprod)
  exact ⟨F,hi,scalar_detected_biform_separation Q T F hF⟩

end Froberg
