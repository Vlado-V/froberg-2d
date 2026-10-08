import Froberg.ProjectedOddTarget
import Froberg.UpperTargetParity

/-! B.7 and the exact old-target deletion identify the full projected
cokernel with the odd quotient used for the scalar contraction argument. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K] [Infinite K] {h m d r s : ℕ}

theorem rename_endpoint_range_le_of_generators {a b t : ℕ}
    (f : Fin a → Fin b) (Q : Fin t → Forms K a d) (q : Fin r → Forms K b d)
    (hgen : ∀ i,(renameForm f (Q i)).val∈
      Submodule.span K (Set.range (fun j => (q j).val))) :
    (endpointMultiplication Q).range.map (renameForm f)≤(endpointMultiplication q).range := by
  rintro _ ⟨_,⟨c,rfl⟩,rfl⟩
  rw [range_endpointMultiplication]
  change MvPolynomial.rename f (endpointMultiplication Q c).val∈
    (Submodule.span K (Set.range (fun j => (q j).val)))*Forms K b d
  rw [endpointMultiplication_val,map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_mul]
  exact Submodule.mul_mem_mul (hgen i) (c i).property.rename_isHomogeneous

def supportedProjectedOddTargetEquiv
    (Q : Fin s → Forms K m d) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K (h+m) d)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous (coreParity h m) (e i))
    (hupper : Function.Surjective (upperTargetMap q))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hfill : (renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range.map D.mkQ=
      ((endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))).map D.mkQ)
    (hold : (endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))≤
      (endpointMultiplication q).range) :
    ProjectedEndpointCokernel D.mkQ q ≃ₗ[K] oddTargetSpace (coreParity h m) q :=
  projectedOddTargetEquiv D (coreParity h m) e q hq
    (supported_scalar_deletion_properties Q q D hD hfill hold).1
    (upperTarget_even_coverage e q hq hupper D
      (supported_scalar_deletion_properties Q q D hD hfill hold).2)

@[simp] theorem supportedProjectedOddTargetEquiv_class
    (Q : Fin s → Forms K m d) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K (h+m) d)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous (coreParity h m) (e i))
    (hupper : Function.Surjective (upperTargetMap q))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hfill : (renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range.map D.mkQ=
      ((endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))).map D.mkQ)
    (hold : (endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))≤
      (endpointMultiplication q).range) (p : Forms K (h+m) (2*d)) :
    supportedProjectedOddTargetEquiv Q e q hq hupper D hD hfill hold (projectedTargetClass D q p)=
      oddTargetClass (coreParity h m) q p := rfl

theorem exists_supported_odd_target_equiv
    (Q : Fin s → Forms K m d) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K (h+m) d)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous (coreParity h m) (e i))
    (hupper : Function.Surjective (upperTargetMap q))
    (hold : (endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))≤
      (endpointMultiplication q).range) :
    ∃ (D : Submodule K (Forms K (h+m) (2*d)))
      (E : ProjectedEndpointCokernel D.mkQ q ≃ₗ[K] oddTargetSpace (coreParity h m) q),
      finrank K D=finrank K (EndpointQuotient K m d
        (Submodule.span K (Set.range (fun i => (Q i).val)))) ∧
      D≤(parityForm (coreParity h m) 1).ker ∧
      Set.InjOn (D.mkQ.comp (renameForm (Fin.natAdd h))) (endpointMultiplication Q).range ∧
      ∀ p,E (projectedTargetClass D q p)=oddTargetClass (coreParity h m) q p := by
  obtain ⟨D,hd,hD,hinj,hfill⟩ := exists_supported_old_target_deletion
    (⟨Fin.natAdd h,Fin.natAdd_injective m h⟩ : Fin m ↪ Fin (h+m)) Q
  exact ⟨D,supportedProjectedOddTargetEquiv Q e q hq hupper D hD hfill hold,hd,
    (supported_scalar_deletion_properties Q q D hD hfill hold).1,hinj,fun _ => rfl⟩

variable {P : Type*} [AddCommGroup P] [Module K P]

theorem supportedProjectedOddTargetEquiv_product
    (Q : Fin s → Forms K m d) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K (h+m) d)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous (coreParity h m) (e i))
    (hupper : Function.Surjective (upperTargetMap q))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hfill : (renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range.map D.mkQ=
      ((endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))).map D.mkQ)
    (hold : (endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))≤
      (endpointMultiplication q).range)
    (F : P →ₗ[K] Forms K (h+m) d)
    (hF : ∀ p,(F p).val.IsWeightedHomogeneous (coreParity h m) 0)
    (p : P) (a : generatorQuotient q) :
    supportedProjectedOddTargetEquiv Q e q hq hupper D hD hfill hold
        (projectedQuotientProduct D.mkQ q (F p) a)=
      oddQuotientProduct (coreParity h m) q F hF p
        (oddCoefficientProjection (coreParity h m) e q hq a) :=
  projectedOddTargetEquiv_product D (coreParity h m) e q hq _ _ F hF p a

end Froberg
