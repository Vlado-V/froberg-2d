module

public import Froberg.CountedJointSelection
public import Froberg.BackgroundFlagSpan
public import Froberg.SupportedOddTarget

@[expose] public section

/-! The generic child flag supplies the supported deletion and even
coverage needed by the concrete background comparison. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q e f u : ℕ}

theorem exists_background_child_deletion
    (Q : Fin q → Forms K m d)
    (E : Fin e → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (hQ : coefficientCokernel K m d q (coefficientCoordinates Q)=genericCokernel K m d q)
    (hu : Function.Surjective (upperTargetMap (backgroundEnumeratedForms
      (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F G))) :
    ∃ D : Submodule K (Forms K (h+m) (2*d)),
      finrank K D=genericCokernel K m d q ∧
      D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range ∧
      Set.InjOn (D.mkQ.comp (renameForm (Fin.natAdd h)))
        (endpointMultiplication (scalarFlagPrefix Q)).range ∧
      ∀ p,parityForm (coreParity h m) 0 p∈D ⊔
        (endpointMultiplication (backgroundEnumeratedForms
          (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F G)).range := by
  let S := Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E
  let family := backgroundEnumeratedForms S F G
  obtain ⟨D,hD,hsupport,hinj,hfill⟩ := exists_supported_old_target_deletion
    (⟨Fin.natAdd h,Fin.natAdd_injective m h⟩ : Fin m ↪ Fin (h+m)) Q
  have hdim : finrank K D=genericCokernel K m d q := by
    rw [hD]
    have hcoord : coefficientForms K m d q (coefficientCoordinates Q)=Q :=
      coefficientCoordinates.symm_apply_apply Q
    have hs : coefficientSpace K m d q (coefficientCoordinates Q)=
        Submodule.span K (Set.range (fun i => (Q i).val)) :=
      congrArg (fun g : Fin q → Forms K m d =>
        Submodule.span K (Set.range (fun i => (g i).val))) hcoord
    change finrank K (EndpointQuotient K m d
      (coefficientSpace K m d q (coefficientCoordinates Q)))=genericCokernel K m d q at hQ
    rw [hs] at hQ
    exact hQ
  have hold : (endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))≤
      (endpointMultiplication family).range := by
    apply rename_endpoint_range_le_of_generators
    intro i
    apply Submodule.subset_span
    refine ⟨Fintype.equivFin _ (Sum.inl (Fin.castAdd e i)),?_⟩
    have hv := congrFun (backgroundEnumeratedForms_reindex S F G)
      (Sum.inl (Fin.castAdd e i))
    exact congrArg Subtype.val (by
      simpa only [Function.comp_apply,Sum.elim_inl,S,Fin.append_left,evenPolynomialToForms_scalar] using hv)
  refine ⟨D,hdim,hsupport,hinj.mono (endpoint_prefix_range_le Q (Nat.sub_le q 1)),?_⟩
  exact upperTarget_even_coverage
    (indexedSplitParity (backgroundSplitIndex (q := q+e) (f := f) (u := u))) family
    (backgroundEnumeratedForms_split_parity S F G) hu D
    (supported_scalar_deletion_properties Q family D hsupport hfill hold).2

variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem childFlag_scalar_properties
    (mu : Forms K m d →ₗ[K] V →ₗ[K] W) (j : ℕ) (C : ℝ)
    (Q : Fin q → Forms K m d)
    (hQ : ChildFlagCondition mu j C (coefficientCoordinates Q)) :
    LinearIndependent K Q ∧
      coefficientCokernel K m d q (coefficientCoordinates Q)=genericCokernel K m d q ∧
      finrank K (EndpointHomology (scalarFlagPrefix Q))=genericHomology K m d (q-1) := by
  have hcoord : coefficientForms K m d q (coefficientCoordinates Q)=Q :=
    coefficientCoordinates.symm_apply_apply Q
  have hi := hQ.1
  have hg : finrank K (EndpointHomology
      (coefficientForms K m d q (coefficientCoordinates Q) ∘ Fin.castLE (Nat.sub_le q 1)))=
        genericHomology K m d (q-1) := hQ.2.2.1
  rw [hcoord] at hi hg
  exact ⟨hi,hQ.2.1,hg⟩

end Froberg
