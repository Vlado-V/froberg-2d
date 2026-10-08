import Froberg.CriticalChildFlag

/-! On the generic scalar flag, a supported deletion has the upper child
cokernel dimension and preserves both upper and hyperplane multiplication
images. These are the exact child data used in the local comparison. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {m n d : ℕ}

theorem critical_child_deletion_principal_open (hm : 0 < m) (f : Fin m ↪ Fin n) (d : ℕ) :
    ∃ P : MvPolynomial (CoefficientIndex m d (upperCount m d)) K,
      (∃ a,eval a P≠0) ∧ ∀ a,eval a P≠0 →
        let Q := coefficientForms K m d (upperCount m d) a
        let old := scalarFlagPrefix Q
        LinearIndependent K Q ∧ LinearIndependent K old ∧
        finrank K (EndpointHomology old)=genericHomology K m d (upperCount m d-1) ∧
        ∃ D : Submodule K (Forms K n (2*d)),
          finrank K D=genericCokernel K m d (upperCount m d) ∧
          D≤(renameForm (K := K) (d := 2*d) f).range ∧
          Set.InjOn (D.mkQ.comp (renameForm f)) (endpointMultiplication Q).range ∧
          Set.InjOn (D.mkQ.comp (renameForm f)) (endpointMultiplication old).range ∧
          (renameForm (K := K) (d := 2*d) f).range.map D.mkQ=
            ((endpointMultiplication Q).range.map (renameForm f)).map D.mkQ := by
  obtain ⟨P,hP,hgood⟩ := critical_child_flag_principal_open (K := K) hm d
  refine ⟨P,hP,?_⟩
  intro a ha
  have hh := hgood a ha
  let Q := coefficientForms K m d (upperCount m d) a
  obtain ⟨D,hD,hsupport,hinj,hfill⟩ := exists_supported_old_target_deletion f Q
  have hdim : finrank K D=genericCokernel K m d (upperCount m d) := by
    change finrank K D=coefficientCokernel K m d (upperCount m d) a at hD
    exact hD.trans hh.2.2.1
  exact ⟨hh.1,hh.2.1,hh.2.2.2.1,D,hdim,hsupport,hinj,
    hinj.mono (endpoint_prefix_range_le Q (Nat.sub_le (upperCount m d) 1)),hfill⟩

end Froberg
