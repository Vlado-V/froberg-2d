module

public import Froberg.FlagReplacement
public import Froberg.EndpointSliceLocalComparison
public import Froberg.SupportedDeletionProjection
public import Froberg.CriticalComparisonCounts

@[expose] public section

/-! The prepared flag comparison using literal endpoint slices. Both the
retained relation after replacement and the projected odd-target coordinates
are derived internally. -/
noncomputable section
namespace Froberg
open Module Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {F I : Type*}
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
variable {h m d r t : ℕ}

theorem exists_critical_comparison_of_endpoint_flag
    (hm : 0 < m) (upper : Bool)
    (hr : r=adjacentCriticalCount upper (h+m) d)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (Q : Fin (upperCount m d) → Forms K m d) (hQ : LinearIndependent K Q)
    (b : I → Forms K (h+m) d) (M : Forms K (h+m) d)
    (hpositive : LinearIndependent K (fun i : Option I =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ (i.elim M b)))
    (hbackground : (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed ((embeddedFlagSpace (renameForm (Fin.natAdd h)) Q ⊔
          Submodule.span K (Set.range b)) ⊔ Submodule.span K {M})=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts (embeddedFlagSpace (renameForm (Fin.natAdd h)) Q)
          (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (ε : K) (hε : ε≠0)
    (q : Fin r → Forms K (h+m) d) (hq : LinearIndependent K q)
    (parity : Fin r → ZMod 2)
    (hqparity : ∀ i,(q i).val.IsWeightedHomogeneous (coreParity h m) (parity i))
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m) (1-parity i)) →
      a.val∈oppositeKoszulSpace q parity)
    (f : Fin t → Forms K (h+m) d) (hf : LinearIndependent K f)
    (hspan : Submodule.span K (Set.range q)=
      replacedFlagBackground (renameForm (Fin.natAdd h)) Q (upperCount_pos hm d) b M ε ⊔
        Submodule.span K (Set.range f))
    (heven : ∀ j,parity j=0 → q j∈
      replacedFlagBackground (renameForm (Fin.natAdd h)) Q (upperCount_pos hm d) b M ε)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed (replacedFlagBackground (renameForm (Fin.natAdd h)) Q
        (upperCount_pos hm d) b M ε)).map (D.mkQ.comp formalPolynomialMultiplication)).comap
        (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := h+m) (d := d)))=⊥)
    (hcoverage : ∀ p,parityForm (coreParity h m) 0 p∈D ⊔ (endpointMultiplication q).range)
    (phi : F →ₗ[K] Forms K (h+m) d)
    (hphi : ∀ p,(phi p).val.IsWeightedHomogeneous (coreParity h m) 0)
    (C : ℝ) (hC : (t : ℝ)≤C)
    (hslices : HasClosedKernelSlices (oddQuotientProduct (coreParity h m) q phi hphi)
      (BilinearCovectorStrata.thinSlices (finrank K (oddTargetSpace (coreParity h m) q)) C))
    (hgeneric : finrank K (EndpointHomology (scalarFlagPrefix Q))=
      genericHomology K m d (upperCount m d-1))
    (hinj : Set.InjOn (D.mkQ.comp (renameForm (Fin.natAdd h)))
      (endpointMultiplication (scalarFlagPrefix Q)).range)
    (hdeleted : finrank K D=genericCokernel K m d (upperCount m d)) :
    Nonempty (LocalComparisonData K (h+m) d
      (adjacentCriticalCount upper (h+m) d) (criticalDefect K m d)) := by
  subst r
  let emb : Fin m ↪ Fin (h+m) := ⟨Fin.natAdd h,by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change h+a.val=h+b.val at hv
    omega⟩
  have hrel := flag_replacement_formal_relations (renameForm emb) (renameForm_injective emb)
    Q hQ (upperCount_pos hm d) b M hpositive
    (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := h+m) (d := d))).ker
    hbackground ε hε
  apply exists_local_comparison_of_endpoint_slices hm D (coreParity h m) parity q hq hqparity
    (fun z hz => supported_deletion_odd_zero D hD z ((Submodule.Quotient.mk_eq_zero D).mpr hz))
    hcoverage hodd
    (replacedFlagBackground (renameForm emb) Q (upperCount_pos hm d) b M ε)
    f hf hspan heven hsep phi hphi C hC hslices
    (scalarFlagPrefix Q) (scalarFlagPrefix_independent Q hQ) rfl hgeneric emb hinj hrel hdeleted

end Froberg
