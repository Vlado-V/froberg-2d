module

public import Froberg.EvenRelativeFamilies
public import Froberg.OddEndpointScalarSlices

@[expose] public section

/-! The actual relative quotient in even-background coordinates. -/
noncomputable section
set_option maxHeartbeats 1400000
namespace Froberg
open Module MvPolynomial TensorProduct BilinearScalarFamily
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f e : ℕ}

theorem evenRelativeFamily_range (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (E : Fin e → biformParitySpace K h m d 0) :
    (evenRelativeFamily hdp Q F E).range.map (evenBackgroundTargetEquiv hdp Q F).toLinearMap=
      (oddEvenRelativeMap (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily E).range := by
  ext z
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨_,(evenRelativeFamily_compatible hdp Q F E a).symm⟩
  · rintro ⟨a,rfl⟩
    let v := fun i => (evenBackgroundSourceEquiv hdp F).symm (a i)
    refine ⟨evenRelativeFamily hdp Q F E v,⟨v,rfl⟩,?_⟩
    rw [LinearEquiv.coe_toLinearMap,evenRelativeFamily_compatible]
    congr 1
    funext i
    exact (evenBackgroundSourceEquiv hdp F).apply_symm_apply (a i)

def evenRelativeQuotientEquiv (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (E : Fin e → biformParitySpace K h m d 0) :
    (EvenBackgroundTarget hdp Q F ⧸ (evenRelativeFamily hdp Q F E).range) ≃ₗ[K]
      ((biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations
        (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily) ⧸
      (oddEvenRelativeMap (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily E).range) :=
  Submodule.Quotient.equiv _ _ (evenBackgroundTargetEquiv hdp Q F)
    (evenRelativeFamily_range hdp Q F E)

theorem evenRelativeQuotient_compatible (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (E : Fin e → biformParitySpace K h m d 0) (p : Forms K m d)
    (v : EvenBackgroundSource hdp F) :
    evenRelativeQuotientEquiv hdp Q F E
      ((evenRelativeFamily hdp Q F E).range.mkQ (evenBackgroundScalar hdp Q F p v))=
      (oddEvenRelativeMap (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily E).range.mkQ
      (oddBackgroundScalarProduct (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily p
          (evenBackgroundSourceEquiv hdp F v)) := by
  change (oddEvenRelativeMap _ _ _ E).range.mkQ
    (evenBackgroundTargetEquiv hdp Q F (evenBackgroundScalar hdp Q F p v))=_
  rw [evenBackgroundEquiv_scalar]

theorem evenRelative_closed_slices (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (E : Fin e → biformParitySpace K h m d 0) (s : ℕ → ℕ)
    (hs : HasClosedKernelSlices (targetPostcompose (evenBackgroundScalar hdp Q F)
      (evenRelativeFamily hdp Q F E).range.mkQ) s) :
    HasClosedKernelSlices (oddEndpointScalarAction
      (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E)
      (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily) s := by
  apply oddEndpointScalarAction_closed_slices
  apply HasClosedKernelSlices.equiv (LinearEquiv.refl K (Forms K m d))
    (evenBackgroundSourceEquiv hdp F) (evenRelativeQuotientEquiv hdp Q F E) _ _ _ s hs
  intro p v
  exact evenRelativeQuotient_compatible hdp Q F E p v

end Froberg
