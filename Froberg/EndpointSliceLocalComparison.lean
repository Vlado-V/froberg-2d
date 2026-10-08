import Froberg.ActualOddLocalComparison
import Froberg.ProjectedOddTarget

/-! Literal endpoint odd slices supply the local-comparison contraction.
The source coordinates and full projected-target identification are
constructed from parity and even coverage, rather than supplied separately. -/
noncomputable section
namespace Froberg
open Module Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {F : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
variable {m n d r t c : ℕ}

theorem exists_local_comparison_of_endpoint_slices
    (htwo : (2 : K)≠0) (hm : 0 < m)
    (D : Submodule K (Forms K n (2*d)))
    (w : Fin n → ZMod 2) (parity : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (hqparity : ∀ i,(q i).val.IsWeightedHomogeneous w (parity i))
    (hD : D≤(parityForm w 1).ker)
    (hcoverage : ∀ p,parityForm w 0 p∈D ⊔ (endpointMultiplication q).range)
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous w (1-parity i)) →
      a.val∈oppositeKoszulSpace q parity)
    (T : Submodule K (Forms K n d)) (f : Fin t → Forms K n d)
    (hf : LinearIndependent K f)
    (hspan : Submodule.span K (Set.range q)=T ⊔ Submodule.span K (Set.range f))
    (heven : ∀ j,parity j=0 → q j∈T)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed T).map (D.mkQ.comp formalPolynomialMultiplication)).comap
        (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := n) (d := d)))=⊥)
    (phi : F →ₗ[K] Forms K n d)
    (hphi : ∀ p,(phi p).val.IsWeightedHomogeneous w 0)
    (C : ℝ) (hC : (t : ℝ)≤C)
    (hslices : HasClosedKernelSlices (oddQuotientProduct w q phi hphi)
      (BilinearCovectorStrata.thinSlices (finrank K (oddTargetSpace w q)) C))
    (old : Fin c → Forms K m d) (hold : LinearIndependent K old)
    (hc : c=upperCount m d-1)
    (hgeneric : finrank K (EndpointHomology old)=genericHomology K m d c)
    (rename : Fin m ↪ Fin n)
    (hinj : Set.InjOn (D.mkQ.comp (renameForm rename)) (endpointMultiplication old).range)
    (hrel : (D.mkQ.comp formalPolynomialMultiplication).ker ⊓ formalMixed T=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts ((Submodule.span K (Set.range old)).map (renameForm rename))
          (renameForm rename).range)
    (hdeleted : finrank K D=genericCokernel K m d (upperCount m d)) :
    Nonempty (LocalComparisonData K n d r (criticalDefect K m d)) := by
  apply exists_local_comparison_of_odd_separation htwo hm D w parity q hq hqparity
    (fun z hz => hD ((Submodule.Quotient.mk_eq_zero D).mp hz)) hodd T f hf hspan heven hsep
    (LinearEquiv.refl K (oddCoefficientSpace w q))
    (projectedOddTargetEquiv D w parity q hqparity hD hcoverage)
    phi (oddQuotientProduct w q phi hphi) _ C hC hslices old hold hc hgeneric rename hinj hrel hdeleted
  intro z v
  exact (projectedOddTargetEquiv_product D w parity q hqparity hD hcoverage phi hphi z v).symm

end Froberg
