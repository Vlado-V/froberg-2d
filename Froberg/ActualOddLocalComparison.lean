module

public import Froberg.ActualParityCoefficientKernel
public import Froberg.RetainedLocalComparison

@[expose] public section

/-! The C.6 local comparison follows from the actual odd-source slices,
C.2 separation, and the retained scalar relation equality of B.5. -/
noncomputable section
namespace Froberg
open Module Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {F V W : Type*}
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {m n d r t c : ℕ}

theorem exists_local_comparison_of_odd_separation (hm : 0 < m)
    (D : Submodule K (Forms K n (2*d)))
    (w : Fin n → ZMod 2) (parity : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (hqparity : ∀ i,(q i).val.IsWeightedHomogeneous w (parity i))
    (hD : ∀ z,D.mkQ z=0 → parityForm w 1 z=0)
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
    (coords : oddCoefficientSpace w q ≃ₗ[K] V)
    (eJ : ProjectedEndpointCokernel D.mkQ q ≃ₗ[K] W)
    (phi : F →ₗ[K] Forms K n d) (mu : F →ₗ[K] V →ₗ[K] W)
    (hmu : ∀ z v,mu z (coords (oddCoefficientProjection w parity q hqparity v))=
      eJ (projectedQuotientProduct D.mkQ q (phi z) v))
    (C : ℝ) (hC : (t : ℝ)≤C)
    (hslices : HasClosedKernelSlices mu (BilinearCovectorStrata.thinSlices (finrank K W) C))
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
  obtain ⟨dual,_,_,hkernel⟩ := exists_actual_odd_retained_kernel w parity q hq hqparity
    D.mkQ hD hodd T f hf hspan heven hsep coords
  apply exists_local_comparison_from_retained hm D q hq dual
    (coords.toLinearMap.comp (oddCoefficientProjection w parity q hqparity))
    eJ phi mu hmu C hC hslices T (by rw [hspan]; exact le_sup_left)
    old hold hc hgeneric rename hinj hrel hkernel hdeleted

end Froberg
