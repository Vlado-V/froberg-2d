import Quartic.GenericF13
import Quartic.ConvolutionF13Endpoint

/-!
# Full mixed-and-child coefficient openness from the convolution witness

The actual convolution columns define a point of the unrestricted mixed
coefficient space. Their polynomial and quotient maps agree with the proved
convolution maps. Thus the finite-rank determinant argument supplies a
nonempty principal open while both E and Q vary, for every canonical m≥41.
-/
noncomputable section
namespace Quartic.GenericF13Endpoint
open Module MvPolynomial GeneralF13 GenericF13
open ConvolutionPresentation ConvolutionOuterIncidence
open ConvolutionOuterGeneric ConvolutionCubicGeneric ProfileCertificate UniformEndpoint
variable {K : Type*} [Field K] {t w q : ℕ}

/-- The original convolution columns as actual unrestricted mixed coefficients. -/
def convolutionMixed (K : Type*) [Field K] (t w : ℕ) : GeneralF13.Mixed K (t+w) (t+2) := by
  classical
  exact fun k r => ∑ i : Fin t, if columnIndex r i = k then
    (⟨X (Fin.castAdd w i), isHomogeneous_X K _⟩ : Forms K (t+w) 1) else 0

/-- The unrestricted polynomial multiplication is exactly the actual convolution presentation. -/
theorem multiplication_convolution :
    GeneralF13.multiplication (convolutionMixed K t w) =
      ConvolutionFree.presentation (K := K) (t := t) (w := w) (j := 2) := by
  classical
  apply LinearMap.ext
  intro u
  funext r
  apply Subtype.ext
  simp only [GeneralF13.multiplication_val, convolutionMixed, AddSubmonoidClass.coe_finsetSum,
    apply_ite, ZeroMemClass.coe_zero, Finset.sum_mul, ite_mul, zero_mul,
    ConvolutionFree.presentation_apply_val]
  rw [Finset.sum_comm]
  simp

/-- The unrestricted quotient map agrees on the nose with the checked actual convolution F₁₃. -/
theorem f13Map_convolution (Q : Coefficients K t w q) :
    GeneralF13.f13Map (convolutionMixed K t w) Q = ConvolutionF13.f13Map Q := by
  apply LinearMap.ext
  intro x
  obtain ⟨u,rfl⟩ := GeneralF13.sourceProjection_surjective (c := t+2) Q x
  rw [GeneralF13.f13Map_sourceProjection, multiplication_convolution]
  change (fun r => Submodule.Quotient.mk (ConvolutionFree.presentation u r)) =
    ConvolutionF13.f13Map Q (fun k => Submodule.Quotient.mk (u k))
  exact (ConvolutionF13.f13Map_mk Q u).symm

/-- The proven convolution tuple is a witness in the unrestricted coefficient family. -/
theorem convolution_conditions (ht : 2 ≤ t) (Q : Coefficients K t w q)
    (hC : Function.Injective (CubicGeneric.cubicMap Q)) (hO : Function.Injective (outerMap Q)) :
    GenericF13.Conditions (convolutionMixed K t w) Q := by
  refine ⟨independent_of_outer_injective ht Q hO,hC,?_⟩
  rw [f13Map_convolution]
  exact ConvolutionF13.f13Map_injective ht Q hO

/-- Transport actual witness spaces along proved equalities of variable and column counts. -/
theorem transport_witness {m c m' c' : ℕ} (hm : m = m') (hc : c = c')
    (h : ∃ E : GeneralF13.Mixed K m c, ∃ Q : Quadrics K m q, GenericF13.Conditions E Q) :
    ∃ E : GeneralF13.Mixed K m' c', ∃ Q : Quadrics K m' q, GenericF13.Conditions E Q := by
  subst m'
  subst c'
  exact h

/-- An actual witness exists in the correct m-variable and c-column unrestricted family. -/
theorem exists_endpoint_witness [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ E : GeneralF13.Mixed K m (mixedCount m upper),
      ∃ Q : Quadrics K m (upperEndpoint m), GenericF13.Conditions E Q := by
  obtain ⟨Q,hQ⟩ := exists_common_conditions (K := K) m hm upper
  have hc := endpoint_columns_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper)+1 := by unfold coreP; omega
  have hv := ConvolutionOuterGeneric.endpoint_variable_count m hm upper
  have hcols : coreP (mixedCount m upper)+1+2 = mixedCount m upper := by unfold coreP; omega
  have h : ∃ E : GeneralF13.Mixed K
      (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper))
      (coreP (mixedCount m upper)+1+2),
      ∃ Q : Quadrics K (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper))
        (upperEndpoint m), GenericF13.Conditions E Q :=
    ⟨convolutionMixed K _ _, Q, convolution_conditions ht Q hQ.2.1 hQ.2.2.2.1⟩
  exact transport_witness hv hcols h

/-- Nonempty principal-open F₁₃ injectivity in the full actual mixed/child coefficient family. -/
theorem generic_endpoint_conditions [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ D : MvPolynomial (MiddleCoordinates.CoefficientIndex m (mixedCount m upper) (upperEndpoint m)) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        GenericF13.Conditions (MiddleCoordinates.decode a).1 (MiddleCoordinates.decode a).2 := by
  obtain ⟨E,Q,hQ,hC,hF⟩ := exists_endpoint_witness (K := K) m hm upper
  obtain ⟨D,hD,hgood⟩ := GenericF13.principal_open_of_witness E Q hQ hC hF
  exact ⟨D,⟨_,hD⟩,hgood⟩

end Quartic.GenericF13Endpoint
