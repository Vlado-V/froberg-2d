module

public import Froberg.GenericDimensions

@[expose] public section

/-! Generic nested child tuples on a single nonempty coefficient open. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial
variable {K : Type*} [Field K] [Infinite K] {n d r s : ℕ}

def prefixCoefficients (hrs : r ≤ s) (a : CoefficientIndex n d s → K) :
    CoefficientIndex n d r → K := fun im => a (Fin.castLE hrs im.1,im.2)

theorem prefix_coefficientForms (hrs : r ≤ s) (a : CoefficientIndex n d s → K) :
    coefficientForms K n d r (prefixCoefficients hrs a)=
      coefficientForms K n d s a ∘ Fin.castLE hrs := rfl

theorem generic_tuple_principal_open (hn : 0 < n) (hr : r ≤ (n+d-1).choose d) :
    ∃ P : MvPolynomial (CoefficientIndex n d r) K,
      (∃ a,eval a P ≠ 0) ∧ ∀ a,eval a P ≠ 0 →
        LinearIndependent K (coefficientForms K n d r a) ∧
        coefficientCokernel K n d r a=genericCokernel K n d r ∧
        finrank K (EndpointHomology (coefficientForms K n d r a))=genericHomology K n d r := by
  obtain ⟨D,hD,hc⟩ := genericCokernel_principal_open K n d r hn
  obtain ⟨E,hE,hi⟩ := coefficient_independence_principal_open (K := K) hn hr
  obtain ⟨a,haD,haE⟩ := principal_opens_intersect hD hE
  refine ⟨D*E,⟨a,by simpa only [map_mul] using mul_ne_zero haD haE⟩,?_⟩
  intro a ha
  obtain ⟨haD,haE⟩ := mul_ne_zero_iff.mp (show eval a D*eval a E ≠ 0 by simpa only [map_mul] using ha)
  exact ⟨hi a haE,hc a haD,(genericHomology_eq_at_generic hn a (hi a haE) (hc a haD)).symm⟩

theorem generic_flag_principal_open (hn : 0 < n) (hrs : r ≤ s)
    (hs : s ≤ (n+d-1).choose d) :
    ∃ P : MvPolynomial (CoefficientIndex n d s) K,
      (∃ a,eval a P ≠ 0) ∧ ∀ a,eval a P ≠ 0 →
        LinearIndependent K (coefficientForms K n d s a) ∧
        coefficientCokernel K n d s a=genericCokernel K n d s ∧
        finrank K (EndpointHomology (coefficientForms K n d s a))=genericHomology K n d s ∧
        finrank K (EndpointHomology (coefficientForms K n d s a ∘ Fin.castLE hrs))=
          genericHomology K n d r := by
  classical
  obtain ⟨D,hD,hd⟩ := generic_tuple_principal_open (K := K) hn hs
  obtain ⟨E,⟨b,hb⟩,he⟩ := generic_tuple_principal_open (K := K) hn (hrs.trans hs)
  let u : CoefficientIndex n d r → CoefficientIndex n d s :=
    fun im => (Fin.castLE hrs im.1,im.2)
  let E' : MvPolynomial (CoefficientIndex n d s) K := rename u E
  have hev (a : CoefficientIndex n d s → K) :
      eval a E'=eval (prefixCoefficients hrs a) E := eval_rename _ _ _
  let b' : CoefficientIndex n d s → K := fun im =>
    if h : im.1.val < r then b (⟨im.1.val,h⟩,im.2) else 0
  have hpre : prefixCoefficients hrs b'=b := by
    funext im
    simp [prefixCoefficients,b',im.1.isLt]
  have hE' : ∃ a,eval a E' ≠ 0 := ⟨b',by rw [hev,hpre]; exact hb⟩
  obtain ⟨a,haD,haE⟩ := principal_opens_intersect hD hE'
  refine ⟨D*E',⟨a,by simpa only [map_mul] using mul_ne_zero haD haE⟩,?_⟩
  intro a ha
  obtain ⟨haD,haE⟩ := mul_ne_zero_iff.mp (show eval a D*eval a E' ≠ 0 by simpa only [map_mul] using ha)
  obtain ⟨hi,hc,hh⟩ := hd a haD
  refine ⟨hi,hc,hh,?_⟩
  rw [← prefix_coefficientForms hrs a]
  exact (he _ ((hev a) ▸ haE)).2.2

end Froberg
