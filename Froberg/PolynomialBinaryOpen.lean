import Froberg.PolynomialProperties

noncomputable section
namespace Froberg
open MvPolynomial
variable {K I : Type*} [Field K] [Infinite K]

theorem principal_property_inter {P Q : (I → K) → Prop}
    (hP : ∃ D : MvPolynomial I K, (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → P a)
    (hQ : ∃ D : MvPolynomial I K, (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → Q a) :
    ∃ D : MvPolynomial I K, (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → P a ∧ Q a := by
  obtain ⟨D,⟨a,ha⟩,hD⟩ := hP
  obtain ⟨E,⟨b,hb⟩,hE⟩ := hQ
  have hd : D≠0 := by intro hz; simpa [hz] using ha
  have he : E≠0 := by intro hz; simpa [hz] using hb
  have hex : ∃ a,eval a (D*E)≠0 := by
    by_contra hh
    push_neg at hh
    apply mul_ne_zero hd he
    apply MvPolynomial.funext
    intro a
    simpa only [map_zero] using hh a
  refine ⟨D*E,hex,?_⟩
  intro a ha
  have hab : eval a D≠0 ∧ eval a E≠0 := by simpa only [map_mul,mul_ne_zero_iff] using ha
  exact ⟨hD a hab.1,hE a hab.2⟩

end Froberg
