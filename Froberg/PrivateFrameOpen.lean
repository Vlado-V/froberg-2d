import Froberg.FrameDisjointOpen
import Froberg.DetectedPrivateOutputs

/-! The private detector requirement is a genuine nonempty open in the
same quadratic frame used by the product and target-row constructions. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type*} [Field K] [Infinite K]

lemma quotient_restrict_injective_of_disjoint
    {V : Type*} [AddCommGroup V] [Module K V]
    (D R : Submodule K V) (hDR : Disjoint D R) :
    Function.Injective (D.mkQ.comp R.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  apply Subtype.ext
  have hxD : x.val∈D := (Submodule.Quotient.mk_eq_zero D).mp hx
  exact Submodule.disjoint_def.mp hDR _ hxD x.property

/-- A fixed general private linear family works for every frame in one
nonempty full-coefficient open. Hence this condition can be intersected
with the H2 product-prefix and B7 frame opens before fixing D. -/
theorem private_detector_frame_open {h b H : ℕ}
    (hh : 0<h) (hcap : H+(2*h-1)≤finrank K (Forms K h 2))
    (w : Fin b → Forms K h 1) (hw : ∀ i,w i≠0)
    (hpair : ∀ p : GeneratorPair b,
      LinearIndependent K (![w p.val.1,w p.val.2] : Fin 2 → Forms K h 1)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin H → Forms K h 2))) K,
      (∃ x,eval x P≠0) ∧
      ∀ f : Fin H → Forms K h 2,eval ((Module.finBasis K _).equivFun f) P≠0 →
        let D := Submodule.span K (Set.range f)
        (∀ i,Function.Injective (D.mkQ.comp (mulForm (w i)))) ∧
        (∀ p : GeneratorPair b,∀ x y,
          D.mkQ (mulForm (w p.val.1) x)+D.mkQ (mulForm (w p.val.2) y)=0 →
          ∃ t : K,x=t • w p.val.2 ∧ y=(-t) • w p.val.1) := by
  classical
  let pair (p : GeneratorPair b) : Fin 2 → Forms K h 1 := ![w p.val.1,w p.val.2]
  let R : Fin b ⊕ GeneratorPair b → Submodule K (Forms K h 2) :=
    Sum.elim (fun i => (mulForm (w i)).range) (fun p => (endpointMultiplication (pair p)).range)
  have hdim : ∀ i,H+finrank K (R i)≤finrank K (Forms K h 2) := by
    intro i
    rcases i with i | p
    · change H+finrank K (mulForm (w i)).range≤_
      rw [LinearMap.finrank_range_of_inj (mulForm_injective (w i) (fun hz => hw i (Subtype.ext hz))),
        finrank_forms K h 1 hh]
      simp only [Nat.add_sub_cancel,Nat.choose_one_right]
      omega
    · change H+finrank K (endpointMultiplication (pair p)).range≤_
      rw [linear_pair_output_finrank hh (pair p) (hpair p)]
      exact hcap
  obtain ⟨P,hP,hgood⟩ := frame_disjoint_principal_open R hdim
  refine ⟨P,hP,?_⟩
  intro f hf
  let D := Submodule.span K (Set.range f)
  have hDR (i) := quotient_restrict_injective_of_disjoint D (R i) (hgood f hf i)
  constructor
  · intro i x y hxy
    have hz : (⟨mulForm (w i) x,LinearMap.mem_range_self _ x⟩ : (mulForm (w i)).range)=
        ⟨mulForm (w i) y,LinearMap.mem_range_self _ y⟩ := hDR (Sum.inl i) hxy
    exact mulForm_injective (w i) (fun hz => hw i (Subtype.ext hz)) (congrArg Subtype.val hz)
  · intro p x y hxy
    exact detected_linear_pair_relation hh (pair p) (hpair p) D.mkQ (hDR (Sum.inr p)) x y hxy

end Froberg
