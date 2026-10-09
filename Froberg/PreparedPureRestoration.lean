module

public import Froberg.PreparedEvenRestoration
public import Froberg.PreparedPureSlots

@[expose] public section

/-! Even-degree restoration in the actual appended quadratic slots. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q h e r : ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def restoredAppendedFamily (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈allEvenIndices d,O j≤homogeneousSubmodule σ K j)
    (p : Space n d q (allEvenIndices d)
      (allEvenCount d h n (e+finrank K (homogeneousSubmodule σ K d))) O)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h n (e+finrank K (homogeneousSubmodule σ K d))))
    (u : Fin (finrank K (homogeneousSubmodule σ K d)) → homogeneousSubmodule σ K d) :
    Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d :=
  (fun i => evenGenerator hO (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2) p (idx i))+
  PolynomialRestoration.pureShift (pureEvenEmbed he)
    (fun k => idx.symm (quadraticTailSlot hd q h n e _ k)) u

theorem restoredAppendedFamily_at_slot (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈allEvenIndices d,O j≤homogeneousSubmodule σ K j)
    (p : Space n d q (allEvenIndices d)
      (allEvenCount d h n (e+finrank K (homogeneousSubmodule σ K d))) O)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h n (e+finrank K (homogeneousSubmodule σ K d))))
    (u : Fin (finrank K (homogeneousSubmodule σ K d)) → homogeneousSubmodule σ K d)
    (k : Fin (finrank K (homogeneousSubmodule σ K d))) :
    (restoredAppendedFamily hd he hO p idx u
      (idx.symm (quadraticTailSlot hd q h n e _ k))).val=
      generator p (quadraticTailSlot hd q h n e _ k)+rename Sum.inl (u k).val := by
  have hi := idx.symm.injective.comp (quadraticTailSlot_injective hd q h n e _)
  have hs := pureShift_at_slot (pureEvenEmbed (n := n) he)
    (fun k => idx.symm (quadraticTailSlot hd q h n e _ k)) hi u k
  simp only [restoredAppendedFamily,Pi.add_apply]
  rw [hs]
  simp only [Equiv.apply_symm_apply,Submodule.coe_add,evenGenerator,pureEvenEmbed]
  rfl

theorem restoredAppendedFamily_away (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈allEvenIndices d,O j≤homogeneousSubmodule σ K j)
    (p : Space n d q (allEvenIndices d)
      (allEvenCount d h n (e+finrank K (homogeneousSubmodule σ K d))) O)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h n (e+finrank K (homogeneousSubmodule σ K d))))
    (u : Fin (finrank K (homogeneousSubmodule σ K d)) → homogeneousSubmodule σ K d)
    (i : Fin r) (hi : ∀ k,quadraticTailSlot hd q h n e _ k≠idx i) :
    (restoredAppendedFamily hd he hO p idx u i).val=generator p (idx i) := by
  have haway : ∀ k,idx.symm (quadraticTailSlot hd q h n e _ k)≠i := by
    intro k hk
    apply hi k
    simpa only [Equiv.apply_symm_apply] using congrArg idx hk
  simp only [restoredAppendedFamily,Pi.add_apply,pureShift_eq_zero_away _ _ _ _ haway,
    add_zero,evenGenerator]

/-- The pure basis and complete positive-row reduction hold simultaneously
for a literal prepared family with the appended quadratic generators. -/
theorem exists_restored_appended_basis (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈allEvenIndices d,O j≤homogeneousSubmodule σ K j)
    (p : Space n d q (allEvenIndices d)
      (allEvenCount d h n (e+finrank K (homogeneousSubmodule σ K d))) O)
    (hp : EvenPositiveReduction p)
    (idx : Fin r ≃ Label q (allEvenIndices d)
      (allEvenCount d h n (e+finrank K (homogeneousSubmodule σ K d)))) :
    ∃ u : Fin (finrank K (homogeneousSubmodule σ K d)) → homogeneousSubmodule σ K d,
      LinearIndependent K u ∧ Submodule.span K (Set.range u)=⊤ ∧
      ∀ c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d,
        PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
          (positiveWeightProjection outputWeight d) (restoredAppendedFamily hd he hO p idx u) c=0 →
        ∃ (M : Fin r → Fin r → K)
          (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (idx i))),
          c-coefficientBoundary (restoredAppendedFamily hd he hO p idx u) M=z.val := by
  letI : Module.Finite K (homogeneousSubmodule σ K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ d)
  obtain ⟨u,hu,hreduce⟩ := restore_even_prepared_basis he hO
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun _ hj => lt_of_lt_of_le (by decide : 0<2) (mem_allEvenIndices.mp hj).1)
    p hp idx (fun k => idx.symm (quadraticTailSlot hd q h n e _ k)) (by
      intro k
      rw [idx.apply_symm_apply,quadraticTailSlot_degree]
      decide)
  exact ⟨u,hu,hu.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _),hreduce⟩

end Froberg.PreparedParameters
