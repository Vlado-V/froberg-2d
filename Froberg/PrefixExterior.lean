import Froberg.ProjectionFailure

/-! A deficient prefix forces every padded mixed determinant to vanish. -/
noncomputable section
namespace Froberg.ProjectionFailure
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {r t l : ℕ}

/-- Independence of a full concatenated tuple implies independence of any
initial portion of the second block. -/
theorem independent_append_prefix (ht : t ≤ l) (a : Fin r → V) (b : Fin l → V)
    (hi : LinearIndependent K (Fin.append a b)) :
    LinearIndependent K (Fin.append a (b ∘ Fin.castLE ht)) := by
  have hr : r+t ≤ r+l := Nat.add_le_add_left ht r
  have he : (Fin.append a b) ∘ Fin.castLE hr = Fin.append a (b ∘ Fin.castLE ht) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hh : Fin.castLE hr (Fin.castAdd t j) = Fin.castAdd l j := Fin.ext rfl
      simp only [Function.comp_apply,hh,Fin.append_left]
    · have hh : Fin.castLE hr (Fin.natAdd r j) = Fin.natAdd r (Fin.castLE ht j) := Fin.ext rfl
      simp only [Function.comp_apply,hh,Fin.append_right]
  rw [← he]
  exact hi.comp (Fin.castLE hr) (Fin.castLE_injective hr)

/-- If a prefix lies in too small a subspace, adding any further rows still
produces a zero exterior product. -/
theorem padded_exterior_eq_zero [FiniteDimensional K V]
    (ht : t ≤ l) (S : Submodule K V) (a : Fin r → V) (b : Fin l → V)
    (ha : ∀ i, a i ∈ S) (hb : ∀ i : Fin t, b (Fin.castLE ht i) ∈ S)
    (hd : finrank K S < r+t) :
    exteriorPower.ιMulti K (r+l) (Fin.append a b) = 0 := by
  apply AlternatingMap.map_linearDependent
  intro hi
  have hp := independent_append_prefix ht a b hi
  have hm : ∀ i, Fin.append a (b ∘ Fin.castLE ht) i ∈ S := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using ha j
    · simpa only [Fin.append_right,Function.comp_apply] using hb j
  have hp' : LinearIndependent K
      (fun i => (⟨Fin.append a (b ∘ Fin.castLE ht) i,hm i⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hp
  have hc := hp'.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hc
  omega

end Froberg.ProjectionFailure
