module

public import Froberg.RestoredOddEventual
public import Froberg.PreparedAllEvenCounts

@[expose] public section

/-! The actual all-even count has critical scalar density. Thus the
restored-only odd injection open is available for the prescribed counts,
including any fixed number of appended quadratic slots. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K] {h d : ℕ}

theorem eventually_counted_restored_odd_open (hd : 3 ≤ d) (heven : d%2=0)
    (h extra : ℕ) (e : ℕ → ℕ)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
        (idx : Fin (Fintype.card (Label (upperCount m d) (allEvenIndices d)
          (allEvenCount d h m (e m+extra)))) ≃
            Label (upperCount m d) (allEvenIndices d) (allEvenCount d h m (e m+extra)))
        (slot : Fin (finrank K (Forms K h d)) →
          Fin (Fintype.card (Label (upperCount m d) (allEvenIndices d)
            (allEvenCount d h m (e m+extra))))),
      let hJ : ∀ j∈allEvenIndices d,j≤d := fun _ hj => (mem_allEvenIndices.mp hj).2.1
      let hEven : ∀ j∈allEvenIndices d,j%2=0 := fun _ hj => (mem_allEvenIndices.mp hj).2.2
      ∃ D : MvPolynomial (Fin (finrank K (RestoredSpace m d (upperCount m d)
          (allEvenIndices d) (allEvenCount d h m (e m+extra)) O))) K,
        (∃ p : RestoredSpace m d (upperCount m d) (allEvenIndices d)
          (allEvenCount d h m (e m+extra)) O,eval (restoredCoordinates hO p) D≠0) ∧
        ∀ p : RestoredSpace m d (upperCount m d) (allEvenIndices d)
          (allEvenCount d h m (e m+extra)) O,eval (restoredCoordinates hO p) D≠0 →
          Function.Injective (restoredOddRowLinear
            (restoredFamilyLinear heven hO hJ hEven idx slot p)) := by
  let r := fun m => Fintype.card (Label (upperCount m d) (allEvenIndices d)
    (allEvenCount d h m (e m+extra)))
  have hr := allEvenLabel_count_limit hd h extra e he
  filter_upwards [eventually_restored_odd_injective_open (K := K) (h := h)
    (by omega) heven r hr] with m hm
  intro O hO idx slot
  exact hm (upperCount m d) (allEvenIndices d) (allEvenCount d h m (e m+extra)) O hO
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2) idx slot

end Froberg.PreparedParameters
