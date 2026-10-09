module

public import Froberg.UpperTargetParity
public import Froberg.EvenRestorationSpace

@[expose] public section

/-! The supported scalar deletion leaves every positive output-weight
component unchanged, as required by the literal restoration reduction. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d : ℕ}

theorem supported_deletion_positive_zero
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (p : Forms K (h+m) (2*d)) (hp : D.mkQ p=0) :
    positiveWeightProjection (coreWeight h m) d p.val=0 := by
  have hm : p∈D := by
    have hh : p∈D.mkQ.ker := hp
    rwa [Submodule.ker_mkQ] at hh
  obtain ⟨b,rfl⟩ := hD hm
  exact positiveWeightProjection_zero _ _ _ (scalar_rename_core_weight_zero b)

theorem supported_deletion_odd_zero
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (p : Forms K (h+m) (2*d)) (hp : D.mkQ p=0) :
    parityForm (coreParity h m) 1 p=0 := by
  apply scalar_range_odd_zero p
  apply hD
  have hh : p∈D.mkQ.ker := hp
  rwa [Submodule.ker_mkQ] at hh

end Froberg
