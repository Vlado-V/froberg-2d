import Froberg.EmptyIntrinsicRow
import Froberg.SingleLayerProfiles
import Froberg.SingleProfileScalar

/-! An inactive new layer is exact at an actual common parameter whenever
its old product columns have one scalar profile and the scalar columns
are injective after that profile is removed. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial MonomialExpansion
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem exists_empty_profile_row_parameter
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (R : J)
    (hz : counts R.val=0) (S : Finset (Fin n)) (j : ℕ)
    (p₀ : Space n d q J counts O)
    (hP : Function.Injective (ProductRows.multiplication counts (layers p₀) J R.val))
    (hprofile : ∀ a,(ProductRows.multiplication counts (layers p₀) J R.val a).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) j)
    (Q : Fin (Fintype.card (Label q J counts)) → Forms K n d)
    (hQ : Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠j) Q (d-R.val))) :
    ∃ p : Space n d q J counts O,
      LinearIndependent K (fun i => intrinsicLayerMap hO R i p) ∧
      (row hO R p).ker=(rowConstants hO R p).range := by
  classical
  letI : IsEmpty (Fin (counts R.val)) := ⟨fun i => by have := i.isLt; omega⟩
  let f := Fintype.equivFin (Label q J counts)
  let p : Space n d q J counts O := (Q ∘ f,p₀.2)
  have hpe : layers p=layers p₀ := rfl
  have hh := intrinsic_empty_single_profile_exact S
    (ProductRows.multiplication counts (layers p) J R.val)
    (by simpa only [hpe] using hP) (by simpa only [hpe] using hprofile) Q hQ
    (fun i => intrinsicLayerMap hO R i p)
  refine ⟨p,linearIndependent_empty_type,?_⟩
  have hh' := bilinearKoszulRow_exact_reindex f (Equiv.refl (Fin (counts R.val)))
    fullBiformScalarProduct Q (fun i => intrinsicLayerMap hO R i p)
    (ProductRows.multiplication counts (layers p) J R.val) hh
  exact hh'

variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_strong_quartic_empty_row_parameter {h : ℕ}
    (T : ℕ → Poly K h →ₗ[K] X)
    (hz : ∀ k∈J,k≠2 → counts k=0) (R : J) (hR : R.val≠2)
    (S : Finset (Fin n)) (hS : S.card≤Sᶜ.card)
    (hm : counts 2≤(2*(h/2).choose 2-finrank K X)*(S.card.choose 2/2))
    (Q : Fin (Fintype.card (Label q J counts)) → Forms K n 4)
    (hQ : Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠2) Q (4-R.val))) :
    ∃ p : Space n 4 q J counts (fun j => Forms K h j⊓(T j).ker),
      LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) R i p) ∧
      (row (fun _ _ => inf_le_left) R p).ker=(rowConstants (fun _ _ => inf_le_left) R p).range := by
  obtain ⟨p,hp,hprofile⟩ := exists_strong_quartic_profile_parameter (q := q) T hz S hS hm
  exact exists_empty_profile_row_parameter (fun _ _ => inf_le_left) R (hz _ R.property hR)
    S 2 p (hp R.val) (hprofile R.val) Q hQ

end Froberg.PreparedParameters
