module

public import Froberg.SharedQuadraticFrame
public import Froberg.PrivateDetectorCapacity

@[expose] public section

/-! The manuscript's rounded quadratic codimension simultaneously fits
all outer symmetric products and the private-power detector conditions. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Filter PrivateColumns
variable {K : Type} [Field K] [Infinite K]

theorem eventually_counted_shared_quadratic_frame {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,
    ∃ o : Fin (outerColumnCount d h) → Forms K h 1,
      LinearIndependent K (pairProducts (fun i => (o i).val)) ∧
      ∀ (a z b : ℕ) (ι : Fin b ↪ Fin z),
      ∃ (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (w : Fin b → Fin h → K)
        (P : MvPolynomial (Fin (finrank K
          (Fin (quadraticOutputDimension d h) → Forms K h 2))) K),
        (∀ i,w i≠0) ∧ (∃ x,eval x P≠0) ∧
        ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
          eval ((Module.finBasis K _).equivFun frame) P≠0 →
          let D := Submodule.span K (Set.range frame)
          ∃ T : Forms K h 2 →ₗ[K] (Fin (finrank K (Forms K h 2 ⧸ D)) → K),
            T.ker=D ∧
            LinearIndependent K (fun p => quadraticPolynomialDetector T
              (pairProducts (fun i => (o i).val) p)) ∧
            (privatePolynomialMap (a := a) (s := d-1) ι
              (fun i => (T.comp (mulForm (e (w i)))).comp e.toLinearMap)).ker=
              Submodule.span K (Set.range
                (koszulVector (privateGenerator (a := a) (s := d-1) ι w))) := by
  filter_upwards [block_parameters_eventually hd,eventually_quadratic_private_detector_capacity hd,
    eventually_ge_atTop (2 : ℕ)] with h hh hp hh2
  let o := coordinateLinearForms (K := K) hh.1
  have ho : LinearIndependent K (pairProducts (fun i => (o i).val)) :=
    coordinateLinearForms_pairProducts_independent hh.1
  refine ⟨o,ho,?_⟩
  intro a z b ι
  have hdim : finrank K (Forms K h 2)=(h+1).choose 2 := by
    rw [finrank_forms K h 2 (by omega)]
    congr 1
  have hdel : deletedTargetCount d h≤(h+1).choose 2 :=
    Nat.choose_le_choose 2 (Nat.add_le_add_right hh.1 1)
  have houter : quadraticOutputDimension d h+(outerColumnCount d h+1).choose 2≤
      finrank K (Forms K h 2) := by
    rw [hdim]
    change (h+1).choose 2-deletedTargetCount d h+deletedTargetCount d h≤(h+1).choose 2
    exact (Nat.sub_add_cancel hdel).le
  exact shared_quadratic_frame_open (a := a) o ho houter hh2
    (by simpa only [hdim] using hp) (by omega : 0<d-1) ι

end Froberg
