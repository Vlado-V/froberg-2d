import Froberg.AllEvenUpperOpen
import Froberg.IndexedPureTail

/-! The common upper-target frame is selected before the pure family.
Its interface uses the actual indexed forms of the final construction. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg Filter Module MvPolynomial Quartic
open scoped Topology
variable {K : Type} [Field K] [CharZero K]

def PureFamilyAdmissible {h d u : ℕ} (U : Fin u → Forms K h d) : Prop :=
  BilinearImage.image (gradedMultiplication (K := K) (n := h) (d := d) (e := 1)).flip
    (Submodule.span K (Set.range U))=⊤ ∧
  (¬Odd d → Submodule.span K (Set.range U)=⊤)

theorem pureFamilyAdmissible_of_span_top {h d u : ℕ} (U : Fin u → Forms K h d)
    (hU : Submodule.span K (Set.range U)=⊤) : PureFamilyAdmissible U := by
  refine ⟨?_,fun _ => hU⟩
  rw [hU]
  apply Submodule.map_injective_of_injective (f := (Forms K h (d+1)).subtype)
    (Submodule.injective_subtype _)
  rw [graded_flip_image_polynomial,Submodule.map_top,Submodule.range_subtype,
    Submodule.map_top,Submodule.range_subtype,forms_mul_forms]

theorem eventually_indexed_upper_frames {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop,∀ F : ℕ → ℕ,
      Tendsto (fun m : ℕ => (F m : ℝ)/(m : ℝ)^(d-1)) atTop
        (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) →
      ∀ᶠ m : ℕ in atTop,∀ r : ℕ,
        countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (r : ℝ) →
        ∃ D : MvPolynomial (Fin (finrank K (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ x,eval x D≠0) ∧
          ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
            eval ((Module.finBasis K _).equivFun frame) D≠0 →
            LinearIndependent K frame ∧
            ∀ (u q : ℕ) (U : Fin u → Forms K h d),PureFamilyAdmissible U →
              HasUpperWitness (m := m) d (F m) r q frame U (fun _ => 0) := by
  filter_upwards [eventually_prepared_target_witness (K := K) hd] with h hh
  intro F hF
  filter_upwards [hh F hF] with m hm
  intro r hr
  obtain ⟨D,hD,hframe⟩ := hm r hr
  refine ⟨D,hD,?_⟩
  intro frame hf
  obtain ⟨hi,hw⟩ := hframe ((Module.finBasis K _).equivFun frame) hf
  simp only [LinearEquiv.symm_apply_apply] at hi hw
  refine ⟨hi,?_⟩
  intro u q U hU
  let S := Submodule.span K (Set.range (fun i => (U i).val))
  have hS : S≤Forms K h d := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact (U i).property)
  have hSm : S=(Submodule.span K (Set.range U)).map (Forms K h d).subtype := by
    rw [Submodule.map_span,←Set.range_comp]
    rfl
  let u₀ : Fin u → S := fun i => ⟨(U i).val,Submodule.subset_span ⟨i,rfl⟩⟩
  have hu₀ : Submodule.span K (Set.range u₀)=⊤ :=
    (Submodule.span_range_subtype_eq_top_iff S (fun i => Submodule.subset_span ⟨i,rfl⟩)).mpr rfl
  have hcut : S*Forms K h 1=Forms K h (d+1) := by
    rw [hSm]
    exact pure_cutoff_polynomial _ hU.1
  have heven : ¬Odd d → S=Forms K h d := by
    intro he
    rw [hSm,hU.2 he,Submodule.map_top,Submodule.range_subtype]
  have hu : (fun i => homogeneousInclusion S hS (u₀ i))=U := by
    funext i
    apply Subtype.ext
    rfl
  have hw' := hw u q S hS u₀ hu₀ hcut heven (fun _ => 0)
    (fun _ => isHomogeneous_zero _ _ _) (fun _ _ _ => by simp)
  rwa [hu] at hw'

theorem OddPureProjectionData.admissible {d h : ℕ} {hd : 1 ≤ d}
    (p : OddPureProjectionData K d h hd) (ho : Odd d) : PureFamilyAdmissible p.U :=
  ⟨p.cutoff,fun hn => False.elim (hn ho)⟩

end Froberg.PreparedTarget
