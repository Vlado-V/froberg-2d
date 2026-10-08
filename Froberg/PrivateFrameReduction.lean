import Froberg.PreparedActualPrivateReduction
import Froberg.PrivateFrameConstraints
import Froberg.PrivateReductionRename

/-! The counted private reduction is an open condition in the full family
of coefficients associated with the actual quadratic output frame. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {w h H c a z d q b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}

def privateFrameOutputs (frame : Fin H → Forms K h 2) (j : ℕ) :
    Submodule K (Poly K h) :=
  if j=2 then outputFrameSpace frame else Forms K h j

theorem privateFrameOutputs_homogeneous (frame : Fin H → Forms K h 2) (j : ℕ) :
    privateFrameOutputs frame j≤Forms K h j := by
  by_cases hj : j=2
  · subst j
    simpa only [privateFrameOutputs,ite_true] using outputFrameSpace_homogeneous frame
  · simp only [privateFrameOutputs,if_neg hj,le_refl]

namespace PreparedParameters

def PrivateReductionOpen {σ : Type*} [Fintype σ] {n t : ℕ}
    (O : ℕ → Submodule K (MvPolynomial σ K))
    [Module.Finite K (Space n d q J counts O)]
    (P : Fin t → FullBiform K σ n 1 (d-1)) : Prop :=
  ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
    (∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0 →
      PrivatePositiveReduction p P

theorem privateReductionOpen_congr_outputs {σ : Type*} [Fintype σ] {n t : ℕ}
    {O O' : ℕ → Submodule K (MvPolynomial σ K)}
    [Module.Finite K (Space n d q J counts O)] [Module.Finite K (Space n d q J counts O')]
    (hO : O=O') (P : Fin t → FullBiform K σ n 1 (d-1)) :
    PrivateReductionOpen (q := q) (J := J) (counts := counts) O P ↔
      PrivateReductionOpen (q := q) (J := J) (counts := counts) O' P := by
  subst O'
  rfl

local instance privateFrameSpaceFinite (frame : Fin H → Forms K h 2) {n : ℕ} :
    Module.Finite K (Space n d q J counts (privateFrameOutputs frame)) :=
  finite_space (fun j _ => privateFrameOutputs_homogeneous frame j)

local instance privateFrameConstrainedSpaceFinite {X : Type*} [AddCommGroup X] [Module K X]
    {n : ℕ} (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) :
    Module.Finite K (Space n d q J counts (constrainedOutputs T)) :=
  finite_space (fun _ _ => inf_le_left)

/-- Transport a private coefficient open to the full finite-variable
frame family. The private columns in the conclusion are fixed in the
original finite-variable coordinates. -/
theorem private_frame_reduction_open_rename
    (hd : 0<d) (hJ : ∀ j∈J,j≤d)
    (f : (Fin w × Bool) ≃ Fin h)
    (frame : Fin H → Forms K h 2)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (v : Fin b → Fin h → K)
    (ι : Fin b ↪ Fin z)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL : L.ker=Submodule.span K (Set.range frame))
    (D : MvPolynomial (Fin (finrank K (Space (a+z) d q J counts
      (constrainedOutputs (pairedFrameConstraint f L))))) K)
    (hD : ∃ p : Space (a+z) d q J counts (constrainedOutputs (pairedFrameConstraint f L)),
      eval ((Module.finBasis K _).equivFun p) D≠0)
    (hgood : ∀ p : Space (a+z) d q J counts (constrainedOutputs (pairedFrameConstraint f L)),
      eval ((Module.finBasis K _).equivFun p) D≠0 →
      PrivatePositiveReduction p (privatePowerBiform (a := a) (d := d)
        (fun i => renamedPrivateColumn f e (v i)) ι)) :
    ∃ D' : MvPolynomial (Fin (finrank K (Space (a+z) d q J counts
        (privateFrameOutputs frame)))) K,
      (∃ p : Space (a+z) d q J counts (privateFrameOutputs frame),
        eval ((Module.finBasis K _).equivFun p) D'≠0) ∧
      ∀ p : Space (a+z) d q J counts (privateFrameOutputs frame),
        eval ((Module.finBasis K _).equivFun p) D'≠0 →
        PrivatePositiveReduction p (privatePowerBiform (a := a) (d := d) (fun i => e (v i)) ι) := by
  let T := pairedFrameConstraint f L
  let O := constrainedOutputs T
  have hO : ∀ j∈J,O j≤homogeneousSubmodule (Fin w × Bool) K j := fun _ _ => inf_le_left
  have hspaces : (fun j => (O j).map (rename f).toLinearMap)=privateFrameOutputs frame := by
    funext j
    exact pairedFrameConstraint_spaces_map f frame L hL j
  letI : Module.Finite K (Space (a+z) d q J counts
      (fun j => (O j).map (rename f).toLinearMap)) := by
    rw [hspaces]
    infer_instance
  have hP : ∀ i,(privatePowerBiform (a := a) (d := d) (fun i => e (v i)) ι i).val=
      rename (Sum.map f id) (privatePowerBiform (a := a) (d := d)
        (fun i => renamedPrivateColumn f e (v i)) ι i).val := by
    intro i
    have hh := privatePowerBiform_output_rename (a := a) (d := d) f
      (fun i => renamedPrivateColumn f e (v i)) ι i
    have hl : (fun i => homogeneousVariableEquiv f 1 (renamedPrivateColumn f e (v i)))=
        (fun i => e (v i)) := by
      funext i
      exact (homogeneousVariableEquiv (K := K) f 1).apply_symm_apply (e (v i))
    rw [hl] at hh
    exact hh
  have hout := private_positive_reduction_open_output_rename hd hO hJ f
    (privatePowerBiform (a := a) (d := d) (fun i => renamedPrivateColumn f e (v i)) ι)
    (privatePowerBiform (a := a) (d := d) (fun i => e (v i)) ι) hP D hD hgood
  exact (privateReductionOpen_congr_outputs hspaces
    (privatePowerBiform (a := a) (d := d) (fun i => e (v i)) ι)).mp hout

end PreparedParameters
end Froberg
