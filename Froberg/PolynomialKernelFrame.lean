import Quartic.HomogeneousEmptyFiberOpen
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Polynomial kernel vectors near a split surjection. The adjugate formula
is defined on the entire parameter space, and recovers the prescribed kernel
vectors at the base point. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Matrix Quartic
open HomogeneousEmptyFiberOpen
variable {K I W : Type*} [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W] {b : ℕ}

theorem exists_polynomial_kernel_frame
    (P : (I → K) → W →ₗ[K] (Fin b → K)) (hP : IsPolynomialFamily P)
    (p₀ : I → K) (S : (Fin b → K) →ₗ[K] W)
    (hS : (P p₀).comp S=LinearMap.id)
    (U : Submodule K W) (hU : U≤(P p₀).ker) :
    ∃ F : (I → K) → U →ₗ[K] W,
      IsPolynomialFamily F ∧
      (∀ p,(P p).comp (F p)=0) ∧ F p₀=U.subtype := by
  classical
  let M (p : I → K) : Matrix (Fin b) (Fin b) K := LinearMap.toMatrix' ((P p).comp S)
  have hentries (i j : Fin b) : ∃ A : MvPolynomial I K,
      ∀ p,eval p A=M p i j := by
    exact hP ((LinearMap.proj i).comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin b → K) (S (Pi.single j 1))))
  choose entries hA using hentries
  let A : Matrix (Fin b) (Fin b) (MvPolynomial I K) := Matrix.of entries
  have hmatrix (p : I → K) : A.map (eval p)=M p := by
    ext i j
    exact hA i j p
  have hdet : IsPolynomialFamily (fun p => (M p).det) := by
    have h := polynomial_eval_family (Matrix.det A)
    have he : (fun p => eval p (Matrix.det A))=(fun p => (M p).det) := by
      funext p
      rw [(eval p).map_det]
      exact congrArg Matrix.det (hmatrix p)
    rwa [he] at h
  have hadj (i j : Fin b) : IsPolynomialFamily (fun p => (M p).adjugate i j) := by
    have h := polynomial_eval_family (A.adjugate i j)
    have he : (fun p => eval p (A.adjugate i j))=(fun p => (M p).adjugate i j) := by
      funext p
      have ha := (eval p).map_adjugate A
      simp only [RingHom.mapMatrix_apply] at ha
      have hh : A.adjugate.map (eval p)=(M p).adjugate :=
        ha.trans (congrArg Matrix.adjugate (hmatrix p))
      exact congrArg (fun N : Matrix (Fin b) (Fin b) K => N i j) hh
    rwa [he] at h
  let F (p : I → K) : U →ₗ[K] W :=
    (M p).det • U.subtype-S.comp ((M p).adjugate.mulVecLin.comp ((P p).comp U.subtype))
  refine ⟨F,?_,?_,?_⟩
  · apply isPolynomialFamily_linearMap
    intro u
    have hcoord (j : Fin b) : IsPolynomialFamily (fun p => P p u.val j) :=
      hP.linear_comp ((LinearMap.proj j).comp
        (LinearMap.applyₗ (R := K) (M₂ := Fin b → K) u.val))
    have hmul : IsPolynomialFamily (fun p => (M p).adjugate *ᵥ P p u.val) := by
      have hs := IsPolynomialFamily.sum (fun i : Fin b =>
        (IsPolynomialFamily.sum (fun j : Fin b => (hadj i j).smul (hcoord j))).linear_comp
          (LinearMap.single K (fun _ : Fin b => K) i))
      convert hs using 1
      funext p
      change (M p).adjugate *ᵥ P p u.val=
        ∑ i,Pi.single i (((M p).adjugate *ᵥ P p u.val) i)
      symm
      ext i
      simp [Pi.single_apply]
    have hh := (hdet.smul (isPolynomialFamily_const u.val)).add
      ((hmul.linear_comp S).linear_comp (-LinearMap.id))
    convert hh using 1
    funext p
    change (M p).det • u.val-S ((M p).adjugate *ᵥ P p u.val)=
      (M p).det • u.val+ -S ((M p).adjugate *ᵥ P p u.val)
    exact sub_eq_add_neg _ _
  · intro p
    apply LinearMap.ext
    intro u
    change P p ((M p).det • u.val-S ((M p).adjugate *ᵥ P p u.val))=0
    rw [map_sub,map_smul]
    have hm (z : Fin b → K) : P p (S z)=M p *ᵥ z :=
      (LinearMap.toMatrix'_mulVec ((P p).comp S) z).symm
    rw [hm,Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec,sub_self]
  · have hm : M p₀=1 := by
      dsimp only [M]
      rw [hS,LinearMap.toMatrix'_id]
    apply LinearMap.ext
    intro u
    change (M p₀).det • u.val-S ((M p₀).adjugate *ᵥ P p₀ u.val)=u.val
    have hu : P p₀ u.val=0 := hU u.property
    rw [hm,Matrix.det_one,one_smul,hu,Matrix.mulVec_zero,map_zero,sub_zero]

end Froberg
