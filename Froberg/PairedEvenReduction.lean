module

public import Froberg.EvenReductionRename

@[expose] public section

/-! A paired-output construction yields the same eventual reduction on
the usual finite set of variables, for every sufficiently large block
size divisible by four. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
universe u
variable {K : Type} [Field K] [Infinite K]

instance homogeneousKernelSpaceFinite {σ : Type*} [Fintype σ]
    {X : Type*} [AddCommGroup X] [Module K X]
    {n d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    (T : ℕ → MvPolynomial σ K →ₗ[K] X) :
    Module.Finite K (Space n d q J counts
      (fun j => homogeneousSubmodule σ K j⊓(T j).ker)) :=
  finite_space (fun _ _ => inf_le_left)

theorem evenReductionOpen_congr_counts {σ : Type*} [Fintype σ]
    {n d q : ℕ} {J : Finset ℕ} {counts counts' : ℕ → ℕ}
    (O : ℕ → Submodule K (MvPolynomial σ K))
    [Module.Finite K (Space n d q J counts O)]
    [Module.Finite K (Space n d q J counts' O)]
    (hcounts : counts=counts') :
    EvenReductionOpen (n := n) (d := d) (q := q) (J := J) (counts := counts) O ↔
      EvenReductionOpen (n := n) (d := d) (q := q) (J := J) (counts := counts') O := by
  subst counts'
  rfl

theorem eventually_even_reduction_from_paired {d : ℕ} (hd : 3≤d)
    (hp : ∀ᶠ w : ℕ in atTop,4∣2*w → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
      let A := Space n d (upperCount n d) (allEvenIndices d)
        (allEvenCount d (2*w) n (e n+extra)) (constrainedOutputs T)
      ∃ D : MvPolynomial (Fin (finrank K A)) K,
        (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
        ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount d h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension d h →
      (∀ R,4≤R → T R=0) →
      let A := Space n d (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+extra)) (fun j => Forms K h j⊓(T j).ker)
      ∃ D : MvPolynomial (Fin (finrank K A)) K,
        (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
        ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  obtain ⟨W,hW⟩ := eventually_atTop.mp hp
  apply eventually_atTop.mpr
  refine ⟨2*W,?_⟩
  intro h hh hdiv extra e he
  let w := h/2
  have htwo : 2*w=h := Nat.mul_div_cancel' (dvd_trans (by decide : 2∣4) hdiv)
  have hw : W≤w := by dsimp [w]; omega
  have hdiv' : 4∣2*w := by simpa only [htwo] using hdiv
  have he' : ∀ᶠ n : ℕ in atTop,
      (e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2) := by
    have hcast : 2*(w : ℝ)=(h : ℝ) := by exact_mod_cast htwo
    simpa only [hcast] using he
  filter_upwards [hW w hw hdiv' extra e he'] with n hn
  intro X _ _ _ T hX hO hT
  let f : (Fin w × Bool) ≃ Fin h := Fintype.equivOfCardEq (by simp [←htwo,Nat.mul_comm])
  let T₀ := fun j => (T j).comp (rename f).toLinearMap
  have hX₀ : finrank K X=deletedTargetCount d (2*w) := by simpa only [htwo] using hX
  have hO₀ : finrank K (constrainedOutputs T₀ 2)=quadraticOutputDimension d (2*w) := by
    exact (homogeneous_kernel_rename_finrank f (T 2) 2).trans (by simpa only [htwo] using hO)
  have hT₀ : ∀ R,4≤R → T₀ R=0 := by
    intro R hR
    simp only [T₀,hT R hR,LinearMap.zero_comp]
  obtain ⟨D,hD,hgood⟩ := hn X T₀ hX₀ hO₀ hT₀
  letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
      (allEvenCount d (2*w) n (e n+extra))
      (fun j => Forms K h j⊓(T j).ker)) := finite_space (fun _ _ => inf_le_left)
  have H := even_positive_reduction_open_constraint_rename T f
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1) D hD hgood
  have hcounts : allEvenCount d (2*w) n (e n+extra)=allEvenCount d h n (e n+extra) := by
    rw [htwo]
  exact (evenReductionOpen_congr_counts (fun j => Forms K h j⊓(T j).ker) hcounts).mp H

end Froberg.PreparedParameters
