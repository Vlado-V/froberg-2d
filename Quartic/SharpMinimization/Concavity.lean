import Quartic.UniformSurplus.Rational
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.Lattice

/-! Concavity of the exact real sharp profile on the free-layer box. -/
namespace Quartic.SharpMinimization
open Quartic.UniformSurplus
noncomputable section

abbrev Layers := Fin 3 → ℝ

def layerBox (w : ℝ) : Set Layers := Set.Icc 0 (fun _ => w)

def layerPolynomial (w C L e₁ e₂ : ℝ) (n : Layers) : ℝ :=
  C+L*n 0+e₁*H₂Real w (n 0)+e₂*H₂Real w (n 1)+
    H₃Real w (n 0)+H₃Real w (n 1)+H₃Real w (n 2)

theorem H₂Real_concave (w : ℝ) : ConcaveOn ℝ (Set.Icc 0 w) (H₂Real w) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb' : b=1-a := by linarith
  subst b
  simp only [smul_eq_mul]
  have heq : H₂Real w (a*x+(1-a)*y)-(a*H₂Real w x+(1-a)*H₂Real w y)=
      a*(1-a)*(x-y)^2/2 := by unfold H₂Real quadraticReal; ring
  have hp : 0 ≤ a*(1-a)*(x-y)^2/2 := by positivity
  linarith

theorem H₃Real_concave (w : ℝ) : ConcaveOn ℝ (Set.Icc 0 w) (H₃Real w) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb' : b=1-a := by linarith
  subst b
  simp only [smul_eq_mul]
  have hax : 0 ≤ (1+a)*(w-x) := mul_nonneg (by linarith) (sub_nonneg.mpr hx.2)
  have hay : 0 ≤ (2-a)*(w-y) := mul_nonneg (by linarith) (sub_nonneg.mpr hy.2)
  have hbracket : 0 ≤ 3*(w+1)-(1+a)*x-(2-a)*y := by nlinarith
  have hp : 0 ≤ a*(1-a)*(x-y)^2*(3*(w+1)-(1+a)*x-(2-a)*y)/6 := by positivity
  have heq : H₃Real w (a*x+(1-a)*y)-(a*H₃Real w x+(1-a)*H₃Real w y)=
      a*(1-a)*(x-y)^2*(3*(w+1)-(1+a)*x-(2-a)*y)/6 := by
    unfold H₃Real cubicReal
    ring
  linarith

theorem layerPolynomial_concave (w C L e₁ e₂ : ℝ) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) :
    ConcaveOn ℝ (layerBox w) (layerPolynomial w C L e₁ e₂) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hqx₀ : x 0 ∈ Set.Icc 0 w := ⟨hx.1 0,hx.2 0⟩
  have hqy₀ : y 0 ∈ Set.Icc 0 w := ⟨hy.1 0,hy.2 0⟩
  have hqx₁ : x 1 ∈ Set.Icc 0 w := ⟨hx.1 1,hx.2 1⟩
  have hqy₁ : y 1 ∈ Set.Icc 0 w := ⟨hy.1 1,hy.2 1⟩
  have hqx₂ : x 2 ∈ Set.Icc 0 w := ⟨hx.1 2,hx.2 2⟩
  have hqy₂ : y 2 ∈ Set.Icc 0 w := ⟨hy.1 2,hy.2 2⟩
  have h₂₀ := mul_le_mul_of_nonneg_left ((H₂Real_concave w).2 hqx₀ hqy₀ ha hb hab) he₁
  have h₂₁ := mul_le_mul_of_nonneg_left ((H₂Real_concave w).2 hqx₁ hqy₁ ha hb hab) he₂
  have h₃₀ := (H₃Real_concave w).2 hqx₀ hqy₀ ha hb hab
  have h₃₁ := (H₃Real_concave w).2 hqx₁ hqy₁ ha hb hab
  have h₃₂ := (H₃Real_concave w).2 hqx₂ hqy₂ ha hb hab
  simp only [layerPolynomial, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  nlinarith only [h₂₀,h₂₁,h₃₀,h₃₁,h₃₂,
    congrArg (fun z : ℝ => z*C) hab, congrArg (fun z : ℝ => z*(L*x 0)) hab]

/-- Jensen's inequality supplies a member of any finite convex combination
whose value is at most the value at the combination. -/
theorem exists_le_of_combination {w : ℝ} {f : Layers → ℝ}
    (hf : ConcaveOn ℝ (layerBox w) f) (v : Fin 3 → ℝ) (p : Fin 3 → Layers)
    (hv : ∀j, 0 ≤ v j) (hvsum : ∑j, v j=1) (hp : ∀j, p j ∈ layerBox w)
    (n : Layers) (hn : ∑j, v j • p j=n) :
    ∃j, f (p j) ≤ f n := by
  obtain ⟨j,hj⟩ := Finite.exists_min (fun j : Fin 3 => f (p j))
  refine ⟨j, ?_⟩
  have hJ := hf.le_map_sum (t:=Finset.univ) (fun k _ => hv k) hvsum (fun k _ => hp k)
  rw [hn] at hJ
  have hle : ∑ k, v k*f (p j) ≤ ∑ k, v k*f (p k) :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hj k) (hv k))
  rw [←Finset.sum_mul,hvsum,one_mul] at hle
  exact hle.trans hJ

end
end Quartic.SharpMinimization
