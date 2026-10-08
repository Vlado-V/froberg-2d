import Froberg.SurjectiveImage
import Mathlib.Tactic

/-! Passing an expansion estimate to a quotient, for subspaces in the
upper half of the quotient source dimension. -/
noncomputable section
namespace Froberg
open Module

lemma quotient_growth_identity {A T r t l G : ℝ} (hA : A ≠ 0) (hAr : A+r ≠ 0) :
    ((T+t)/(A+r))*(l+r)+G*(A-l)-t =
      (T/A)*l+(G-(t-((T+t)/(A+r))*r)/A)*(A-l) := by
  field_simp
  <;> ring

namespace SurjectiveImage
variable {K F V V' W W' : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module K W]
  [AddCommGroup W'] [Module K W']
  [FiniteDimensional K V] [FiniteDimensional K V']
  [FiniteDimensional K W] [FiniteDimensional K W']

lemma quotient_upper_growth
    (mu : F →ₗ[K] V →ₗ[K] W) (nu : F →ₗ[K] V' →ₗ[K] W')
    (p : V →ₗ[K] V') (q : W →ₗ[K] W') (hp : Function.Surjective p)
    (hq : Function.Surjective q) (hc : ∀ f v,nu f (p v)=q (mu f v))
    (hA : 0 < finrank K V') (G : ℝ)
    (hg : ∀ S : Submodule K V,
      ((finrank K W : ℝ)/finrank K V)*finrank K S+
        G*min (finrank K S : ℝ) ((finrank K V : ℝ)-finrank K S) ≤
        (finrank K (Quartic.BilinearImage.image mu S) : ℝ))
    (L : Submodule K V') (hL : (finrank K V' : ℝ)/2 ≤ finrank K L) :
    ((finrank K W' : ℝ)/finrank K V')*finrank K L+
      (G-((finrank K (LinearMap.ker q) : ℝ)-
        ((finrank K W : ℝ)/finrank K V)*finrank K (LinearMap.ker p))/finrank K V')*
        ((finrank K V' : ℝ)-finrank K L) ≤
      (finrank K (Quartic.BilinearImage.image nu L) : ℝ) := by
  have hdV := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp,finrank_top] at hdV
  have hdW := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hq,finrank_top] at hdW
  have hdS := finrank_preimage p hp L
  have hgS := hg (L.comap p)
  have hdim := image_finrank_le mu nu p q hp hc L
  have hdVR : (finrank K V' : ℝ)+finrank K (LinearMap.ker p)=finrank K V := by exact_mod_cast hdV
  have hdWR : (finrank K W' : ℝ)+finrank K (LinearMap.ker q)=finrank K W := by exact_mod_cast hdW
  have hdSR : (finrank K (L.comap p) : ℝ)=finrank K L+finrank K (LinearMap.ker p) := by exact_mod_cast hdS
  have hdIR : (finrank K (Quartic.BilinearImage.image mu (L.comap p)) : ℝ) ≤
      finrank K (Quartic.BilinearImage.image nu L)+finrank K (LinearMap.ker q) := by exact_mod_cast hdim
  have hpos : (0 : ℝ) < finrank K V' := by exact_mod_cast hA
  have hr : (0 : ℝ) ≤ finrank K (LinearMap.ker p) := Nat.cast_nonneg _
  have hm : min (finrank K (L.comap p) : ℝ) ((finrank K V : ℝ)-finrank K (L.comap p)) =
      (finrank K V' : ℝ)-finrank K L := by
    rw [hdSR,← hdVR,min_eq_right (by linarith)]
    ring
  rw [hm,hdSR] at hgS
  have hid := quotient_growth_identity (T := (finrank K W' : ℝ))
    (r := (finrank K (LinearMap.ker p) : ℝ))
    (t := (finrank K (LinearMap.ker q) : ℝ)) (l := (finrank K L : ℝ)) (G := G)
    hpos.ne' (show (finrank K V' : ℝ)+finrank K (LinearMap.ker p) ≠ 0 by positivity)
  rw [hdVR,hdWR] at hid
  linarith

end SurjectiveImage
end Froberg
