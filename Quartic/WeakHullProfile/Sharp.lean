import Quartic.WeakHullProfile.Interpolation
import Quartic.UniformSurplus.Rational

/-! The sharp rational profile dominates its explicit weak prefix mixture. -/
namespace Quartic.WeakHullProfile
open HullCertificate ProfileCertificate Counts SharpCertificate

 theorem quadratic_cast (w : ℕ) : (b2 w : ℚ)=(w:ℚ)*((w:ℚ)+1)/2 := by
  have h : (2:ℚ)*(b2 w:ℚ)=(w:ℚ)*((w:ℚ)+1) := by exact_mod_cast b2_scaled w
  linarith

 theorem cubic_cast (w : ℕ) : (b3 w : ℚ)=(w:ℚ)*((w:ℚ)+1)*((w:ℚ)+2)/6 := by
  have h : (6:ℚ)*(b3 w:ℚ)=(w:ℚ)*((w:ℚ)+1)*((w:ℚ)+2) := by exact_mod_cast b3_scaled w
  linarith

 theorem quadratic_chord (w:ℕ) (y:ℚ) (hy0:0 ≤ y) (hy1:y ≤ 1) :
    (b2 w:ℚ)*y ≤ H₂ w ((w:ℚ)*y) := by
  have h:0 ≤ (w:ℚ)^2*y*(1-y)/2 := by positivity
  rw [quadratic_cast]
  unfold H₂
  push_cast
  nlinarith

 theorem cubic_chord (w:ℕ) (y:ℚ) (hy0:0 ≤ y) (hy1:y ≤ 1) :
    (b3 w:ℚ)*y ≤ H₃ w ((w:ℚ)*y) := by
  have hyA:0 ≤ 1-y := by linarith
  have hyB:0 ≤ 2-y := by linarith
  have h:0 ≤ (w:ℚ)^2*y*(1-y)*((w:ℚ)*(2-y)+3)/6 := by positivity
  rw [cubic_cast]
  unfold H₃
  push_cast
  nlinarith

 theorem weighted_max_bound (x y₁ y₂ y₃:ℚ) (hx0:0 ≤ x) (hx1:x ≤ 1)
    (hy:Ordered y₁ y₂ y₃) :
    weighted (fun r=>max x ((r.val:ℚ)/3)) y₁ y₂ y₃ ≤ x+(1-x)*y₁ := by
  let f:Fin 4→ℚ := ![x,1,1,1]
  have h:∀r:Fin 4,max x ((r.val:ℚ)/3) ≤ f r := by
    intro r
    fin_cases r <;> norm_num [f,max_eq_left hx0,max_le_iff,hx1]
  have hw:=weighted_mono hy h
  dsimp [weighted,f] at hw ⊢
  linarith

 theorem weighted_image_formula (A B:ℤ) (w:ℕ) (x y₁ y₂ y₃:ℚ)
    (hx0:0 ≤ x) (hx1:x ≤ 1) :
    weighted (fun r=>weakImage A B w (b2 w) (b3 w) x r) y₁ y₂ y₃=
      (B:ℚ)*(w:ℚ)*weighted (fun r=>max x ((r.val:ℚ)/3)) y₁ y₂ y₃+
      (A:ℚ)*(b2 w:ℚ)*(x+(max x (1/2)-x)*y₁+(1-max x (1/2))*y₂)+
      (b3 w:ℚ)*(y₁+y₂+y₃) := by
  norm_num [weighted,weakImage,max_eq_left hx0,max_eq_right hx1]
  ring

 def fractionSharp (A B:ℤ) (w:ℕ) (b x y₁ y₂ y₃:ℚ) : ℚ :=
  b*w+((B:ℚ)-b)*w*y₁+
    (A:ℚ)*(x*(b2 w:ℚ)+(max x (1/2)-x)*H₂ w ((w:ℚ)*y₁)+
      (1-max x (1/2))*H₂ w ((w:ℚ)*y₂))+
    H₃ w ((w:ℚ)*y₁)+H₃ w ((w:ℚ)*y₂)+H₃ w ((w:ℚ)*y₃)

/-- Endpoint chords and the linear core shadow bound dominate the weak mixture. -/
 theorem weighted_le_fraction (A B:ℤ) (w:ℕ) (b x y₁ y₂ y₃:ℚ)
    (hA:0 ≤ A) (hB:0 ≤ B) (hx0:0 ≤ x) (hx1:x ≤ 1)
    (hy:Ordered y₁ y₂ y₃) (hb:(B:ℚ)*x ≤ b) :
    weighted (fun r=>weakImage A B w (b2 w) (b3 w) x r) y₁ y₂ y₃ ≤
      fractionSharp A B w b x y₁ y₂ y₃ := by
  have hAQ:(0:ℚ) ≤ A := by exact_mod_cast hA
  have hBQ:(0:ℚ) ≤ B := by exact_mod_cast hB
  have hy₁0:0 ≤ y₁:=hy.1.trans (hy.2.1.trans hy.2.2.1)
  have hy₂0:0 ≤ y₂:=hy.1.trans hy.2.1
  have hy₂1:y₂ ≤ 1:=hy.2.2.1.trans hy.2.2.2
  have hy₃1:y₃ ≤ 1:=hy.2.1.trans hy₂1
  have hhalf:max x (1/2) ≤ 1:=max_le hx1 (by norm_num)
  have hfirst:=mul_le_mul_of_nonneg_left (weighted_max_bound x y₁ y₂ y₃ hx0 hx1 hy)
    (mul_nonneg hBQ (by positivity : (0:ℚ) ≤ w))
  have hbdiff:0 ≤ (b-(B:ℚ)*x)*(w:ℚ)*(1-y₁):=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hb) (by positivity)) (sub_nonneg.mpr hy.2.2.2)
  have hq₁:=mul_le_mul_of_nonneg_left (quadratic_chord w y₁ hy₁0 hy.2.2.2)
    (mul_nonneg hAQ (sub_nonneg.mpr (le_max_left x (1/2))))
  have hq₂:=mul_le_mul_of_nonneg_left (quadratic_chord w y₂ hy₂0 hy₂1)
    (mul_nonneg hAQ (sub_nonneg.mpr hhalf))
  have hc₁:=cubic_chord w y₁ hy₁0 hy.2.2.2
  have hc₂:=cubic_chord w y₂ hy₂0 hy₂1
  have hc₃:=cubic_chord w y₃ hy.1 hy₃1
  rw [weighted_image_formula A B w x y₁ y₂ y₃ hx0 hx1]
  unfold fractionSharp
  nlinarith

 def weakAverage (m c i:ℕ) (n₁ n₂ n₃:ℚ) : ℚ :=
  weighted (fun r=>weakImage (coreA c) (coreB c) (freeW m c)
    (b2 (freeW m c)) (b3 (freeW m c)) ((i:ℚ)/(coreA c:ℚ)) r)
    (n₁/(freeW m c:ℚ)) (n₂/(freeW m c:ℚ)) (n₃/(freeW m c:ℚ))

 theorem coreA_pos (c:ℕ) (hc:4 ≤ c) : 0 < coreA c := by
  unfold coreA coreP
  omega

 theorem freeW_pos (m c:ℕ) : 0 < freeW m c := by
  unfold freeW
  omega

 theorem normalized_ordered (m c:ℕ) (n₁ n₂ n₃:ℚ)
    (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m c:ℚ)) :
    Ordered (n₁/(freeW m c:ℚ)) (n₂/(freeW m c:ℚ)) (n₃/(freeW m c:ℚ)) := by
  have hw:(0:ℚ)<freeW m c:=by exact_mod_cast freeW_pos m c
  exact ⟨div_nonneg hn.1 hw.le,(div_le_div_iff_of_pos_right hw).mpr hn.2.1,
    (div_le_div_iff_of_pos_right hw).mpr hn.2.2.1,(div_le_one hw).mpr hn.2.2.2⟩

 theorem fractionSharp_source (m c i:ℕ) (hc:4 ≤ c) (n₁ n₂ n₃:ℚ) :
    fractionSharp (coreA c) (coreB c) (freeW m c) (coreShadow c i)
      ((i:ℚ)/(coreA c:ℚ)) (n₁/(freeW m c:ℚ)) (n₂/(freeW m c:ℚ)) (n₃/(freeW m c:ℚ))=
      sharpProfile (parameters m c i) n₁ n₂ n₃ := by
  have hA:(0:ℚ)<coreA c:=by exact_mod_cast coreA_pos c hc
  have hw:(0:ℚ)<freeW m c:=by exact_mod_cast freeW_pos m c
  have hhalf:(coreA c:ℚ)*(1/2)=(coreP c:ℚ):=by simp [coreA]; ring
  have hAx:(coreA c:ℚ)*((i:ℚ)/(coreA c:ℚ))=(i:ℚ):=by field_simp
  have hAm:(coreA c:ℚ)*max ((i:ℚ)/(coreA c:ℚ)) (1/2)=max (i:ℚ) (coreP c:ℚ):=by
    rw [mul_max_of_nonneg _ _ hA.le,hAx,hhalf]
  have he₁:(coreA c:ℚ)*(max ((i:ℚ)/(coreA c:ℚ)) (1/2)-(i:ℚ)/(coreA c:ℚ))=
      max ((coreP c:ℚ)-(i:ℚ)) 0:=by
    rw [mul_sub,hAm,hAx,← max_sub_sub_right]
    simp [max_comm]
  have he₂:(coreA c:ℚ)*(1-max ((i:ℚ)/(coreA c:ℚ)) (1/2))=
      (coreA c:ℚ)-max (i:ℚ) (coreP c:ℚ):=by rw [mul_sub,mul_one,hAm]
  unfold fractionSharp sharpProfile parameters
  push_cast
  simp only [mul_div_cancel₀ _ (ne_of_gt hw)]
  rw [show (coreShadow c i:ℚ)*(freeW m c:ℚ)+((coreB c:ℚ)-(coreShadow c i:ℚ))*(freeW m c:ℚ)*
      (n₁/(freeW m c:ℚ))=
      (coreShadow c i:ℚ)*(freeW m c:ℚ)+((coreB c:ℚ)-(coreShadow c i:ℚ))*n₁ by
        field_simp]
  rw [show (coreA c:ℚ)*((i:ℚ)/(coreA c:ℚ)*(b2 (freeW m c):ℚ)+
      (max ((i:ℚ)/(coreA c:ℚ)) (1/2)-(i:ℚ)/(coreA c:ℚ))*H₂ (freeW m c) n₁+
      (1-max ((i:ℚ)/(coreA c:ℚ)) (1/2))*H₂ (freeW m c) n₂)=
      (i:ℚ)*(b2 (freeW m c):ℚ)+max ((coreP c:ℚ)-(i:ℚ)) 0*H₂ (freeW m c) n₁+
      ((coreA c:ℚ)-max (i:ℚ) (coreP c:ℚ))*H₂ (freeW m c) n₂ by
        calc
          _=(coreA c:ℚ)*((i:ℚ)/(coreA c:ℚ))*(b2 (freeW m c):ℚ)+
            ((coreA c:ℚ)*(max ((i:ℚ)/(coreA c:ℚ)) (1/2)-(i:ℚ)/(coreA c:ℚ)))*H₂ (freeW m c) n₁+
            ((coreA c:ℚ)*(1-max ((i:ℚ)/(coreA c:ℚ)) (1/2)))*H₂ (freeW m c) n₂:=by ring
          _= _:=by rw [hAx,he₁,he₂]]
  simp only [FiniteCounts.quadratics_eq_b2]
  ring

/-- The full source sharp profile bounds the explicit weak prefix average. -/
 theorem weakAverage_le_sharp (m c i:ℕ) (hc:4 ≤ c) (hi:i ≤ coreA c) (n₁ n₂ n₃:ℚ)
    (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m c:ℚ)) :
    weakAverage m c i n₁ n₂ n₃ ≤ sharpProfile (parameters m c i) n₁ n₂ n₃ := by
  have hA:(0:ℚ)<coreA c:=by exact_mod_cast coreA_pos c hc
  have hB:0 ≤ coreB c:=by rw [coreB_eq_binomial]; positivity
  have hiQ:(i:ℚ) ≤ coreA c:=by exact_mod_cast hi
  have hb:(coreB c:ℚ)*((i:ℚ)/(coreA c:ℚ)) ≤ (coreShadow c i:ℚ):=by
    have h:=UniformSurplus.core_shadow_linear c i hc hi
    rw [← mul_div_assoc]
    exact_mod_cast h
  exact (weighted_le_fraction (coreA c) (coreB c) (freeW m c) (coreShadow c i)
    ((i:ℚ)/(coreA c:ℚ)) _ _ _ (by positivity) hB (by positivity)
    ((div_le_one hA).mpr hiQ) (normalized_ordered m c n₁ n₂ n₃ hn) hb).trans_eq
      (fractionSharp_source m c i hc n₁ n₂ n₃)

end Quartic.WeakHullProfile
