import Quartic.HullCertificate.Rational

/-! Explicit rational interpolation of the eight weak vertices in a knot cell. -/
namespace Quartic.WeakHullProfile
open HullCertificate ProfileCertificate Counts

def weighted (f : Fin 4 → ℚ) (y₁ y₂ y₃ : ℚ) : ℚ  := 
  (1-y₁)*f 0+(y₁-y₂)*f 1+(y₂-y₃)*f 2+y₃*f 3

def Ordered (y₁ y₂ y₃ : ℚ) : Prop  := 
  0  ≤  y₃ ∧ y₃  ≤  y₂ ∧ y₂  ≤  y₁ ∧ y₁  ≤  1

def endpoint (cell : Fin 4) (side : Fin 2) : ℚ  :=  (knot (cell.val+side.val):ℚ)/6

def weights (s y₁ y₂ y₃ : ℚ) : Fin 8 → ℚ  := 
  ![(1-s)*(1-y₁),s*(1-y₁),(1-s)*(y₁-y₂),s*(y₁-y₂),
    (1-s)*(y₂-y₃),s*(y₂-y₃),(1-s)*y₃,s*y₃]

theorem weights_nonnegative (s y₁ y₂ y₃ : ℚ) (hs0 : 0  ≤  s) (hs1 : s  ≤  1)
    (hy : Ordered y₁ y₂ y₃) (v : Fin 8) : 0  ≤  weights s y₁ y₂ y₃ v  :=  by
  have h0 : 0  ≤  1-s  :=  by linarith
  have h1 : 0  ≤  1-y₁  :=  by linarith [hy.2.2.2]
  have h2 : 0  ≤  y₁-y₂  :=  by linarith [hy.2.2.1]
  have h3 : 0  ≤  y₂-y₃  :=  by linarith [hy.2.1]
  have h4 : 0  ≤  y₃  :=  hy.1
  fin_cases v <;> norm_num [weights] <;> positivity

theorem weights_sum (s y₁ y₂ y₃ : ℚ) : ∑v,weights s y₁ y₂ y₃ v=1  :=  by
  norm_num [weights,Fin.sum_univ_succ]
  ring

theorem weighted_mono {f g : Fin 4 → ℚ} {y₁ y₂ y₃ : ℚ}
    (hy : Ordered y₁ y₂ y₃) (hfg : ∀r,f r ≤ g r) :
    weighted f y₁ y₂ y₃ ≤ weighted g y₁ y₂ y₃  :=  by
  have h0  :=  mul_le_mul_of_nonneg_left (hfg 0) (sub_nonneg.mpr hy.2.2.2)
  have h1  :=  mul_le_mul_of_nonneg_left (hfg 1) (sub_nonneg.mpr hy.2.2.1)
  have h2  :=  mul_le_mul_of_nonneg_left (hfg 2) (sub_nonneg.mpr hy.2.1)
  have h3  :=  mul_le_mul_of_nonneg_left (hfg 3) hy.1
  unfold weighted
  linarith

theorem knot_interval (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃cell:Fin 4,endpoint cell 0 ≤ x ∧ x ≤ endpoint cell 1  :=  by
  by_cases h0 : x ≤ 1/3
  · exact ⟨0,by norm_num [endpoint,knot]; exact ⟨hx0,h0⟩⟩
  by_cases h1 : x ≤ 1/2
  · exact ⟨1,by norm_num [endpoint,knot]; exact ⟨by linarith,h1⟩⟩
  by_cases h2 : x ≤ 2/3
  · exact ⟨2,by norm_num [endpoint,knot]; exact ⟨by linarith,h2⟩⟩
  exact ⟨3,by norm_num [endpoint,knot]; exact ⟨by linarith,hx1⟩⟩

theorem endpoint_gap (cell:Fin 4) : 0<endpoint cell 1-endpoint cell 0  :=  by
  fin_cases cell <;> norm_num [endpoint,knot]

theorem max_interpolate (lo hi x k s : ℚ) (hxlo:lo ≤ x) (hxhi:x ≤ hi)
    (hside:k ≤ lo ∨ hi ≤ k) (hx:x=(1-s)*lo+s*hi) :
    max x k=(1-s)*max lo k+s*max hi k  :=  by
  rcases hside with h|h
  · rw [max_eq_left (h.trans hxlo),max_eq_left h,max_eq_left (h.trans (hxlo.trans hxhi))]
    exact hx
  · rw [max_eq_right (hxhi.trans h),max_eq_right ((hxlo.trans hxhi).trans h),max_eq_right h]
    ring

theorem image_interpolate (A B w Q C : ℤ) (cell r:Fin 4) (x s:ℚ)
    (hxlo:endpoint cell 0 ≤ x) (hxhi:x ≤ endpoint cell 1)
    (hx:x=(1-s)*endpoint cell 0+s*endpoint cell 1) :
    weakImage A B w Q C x r=
      (1-s)*weakImage A B w Q C (endpoint cell 0) r+
      s*weakImage A B w Q C (endpoint cell 1) r  :=  by
  have hsep : (r.val:ℚ)/3 ≤ endpoint cell 0 ∨ endpoint cell 1 ≤ (r.val:ℚ)/3  :=  by
    fin_cases cell <;> fin_cases r <;> norm_num [endpoint,knot]
  have hhalf : min ((r.val:ℚ)/2) 1 ≤ endpoint cell 0 ∨
      endpoint cell 1 ≤ min ((r.val:ℚ)/2) 1  :=  by
    fin_cases cell <;> fin_cases r <;> norm_num [endpoint,knot]
  unfold weakImage
  rw [max_interpolate _ _ _ _ _ hxlo hxhi hsep hx,
    max_interpolate _ _ _ _ _ hxlo hxhi hhalf hx]
  ring

theorem weighted_source (A w:ℤ) (x y₁ y₂ y₃:ℚ) :
    weighted (fun r=>weakSource A w x r) y₁ y₂ y₃=
      (A:ℚ)*x+(w:ℚ)*(y₁+y₂+y₃)  :=  by
  norm_num [weighted,weakSource]
  ring

theorem vertex_source_sum (m c:ℕ) (cell:Fin 4) (x s y₁ y₂ y₃:ℚ)
    (hx:x=(1-s)*endpoint cell 0+s*endpoint cell 1) :
    (∑v,weights s y₁ y₂ y₃ v*((vertex m c cell v).x:ℚ)/6)=
      (coreA c:ℚ)*x+(freeW m c:ℚ)*(y₁+y₂+y₃)  :=  by
  simp_rw [mul_div_assoc,vertex_source]
  norm_num [weights,Fin.sum_univ_succ,weakSource]
  rw [hx]
  simp only [endpoint,Fin.val_zero,Fin.val_one,add_zero]
  ring

theorem vertex_image_sum (m c:ℕ) (cell:Fin 4) (x s y₁ y₂ y₃:ℚ)
    (hxlo:endpoint cell 0 ≤ x) (hxhi:x ≤ endpoint cell 1)
    (hx:x=(1-s)*endpoint cell 0+s*endpoint cell 1) :
    (∑v,weights s y₁ y₂ y₃ v*((vertex m c cell v).y:ℚ)/6)=
      weighted (fun r=>weakImage (coreA c) (coreB c) (freeW m c)
        (b2 (freeW m c)) (b3 (freeW m c)) x r) y₁ y₂ y₃  :=  by
  simp_rw [mul_div_assoc,vertex_image]
  have heq  :=  image_interpolate (coreA c) (coreB c) (freeW m c)
    (b2 (freeW m c)) (b3 (freeW m c)) cell
  rw [weighted]
  rw [heq 0 x s hxlo hxhi hx,heq 1 x s hxlo hxhi hx,
    heq 2 x s hxlo hxhi hx,heq 3 x s hxlo hxhi hx]
  norm_num [weights,Fin.sum_univ_succ,endpoint]
  ring

/-- A profile prefix mixture belongs to the certified hull in its knot cell. -/
theorem weighted_in_hull (m c:ℕ) (cell:Fin 4) (x y₁ y₂ y₃:ℚ)
    (hxlo:endpoint cell 0 ≤ x) (hxhi:x ≤ endpoint cell 1) (hy:Ordered y₁ y₂ y₃) :
    InVertexHull m c cell ((coreA c:ℚ)*x+(freeW m c:ℚ)*(y₁+y₂+y₃))
      (weighted (fun r=>weakImage (coreA c) (coreB c) (freeW m c)
        (b2 (freeW m c)) (b3 (freeW m c)) x r) y₁ y₂ y₃)  :=  by
  let s  :=  (x-endpoint cell 0)/(endpoint cell 1-endpoint cell 0)
  have hgap := endpoint_gap cell
  have hs0:0 ≤ s := div_nonneg (sub_nonneg.mpr hxlo) hgap.le
  have hs1:s ≤ 1 := (div_le_one hgap).mpr (by linarith)
  have hx:x=(1-s)*endpoint cell 0+s*endpoint cell 1  :=  by
    dsimp [s]
    field_simp
    ring
  exact ⟨weights s y₁ y₂ y₃,weights_nonnegative s y₁ y₂ y₃ hs0 hs1 hy,
    weights_sum s y₁ y₂ y₃,vertex_source_sum m c cell x s y₁ y₂ y₃ hx,
    vertex_image_sum m c cell x s y₁ y₂ y₃ hxlo hxhi hx⟩

end Quartic.WeakHullProfile
