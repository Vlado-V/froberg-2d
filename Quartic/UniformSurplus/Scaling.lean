module

public import Quartic.UniformSurplus.Sharp

@[expose] public section

/-! Exact conversion of the normalized profile inequality back to the
unscaled real polynomial in `sc:sharp-expression`. -/
namespace Quartic.UniformSurplus
open Quartic.UniformCertificate
noncomputable section

def quadraticReal (w : ℝ) : ℝ := w*(w+1)/2
def cubicReal (w : ℝ) : ℝ := w*(w+1)*(w+2)/6
def H₂Real (w n : ℝ) : ℝ := quadraticReal w-quadraticReal (w-n)
def H₃Real (w n : ℝ) : ℝ := cubicReal w-cubicReal (w-n)

def sharpReal (A B w b i n₁ n₂ n₃ : ℝ) : ℝ :=
  b*w+(B-b)*n₁+i*quadraticReal w+
    max (A/2-i) 0*H₂Real w n₁+(A-max i (A/2))*H₂Real w n₂+
    H₃Real w n₁+H₃Real w n₂+H₃Real w n₃

def totalReal (A B w : ℝ) : ℝ := B*w+A*quadraticReal w+3*cubicReal w

theorem normalized_counts (m t A B w : ℝ) (hm : m ≠ 0)
    (hA : A=2*(t-1)) (hB : B=t*(t-1)/2) (hw : w=m-t) :
    coreA (t/m) (1/m)=A/m ∧ coreB (t/m) (1/m)=B/m^2 ∧
    freeW (t/m)=w/m ∧ quadratic (t/m) (1/m)=quadraticReal w/m^2 ∧
    cubic (t/m) (1/m)=cubicReal w/m^3 ∧
    sourceDim (t/m) (1/m)=(A+3*w)/m ∧
    targetDim (t/m) (1/m)=totalReal A B w/m^3 := by
  subst A B w
  simp only [sourceDim, targetDim, totalReal, coreA, coreB, quadratic, cubic,
    freeW, quadraticReal, cubicReal]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp

theorem max_half_ratio (A i : ℝ) (hA : 0 < A) :
    max (i/A) (1/2) = max i (A/2)/A := by
  have hhalf : (1/2:ℝ)=(A/2)/A := by field_simp
  rw [hhalf, max_div_div_right (le_of_lt hA)]

theorem max_minus (i p : ℝ) : max i p-i = max (p-i) 0 := by
  by_cases h : i ≤ p
  · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  · rw [max_eq_left (le_of_not_ge h), max_eq_right (by linarith)]
    ring

theorem normalized_dimension (m t A w i n₁ n₂ n₃ : ℝ)
    (hm : m ≠ 0) (hA : A ≠ 0) (hw : w ≠ 0)
    (hcore : coreA (t/m) (1/m)=A/m) (hfree : freeW (t/m)=w/m) :
    profileDim (t/m) (1/m) (i/A) (n₁/w) (n₂/w) (n₃/w)=
      (i+n₁+n₂+n₃)/m := by
  unfold profileDim
  rw [hcore,hfree]
  field_simp
  ring

theorem normalized_sharp (m t A B w b i n₁ n₂ n₃ : ℝ)
    (hm : m ≠ 0) (hA : 0 < A) (hw : w ≠ 0)
    (hcounts : coreA (t/m) (1/m)=A/m ∧ coreB (t/m) (1/m)=B/m^2 ∧
      freeW (t/m)=w/m ∧ quadratic (t/m) (1/m)=quadraticReal w/m^2 ∧
      cubic (t/m) (1/m)=cubicReal w/m^3) :
    sharpNormalized (t/m) (1/m) (b/m^2) (i/A) (n₁/w) (n₂/w) (n₃/w)=
      sharpReal A B w b i n₁ n₂ n₃/m^3 := by
  have hAne := ne_of_gt hA
  unfold sharpNormalized layer₂ layer₃
  rw [hcounts.1,hcounts.2.1,hcounts.2.2.1,hcounts.2.2.2.1,hcounts.2.2.2.2,
    max_half_ratio A i hA]
  unfold sharpReal H₂Real H₃Real quadraticReal cubicReal
  rw [←max_minus i (A/2)]
  field_simp
  ring

/-- The exact uniform numerical surplus, in the original (unscaled) real
sharp expression, for every real ordered layer profile. -/
theorem sharp_real_surplus (m t A B w b i n₁ n₂ n₃ : ℝ)
    (hm : 64 ≤ m) (htlo : m/2 ≤ t) (hthi : t ≤ 14*m/25)
    (hA : A=2*(t-1)) (hB : B=t*(t-1)/2) (hw : w=m-t)
    (hi0 : 0 ≤ i) (hiA : i ≤ A)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ w)
    (hb : B*i/A ≤ b) :
    totalReal A B w/(A+3*w)*(i+n₁+n₂+n₃)+
      m^2/100*min (i+n₁+n₂+n₃) (A+3*w-(i+n₁+n₂+n₃)) ≤
    sharpReal A B w b i n₁ n₂ n₃ := by
  have hmpos : 0 < m := by linarith
  have hApos : 0 < A := by linarith
  have hwpos : 0 < w := by linarith
  have hap : 0 < A+3*w := by positivity
  have hmne := ne_of_gt hmpos
  have hAne := ne_of_gt hApos
  have hwne := ne_of_gt hwpos
  have hcounts := normalized_counts m t A B w hmne hA hB hw
  have hz0 : 1/2 ≤ t/m := (le_div_iff₀ hmpos).mpr (by linarith)
  have hz1 : t/m ≤ 14/25 := (div_le_iff₀ hmpos).mpr (by linarith)
  have hu0 : 0 ≤ 1/m := by positivity
  have hu1 : 1/m ≤ 1/64 := (div_le_iff₀ hmpos).mpr (by linarith)
  have hx0 : 0 ≤ i/A := div_nonneg hi0 (le_of_lt hApos)
  have hx1 : i/A ≤ 1 := (div_le_one hApos).mpr hiA
  have hy : OrderedProfile (n₁/w) (n₂/w) (n₃/w) :=
    ⟨div_nonneg hn.1 (le_of_lt hwpos),
      (div_le_div_iff_of_pos_right hwpos).mpr hn.2.1,
      (div_le_div_iff_of_pos_right hwpos).mpr hn.2.2.1,
      (div_le_one hwpos).mpr hn.2.2.2⟩
  have hb' : coreB (t/m) (1/m)*(i/A) ≤ b/m^2 := by
    rw [hcounts.2.1]
    have h := (div_le_div_iff_of_pos_right (sq_pos_of_pos hmpos)).mpr hb
    convert h using 1
    ring
  have h := sharp_normalized_surplus (t/m) (1/m) (b/m^2) (i/A)
    (n₁/w) (n₂/w) (n₃/w) hz0 hz1 hu0 hu1 hx0 hx1 hy hb'
  rw [normalized_sharp m t A B w b i n₁ n₂ n₃ hmne hApos hwne
    ⟨hcounts.1,hcounts.2.1,hcounts.2.2.1,hcounts.2.2.2.1,hcounts.2.2.2.2.1⟩,
    normalized_dimension m t A w i n₁ n₂ n₃ hmne hAne hwne hcounts.1 hcounts.2.2.1,
    hcounts.2.2.2.2.2.1,hcounts.2.2.2.2.2.2] at h
  rw [←sub_div, min_div_div_right (le_of_lt hmpos)] at h
  have hscale : totalReal A B w/m^3/((A+3*w)/m)*((i+n₁+n₂+n₃)/m)+
      1/100*(min (i+n₁+n₂+n₃) (A+3*w-(i+n₁+n₂+n₃))/m) =
      (totalReal A B w/(A+3*w)*(i+n₁+n₂+n₃)+
        m^2/100*min (i+n₁+n₂+n₃) (A+3*w-(i+n₁+n₂+n₃)))/m^3 := by
    field_simp
  rw [hscale] at h
  exact (div_le_div_iff_of_pos_right (pow_pos hmpos 3)).mp h

end
end Quartic.UniformSurplus
