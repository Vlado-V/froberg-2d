module

public import Quartic.FreeMonomialCounts
public import Quartic.UniformSurplus.Rational

@[expose] public section

/-!
# Sharp-profile arithmetic for actual free-monomial index sets

These lemmas sum pointwise rank lower bounds over the exact exponent vectors
used by the free-coefficient decomposition. Repeated variables are included.
The hypotheses are numerical inequalities; no image-rank geometry is assumed
implicitly.
-/
namespace Quartic.LayerRankCounts
open Quartic.FreeMonomialCounts Quartic.Counts Quartic.ProfileCertificate
noncomputable section

/-- Number of variable blocks whose rank is at least h. -/
def levelCount {w : ℕ} (r : Fin w → ℕ) (h : ℕ) : ℕ :=
  Fintype.card {ν // h ≤ r ν}

/-- A free monomial meets the h-th rank layer. -/
def Meets {w k : ℕ} (r : Fin w → ℕ) (h : ℕ) (β : ExactExponent w k) : Prop :=
  ∃ν, h ≤ r ν ∧ 0 < β.val ν

instance {w k : ℕ} (r : Fin w → ℕ) (h : ℕ) (β : ExactExponent w k) : Decidable (Meets r h β) := by
  unfold Meets
  infer_instance

theorem levelCount_mono {w : ℕ} (r : Fin w → ℕ) {h k : ℕ} (hhk : h ≤ k) :
    levelCount r k ≤ levelCount r h := by
  unfold levelCount
  exact Fintype.card_le_of_injective (fun x => (⟨x.val,hhk.trans x.property⟩ : {ν // h ≤ r ν}))
    (by intro x y heq; exact Subtype.ext (congrArg (fun z : {ν // h ≤ r ν} => z.val) heq))

theorem levelCount_le {w : ℕ} (r : Fin w → ℕ) (h : ℕ) : levelCount r h ≤ w := by
  unfold levelCount
  simpa using Fintype.card_subtype_le (fun ν => h ≤ r ν)

theorem meets_mono {w k : ℕ} (r : Fin w → ℕ) {h j : ℕ} (hhj : h ≤ j)
    {β : ExactExponent w k} (hβ : Meets r j β) : Meets r h β := by
  obtain ⟨ν,hν,hpos⟩ := hβ
  exact ⟨ν,hhj.trans hν,hpos⟩

theorem sum_indicator {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (a : ℤ) :
    (∑x:α, if P x then a else 0)=a*(Fintype.card {x // P x}:ℤ) := by
  classical
  simp [Fintype.card_subtype,Finset.sum_ite,Finset.sum_const,mul_comm]

/-- The total block rank equals the sum of its three layer counts. -/
theorem rank_sum_eq_layers {w : ℕ} (r : Fin w → ℕ) (hr : ∀ν,r ν ≤ 3) :
    (∑ν, (r ν:ℤ))=(levelCount r 1:ℤ)+(levelCount r 2:ℤ)+(levelCount r 3:ℤ) := by
  classical
  have hp (ν : Fin w) : (r ν:ℤ)=
      (if 1 ≤ r ν then 1 else 0)+(if 2 ≤ r ν then 1 else 0)+(if 3 ≤ r ν then 1 else 0) := by
    have h := hr ν
    interval_cases hν : r ν <;> norm_num
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [sum_indicator,one_mul,levelCount]

/-- Natural-number version for the source decomposition dimension. -/
theorem rank_sum_nat_eq_layers {w : ℕ} (r : Fin w → ℕ) (hr : ∀ν,r ν ≤ 3) :
    (∑ν,r ν)=levelCount r 1+levelCount r 2+levelCount r 3 := by
  exact_mod_cast rank_sum_eq_layers r hr

theorem quadratic_meeting_count {w : ℕ} (r : Fin w → ℕ) (h : ℕ) :
    (Fintype.card {β : ExactExponent w 2 // Meets r h β}:ℤ)=h2 w (levelCount r h) := by
  exact h2_counts_monomials w (fun ν => h ≤ r ν)

theorem cubic_meeting_count {w : ℕ} (r : Fin w → ℕ) (h : ℕ) :
    (Fintype.card {β : ExactExponent w 3 // Meets r h β}:ℤ)=h3 w (levelCount r h) := by
  exact h3_counts_monomials w (fun ν => h ≤ r ν)

/-- The original integer sharp expression. -/
def sharpCount (w p i : ℕ) (B b : ℤ) (n₁ n₂ n₃ : ℕ) : ℤ :=
  b*(w:ℤ)+(B-b)*(n₁:ℤ)+(i:ℤ)*b2 w+
    max ((p:ℤ)-(i:ℤ)) 0*h2 w n₁+
    (((2*p:ℕ):ℤ)-max (i:ℤ) (p:ℤ))*h2 w n₂+h3 w n₁+h3 w n₂+h3 w n₃

/-- One-variable layers: the core shadow is always present, and a nonzero
output block supplies the full core degree-two space. -/
theorem linear_rank_sum {w : ℕ} (r R : Fin w → ℕ) (B b : ℤ)
    (hbase : ∀ν,b ≤ (R ν:ℤ)) (hfull : ∀ν,0 < r ν → B ≤ (R ν:ℤ)) :
    b*(w:ℤ)+(B-b)*(levelCount r 1:ℤ) ≤ ∑ν,(R ν:ℤ) := by
  classical
  have hp (ν : Fin w) : b+(if 1 ≤ r ν then B-b else 0) ≤ (R ν:ℤ) := by
    split_ifs with h
    · have hh := hfull ν (by omega)
      linarith
    · simpa using hbase ν
  have h := Finset.sum_le_sum (fun ν (_ : ν ∈ Finset.univ) => hp ν)
  rw [Finset.sum_add_distrib,sum_indicator] at h
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,levelCount,mul_comm] using h

/-- The nested quadratic thresholds combine into the two source coefficients. -/
theorem quadratic_pointwise (p i R : ℕ) (_hi : i ≤ 2*p) (P₁ P₂ : Prop)
    [Decidable P₁] [Decidable P₂] (hsub : P₂ → P₁)
    (hbase : i ≤ R) (h₁ : P₁ → p ≤ R) (h₂ : P₂ → 2*p ≤ R) :
    (i:ℤ)+(if P₁ then max ((p:ℤ)-(i:ℤ)) 0 else 0)+
      (if P₂ then ((2*p:ℕ):ℤ)-max (i:ℤ) (p:ℤ) else 0) ≤ (R:ℤ) := by
  by_cases hP₂ : P₂
  · have hP₁ := hsub hP₂
    simp only [ite_eq_left hP₁,ite_eq_left hP₂]
    have h := h₂ hP₂
    have hR : ((2*p:ℕ):ℤ) ≤ (R:ℤ) := by exact_mod_cast h
    by_cases hip : i ≤ p
    · have hir : (i:ℤ) ≤ (p:ℤ) := by exact_mod_cast hip
      rw [max_eq_left (sub_nonneg.mpr hir),max_eq_right hir]
      omega
    · have hir : (p:ℤ) ≤ (i:ℤ) := by omega
      rw [max_eq_right (by omega),max_eq_left hir]
      omega
  · simp only [ite_eq_right hP₂,add_zero]
    by_cases hP₁ : P₁
    · simp only [ite_eq_left hP₁]
      have h := h₁ hP₁
      by_cases hip : i ≤ p
      · rw [max_eq_left (by omega)]
        omega
      · rw [max_eq_right (by omega)]
        omega
    · simp only [ite_eq_right hP₁,add_zero]
      exact_mod_cast hbase

/-- Summing quadratic layer ranks gives exactly the source H₂ contributions. -/
theorem quadratic_rank_sum {w : ℕ} (r : Fin w → ℕ) (R : ExactExponent w 2 → ℕ)
    (p i : ℕ) (hi : i ≤ 2*p) (hbase : ∀β,i ≤ R β)
    (h₁ : ∀β,Meets r 1 β → p ≤ R β) (h₂ : ∀β,Meets r 2 β → 2*p ≤ R β) :
    (i:ℤ)*b2 w+max ((p:ℤ)-(i:ℤ)) 0*h2 w (levelCount r 1)+
      (((2*p:ℕ):ℤ)-max (i:ℤ) (p:ℤ))*h2 w (levelCount r 2) ≤ ∑β,(R β:ℤ) := by
  classical
  have h := Finset.sum_le_sum (fun β (_ : β ∈ Finset.univ) =>
    quadratic_pointwise p i (R β) hi (Meets r 1 β) (Meets r 2 β)
      (meets_mono r (by decide)) (hbase β) (h₁ β) (h₂ β))
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,sum_indicator,sum_indicator,
    quadratic_meeting_count,quadratic_meeting_count] at h
  have hcard : (Fintype.card (ExactExponent w 2):ℤ)=b2 w := by
    rw [exactExponent_card]
    unfold b2
    congr 1
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard,mul_comm] using h

/-- Cubic layers contain all incident output blocks, so each met rank threshold
contributes one to a valid lower bound. -/
theorem cubic_rank_sum {w : ℕ} (r : Fin w → ℕ) (R : ExactExponent w 3 → ℕ)
    (hincident : ∀β ν,0 < β.val ν → r ν ≤ R β) :
    h3 w (levelCount r 1)+h3 w (levelCount r 2)+h3 w (levelCount r 3) ≤ ∑β,(R β:ℤ) := by
  classical
  have hlevel (β : ExactExponent w 3) (h : ℕ) (hβ : Meets r h β) : h ≤ R β := by
    obtain ⟨ν,hν,hpos⟩ := hβ
    exact hν.trans (hincident β ν hpos)
  have hp (β : ExactExponent w 3) :
      (if Meets r 1 β then (1:ℤ) else 0)+(if Meets r 2 β then 1 else 0)+
        (if Meets r 3 β then 1 else 0) ≤ (R β:ℤ) := by
    by_cases h₃ : Meets r 3 β
    · have h₂ := meets_mono r (by decide : 2 ≤ 3) h₃
      have h₁ := meets_mono r (by decide : 1 ≤ 3) h₃
      simp only [ite_eq_left h₁,ite_eq_left h₂,ite_eq_left h₃]
      exact_mod_cast hlevel β 3 h₃
    · simp only [ite_eq_right h₃,add_zero]
      by_cases h₂ : Meets r 2 β
      · have h₁ := meets_mono r (by decide : 1 ≤ 2) h₂
        simp only [ite_eq_left h₁,ite_eq_left h₂]
        exact_mod_cast hlevel β 2 h₂
      · simp only [ite_eq_right h₂,add_zero]
        by_cases h₁ : Meets r 1 β
        · simp only [ite_eq_left h₁]
          exact_mod_cast hlevel β 1 h₁
        · simp only [ite_eq_right h₁]
          positivity
  have h := Finset.sum_le_sum (fun β (_ : β ∈ Finset.univ) => hp β)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,sum_indicator,sum_indicator,sum_indicator,
    cubic_meeting_count,cubic_meeting_count,cubic_meeting_count] at h
  simpa only [one_mul] using h

/-- The sharp-profile lower bound from pointwise ranks on all actual degree-one,
two and three free-monomial layers. -/
theorem sharp_rank_sum {w : ℕ} (r R₁ : Fin w → ℕ)
    (R₂ : ExactExponent w 2 → ℕ) (R₃ : ExactExponent w 3 → ℕ)
    (p i : ℕ) (B b : ℤ) (hi : i ≤ 2*p)
    (hbase₁ : ∀ν,b ≤ (R₁ ν:ℤ)) (hfull₁ : ∀ν,0 < r ν → B ≤ (R₁ ν:ℤ))
    (hbase₂ : ∀β,i ≤ R₂ β)
    (h₁₂ : ∀β,Meets r 1 β → p ≤ R₂ β) (h₂₂ : ∀β,Meets r 2 β → 2*p ≤ R₂ β)
    (hincident₃ : ∀β ν,0 < β.val ν → r ν ≤ R₃ β) :
    sharpCount w p i B b (levelCount r 1) (levelCount r 2) (levelCount r 3) ≤
      (∑ν,(R₁ ν:ℤ))+(∑β,(R₂ β:ℤ))+(∑β,(R₃ β:ℤ)) := by
  have h₁ := linear_rank_sum r R₁ B b hbase₁ hfull₁
  have h₂ := quadratic_rank_sum r R₂ p i hi hbase₂ h₁₂ h₂₂
  have h₃ := cubic_rank_sum r R₃ hincident₃
  unfold sharpCount
  linarith

/-- The profile layer counts always satisfy the ordered simplex bounds. -/
theorem levelCounts_ordered {w : ℕ} (r : Fin w → ℕ) :
    levelCount r 3 ≤ levelCount r 2 ∧ levelCount r 2 ≤ levelCount r 1 ∧ levelCount r 1 ≤ w :=
  ⟨levelCount_mono r (by decide),levelCount_mono r (by decide),levelCount_le r 1⟩

theorem h2_cast (w n : ℕ) (hn : n ≤ w) :
    (h2 w n:ℝ)=UniformSurplus.H₂Real w n := by
  simp only [h2,FiniteCounts.quadratics_eq_b2,Int.cast_sub,UniformScalar.b2_cast,
    Nat.cast_sub hn,UniformSurplus.H₂Real,UniformSurplus.quadraticReal]

theorem h3_cast (w n : ℕ) (hn : n ≤ w) :
    (h3 w n:ℝ)=UniformSurplus.H₃Real w n := by
  simp only [h3,FiniteCounts.cubics_eq_b3,Int.cast_sub,UniformScalar.b3_cast,
    Nat.cast_sub hn,UniformSurplus.H₃Real,UniformSurplus.cubicReal]

/-- Exact equality with the source sharp profile, including its ceiling/binomial
core shadow and both free quadratic and cubic monomial layers. -/
theorem sharpCount_cast (m c i n₁ n₂ n₃ : ℕ)
    (hn₁ : n₁ ≤ freeW m c) (hn₂ : n₂ ≤ freeW m c) (hn₃ : n₃ ≤ freeW m c) :
    (sharpCount (freeW m c) (coreP c) i (coreB c) (SharpCertificate.coreShadow c i) n₁ n₂ n₃:ℝ)=
      UniformSurplus.sourceSharp m c i n₁ n₂ n₃ := by
  have hhalf : (coreA c:ℝ)/2=(coreP c:ℝ) := by
    simp only [coreA,Nat.cast_mul,Nat.cast_ofNat]
    ring
  unfold sharpCount
  push_cast
  rw [UniformScalar.b2_cast,h2_cast _ _ hn₁,h2_cast _ _ hn₂,
    h3_cast _ _ hn₁,h3_cast _ _ hn₂,h3_cast _ _ hn₃]
  unfold UniformSurplus.sourceSharp UniformSurplus.sharpReal
  rw [hhalf]
  simp only [coreA,Nat.cast_mul,Nat.cast_ofNat,UniformSurplus.quadraticReal]

/-- The original real sharp-profile expression is bounded by the summed ranks
of actual free-monomial layers, assuming precisely the stated pointwise bounds. -/
theorem source_sharp_rank_sum (m c i : ℕ) (hi : i ≤ coreA c)
    (r R₁ : Fin (freeW m c) → ℕ)
    (R₂ : ExactExponent (freeW m c) 2 → ℕ) (R₃ : ExactExponent (freeW m c) 3 → ℕ)
    (hbase₁ : ∀ν,SharpCertificate.coreShadow c i ≤ (R₁ ν:ℤ))
    (hfull₁ : ∀ν,0 < r ν → coreB c ≤ (R₁ ν:ℤ))
    (hbase₂ : ∀β,i ≤ R₂ β)
    (h₁₂ : ∀β,Meets r 1 β → coreP c ≤ R₂ β)
    (h₂₂ : ∀β,Meets r 2 β → coreA c ≤ R₂ β)
    (hincident₃ : ∀β ν,0 < β.val ν → r ν ≤ R₃ β) :
    UniformSurplus.sourceSharp m c i (levelCount r 1) (levelCount r 2) (levelCount r 3) ≤
      (((∑ν,R₁ ν)+(∑β,R₂ β)+(∑β,R₃ β):ℕ):ℝ) := by
  have h := sharp_rank_sum r R₁ R₂ R₃ (coreP c) i (coreB c)
    (SharpCertificate.coreShadow c i) hi hbase₁ hfull₁ hbase₂ h₁₂ h₂₂ hincident₃
  have hr : (sharpCount (freeW m c) (coreP c) i (coreB c) (SharpCertificate.coreShadow c i)
      (levelCount r 1) (levelCount r 2) (levelCount r 3):ℝ) ≤
      (((∑ν,R₁ ν)+(∑β,R₂ β)+(∑β,R₃ β):ℕ):ℝ) := by exact_mod_cast h
  rw [sharpCount_cast m c i _ _ _ (levelCount_le r 1) (levelCount_le r 2) (levelCount_le r 3)] at hr
  exact hr

end
end Quartic.LayerRankCounts
