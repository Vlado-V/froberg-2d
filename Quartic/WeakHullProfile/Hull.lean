module

public import Quartic.WeakHullProfile.Sharp

@[expose] public section

/-! Every admissible sharp profile lies above an explicit point of one weak hull. -/
namespace Quartic.WeakHullProfile
open HullCertificate ProfileCertificate SharpCertificate Counts

 theorem normalized_source (m c i:ℕ) (hc:4 ≤ c) (n₁ n₂ n₃:ℚ) :
    (coreA c:ℚ)*((i:ℚ)/(coreA c:ℚ))+
      (freeW m c:ℚ)*(n₁/(freeW m c:ℚ)+n₂/(freeW m c:ℚ)+n₃/(freeW m c:ℚ))=
      (i:ℚ)+n₁+n₂+n₃ := by
  have hA:(coreA c:ℚ)≠0:=ne_of_gt (by exact_mod_cast coreA_pos c hc)
  have hw:(freeW m c:ℚ)≠0:=ne_of_gt (by exact_mod_cast freeW_pos m c)
  field_simp
  ring

/-- The sharp profile is above a genuine convex combination of the eight
vertices in one knot cell, with exactly the same source coordinate. -/
 theorem exists_hull_below_sharp (m c i:ℕ) (hc:4 ≤ c) (hi:i ≤ coreA c)
    (n₁ n₂ n₃:ℚ) (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m c:ℚ)) :
    ∃cell:Fin 4,
      endpoint cell 0 ≤ (i:ℚ)/(coreA c:ℚ) ∧ (i:ℚ)/(coreA c:ℚ) ≤ endpoint cell 1 ∧
      InVertexHull m c cell ((i:ℚ)+n₁+n₂+n₃) (weakAverage m c i n₁ n₂ n₃) ∧
      weakAverage m c i n₁ n₂ n₃ ≤ sharpProfile (parameters m c i) n₁ n₂ n₃ := by
  have hA:(0:ℚ)<coreA c:=by exact_mod_cast coreA_pos c hc
  have hiQ:(i:ℚ) ≤ coreA c:=by exact_mod_cast hi
  obtain ⟨cell,hlo,hhi⟩:=knot_interval ((i:ℚ)/(coreA c:ℚ))
    (by positivity) ((div_le_one hA).mpr hiQ)
  have hp:=weighted_in_hull m c cell ((i:ℚ)/(coreA c:ℚ))
    (n₁/(freeW m c:ℚ)) (n₂/(freeW m c:ℚ)) (n₃/(freeW m c:ℚ))
    hlo hhi (normalized_ordered m c n₁ n₂ n₃ hn)
  rw [normalized_source m c i hc] at hp
  exact ⟨cell,hlo,hhi,hp,weakAverage_le_sharp m c i hc hi n₁ n₂ n₃ hn⟩

/-- The cell containing the core fraction contains the full source dimension
in precisely the integer interval used by the finite certificates. -/
 theorem eligible_of_cell (m c i:ℕ) (hc:4 ≤ c) (cell:Fin 4)
    (n₁ n₂ n₃:ℚ) (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m c:ℚ))
    (hxlo:endpoint cell 0 ≤ (i:ℚ)/(coreA c:ℚ))
    (hxhi:(i:ℚ)/(coreA c:ℚ) ≤ endpoint cell 1)
    (d:ℤ) (hdlo:1 ≤ d) (hdhi:d<(totalA m c:ℤ))
    (hd:(i:ℚ)+n₁+n₂+n₃=(d:ℚ)) : Eligible m c cell d := by
  have hA:(0:ℚ)<coreA c:=by exact_mod_cast coreA_pos c hc
  have hAx:(coreA c:ℚ)*((i:ℚ)/(coreA c:ℚ))=(i:ℚ):=mul_div_cancel₀ _ (ne_of_gt hA)
  have hl:=mul_le_mul_of_nonneg_left hxlo hA.le
  have hu:=mul_le_mul_of_nonneg_left hxhi hA.le
  rw [hAx] at hl hu
  have helo:(sourceLower m c cell:ℚ)=6*(coreA c:ℚ)*endpoint cell 0:=by
    simp [sourceLower,endpoint]
    ring
  have hehi:(sourceUpper m c cell:ℚ)=6*(coreA c:ℚ)*endpoint cell 1+18*(freeW m c:ℚ):=by
    simp [sourceUpper,endpoint]
    ring
  have hlow:(sourceLower m c cell:ℚ) ≤ 6*(d:ℚ):=by
    rw [helo]
    linarith [hn.1,hn.2.1,hn.2.2.1]
  have hupp:6*(d:ℚ) ≤ (sourceUpper m c cell:ℚ):=by
    rw [hehi]
    linarith [hn.2.1,hn.2.2.1,hn.2.2.2]
  exact ⟨hdlo,hdhi,by exact_mod_cast hlow,by exact_mod_cast hupp⟩

/-- The integral source range is supplied together with the actual weak-hull witness. -/
 theorem exists_eligible_hull (m c i:ℕ) (hc:4 ≤ c) (hi:i ≤ coreA c)
    (n₁ n₂ n₃:ℚ) (hn:0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (freeW m c:ℚ))
    (d:ℤ) (hdlo:1 ≤ d) (hdhi:d<(totalA m c:ℤ))
    (hd:(i:ℚ)+n₁+n₂+n₃=(d:ℚ)) :
    ∃cell:Fin 4, Eligible m c cell d ∧
      InVertexHull m c cell d (weakAverage m c i n₁ n₂ n₃) ∧
      weakAverage m c i n₁ n₂ n₃ ≤ sharpProfile (parameters m c i) n₁ n₂ n₃ := by
  obtain ⟨cell,hlo,hhi,hpoint,himage⟩:=exists_hull_below_sharp m c i hc hi n₁ n₂ n₃ hn
  rw [hd] at hpoint
  exact ⟨cell,eligible_of_cell m c i hc cell n₁ n₂ n₃ hn hlo hhi d hdlo hdhi hd,hpoint,himage⟩

end Quartic.WeakHullProfile
