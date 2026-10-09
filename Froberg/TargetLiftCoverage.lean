module

public import Froberg.AllTargetElimination

@[expose] public section

/-! The low, middle and pure rows cover the entire positive target range. -/
noncomputable section
namespace Froberg
variable {K : Type} [Field K] {h m d : ℕ}

theorem target_lifts_cover (hd : 3≤d) (I : Submodule K (Poly K (h+m)))
    (h₂ : TargetLift I d 2) (h₃ : TargetLift I d 3) (h₄ : TargetLift I d 4)
    (hmid : ∀ b,5≤b → b≤d → (b<d ∨ Odd d) → TargetLift I d b)
    (heven : ¬Odd d → TargetLift I d d)
    (hupper : ∀ b,d+1≤b → b≤2*d → TargetLift I d b) :
    ∀ b,2≤b → b≤2*d → TargetLift I d b := by
  intro b hb hbmax
  by_cases hbd : b≤d
  · by_cases hb2 : b=2
    · simpa only [hb2] using h₂
    by_cases hb3 : b=3
    · simpa only [hb3] using h₃
    by_cases hb4 : b=4
    · simpa only [hb4] using h₄
    by_cases hbsmall : b<d
    · exact hmid b (by omega) hbd (Or.inl hbsmall)
    have hbeq : b=d := by omega
    subst b
    by_cases hod : Odd d
    · exact hmid d (by omega) le_rfl (Or.inr hod)
    · exact heven hod
  · exact hupper b (by omega) hbmax

end Froberg
