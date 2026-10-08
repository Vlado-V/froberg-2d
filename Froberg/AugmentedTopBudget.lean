import Froberg.TopIncidenceLimit
import Froberg.TopFactorialGap

/-! The rounded scalar reserve fits the actual projected top-row map. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem eventually_augmented_top_budget {d h a b : ℕ} (hd : 3≤d)
    (ha : 0<a) (hb : 0<b) (hratio : (h : ℝ)/(2*(d : ℝ))≤(b : ℝ)/a)
    (qF qS : ℕ → ℕ)
    (hF : Tendsto (fun m : ℕ => (qF m : ℝ)/(m : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))))
    (hS : Tendsto (fun m : ℕ => (qS m : ℝ)/(m : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∀ᶠ m : ℕ in atTop,
      (qF m+a*m)*(a*m)+(qS m+scalarReserveCount d m+b)*b≤b*(m+d-1).choose d := by
  apply eventually_top_incidence_budget hd qF (fun m => qS m+scalarReserveCount d m)
    _ _ hF
  · simpa only [Nat.cast_add,add_div] using hS.add (scalarReserveCount_limit (show 0<d by omega))
  · exact top_factorial_gap hd ha hb hratio

end Froberg
