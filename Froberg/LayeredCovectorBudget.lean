module

public import Mathlib.Tactic

@[expose] public section

/-! The exact natural-number budget for the common scalar incidence step.
All higher target dimensions and all graph coordinates are retained. -/
namespace Froberg

/-- The first-stage layer ranks and the common scalar equations beat the
closed-base and graph dimensions under the displayed finite gain margin. -/
theorem layered_covector_equation_budget
    {T₀ H H₀ j q a k k₀ C M g base slices loss : ℕ}
    (hk : k≤a) (hk₀ : k₀≤k)
    (hbase : base+C*k₀≤T₀)
    (hambient : T₀+H≤j+q*a+H₀)
    (hgraph : g≤a*k) (hslices : j≤slices+loss)
    (hgain : H₀+(a+q)*k+loss<C*k₀+M*(k-k₀)) :
    base+g+H<M*(k-k₀)+q*(a-k)+slices := by
  have ha := Nat.sub_add_cancel hk
  have hq : q*(a-k)+q*k=q*a := by rw [← Nat.mul_add,ha]
  nlinarith

/-- A single uniform layer rate is sufficient for every nonzero profile. -/
theorem layered_covector_gain {H₀ a q k k₀ C M loss L : ℕ}
    (hk : 0<k) (hk₀ : k₀≤k) (hC : L≤C) (hM : L≤M)
    (hloss : loss≤L*k/2)
    (hsmall : 2*(H₀+a+q)+1≤L) :
    H₀+(a+q)*k+loss<C*k₀+M*(k-k₀) := by
  have hsplit := Nat.sub_add_cancel hk₀
  have hhalf : 2*(L*k/2)≤L*k := Nat.mul_div_le _ _
  have hrate : L*k≤C*k₀+M*(k-k₀) := by
    calc
      L*k=L*k₀+L*(k-k₀) := by nlinarith [hsplit]
      _≤C*k₀+M*(k-k₀) := Nat.add_le_add (Nat.mul_le_mul_right _ hC) (Nat.mul_le_mul_right _ hM)
  have hH : H₀≤H₀*k := Nat.le_mul_of_pos_right _ hk
  nlinarith

end Froberg
