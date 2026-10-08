import Froberg.LayeredCovectorBudget

/-! Exact finite arithmetic for the homogeneous bottom cuts and the one
shared affine homogenization coordinate in the kernel-chart argument. -/
namespace Froberg

theorem affine_kernel_equation_budget
    {T₀ H H₀ j q a k k₀ C M base slices loss : ℕ}
    (hk : k≤a) (hk₀ : k₀≤k)
    (hbase : (base+1)+C*k₀≤T₀)
    (hambient : T₀+H≤j+q*a+H₀)
    (hslices : j≤slices+loss)
    (hgain : H₀+(a+q)*k+loss<C*k₀+M*(k-k₀)) :
    base+a*k+(H+1)<M*(k-k₀)+q*(a-k)+slices := by
  have h := layered_covector_equation_budget hk hk₀ hbase hambient (le_refl (a*k)) hslices hgain
  omega

/-- One rate and one loss bound yield the budget simultaneously for all
kernel profiles above the chosen positive threshold. -/
theorem affine_kernel_uniform_budget
    {T₀ H H₀ j q a a₀ C M slices loss L threshold : ℕ}
    (base : Fin (a₀+1) → ℕ)
    (hthreshold : 0<threshold)
    (hbase : ∀ k₀ : Fin (a₀+1),base k₀+C*k₀.val≤T₀)
    (hambient : T₀+H≤j+q*a+H₀)
    (hslices : j≤slices+loss)
    (hC : L≤C) (hM : L≤M)
    (hloss : loss≤L*threshold/2)
    (hsmall : 2*(H₀+a+q)+1≤L) :
    ∀ k : Fin (a+1),∀ k₀ : Fin (a₀+1),threshold≤k.val → k₀.val≤k.val →
      base k₀+a*k.val+H<M*(k.val-k₀.val)+q*(a-k.val)+slices := by
  intro k k₀ ht hkk
  have hloss' : loss≤L*k.val/2 := hloss.trans
    (Nat.div_le_div_right (Nat.mul_le_mul_left L ht))
  exact layered_covector_equation_budget (by omega) hkk (hbase k₀) hambient (le_refl _) hslices
    (layered_covector_gain (hthreshold.trans_le ht) hkk hC hM hloss' hsmall)

end Froberg
