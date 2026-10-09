module

public import Froberg.SparseBlockCount

@[expose] public section

/-! Sparse block counts normalized by the full output variable count. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

def fullSparseBlockCount (γ : ℝ) (j s h : ℕ) : ℕ :=
  ⌈(γ*(s.factorial : ℝ))*(h : ℝ)^j⌉₊+1

theorem fullSparseBlockCount_eq (γ : ℝ) (j s h : ℕ) :
    fullSparseBlockCount γ j s h = sparseBlockCount (γ/2^j) j s h := by
  have he : (γ/2^j*2^j*(s.factorial : ℝ))*(h : ℝ)^j =
      (γ*(s.factorial : ℝ))*(h : ℝ)^j := by field_simp
  simp only [fullSparseBlockCount,sparseBlockCount,he]

theorem fullSparseBlockCount_limit {j s : ℕ} (hj : 0<j) (γ : ℝ) (hγ : 0≤γ) :
    Tendsto (fun h : ℕ => (fullSparseBlockCount γ j s h : ℝ)/(h : ℝ)^j)
      atTop (𝓝 (γ*(s.factorial : ℝ))) := by
  have he : γ/2^j*2^j*(s.factorial : ℝ)=γ*(s.factorial : ℝ) := by field_simp
  simpa only [fullSparseBlockCount_eq,he] using
    sparseBlockCount_limit (s := s) hj (γ/2^j) (by positivity)

theorem fullSparseBlockCount_eventually_covers (γ : ℝ) (hγ : 0≤γ) (j h : ℕ)
    {s : ℕ} (hs : 0<s) :
    ∀ᶠ n : ℕ in atTop, ⌈γ*(h : ℝ)^j*(n : ℝ)^s⌉₊ ≤
      fullSparseBlockCount γ j s h*(n+s-1).choose s := by
  have he : γ/2^j*(2*(h : ℝ))^j = γ*(h : ℝ)^j := by rw [mul_pow]; field_simp
  simpa only [fullSparseBlockCount_eq,he] using
    sparseBlockCount_eventually_covers (γ/2^j) (by positivity) j h hs

end Froberg
