module

public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Tactic

@[expose] public section

/-! Adjacent shifted parity classes cover all sufficiently large natural
numbers. This allows balanced core constructions to be assembled globally. -/
namespace Froberg
open Filter

theorem eventually_of_even_odd_shift (u : ℕ) (P : ℕ → Prop)
    (heven : ∀ᶠ v : ℕ in atTop,P (2*v+u))
    (hodd : ∀ᶠ v : ℕ in atTop,P (2*v+u+1)) :
    ∀ᶠ m : ℕ in atTop,P m := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp heven
  obtain ⟨b,hb⟩ := eventually_atTop.mp hodd
  apply eventually_atTop.mpr
  refine ⟨2*max a b+u,?_⟩
  intro m hm
  have hu : u ≤ m := by omega
  have hv : max a b ≤ (m-u)/2 := by omega
  have hr := Nat.mod_lt (m-u) (by decide : 0 < 2)
  by_cases hzero : (m-u)%2=0
  · have he : 2*((m-u)/2)+u=m := by omega
    simpa only [he] using ha ((m-u)/2) (le_trans (le_max_left a b) hv)
  · have ho : 2*((m-u)/2)+u+1=m := by omega
    simpa only [ho] using hb ((m-u)/2) (le_trans (le_max_right a b) hv)

theorem eventually_of_twice_add_shifts (u : ℕ) (P : ℕ → Prop)
    (heven : ∀ᶠ v : ℕ in atTop,P (v+v+u))
    (hodd : ∀ᶠ v : ℕ in atTop,P (v+v+(u+1))) :
    ∀ᶠ m : ℕ in atTop,P m := by
  apply eventually_of_even_odd_shift u P
  · simpa only [two_mul] using heven
  · simpa only [two_mul,Nat.add_assoc] using hodd

theorem exists_common_eventual_threshold {ι : Type*} [Finite ι]
    (P : ι → ℕ → Prop) (hP : ∀ i,∀ᶠ m : ℕ in atTop,P i m) :
    ∃ N : ℕ,∀ m,N ≤ m → ∀ i,P i m :=
  eventually_atTop.mp (eventually_all.mpr hP)

end Froberg
