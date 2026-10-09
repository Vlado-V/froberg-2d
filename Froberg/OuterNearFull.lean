module

public import Froberg.OuterGrowthTransfer
public import Froberg.BadTargetCount

@[expose] public section

/-! A direct quadratic small-defect bound in the actual outer quotient. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module Finset Quartic.HomogeneousCoefficientCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s h : ℕ}
variable (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)

/-- One full source fiber fills every divisible target fiber. -/
theorem fiberShadow_eq_top_of_full {d : ℕ}
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (a : Exponent n s) (b : Exponent n (s+d)) (hab : a.val ≤ b.val) (ha : C a = ⊤) :
    fiberShadow e v C b = ⊤ := by
  apply top_unique
  have hh := le_iSup (fun a : {a : Exponent n s // a.val ≤ b.val} =>
    (C a.val).map (fiberProjection e v a.property)) ⟨a,hab⟩
  have hsurj : Function.Surjective (fiberProjection e v hab) :=
    Submodule.factor_surjective (relationFiber_mono e v hab)
  rw [ha,Submodule.map_top,LinearMap.range_eq_top.mpr hsurj] at hh
  exact hh

/-- Counting non-full source fibers costs at most the source codimension. -/
theorem card_nonfull_sources_le
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val)) :
    (univ.filter (fun a => C a ≠ ⊤)).card ≤
      (∑ a : Exponent n s, finrank K ((Fin h → K) ⧸ relationFiber e v a.val)) -
        ∑ a, finrank K (C a) := by
  classical
  let B := univ.filter (fun a => C a ≠ ⊤)
  have hc : B.card ≤ ∑ a : Exponent n s,
      (finrank K ((Fin h → K) ⧸ relationFiber e v a.val) - finrank K (C a)) := by
    calc
      B.card = ∑ a ∈ B, 1 := by simp
      _ ≤ ∑ a ∈ B, (finrank K ((Fin h → K) ⧸ relationFiber e v a.val) - finrank K (C a)) := by
        apply sum_le_sum
        intro a ha
        have hne := (mem_filter.mp ha).2
        have hle := Submodule.finrank_le (C a)
        have hneq : finrank K (C a) ≠ finrank K ((Fin h → K) ⧸ relationFiber e v a.val) :=
          fun hh => hne (Submodule.eq_top_of_finrank_eq hh)
        omega
      _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
  have hs : (∑ a : Exponent n s,
      (finrank K ((Fin h → K) ⧸ relationFiber e v a.val) - finrank K (C a))) +
      ∑ a, finrank K (C a) =
      ∑ a : Exponent n s, finrank K ((Fin h → K) ⧸ relationFiber e v a.val) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun a _ => Nat.sub_add_cancel (Submodule.finrank_le (C a)))
  change B.card ≤ _
  omega

/-- Every non-full target has all its degree-s divisors among the non-full sources. -/
theorem card_nonfull_targets_le
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val)) :
    (univ.filter (fun b : Exponent n (s+(s+1)) => fiberShadow e v C b ≠ ⊤)).card ≤
      (univ.filter (fun a => C a ≠ ⊤)).card ^ 2 * n := by
  classical
  let B := univ.filter (fun a => C a ≠ ⊤)
  let T := univ.filter (fun b : Exponent n (s+(s+1)) => fiberShadow e v C b ≠ ⊤)
  have hB : (B.image Subtype.val).card = B.card := card_image_of_injOn
    (fun _ _ _ _ hh => Subtype.ext hh)
  have hT : (T.image Subtype.val).card = T.card := card_image_of_injOn
    (fun _ _ _ _ hh => Subtype.ext hh)
  have hh := Froberg.card_bad_targets_le_square_mul (s := s) (B.image Subtype.val) (T.image Subtype.val)
    (by
      intro b hb
      obtain ⟨b,hb',rfl⟩ := mem_image.mp hb
      have hd := b.property
      omega)
    (by
      intro b hb a ha hab
      obtain ⟨b,hb',rfl⟩ := mem_image.mp hb
      let a' : Exponent n s := ⟨a,ha⟩
      have hne : C a' ≠ ⊤ := by
        intro hfull
        exact (mem_filter.mp hb').2 (fiberShadow_eq_top_of_full e v C a' b hab hfull)
      exact mem_image.mpr ⟨a',mem_filter.mpr ⟨mem_univ _,hne⟩,rfl⟩)
  rwa [hB,hT] at hh

/-- The small-defect quadratic bound, for actual independent monomial fibers. -/
theorem fiber_image_codimension_le (he : ∀ i, (e i).degree = s)
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val)) :
    (∑ b : Exponent n (s+(s+1)), finrank K ((Fin h → K) ⧸ relationFiber e v b.val)) -
      finrank K (Quartic.BilinearImage.image (fiberMultiply (d := s+1) e v he)
        (Submodule.pi Set.univ C)) ≤
    h * (((∑ a : Exponent n s, finrank K ((Fin h → K) ⧸ relationFiber e v a.val)) -
      ∑ a, finrank K (C a)) ^ 2 * n) := by
  classical
  let T := univ.filter (fun b : Exponent n (s+(s+1)) => fiberShadow e v C b ≠ ⊤)
  let defect (b : Exponent n (s+(s+1))) :=
    finrank K ((Fin h → K) ⧸ relationFiber e v b.val) - finrank K (fiberShadow e v C b)
  have hd : ∀ b, defect b ≤ if b ∈ T then h else 0 := by
    intro b
    by_cases hb : b ∈ T
    · rw [if_pos hb]
      exact (Nat.sub_le _ _).trans (by simpa using (relationFiber e v b.val).finrank_quotient_le)
    · rw [if_neg hb]
      have hfull : fiberShadow e v C b = ⊤ := by simpa [T] using hb
      have heq := congrArg (fun S : Submodule K ((Fin h → K) ⧸ relationFiber e v b.val) => finrank K S) hfull
      rw [finrank_top] at heq
      change _ - finrank K (fiberShadow e v C b) ≤ 0
      omega
  have hdSum : (∑ b, defect b) ≤ h*T.card := by
    have hh := sum_le_sum (fun b (_ : b ∈ (univ : Finset (Exponent n (s+(s+1))))) => hd b)
    have hi : (∑ b : Exponent n (s+(s+1)), if b ∈ T then h else 0) = T.card*h := by
      rw [← sum_filter]
      simp
    rw [hi,mul_comm T.card h] at hh
    exact hh
  have hsum : (∑ b, defect b) + ∑ b : Exponent n (s+(s+1)), finrank K (fiberShadow e v C b) =
      ∑ b : Exponent n (s+(s+1)), finrank K ((Fin h → K) ⧸ relationFiber e v b.val) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun b _ => Nat.sub_add_cancel (Submodule.finrank_le (fiberShadow e v C b)))
  have hi := sum_shadow_finrank_le_image (d := s+1) e v he C
  have htarget := card_nonfull_targets_le e v C
  have hsource := card_nonfull_sources_le e v C
  have hpow := Nat.pow_le_pow_left hsource 2
  have hmul := Nat.mul_le_mul_left h
    (htarget.trans (Nat.mul_le_mul_right n hpow))
  change h*T.card ≤ _ at hmul
  omega

/-- The quadratic small-defect estimate for every actual source subspace,
without a genericity hypothesis and without a monomial-subspace assumption. -/
theorem outer_image_codimension_le (he : ∀ i, (e i).degree = s)
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    finrank K ((Fin h → Forms K n (s+(s+1))) ⧸ relationSpace (d := s+1) e v he) -
      finrank K (outerImage (d := s+1) e v he L) ≤
    h * ((finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) -
      finrank K L) ^ 2 * n) := by
  obtain ⟨C,hCdim,hCimage⟩ := exists_initial_monomial_fibers (d := s+1) e v he L
  have hb := fiber_image_codimension_le e v he C
  have ht : (∑ b : Exponent n (s+(s+1)),
      finrank K ((Fin h → K) ⧸ relationFiber e v b.val)) =
      finrank K ((Fin h → Forms K n (s+(s+1))) ⧸ relationSpace (d := s+1) e v he) := by
    simpa only [Module.finrank_pi_fintype] using (quotientFiberEquiv (d := s+1) e v he).finrank_eq.symm
  rw [ht,sum_source_fiber_finrank e v he,hCdim] at hb
  exact (Nat.sub_le_sub_left hCimage _).trans hb

/-- All scalar multipliers together generate the whole actual target quotient. -/
theorem outerImage_top (he : ∀ i, (e i).degree = s) :
    outerImage (d := s+1) e v he ⊤ = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hh := outer_image_codimension_le e v he ⊤
  simp only [finrank_top,Nat.sub_self,zero_pow (by omega : 2 ≠ 0),zero_mul,mul_zero] at hh
  have hl := (outerImage (d := s+1) e v he ⊤).finrank_le
  omega

end Froberg.AttachedMultiplication
