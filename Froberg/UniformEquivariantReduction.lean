module

public import Froberg.CharacteristicDivisibility
public import Froberg.UniformArithmeticVanishing
public import Froberg.UniformDefectBounds
public import Froberg.CriticalApproximation
public import Froberg.UniformStatement

@[expose] public section

/-! The arithmetic reduction for actual endpoint defects, uniformly in the
infinite coefficient field. The recurrence step and starting point are common;
the dimension bound and the arithmetic witness choices are independent of the
field and its characteristic. -/
noncomputable section
namespace Froberg

/-- A common recurrence for an arbitrary indexed family of infinite fields
implies a common vanishing threshold for their actual critical defects. -/
theorem family_criticalDefect_eventually_zero_of_recurrence
    {ι : Type*} (K : ι → Type) [∀ i, Field (K i)] [∀ i, Infinite (K i)]
    {d h n₀ : ℕ} (hd : 2 ≤ d) (hh : 0 < h)
    (hstep : ∀ i n, n₀ ≤ n →
      criticalDefect (K i) (n + h) d ≤ criticalDefect (K i) n d) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ i n, N ≤ n → criticalDefect (K i) n d = 0 := by
  let t := max n₀ 1
  let M := (t + h - 1 + 2 * d - 1).choose (2 * d)
  have hbound (i : ι) : ∀ n, t ≤ n → criticalDefect (K i) n d ≤ M :=
    criticalDefect_bound_from_recurrence hh (by dsimp [t]; omega)
      (fun n hn => hstep i n (by dsimp [t] at hn; omega))
  obtain ⟨P, hPdeg, _, hI, happ⟩ := exists_critical_polynomial_approximation hd
  obtain ⟨N, hN⟩ := uniform_arithmetic_eventual_vanishing d h t M
    (by omega) hh P (by omega) hI (fun n => kappa n d) happ
    ⟨1, fun n hn => (kappa_bounds (by omega : 0 < n) d).1.le⟩
    (fun i n => genericHomology (K i) n d (lowerCount n d))
    (fun i n => genericCokernel (K i) n d (upperCount n d))
    (fun i => ringChar (K i))
    (fun i => (CharP.char_is_prime_or_zero (K i) (ringChar (K i))).symm)
    (fun i n hn => hstep i n (by dsimp [t] at hn; omega)) hbound
    (fun i n hn ℓ hℓ hchar =>
      (generic_defects_divisibility_of_characteristic_coprime
        (K := K i) (by dsimp [t] at hn; omega)
        (lowerCount_le_monomial_count (by dsimp [t] at hn; omega) d) hℓ hchar).1)
    (fun i n hn ℓ hℓ hchar =>
      (generic_defects_divisibility_of_characteristic_coprime
        (K := K i) (by dsimp [t] at hn; omega)
        (upperCount_le_monomial_count (by dsimp [t] at hn; omega) d) hℓ hchar).2)
  refine ⟨max N 1, by omega, ?_⟩
  intro i n hn
  obtain ⟨hH, hC⟩ := hN i n (by omega)
  simp only [criticalDefect, hH, hC, max_self]

/-- Packaging all small infinite fields as one index type lets the arithmetic
selection occur once, before quantification over the field. -/
private structure InfiniteFieldData where
  carrier : Type
  field : Field carrier
  infinite : Infinite carrier

attribute [instance] InfiniteFieldData.field InfiniteFieldData.infinite

/-- The field-independent recurrence contract implies actual uniform critical
vanishing, including fields of characteristic two. -/
theorem UniformCriticalRecurrence.criticalDefect_eventually_zero
    {d : ℕ} (hrec : UniformCriticalRecurrence d) (hd : 2 ≤ d) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (K : Type) [Field K] [Infinite K],
      ∀ n, N ≤ n → criticalDefect K n d = 0 := by
  obtain ⟨h, n₀, hh, hstep⟩ := hrec
  obtain ⟨N, hNpos, hN⟩ := family_criticalDefect_eventually_zero_of_recurrence
    InfiniteFieldData.carrier hd hh (fun i => hstep i.carrier)
  refine ⟨N, hNpos, ?_⟩
  intro K _ _ n hn
  exact hN ⟨K, inferInstance, inferInstance⟩ n hn

/-- The revised manuscript's uniform arithmetic conclusion: the shared
recurrence suffices for all admissible generator counts over every infinite
field, with one threshold. -/
theorem UniformCriticalRecurrence.endpoints
    {d : ℕ} (hrec : UniformCriticalRecurrence d) (hd : 2 ≤ d) :
    UniformEndpointStatement d := by
  obtain ⟨N, hNpos, hN⟩ := hrec.criticalDefect_eventually_zero hd
  refine ⟨N, hNpos, ?_⟩
  intro K _ _ n hn
  exact genericEndpoints_of_criticalDefect_zero (by omega) (hN K n hn)

end Froberg
