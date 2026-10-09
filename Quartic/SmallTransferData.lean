module

public import Quartic.SharedChildFlag
public import Quartic.ActualSmallResponseRank
public import Quartic.ActualDeformationColumns

@[expose] public section

/-! Actual child flag and maximal response at the same small-range parameter. -/
noncomputable section
namespace Quartic.SmallTransferData
open Module MvPolynomial UniformEndpoint SmallCovectorCommonOpen
open ActualSmallMotionAvoidance ActualDeformationResponse ActualDeformationColumns
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
set_option maxHeartbeats 1500000

/-- The one marked space is realized by actual child cycles and has exactly
δ dimensions. Both child and response conditions hold at the same actual
parameter, as required to apply the exact deformation columns. -/
theorem exists_data (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40) (upper : Bool)
    (hchild : ∀ q,q ≤ (m+1).choose 2 → GenericQuartic K m q) :
    ∃ p : Parameters K m upper,∃ k : Fin (upperEndpoint m),
      ∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
      SimultaneousBlockConditions.BlockConditions (baseProjection p) ∧
      GenericF13.Conditions (G p) (Q p) ∧
      Function.Surjective (quadraticMultiplication (Q p)) ∧
      (finrank K (childMarkedCoefficient (Q p) k).range:ℤ)=Counts.delta m (upperEndpoint m) ∧
      Function.Injective (AugmentedGeneric.quotientAugmented
        (AugmentedGeneric.productMap (G p)) (Q p) r) ∧
      (finrank K (LinearMap.range (response (G p) (Q p) r
        (childMarkedCoefficient (Q p) k).range s)):ℤ)=
        min (Counts.hTotal m (upperEndpoint m) (mixedCount m upper))
          (Counts.j m (upperEndpoint m) (mixedCount m upper)) := by
  classical
  have hpoly : IsPolynomialFamily (Q (K := K) (m := m) (upper := upper)) :=
    isPolynomialFamily_linear (AugmentedGeneric.coefficientChild.comp baseProjection)
  have hsurj : Function.Surjective (Q (K := K) (m := m) (upper := upper)) := by
    intro h
    refine ⟨SmallCovectorCommonOpen.encode (AugmentedGeneric.encode 0 h 0) 0,?_⟩
    simp only [Q,baseProjection_encode,AugmentedGeneric.coefficientChild_encode]
  obtain ⟨A,⟨a,ha⟩,hA⟩ := SharedChildFlag.endpoint_principal_open (by omega : 1 ≤ m)
    (upperEndpoint m) rfl Q hpoly hsurj hchild
  obtain ⟨B,⟨b,hb⟩,hB⟩ := ActualSmallResponseRank.common_open (K := K) m hmlo hmhi upper (by norm_num)
  have hA0 : A≠0 := by intro h; simp [h] at ha
  have hB0 : B≠0 := by intro h; simp [h] at hb
  obtain ⟨p,hp⟩ := nonempty_principal_intersection (![A,B] : Fin 2 →
    MvPolynomial (SmallCovectorCommonOpen.ParameterIndex m upper m
      (mixedCount m upper) (upperEndpoint m)) K) (by intro i; fin_cases i <;> assumption)
  obtain ⟨_,hchildSurj,k,hk⟩ := hA p (hp 0)
  obtain ⟨hblock,hf13,_,hresponse⟩ := hB p (hp 1)
  let U := (childMarkedCoefficient (Q p) k).range
  have hdim : (finrank K U:ℤ)=Counts.delta m (upperEndpoint m) := hk
  obtain ⟨r,s,haug,hrank⟩ := hresponse U
  refine ⟨p,k,r,s,hblock,hf13,hchildSurj,hdim,haug,?_⟩
  have hsource := source_finrank (G p) (Q p) r U hblock.1.1 hblock.1.2.1 haug hblock.1.2.2.1
  have hj := ActualSplitCokernel.rawJ_finrank_eq_j (G p) (Q p) hf13.1 hf13.2.1 hf13.2.2
  change (finrank K (LinearMap.range (response (G p) (Q p) r U s)):ℤ)=_
  rw [hrank,Nat.cast_min,hsource,hj,hdim]
  congr 1
  unfold Counts.hTotal Counts.k31
  push_cast
  ring

end Quartic.SmallTransferData
