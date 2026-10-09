module

public import Quartic.ThreeBlockOmega
public import Quartic.AugmentedMiddle

@[expose] public section

/-! The distinguished direction `ωu-v` separates the actual pure-block
homology from all distinguished coefficients over arbitrary characteristic. -/
noncomputable section
namespace Quartic.AugmentedMiddleOmega
open Module MvPolynomial HomologyCoordinates AugmentedMiddle
set_option maxHeartbeats 600000
variable {K : Type*} [Field K]

section LinearAlgebra
variable {V A : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup A] [Module K A]

def augmentedMap (ω : K) (f : V →ₗ[K] A) (r : Fin 4 → A) :
    (V × (A × BlockHomology K)) →ₗ[K] A × A :=
  (f.prod 0).coprod (((ω • LinearMap.id : A →ₗ[K] A).prod (-LinearMap.id)).coprod
    (pureTrace r))

@[simp] theorem augmentedMap_apply (ω : K) (f : V →ₗ[K] A) (r : Fin 4 → A)
    (b : V) (a : A) (ξ : BlockHomology K) :
    augmentedMap ω f r (b, a, ξ) =
      (f b + ω • a + (pureTrace r ξ).1, -a + (pureTrace r ξ).2) := by
  apply Prod.ext <;> simp [augmentedMap, add_assoc]

theorem pureTrace_contract (ω : K) (r : Fin 4 → A) (ξ : BlockHomology K) :
    (pureTrace r ξ).1 + ω • (pureTrace r ξ).2 =
      ∑ i, ThreeBlockOmega.scalarCoefficientMap ω ξ i • r i := by
  simp [pureTrace, ThreeBlockOmega.scalarCoefficientMap, Finset.smul_sum,
    smul_smul, add_smul, Finset.sum_add_distrib]

theorem augmentedMap_injective (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (f : V →ₗ[K] A) (hf : Function.Injective f) (r : Fin 4 → A)
    (hr : LinearIndependent K (fun i : Fin 3 => f.range.mkQ (r i.castSucc))) :
    Function.Injective (augmentedMap ω f r) := by
  have hsumω : 1 + ω ≠ 0 := by
    intro h
    exact hω1 (eq_neg_of_add_eq_zero_right h)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  rintro ⟨b, a, ξ⟩ h
  change augmentedMap ω f r (b, a, ξ) = 0 at h
  obtain ⟨t, rfl⟩ := homologyEquiv.surjective ξ
  have hsum := congrArg (fun p : A × A => f.range.mkQ (p.1 + ω • p.2)) h
  rw [augmentedMap_apply] at hsum
  have hfb : f.range.mkQ (f b) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩
  have heq : (f b + ω • a + (pureTrace r (homologyEquiv t)).1) +
      ω • (-a + (pureTrace r (homologyEquiv t)).2) =
      f b + ((pureTrace r (homologyEquiv t)).1 +
        ω • (pureTrace r (homologyEquiv t)).2) := by
    simp only [smul_add, smul_neg]
    abel
  rw [heq, pureTrace_contract] at hsum
  simp only [map_add, hfb, zero_add, map_sum, map_smul,
    ThreeBlockOmega.scalarCoefficientMap_coordinates,
    ThreeBlockOmega.scalarCoefficients_formula, Fin.sum_univ_succ,
    Matrix.cons_val_zero] at hsum
  let d : Fin 3 → K := ![-(1 + ω) * t 0, ω * t 1, t 2]
  have hd : ∑ i : Fin 3, d i • f.range.mkQ (r i.castSucc) = 0 := by
    simpa [d, Fin.sum_univ_succ, add_assoc] using hsum
  have hzero := Fintype.linearIndependent_iff.mp hr d hd
  have ht0 : t 0 = 0 := by
    have hz := hzero 0
    change -(1 + ω) * t 0 = 0 at hz
    exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hsumω)
  have ht1 : t 1 = 0 := by
    have hz := hzero 1
    change ω * t 1 = 0 at hz
    exact (mul_eq_zero.mp hz).resolve_left hω
  have ht2 : t 2 = 0 := hzero 2
  have ht : t = 0 := by funext i; fin_cases i <;> assumption
  simp only [ht, map_zero] at h
  have ha : a = 0 := by simpa using congrArg Prod.snd h
  have hb : b = 0 := by
    apply hf
    simpa [ha] using congrArg Prod.fst h
  change (b, a, homologyEquiv t) = 0
  simp [hb, ha, ht]

def augmentedOnSubspace (ω : K) (f : V →ₗ[K] A) (r : Fin 4 → A) (U : Submodule K A) :
    (V × (U × BlockHomology K)) →ₗ[K] A × A :=
  (augmentedMap ω f r).comp
    ((LinearMap.id : V →ₗ[K] V).prodMap (U.subtype.prodMap LinearMap.id))

theorem augmentedOnSubspace_injective (ω : K) (f : V →ₗ[K] A) (r : Fin 4 → A)
    (h : Function.Injective (augmentedMap ω f r)) (U : Submodule K A) :
    Function.Injective (augmentedOnSubspace ω f r U) := by
  intro x y hxy
  have he := h hxy
  change (x.1, (x.2.1.val, x.2.2)) = (y.1, (y.2.1.val, y.2.2)) at he
  exact Prod.ext (congrArg (fun z : V × (A × BlockHomology K) => z.1) he)
    (Prod.ext (Subtype.ext (congrArg (fun z : V × (A × BlockHomology K) => z.2.1) he))
      (congrArg (fun z : V × (A × BlockHomology K) => z.2.2) he))

variable [FiniteDimensional K A]

theorem exists_motions (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (f : V →ₗ[K] A) (hf : Function.Injective f)
    (hbudget : finrank K V + 3 ≤ finrank K A) :
    ∃ r : Fin 4 → A, r 3 = 0 ∧ Function.Injective (augmentedMap ω f r) := by
  let C := f.range
  have hc : finrank K C = finrank K V := LinearMap.finrank_range_of_inj hf
  have hquot := C.finrank_quotient_add_finrank
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank
    (show 3 ≤ finrank K (A ⧸ C) by omega)
  let v : Fin 3 → A := fun i => Classical.choose (C.mkQ_surjective (s i))
  have hv (i : Fin 3) : C.mkQ (v i) = s i := Classical.choose_spec (C.mkQ_surjective (s i))
  let r : Fin 4 → A := ![v 0, v 1, v 2, 0]
  refine ⟨r, rfl, augmentedMap_injective ω hω hω1 f hf r ?_⟩
  have he : (fun i : Fin 3 => C.mkQ (r i.castSucc)) = s := by
    funext i
    fin_cases i <;> exact hv _
  exact he ▸ hs

theorem exists_quotient_motions (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (f : V →ₗ[K] A) (hf : Function.Injective f) (q : ℕ)
    (hbudget : q + finrank K V + 3 ≤ finrank K A) :
    ∃ Q : Submodule K A, finrank K Q = q ∧ Function.Injective (quotientAlong f Q) ∧
      ∃ r : Fin 4 → A ⧸ Q, r 3 = 0 ∧
        Function.Injective (augmentedMap ω (quotientAlong f Q) r) := by
  have hrange : finrank K f.range = finrank K V := LinearMap.finrank_range_of_inj hf
  obtain ⟨Q, hQ, hdis⟩ := exists_disjoint_subspace f.range q (by omega)
  have hfQ := quotientAlong_injective f hf Q hdis
  have hdim := Q.finrank_quotient_add_finrank
  obtain ⟨r, hr, hinj⟩ := exists_motions ω hω hω1 (quotientAlong f Q) hfQ (by omega)
  exact ⟨Q, hQ, hfQ, r, hr, hinj⟩

end LinearAlgebra

theorem augmented_witness {m c q : ℕ} (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (hc : c ≤ m) (hbudget : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2) :
    LinearIndependent K (mixedFamily (K := K) hc) ∧
    ∃ Q : Submodule K (Forms K m 2), finrank K Q = q ∧
      Function.Injective (quotientAlong (activeForms hc 2) Q) ∧
      ∃ r : Fin 4 → Forms K m 2 ⧸ Q, r 3 = 0 ∧
        Function.Injective (augmentedMap ω (quotientAlong (activeForms hc 2) Q) r) ∧
        ∀ U : Submodule K (Forms K m 2 ⧸ Q),
          Function.Injective (augmentedOnSubspace ω (quotientAlong (activeForms hc 2) Q) r U) := by
  refine ⟨mixedFamily_independent hc, ?_⟩
  obtain ⟨Q, hQ, hfQ, r, hr, hinj⟩ := exists_quotient_motions ω hω hω1
    (activeForms (K := K) hc 2) (activeForms_injective hc 2) q
    (by simpa only [finrank_quadrics] using hbudget)
  exact ⟨Q, hQ, hfQ, r, hr, hinj, augmentedOnSubspace_injective ω _ r hinj⟩

end Quartic.AugmentedMiddleOmega
