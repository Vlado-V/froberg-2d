module

public import Quartic.HomologyCoordinates
public import Quartic.MiddleCoordinates

@[expose] public section

/-!
# An actual augmented middle-multiplication witness

The independent mixed specialization is `E = x L`, where `L` is the span of
the first `c` child variables. Its symmetric products are actual renamed
quadrics. The pure traces use the actual coefficient maps on pure-block
Koszul homology. The dimension budget constructs the child space and motions.
-/

noncomputable section
namespace Quartic.AugmentedMiddle
open Module MvPolynomial HomologyCoordinates ThreeBlockQuotient
set_option maxHeartbeats 400000
variable {K : Type*} [Field K]

section LinearAlgebra
variable {V A : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup A] [Module K A]

/-- The trace of actual pure homology under four quadratic motions. -/
def pureTrace (r : Fin 4 → A) : BlockHomology K →ₗ[K] A × A where
  toFun ξ := (∑ i, (homologyReduction ξ i).1 • r i,
    ∑ i, (homologyReduction ξ i).2 • r i)
  map_add' ξ η := by simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' s ξ := by simp [map_smul, smul_smul, Finset.smul_sum]

/-- These are the actual coefficient maps `R_i : H_X → P`, in the proved quotient coordinates. -/
theorem pureTrace_actual_coefficients (r : Fin 4 → A) (ξ : BlockHomology K) :
    pureTrace r ξ =
      (∑ i, (quotientEquiv (coefficientMap i ξ)).1 • r i,
       ∑ i, (quotientEquiv (coefficientMap i ξ)).2 • r i) := by
  simp [pureTrace, coefficientMap]

/-- Products, the fixed marked motion `(u-v)`, and the actual pure trace. -/
def augmentedMap (f : V →ₗ[K] A) (r : Fin 4 → A) :
    (V × (A × BlockHomology K)) →ₗ[K] A × A :=
  (f.prod 0).coprod (((LinearMap.id : A →ₗ[K] A).prod (-LinearMap.id)).coprod (pureTrace r))

@[simp] theorem augmentedMap_apply (f : V →ₗ[K] A) (r : Fin 4 → A)
    (b : V) (a : A) (ξ : BlockHomology K) :
    augmentedMap f r (b, a, ξ) = (f b + a + (pureTrace r ξ).1,
      -a + (pureTrace r ξ).2) := by
  apply Prod.ext <;> simp [augmentedMap, add_assoc]

theorem pureTrace_sum (r : Fin 4 → A) (ξ : BlockHomology K) :
    (pureTrace r ξ).1 + (pureTrace r ξ).2 = ∑ i, scalarCoefficientMap ξ i • r i := by
  simp only [pureTrace, LinearMap.coe_mk, AddHom.coe_mk, scalarCoefficientMap,
    LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply, add_smul,
    Finset.sum_add_distrib]

theorem augmentedMap_injective (f : V →ₗ[K] A) (hf : Function.Injective f)
    (r : Fin 4 → A) (h2 : (2 : K) ≠ 0)
    (hr : LinearIndependent K (fun i : Fin 3 => f.range.mkQ (r i.castSucc))) :
    Function.Injective (augmentedMap f r) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  rintro ⟨b, a, ξ⟩ h
  change augmentedMap f r (b, a, ξ) = 0 at h
  obtain ⟨t, rfl⟩ := homologyEquiv.surjective ξ
  have hsum := congrArg (fun p : A × A => f.range.mkQ (p.1 + p.2)) h
  rw [augmentedMap_apply] at hsum
  have hfb : f.range.mkQ (f b) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩
  have heq : (f b + a + (pureTrace r (homologyEquiv t)).1) +
      (-a + (pureTrace r (homologyEquiv t)).2) =
      f b + ((pureTrace r (homologyEquiv t)).1 + (pureTrace r (homologyEquiv t)).2) := by abel
  rw [heq, pureTrace_sum] at hsum
  simp only [map_add, hfb, zero_add, map_sum, map_smul, scalarCoefficientMap_coordinates,
    ThreeBlock.scalarCoefficients_formula, Fin.sum_univ_succ,
    Matrix.cons_val_zero] at hsum
  let d : Fin 3 → K := ![-2 * t 0, t 1, t 2]
  have hd : ∑ i : Fin 3, d i • f.range.mkQ (r i.castSucc) = 0 := by
    simpa [d, Fin.sum_univ_succ, add_assoc] using hsum
  have hzero := Fintype.linearIndependent_iff.mp hr d hd
  have ht0 : t 0 = 0 := by
    have h := hzero 0
    change (-2 : K) * t 0 = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr h2)
  have ht1 : t 1 = 0 := hzero 1
  have ht2 : t 2 = 0 := hzero 2
  have ht : t = 0 := by funext i; fin_cases i <;> assumption
  simp only [ht, map_zero] at h
  have ha : a = 0 := by simpa using congrArg Prod.snd h
  have hb : b = 0 := by
    apply hf
    simpa [ha] using congrArg Prod.fst h
  change (b, a, homologyEquiv t) = 0
  simp [hb, ha, ht]

/-- The same witness works simultaneously for every marked coefficient subspace. -/
def augmentedOnSubspace (f : V →ₗ[K] A) (r : Fin 4 → A) (U : Submodule K A) :
    (V × (U × BlockHomology K)) →ₗ[K] A × A :=
  (augmentedMap f r).comp
    ((LinearMap.id : V →ₗ[K] V).prodMap (U.subtype.prodMap LinearMap.id))

theorem augmentedOnSubspace_injective (f : V →ₗ[K] A) (r : Fin 4 → A)
    (h : Function.Injective (augmentedMap f r)) (U : Submodule K A) :
    Function.Injective (augmentedOnSubspace f r U) := by
  intro x y hxy
  have he := h hxy
  change (x.1, (x.2.1.val, x.2.2)) = (y.1, (y.2.1.val, y.2.2)) at he
  have h₁ : x.1 = y.1 := congrArg (fun z : V × (A × BlockHomology K) => z.1) he
  have h₂ : x.2.1.val = y.2.1.val := congrArg (fun z : V × (A × BlockHomology K) => z.2.1) he
  have h₃ : x.2.2 = y.2.2 := congrArg (fun z : V × (A × BlockHomology K) => z.2.2) he
  exact Prod.ext h₁ (Prod.ext (Subtype.ext h₂) h₃)

variable [FiniteDimensional K A]

/-- A quadratic relation subspace can be chosen disjoint from the prescribed products. -/
theorem exists_disjoint_subspace (C : Submodule K A) (q : ℕ)
    (hq : q + finrank K C ≤ finrank K A) :
    ∃ Q : Submodule K A, finrank K Q = q ∧ Disjoint C Q := by
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl C
  have hd := Submodule.finrank_add_eq_of_isCompl hD
  obtain ⟨Q, _, hQ⟩ := SplitMiddle22.exists_extension_finrank (⊥ : Submodule K D) q
    (by simp) (by omega)
  refine ⟨Q.map D.subtype, ?_, ?_⟩
  · simpa using hQ
  · apply hD.disjoint.mono_right
    rintro x ⟨v, _, rfl⟩
    exact v.property

/-- The numerical codimension budget supplies the three actual quotient motions. -/
theorem exists_motions (f : V →ₗ[K] A) (hf : Function.Injective f)
    (hbudget : finrank K V + 3 ≤ finrank K A) (h2 : (2 : K) ≠ 0) :
    ∃ r : Fin 4 → A, r 3 = 0 ∧ Function.Injective (augmentedMap f r) := by
  let C := f.range
  have hc : finrank K C = finrank K V := LinearMap.finrank_range_of_inj hf
  have hquot := C.finrank_quotient_add_finrank
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank
    (show 3 ≤ finrank K (A ⧸ C) by omega)
  let v : Fin 3 → A := fun i => Classical.choose (C.mkQ_surjective (s i))
  have hv (i : Fin 3) : C.mkQ (v i) = s i := Classical.choose_spec (C.mkQ_surjective (s i))
  let r : Fin 4 → A := ![v 0, v 1, v 2, 0]
  refine ⟨r, rfl, augmentedMap_injective f hf r h2 ?_⟩
  have he : (fun i : Fin 3 => C.mkQ (r i.castSucc)) = s := by
    funext i
    fin_cases i <;> exact hv _
  exact he ▸ hs

/-- Actual product coordinates after imposing the child quadratic relations. -/
def quotientAlong (f : V →ₗ[K] A) (Q : Submodule K A) : V →ₗ[K] A ⧸ Q :=
  Q.mkQ.comp f

omit [FiniteDimensional K A] in
theorem quotientAlong_injective (f : V →ₗ[K] A) (hf : Function.Injective f)
    (Q : Submodule K A) (hdis : Disjoint f.range Q) :
    Function.Injective (quotientAlong f Q) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  have hQ : f v ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp hv
  have hz : f v = 0 := (Submodule.disjoint_def.mp hdis) (f v) ⟨v, rfl⟩ hQ
  exact hf (hz.trans f.map_zero.symm)

/-- Construct the child relations and motions solely from the numerical budget. -/
theorem exists_quotient_motions (f : V →ₗ[K] A) (hf : Function.Injective f) (q : ℕ)
    (hbudget : q + finrank K V + 3 ≤ finrank K A) (h2 : (2 : K) ≠ 0) :
    ∃ Q : Submodule K A, finrank K Q = q ∧ Function.Injective (quotientAlong f Q) ∧
      ∃ r : Fin 4 → A ⧸ Q, r 3 = 0 ∧ Function.Injective (augmentedMap (quotientAlong f Q) r) := by
  have hrange : finrank K f.range = finrank K V := LinearMap.finrank_range_of_inj hf
  obtain ⟨Q, hQ, hdis⟩ := exists_disjoint_subspace f.range q (by omega)
  have hfQ := quotientAlong_injective f hf Q hdis
  have hdim := Q.finrank_quotient_add_finrank
  obtain ⟨r, hr, hinj⟩ := exists_motions (quotientAlong f Q) hfQ (by omega) h2
  exact ⟨Q, hQ, hfQ, r, hr, hinj⟩

end LinearAlgebra

section PolynomialSpecialization
variable {m c q : ℕ}

/-- The actual child polynomial embedding of the first `c` variables. -/
def activeForms (hc : c ≤ m) (d : ℕ) : Forms K c d →ₗ[K] Forms K m d where
  toFun f := ⟨rename (Fin.castLE hc) f.val, f.property.rename_isHomogeneous⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (by simp)

theorem activeForms_injective (hc : c ≤ m) (d : ℕ) :
    Function.Injective (activeForms (K := K) hc d) := by
  intro f g h
  apply Subtype.ext
  apply MvPolynomial.rename_injective (Fin.castLE hc) (Fin.castLE_injective hc)
  exact congrArg Subtype.val h

/-- An actual monomial in the symmetric-product coordinates. -/
def quadraticMonomial (i j : Fin c) : Forms K c 2 :=
  ⟨X i * X j, (isHomogeneous_X K i).mul (isHomogeneous_X K j)⟩

def activeVariable (hc : c ≤ m) (i : Fin c) : Forms K m 1 :=
  ⟨X (Fin.castLE hc i), isHomogeneous_X K _⟩

/-- The concrete mixed specialization `g_i=x y_i`. -/
def mixedFamily (hc : c ≤ m) (i : Fin c) : MiddleCoordinates.Mixed K m :=
  ![activeVariable hc i, 0, 0]

theorem mixedFamily_independent (hc : c ≤ m) :
    LinearIndependent K (mixedFamily (K := K) hc) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro t ht i
  have h := congrArg (fun f : MiddleCoordinates.Mixed K m =>
    (f 0).val.coeff (Finsupp.single (Fin.castLE hc i) 1)) ht
  simpa [mixedFamily, activeVariable, Submodule.coe_sum, Submodule.coe_smul,
    coeff_sum, coeff_smul, coeff_X, Finsupp.single_eq_single_iff,
    smul_eq_mul, Pi.smul_apply, Finset.sum_apply] using h

theorem mixedFamily_product (hc : c ≤ m) (i j : Fin c) :
    MiddleCoordinates.projectedProduct (mixedFamily (K := K) hc i) (mixedFamily hc j) =
      (activeForms hc 2 (quadraticMonomial i j), 0) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [MiddleCoordinates.projectedProduct, MiddleCoordinates.mulLinear,
      mixedFamily, activeVariable, activeForms, quadraticMonomial]

/-- Uniform concrete augmented witness on the actual child polynomial quotient.
The same motions work for every subspace of marked child coefficients. -/
theorem augmented_witness (hc : c ≤ m)
    (hbudget : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2)
    (h2 : (2 : K) ≠ 0) :
    LinearIndependent K (mixedFamily (K := K) hc) ∧
    ∃ Q : Submodule K (Forms K m 2), finrank K Q = q ∧
      Function.Injective (quotientAlong (activeForms hc 2) Q) ∧
      ∃ r : Fin 4 → Forms K m 2 ⧸ Q, r 3 = 0 ∧
        Function.Injective (augmentedMap (quotientAlong (activeForms hc 2) Q) r) ∧
        ∀ U : Submodule K (Forms K m 2 ⧸ Q),
          Function.Injective (augmentedOnSubspace (quotientAlong (activeForms hc 2) Q) r U) := by
  refine ⟨mixedFamily_independent hc, ?_⟩
  obtain ⟨Q, hQ, hfQ, r, hr, hinj⟩ := exists_quotient_motions (activeForms (K := K) hc 2)
    (activeForms_injective hc 2) q (by simpa only [finrank_quadrics] using hbudget) h2
  exact ⟨Q, hQ, hfQ, r, hr, hinj, augmentedOnSubspace_injective _ r hinj⟩

end PolynomialSpecialization
end Quartic.AugmentedMiddle
