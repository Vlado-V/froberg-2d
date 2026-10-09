module

public import Froberg.GenericDimensions
public import Quartic.PolynomialRankOpen

@[expose] public section

/-! First-order rank gain for an actual linear pencil.  The construction
uses image lifts and cycle lifts, so no matrix-factorization premise remains. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial Quartic

section LinearPencil
variable {K V W J : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup J] [Module K J]

/-- The first derivative, restricted to the old kernel and then projected. -/
def firstResponse (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J) : M₀.ker →ₗ[K] J :=
  π.comp (M₁.comp M₀.ker.subtype)

/-- A nonzero first-normal minor forces the corresponding rank gain on an
explicit principal open of nonzero parameters. -/
theorem firstResponse_rank_gain_principal_open
    (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J) (hπ : π.comp M₀ = 0) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K M₀.range + finrank K (firstResponse M₀ M₁ π).range ≤
          finrank K (M₀ + ε • M₁).range := by
  classical
  let R := firstResponse M₀ M₁ π
  obtain ⟨P, hP⟩ := M₀.rangeRestrict.exists_rightInverse_of_surjective M₀.range_rangeRestrict
  obtain ⟨S, hS⟩ := R.rangeRestrict.exists_rightInverse_of_surjective R.range_rangeRestrict
  have hPval (u : M₀.range) : M₀ (P u) = u.val :=
    congrArg Subtype.val (LinearMap.congr_fun hP u)
  have hSval (u : R.range) : R (S u) = u.val :=
    congrArg Subtype.val (LinearMap.congr_fun hS u)
  let B : R.range →ₗ[K] W := M₁.comp (M₀.ker.subtype.comp S)
  have hB (u : R.range) : π (B u) = u.val := hSval u
  let E₀ : (M₀.range × R.range) →ₗ[K] W := M₀.range.subtype.coprod B
  let E₁ : (M₀.range × R.range) →ₗ[K] W := (M₁.comp P).comp (LinearMap.fst K _ _)
  have hπu (u : M₀.range) : π u.val = 0 := by
    rw [← hPval u]
    exact LinearMap.congr_fun hπ (P u)
  have hE₀ : Function.Injective E₀ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    change x.1.val + B x.2 = 0 at hx
    have hy : x.2 = 0 := by
      apply Subtype.ext
      have hh := congrArg π hx
      simpa only [map_add, hπu, hB, zero_add, map_zero, Submodule.coe_zero] using hh
    have hu : x.1 = 0 := by
      apply Subtype.ext
      simpa only [hy, map_zero, add_zero, Submodule.coe_zero] using hx
    exact Prod.ext hu hy
  let E : (Fin 1 → K) → ((M₀.range × R.range) →ₗ[K] W) := fun a => E₀ + a 0 • E₁
  have hEpoly : IsPolynomialFamily E :=
    (isPolynomialFamily_const E₀).add
      ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul (isPolynomialFamily_const E₁))
  obtain ⟨D, hD, hEinj⟩ := injective_polynomial_principal_open E hEpoly 0
    (by simpa [E] using hE₀)
  refine ⟨D, hD, ?_⟩
  intro ε he hDa
  let a : Fin 1 → K := fun _ => ε
  have hsub : (E a).range ≤ (M₀ + ε • M₁).range := by
    rintro _ ⟨x, rfl⟩
    refine ⟨P x.1 + ε⁻¹ • (S x.2).val, ?_⟩
    have hcycle : M₀ (S x.2).val = 0 := (S x.2).property
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
      hPval, hcycle, zero_add, smul_smul,
      inv_mul_cancel₀ he, one_smul]
    change x.1.val + ε • M₁ (P x.1) + B x.2 =
      x.1.val + B x.2 + ε • M₁ (P x.1)
    abel
  have hr := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj (hEinj a hDa), Module.finrank_prod] at hr
  exact hr

end LinearPencil

section Descent
variable {K E T J : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup T] [Module K T]
  [AddCommGroup J] [Module K J]

/-- Descent to a kernel modulo its boundary, elaborated before specializing
to the polynomial complex. -/
def descendCycleMap (M : E →ₗ[K] T) (B : Submodule K E)
    (N : M.ker →ₗ[K] J) (hN : kernelBoundary M B ≤ N.ker) :
    KernelModulo M B →ₗ[K] J := (kernelBoundary M B).liftQ N hN

theorem range_descendCycleMap (M : E →ₗ[K] T) (B : Submodule K E)
    (N : M.ker →ₗ[K] J) (hN : kernelBoundary M B ≤ N.ker) :
    (descendCycleMap M B N hN).range = N.range :=
  Submodule.range_liftQ _ _ _

end Descent

section PolynomialNormalMap
variable {K : Type*} [Field K] {n d r : ℕ}

abbrev EndpointCokernel (q : Fin r → Forms K n d) :=
  Forms K n (2 * d) ⧸ (endpointMultiplication q).range

def endpointNormalCycles (q p : Fin r → Forms K n d) :
    (endpointMultiplication q).ker →ₗ[K] EndpointCokernel q :=
  (endpointMultiplication q).range.mkQ.comp
    ((endpointMultiplication p).comp (endpointMultiplication q).ker.subtype)

theorem endpointMultiplication_cross_koszul (q p : Fin r → Forms K n d)
    (ij : GeneratorPair r) :
    endpointMultiplication p (koszulVector q ij) =
      -endpointMultiplication q (koszulVector p ij) := by
  classical
  apply Subtype.ext
  simp only [Submodule.coe_neg, endpointMultiplication_val]
  have hcoe (i j : Fin r) (a : Forms K n d) :
      ((if i = j then a else 0) : Forms K n d).val = if i = j then a.val else 0 := by
    split_ifs <;> rfl
  simp only [koszulVector, Submodule.coe_sub, hcoe, mul_sub, mul_ite, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Constant Koszul boundaries disappear from the first derivative in the cokernel. -/
theorem incoming_le_ker_endpointNormalCycles (q p : Fin r → Forms K n d) :
    incomingInKernel q ≤ (endpointNormalCycles q p).ker := by
  have hspan : koszulSpace q ≤ ((endpointMultiplication q).range.mkQ.comp
      (endpointMultiplication p)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    change (endpointMultiplication q).range.mkQ
      (endpointMultiplication p (koszulVector q ij)) = 0
    rw [endpointMultiplication_cross_koszul, map_neg]
    have hz : (endpointMultiplication q).range.mkQ
        (endpointMultiplication q (koszulVector p ij)) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨koszulVector p ij, rfl⟩
    rw [hz, neg_zero]
  intro a ha
  exact hspan ha

/-- The manuscript's first normal map on actual Koszul homology classes. -/
def endpointNormalMap (q p : Fin r → Forms K n d) :
    EndpointHomology q →ₗ[K] EndpointCokernel q :=
  descendCycleMap (endpointMultiplication q) (koszulSpace q) (endpointNormalCycles q p)
    (incoming_le_ker_endpointNormalCycles q p)

theorem range_endpointNormalMap (q p : Fin r → Forms K n d) :
    (endpointNormalMap q p).range = (endpointNormalCycles q p).range := by
  exact range_descendCycleMap _ _ _ _

theorem endpoint_normal_rank_gain_principal_open [Infinite K] (q p : Fin r → Forms K n d) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K (endpointMultiplication q).range + finrank K (endpointNormalMap q p).range ≤
          finrank K (endpointMultiplication q + ε • endpointMultiplication p).range := by
  have hπ : (endpointMultiplication q).range.mkQ.comp (endpointMultiplication q) = 0 := by
    apply LinearMap.ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
  obtain ⟨D, hD, hprop⟩ := firstResponse_rank_gain_principal_open
    (endpointMultiplication q) (endpointMultiplication p) (endpointMultiplication q).range.mkQ hπ
  refine ⟨D, hD, fun ε hε hDε => ?_⟩
  rw [range_endpointNormalMap]
  exact hprop ε hε hDε

theorem endpointMultiplication_motion (q p : Fin r → Forms K n d) (ε : K) :
    endpointMultiplication (q + ε • p) = endpointMultiplication q + ε • endpointMultiplication p := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp [endpointMultiplication_val, add_mul, Finset.sum_add_distrib, ← Finset.smul_sum]

theorem independent_motion_principal_open [Infinite K] (q p : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧ ∀ ε : K,
      eval (fun _ => ε) D ≠ 0 → LinearIndependent K (q + ε • p) := by
  let family : Fin r → (Fin 1 → K) → Forms K n d := fun i a => q i + a 0 • p i
  have hpoly : ∀ i, IsPolynomialFamily (family i) := fun i =>
    (isPolynomialFamily_const (q i)).add
      ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul (isPolynomialFamily_const (p i)))
  obtain ⟨D, hD, hprop⟩ := independent_polynomial_principal_open family hpoly 0
    (by simpa [family] using hq)
  exact ⟨D, hD, fun ε hε => hprop (fun _ => ε) hε⟩

/-- Lemma C.5 for the actual polynomial Koszul complex: a normal map of
rank `s` gives a nonzero motion parameter lowering first homology by at least `s`. -/
theorem exists_endpoint_normal_homology_drop [Infinite K] (q p : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    ∃ ε : K, ε ≠ 0 ∧ LinearIndependent K (q + ε • p) ∧
      finrank K (EndpointHomology (q + ε • p)) + finrank K (endpointNormalMap q p).range ≤
        finrank K (EndpointHomology q) := by
  classical
  obtain ⟨D, hD, hRank⟩ := endpoint_normal_rank_gain_principal_open q p
  obtain ⟨E, hE, hInd⟩ := independent_motion_principal_open q p hq
  have hDE : ∃ a : Fin 1 → K, eval a (D * E) ≠ 0 :=
    ⟨0, by simpa using mul_ne_zero hD hE⟩
  have hX : ∃ a : Fin 1 → K, eval a (X (0 : Fin 1)) ≠ 0 := ⟨fun _ => 1, by simp⟩
  obtain ⟨a, haDE, haX⟩ := principal_opens_intersect hDE hX
  have ha : (fun _ : Fin 1 => a 0) = a := by ext i; fin_cases i; rfl
  have haD : eval (fun _ => a 0) D ≠ 0 := by
    rw [ha]
    exact (mul_ne_zero_iff.mp (by simpa using haDE)).1
  have haE : eval (fun _ => a 0) E ≠ 0 := by
    rw [ha]
    exact (mul_ne_zero_iff.mp (by simpa using haDE)).2
  have hε : a 0 ≠ 0 := by simpa using haX
  have hi := hInd (a 0) haE
  have hrank := hRank (a 0) hε haD
  rw [← endpointMultiplication_motion] at hrank
  have hbefore := (endpointMultiplication q).finrank_range_add_finrank_ker
  have hafter := (endpointMultiplication (q + a 0 • p)).finrank_range_add_finrank_ker
  have hHbefore := homology_add_pairs q hq
  have hHafter := homology_add_pairs (q + a 0 • p) hi
  exact ⟨a 0, hε, hi, by omega⟩

end PolynomialNormalMap
end Froberg
