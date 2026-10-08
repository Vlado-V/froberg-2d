import Quartic.SliceFiniteModule
import Quartic.FiniteAlgebraicKernelAvoidance
import Quartic.HomogeneousSliceNormalization

/-! The empty-section to dependent-motion bridge on actual affine slice charts. -/
noncomputable section
universe u
namespace Quartic.SliceMotionAvoidance
open MvPolynomial Matrix Algebra KernelPolynomialCharts SliceFiniteModule
variable {K : Type u} [Field K] [Infinite K]
variable {q fcount s a b n l r₁ r₂ : ℕ}

/-- An empty projective linear section gives a nonempty open avoiding both
successive kernel equations on the chart where its first slice is one.
The component dimension bound is derived from the empty-section hypothesis. -/
theorem principal_open_dehom {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (d : Fin fcount → ℕ) (f : ∀ i, Forms K q (d i))
    (ℓ : Fin (s+1) → Forms K q 1)
    (hempty : ∀ t : Fin q → L, (∀ i, aeval t (f i).val = 0) →
      (∀ i, aeval t (ℓ i).val = 0) → t = 0)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial (Fin q) K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (Fin q ⊕ Fin n) K))
    (hcount : s < r₁+r₂) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin l) K,
      (∃ z : Fin n ⊕ Fin l → K, eval z P ≠ 0) ∧
      ∀ z, eval z P ≠ 0 → ∀ t : Fin q → K,
        (∀ i, eval t (f i).val = 0) → eval t (ℓ 0).val = 1 →
        let x := fun i => z (Sum.inl i)
        let y := fun j => z (Sum.inr j)
        r₁ ≤ (evaluated A t).rank →
        r₂ ≤ (evaluated B (Sum.elim t x)).rank →
        evaluated A t *ᵥ x ≠ 0 ∨ evaluated B (Sum.elim t x) *ᵥ y ≠ 0 := by
  let I : Ideal (Poly K q) := Ideal.span (Set.range (fun i => (f i).val))
  let J := dehomIdeal I ℓ
  let R := (Poly K q) ⧸ J
  let base : Fin q → R := fun i => Ideal.Quotient.mk J (X i)
  let slices : Fin s → R := fun i => Ideal.Quotient.mkₐ K J (ℓ i.succ).val
  let : Module.Finite (Algebra.adjoin K (Set.range slices)) R :=
    finite_dehom_of_geometric_empty I d f ℓ
      (fun i => Ideal.subset_span ⟨i,rfl⟩) hempty
  obtain ⟨P,hP,havoid⟩ := FiniteAlgebraicKernelAvoidance.principal_open_two_stage
    slices base A B hcount
  refine ⟨P,hP,?_⟩
  intro z hz t htf htℓ
  dsimp only
  intro hr hs
  have hJ : J ≤ RingHom.ker (aeval t).toRingHom := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      exact htf i
    · apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change eval t ((ℓ 0).val-1) = 0
      rw [map_sub,map_one,htℓ,sub_self]
  let φ : R →ₐ[K] K := Ideal.Quotient.liftₐ J (aeval t) (fun p hp => hJ hp)
  have hbase : (fun i => φ (base i)) = t := by
    funext i
    exact aeval_X t i
  have h := havoid z hz φ
  dsimp only at h
  rw [hbase] at h
  exact h hr hs

open HomogeneousSliceNormalization

/-- Empty linear sections control the unsliced homogeneous locus for two
successive motion constraints. Every nonzero covector is covered by an actual
normalized slice chart. Matrix scaling is an explicit algebraic compatibility
condition, not a dimension or generic-fiber assumption. -/
theorem principal_open_projective_succ {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (d : Fin fcount → ℕ) (f : ∀ i, Forms K q (d i))
    (ℓ : Fin (s+1) → Forms K q 1)
    (hempty : ∀ t : Fin q → L, (∀ i, aeval t (f i).val = 0) →
      (∀ i, aeval t (ℓ i).val = 0) → t = 0)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial (Fin q) K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (Fin q ⊕ Fin n) K))
    (hA : ∀ (c : K) t, evaluated A (c • t) = c • evaluated A t)
    (hB : ∀ (c : K) t x, evaluated B (Sum.elim (c • t) x) =
      c • evaluated B (Sum.elim t x))
    (hcount : s < r₁+r₂) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin l) K,
      (∃ z : Fin n ⊕ Fin l → K, eval z P ≠ 0) ∧
      ∀ z, eval z P ≠ 0 → ∀ t : Fin q → K, t ≠ 0 →
        (∀ i, eval t (f i).val = 0) →
        let x := fun i => z (Sum.inl i)
        let y := fun j => z (Sum.inr j)
        r₁ ≤ (evaluated A t).rank →
        r₂ ≤ (evaluated B (Sum.elim t x)).rank →
        evaluated A t *ᵥ x ≠ 0 ∨ evaluated B (Sum.elim t x) *ᵥ y ≠ 0 := by
  classical
  choose P hP havoid using fun i : Fin (s+1) => principal_open_dehom d f
    (moveSlice ℓ i) (geometric_empty_moveSlice d f ℓ hempty i) A B hcount
  have hPnz (i : Fin (s+1)) : P i ≠ 0 := by
    intro he
    obtain ⟨z,hz⟩ := hP i
    exact hz (by rw [he,map_zero])
  refine ⟨∏ i, P i,PolynomialImageAvoidance.exists_eval_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hPnz i)),?_⟩
  intro z hz t ht htf
  dsimp only
  intro hr hs
  by_contra! hbad
  obtain ⟨i,hi,huf,hul,_⟩ := exists_normalized_chart_of_geometric_empty d f ℓ hempty t ht htf
  let u := normalize (ℓ i) t
  let c : K := (aeval t (ℓ i).val)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hi
  have heu : u = c • t := rfl
  have hr' : r₁ ≤ (evaluated A u).rank := by
    rw [heu,hA,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)]
    exact hr
  have hs' : r₂ ≤ (evaluated B (Sum.elim u (fun j => z (Sum.inl j)))).rank := by
    rw [heu,hB,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)]
    exact hs
  have ha : evaluated A u *ᵥ (fun j => z (Sum.inl j)) = 0 := by
    rw [heu,hA,Matrix.smul_mulVec,hbad.1,smul_zero]
  have hb : evaluated B (Sum.elim u (fun j => z (Sum.inl j))) *ᵥ
      (fun j => z (Sum.inr j)) = 0 := by
    rw [heu,hB,Matrix.smul_mulVec,hbad.2,smul_zero]
  have hzi : eval z (P i) ≠ 0 := by
    rw [map_prod] at hz
    exact (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
  exact (havoid i z hzi u huf hul hr' hs').elim (fun h => h ha) (fun h => h hb)

/-- The complete empty-section to motion-avoidance theorem, including the
zero-slice case. The numerical premise is the literal sum-of-ranks bound.
No generic-fiber or rational-parametrization premise remains. -/
theorem principal_open_projective {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (d : Fin fcount → ℕ) (f : ∀ i, Forms K q (d i))
    (ℓ : Fin s → Forms K q 1)
    (hempty : ∀ t : Fin q → L, (∀ i, aeval t (f i).val = 0) →
      (∀ i, aeval t (ℓ i).val = 0) → t = 0)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial (Fin q) K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (Fin q ⊕ Fin n) K))
    (hA : ∀ (c : K) t, evaluated A (c • t) = c • evaluated A t)
    (hB : ∀ (c : K) t x, evaluated B (Sum.elim (c • t) x) =
      c • evaluated B (Sum.elim t x))
    (hcount : s ≤ r₁+r₂) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin l) K,
      (∃ z : Fin n ⊕ Fin l → K, eval z P ≠ 0) ∧
      ∀ z, eval z P ≠ 0 → ∀ t : Fin q → K, t ≠ 0 →
        (∀ i, eval t (f i).val = 0) →
        let x := fun i => z (Sum.inl i)
        let y := fun j => z (Sum.inr j)
        r₁ ≤ (evaluated A t).rank →
        r₂ ≤ (evaluated B (Sum.elim t x)).rank →
        evaluated A t *ᵥ x ≠ 0 ∨ evaluated B (Sum.elim t x) *ᵥ y ≠ 0 := by
  cases s with
  | zero =>
    have hempty' : ∀ t : Fin q → L, (∀ i, aeval t (f i).val = 0) → t = 0 := by
      intro t ht
      exact hempty t ht (fun i => Fin.elim0 i)
    obtain ⟨N,hN,hcert⟩ := HomogeneousMultiplicationCertificate.exists_surjective_degree d f hempty'
    refine ⟨1,⟨0,by simp⟩,?_⟩
    intro z _ t ht htf
    exact (ht (HomogeneousMultiplicationCertificate.zero_of_surjective d f N hN hcert t htf)).elim
  | succ s =>
    exact principal_open_projective_succ d f ℓ hempty A B hA hB (by omega)

end Quartic.SliceMotionAvoidance
