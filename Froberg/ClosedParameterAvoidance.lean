import Froberg.ClosedBaseParameters

/-! Projective closed-base avoidance with free graph parameters and two
successive dependent systems of linear equations. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open MvPolynomial Matrix Quartic Quartic.KernelPolynomialCharts
open Quartic.HomogeneousSliceNormalization
variable {K : Type*} [Field K] [Infinite K]
variable {q N s fcount a b n l r₁ r₂ : ℕ}

theorem principal_open_projective_with_parameters
    {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (degrees : Fin fcount → ℕ) (f : ∀ i, Forms K q (degrees i))
    (ell : Fin s → Forms K q 1)
    (hempty : ∀ t : Fin q → L, (∀ i, aeval t (f i).val=0) →
      (∀ j, aeval t (ell j).val=0) → t=0)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial (Fin (q+N)) K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (Fin (q+N) ⊕ Fin n) K))
    (hA : ∀ (c : K) t u, evaluated A (Fin.append (c • t) u)=c • evaluated A (Fin.append t u))
    (hB : ∀ (c : K) t u x, evaluated B (Sum.elim (Fin.append (c • t) u) x)=
      c • evaluated B (Sum.elim (Fin.append t u) x))
    (hcount : s+N≤r₁+r₂) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin l) K,
      (∃ z, eval z P ≠ 0) ∧ ∀ z, eval z P ≠ 0 →
        ∀ t : Fin q → K, t ≠ 0 → (∀ i,eval t (f i).val=0) → ∀ u : Fin N → K,
          r₁ ≤ (evaluated A (Fin.append t u)).rank →
          r₂ ≤ (evaluated B (Sum.elim (Fin.append t u) (fun i => z (.inl i)))).rank →
          Matrix.mulVec (evaluated A (Fin.append t u)) (fun i => z (.inl i)) ≠ 0 ∨
          Matrix.mulVec (evaluated B (Sum.elim (Fin.append t u) (fun i => z (.inl i))))
            (fun j => z (.inr j)) ≠ 0 := by
  classical
  cases s with
  | zero =>
    have hempty' : ∀ t : Fin q → L, (∀ i, aeval t (f i).val=0) → t=0 := by
      intro t ht
      exact hempty t ht (fun i => Fin.elim0 i)
    obtain ⟨D,hD,hcert⟩ := HomogeneousMultiplicationCertificate.exists_surjective_degree degrees f hempty'
    refine ⟨1,⟨0,by simp⟩,?_⟩
    intro z _ t ht hf
    exact (ht (HomogeneousMultiplicationCertificate.zero_of_surjective degrees f D hD hcert t hf)).elim
  | succ s =>
    have hc : s+N<r₁+r₂ := by omega
    choose P hP havoid using fun i : Fin (s+1) =>
      principal_open_dehom_with_parameters degrees f (moveSlice ell i)
        (geometric_empty_moveSlice degrees f ell hempty i) A B hc
    have hPnz (i : Fin (s+1)) : P i ≠ 0 := by
      obtain ⟨z,hz⟩ := hP i
      intro he
      exact hz (by rw [he,map_zero])
    refine ⟨∏ i, P i,PolynomialImageAvoidance.exists_eval_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hPnz i)),?_⟩
    intro z hz t ht hf u hr hs
    by_contra! hbad
    obtain ⟨i,hi,huf,hul,_⟩ := exists_normalized_chart_of_geometric_empty degrees f ell hempty t ht hf
    let v := normalize (ell i) t
    let c : K := (aeval t (ell i).val)⁻¹
    have hcnz : c ≠ 0 := inv_ne_zero hi
    have hev : v=c • t := rfl
    have hr' : r₁ ≤ (evaluated A (Fin.append v u)).rank := by
      rw [hev,hA,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hcnz)]
      exact hr
    have hs' : r₂ ≤ (evaluated B (Sum.elim (Fin.append v u) (fun j => z (.inl j)))).rank := by
      rw [hev,hB,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hcnz)]
      exact hs
    have ha : Matrix.mulVec (evaluated A (Fin.append v u)) (fun j => z (.inl j))=0 := by
      rw [hev,hA,Matrix.smul_mulVec,hbad.1,smul_zero]
    have hb : Matrix.mulVec (evaluated B (Sum.elim (Fin.append v u) (fun j => z (.inl j))))
        (fun j => z (.inr j))=0 := by
      rw [hev,hB,Matrix.smul_mulVec,hbad.2,smul_zero]
    have hzi : eval z (P i) ≠ 0 := by
      rw [map_prod] at hz
      exact Finset.prod_ne_zero_iff.mp hz i (Finset.mem_univ i)
    exact (havoid i z hzi v huf hul u hr' hs').elim (fun h => h ha) (fun h => h hb)

end Froberg
