module

public import Quartic.AmbientCovectorSpreading
public import Quartic.AmbientCovectorTransport
public import Quartic.SliceMotionAvoidance

@[expose] public section

/-! Actual ambient closed slices with arbitrary threshold slice counts. -/
noncomputable section
namespace Quartic.AmbientSliceMotion
open Module MvPolynomial Matrix KernelPolynomialCharts
open BilinearCoefficientKernel BilinearCovectorCharts
variable {K : Type*} [Field K] [IsAlgClosed K]
variable {a b T c q a₁ a₂ n₁ n₂ r₁ r₂ : ℕ}
set_option maxHeartbeats 1500000

abbrev Threshold (a c : ℕ) := Fin (a-c+1)

theorem kernel_lower
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (E : Fin c → Fin a → K) (hE : LinearIndependent K E) (ell : Fin T → K)
    (hann : ∀ j f,covector ell (mu f (E j))=0) :
    c ≤ finrank K (LinearMap.ker (relationMap mu ell)) := by
  have hle : Submodule.span K (Set.range E) ≤ LinearMap.ker (relationMap mu ell) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact (AmbientCovectorTransport.mem_relationMap_ker_iff mu ell (E j)).mpr (hann j)
  have h := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card hE,Fintype.card_fin] at h

theorem principal_open_two_stage
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (E : Fin c → Fin a → K) (Q : Fin q → Fin b → K)
    (d s : ℕ) (Z : Fin s → Fin T → K) (hd : d+c ≤ a)
    (hempty : ∀ ell : Fin T → K,d+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      (∀ j f,covector ell (mu f (E j))=0) →
      (∀ i v,covector ell (mu (Q i) v)=0) →
      (∀ j,covector ell (Z j)=0) → ell=0)
    (A : Matrix (Fin a₁) (Fin n₁) (MvPolynomial (Fin T) K))
    (B : Matrix (Fin a₂) (Fin n₂) (MvPolynomial (Fin T ⊕ Fin n₁) K))
    (hA : ∀ (s : K) ell,evaluated A (s • ell)=s • evaluated A ell)
    (hB : ∀ (s : K) ell x,evaluated B (Sum.elim (s • ell) x)=s • evaluated B (Sum.elim ell x))
    (hcount : s ≤ r₁+r₂) :
    ∃ P : MvPolynomial (Fin n₁ ⊕ Fin n₂) K,
      (∃ z,eval z P≠0) ∧∀ z,eval z P≠0 →∀ ell : Fin T → K,ell≠0 →
      d+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      (∀ j f,covector ell (mu f (E j))=0) →
      (∀ i v,covector ell (mu (Q i) v)=0) →
      r₁ ≤ (evaluated A ell).rank →
      r₂ ≤ (evaluated B (Sum.elim ell (fun i => z (Sum.inl i)))).rank →
      evaluated A ell *ᵥ (fun i => z (Sum.inl i))≠0 ∨
        evaluated B (Sum.elim ell (fun i => z (Sum.inl i))) *ᵥ (fun i => z (Sum.inr i))≠0 := by
  have he : ∀ ell : Fin T → K,
      (∀ j,aeval ell (AmbientCovectorSpreading.finiteOriginalEquations (d := d) mu E Q j).val=0) →
      (∀ j,aeval ell (AmbientCovectorSpreading.slices Z j).val=0) → ell=0 := by
    intro ell hf hZ
    have h := (AmbientCovectorSpreading.finite_original_equations_iff mu E Q hd ell).mp
      (by simpa only [aeval_eq_eval] using hf)
    apply hempty ell h.1 h.2.1 h.2.2
    intro j
    simpa only [aeval_eq_eval,AmbientCovectorSpreading.slices,ClosedCovectorEquations.eval_linearForm] using hZ j
  obtain ⟨P,hP,hgood⟩ := SliceMotionAvoidance.principal_open_projective (L := K)
    (AmbientCovectorSpreading.finiteDegree a b c q d)
    (AmbientCovectorSpreading.finiteOriginalEquations mu E Q)
    (AmbientCovectorSpreading.slices Z) he A B hA hB hcount
  refine ⟨P,hP,?_⟩
  intro z hz ell hell hker hE hQ
  apply hgood z hz ell hell
  exact (AmbientCovectorSpreading.finite_original_equations_iff mu E Q hd ell).mpr ⟨hker,hE,hQ⟩

theorem principal_open_all_kernel_ranks
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (E : Fin c → Fin a → K) (Q : Fin q → Fin b → K) (hE : LinearIndependent K E)
    (slices : Threshold a c → ℕ)
    (Z : (d : Threshold a c) → Fin (slices d) → Fin T → K)
    (hempty : ∀ d : Threshold a c,∀ ell : Fin T → K,
      d.val+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      (∀ j f,covector ell (mu f (E j))=0) →
      (∀ i v,covector ell (mu (Q i) v)=0) →
      (∀ j,covector ell (Z d j)=0) → ell=0)
    (A : Matrix (Fin a₁) (Fin n₁) (MvPolynomial (Fin T) K))
    (B : Matrix (Fin a₂) (Fin n₂) (MvPolynomial (Fin T ⊕ Fin n₁) K))
    (hA : ∀ (s : K) ell,evaluated A (s • ell)=s • evaluated A ell)
    (hB : ∀ (s : K) ell x,evaluated B (Sum.elim (s • ell) x)=s • evaluated B (Sum.elim ell x))
    (r₁ r₂ : Threshold a c → ℕ) (hcount : ∀ d,slices d ≤ r₁ d+r₂ d)
    (Good : (Fin n₁ ⊕ Fin n₂ → K) → Prop)
    (hr₁ : ∀ d : Threshold a c,∀ ell : Fin T → K,ell≠0 →
      (∀ j f,covector ell (mu f (E j))=0) → (∀ i v,covector ell (mu (Q i) v)=0) →
      finrank K (LinearMap.ker (relationMap mu ell))=d.val+c →
      ∀ z,Good z → r₁ d ≤ (evaluated A ell).rank)
    (hr₂ : ∀ d : Threshold a c,∀ ell : Fin T → K,ell≠0 →
      (∀ j f,covector ell (mu f (E j))=0) → (∀ i v,covector ell (mu (Q i) v)=0) →
      finrank K (LinearMap.ker (relationMap mu ell))=d.val+c →
      ∀ z,Good z → evaluated A ell *ᵥ (fun i => z (Sum.inl i))=0 →
      r₂ d ≤ (evaluated B (Sum.elim ell (fun i => z (Sum.inl i)))).rank) :
    ∃ P : MvPolynomial (Fin n₁ ⊕ Fin n₂) K,
      (∃ z,eval z P≠0) ∧∀ z,eval z P≠0 → Good z →∀ ell : Fin T → K,ell≠0 →
      (∀ j f,covector ell (mu f (E j))=0) → (∀ i v,covector ell (mu (Q i) v)=0) →
      evaluated A ell *ᵥ (fun i => z (Sum.inl i))≠0 ∨
        evaluated B (Sum.elim ell (fun i => z (Sum.inl i))) *ᵥ (fun i => z (Sum.inr i))≠0 := by
  classical
  have hc : c ≤ a := by
    have h := (Submodule.span K (Set.range E)).finrank_le
    rw [finrank_span_eq_card hE,Fintype.card_fin,Module.finrank_fin_fun] at h
    exact h
  choose P hP hgood using fun d : Threshold a c =>
    principal_open_two_stage mu E Q d.val (slices d) (Z d) (by have hd := d.isLt; omega)
      (hempty d) A B hA hB (hcount d)
  have hPnz (d : Threshold a c) : P d≠0 := by
    obtain ⟨z,hz⟩ := hP d
    intro h
    exact hz (by rw [h,map_zero])
  refine ⟨∏ d,P d,PolynomialImageAvoidance.exists_eval_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun d _ => hPnz d)),?_⟩
  intro z hz hGood ell hell hEA hQ
  by_contra! hbad
  have hlo := kernel_lower mu E hE ell hEA
  have hdim : finrank K (LinearMap.ker (relationMap mu ell)) ≤ a := by
    simpa only [Module.finrank_fin_fun] using (LinearMap.ker (relationMap mu ell)).finrank_le
  let d : Threshold a c := ⟨finrank K (LinearMap.ker (relationMap mu ell))-c,by omega⟩
  have hd : finrank K (LinearMap.ker (relationMap mu ell))=d.val+c := by dsimp [d]; omega
  have hz' : eval z (P d)≠0 := by
    rw [map_prod] at hz
    exact Finset.prod_ne_zero_iff.mp hz d (Finset.mem_univ d)
  have h := hgood d z hz' ell hell hd.ge hEA hQ (hr₁ d ell hell hEA hQ hd z hGood)
    (hr₂ d ell hell hEA hQ hd z hGood hbad.1)
  exact h.elim (fun h => h hbad.1) (fun h => h hbad.2)

end Quartic.AmbientSliceMotion
