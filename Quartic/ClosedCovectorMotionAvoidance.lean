import Quartic.ConvolutionClosedSlices
import Quartic.SliceMotionAvoidance

/-!
# From actual closed covector slices to successive motion avoidance

The unsliced equations contain only the relation minors and the shared-Q
annihilation equations. The auxiliary Z equations are supplied separately
as the linear slices; they are never retained in the unsliced locus.
-/
noncomputable section
namespace Quartic.ClosedCovectorMotionAvoidance
open Module MvPolynomial Matrix KernelPolynomialCharts
open BilinearCoefficientKernel BilinearCovectorCharts ClosedCovectorEquations
variable {K : Type*} [Field K] [IsAlgClosed K]
variable {a B T q s d a₁ a₂ n₁ n₂ r₁ r₂ : ℕ}

omit [IsAlgClosed K] in
/-- The geometric empty-section hypothesis for the correct unsliced family:
minors plus Q, with every auxiliary linear equation outside that family. -/
theorem split_empty_section
    (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (Q : Fin q → Fin B → K) (Z : Fin s → Fin T → K) (hd : d ≤ a)
    (hempty : ∀ ell : Fin T → K,
      d ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      ((∀ i v,covector ell (mu (Q i) v)=0) ∧ (∀ j,covector ell (Z j)=0)) → ell=0) :
    ∀ ell : Fin T → K,
      (∀ i,aeval ell (finiteEquations (d := d) mu (Q,Fin.elim0) i).val=0) →
      (∀ j,aeval ell (linearForm (Z j)).val=0) → ell=0 := by
  intro ell hf hZ
  have he := (finite_equations_iff mu (Q,Fin.elim0) hd ell).mp
    (by simpa only [aeval_eq_eval] using hf)
  apply hempty ell he.1
  refine ⟨he.2.1,?_⟩
  intro j
  simpa only [aeval_eq_eval,eval_linearForm] using hZ j

/-- The checked empty-slice statement yields an open avoiding two actual
successive motion constraints on the unsliced closed covector threshold. -/
theorem principal_open_two_stage
    (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (Q : Fin q → Fin B → K) (Z : Fin s → Fin T → K) (hd : d ≤ a)
    (hempty : ∀ ell : Fin T → K,
      d ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      ((∀ i v,covector ell (mu (Q i) v)=0) ∧ (∀ j,covector ell (Z j)=0)) → ell=0)
    (A : Matrix (Fin a₁) (Fin n₁) (MvPolynomial (Fin T) K))
    (B₂ : Matrix (Fin a₂) (Fin n₂) (MvPolynomial (Fin T ⊕ Fin n₁) K))
    (hA : ∀ (c : K) ell,evaluated A (c • ell)=c • evaluated A ell)
    (hB : ∀ (c : K) ell x,evaluated B₂ (Sum.elim (c • ell) x)=
      c • evaluated B₂ (Sum.elim ell x))
    (hcount : s ≤ r₁+r₂) :
    ∃ P : MvPolynomial (Fin n₁ ⊕ Fin n₂) K,
      (∃ z : Fin n₁ ⊕ Fin n₂ → K,eval z P ≠ 0) ∧
      ∀ z,eval z P ≠ 0 → ∀ ell : Fin T → K,ell ≠ 0 →
        d ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
        (∀ i v,covector ell (mu (Q i) v)=0) →
        let x := fun i => z (Sum.inl i)
        let y := fun j => z (Sum.inr j)
        r₁ ≤ (evaluated A ell).rank →
        r₂ ≤ (evaluated B₂ (Sum.elim ell x)).rank →
        evaluated A ell *ᵥ x ≠ 0 ∨ evaluated B₂ (Sum.elim ell x) *ᵥ y ≠ 0 := by
  obtain ⟨P,hP,hgood⟩ := SliceMotionAvoidance.principal_open_projective (L := K)
    (finiteDegree a B q 0 d) (finiteEquations (d := d) mu (Q,Fin.elim0))
    (fun j => linearForm (Z j)) (split_empty_section mu Q Z hd hempty) A B₂ hA hB hcount
  refine ⟨P,hP,?_⟩
  intro z hz ell hell hker hQ
  apply hgood z hz ell hell
  exact (finite_equations_iff mu (Q,Fin.elim0) hd ell).mpr
    ⟨hker,hQ,fun j => Fin.elim0 j⟩

/-- A finite product over every actual relation-kernel dimension removes all
rank premises from the conclusion. The second rank bound is required only
on the first kernel, so the two stages are explicitly allowed to depend. -/
theorem principal_open_all_kernel_ranks
    (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (Q : Fin q → Fin B → K) (slices : Fin (a+1) → ℕ)
    (Z : (d : Fin (a+1)) → Fin (slices d) → Fin T → K)
    (hempty : ∀ d : Fin (a+1),∀ ell : Fin T → K,
      d.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      ((∀ i v,covector ell (mu (Q i) v)=0) ∧ (∀ j,covector ell (Z d j)=0)) → ell=0)
    (A : Matrix (Fin a₁) (Fin n₁) (MvPolynomial (Fin T) K))
    (B₂ : Matrix (Fin a₂) (Fin n₂) (MvPolynomial (Fin T ⊕ Fin n₁) K))
    (hA : ∀ (c : K) ell,evaluated A (c • ell)=c • evaluated A ell)
    (hB : ∀ (c : K) ell x,evaluated B₂ (Sum.elim (c • ell) x)=
      c • evaluated B₂ (Sum.elim ell x))
    (r₁ r₂ : Fin (a+1) → ℕ) (hcount : ∀ d,slices d ≤ r₁ d+r₂ d)
    (Good : (Fin n₁ ⊕ Fin n₂ → K) → Prop)
    (hr₁ : ∀ d : Fin (a+1),∀ ell : Fin T → K,ell ≠ 0 →
      (∀ i v,covector ell (mu (Q i) v)=0) →
      finrank K (LinearMap.ker (relationMap mu ell))=d.val →
      ∀ z : Fin n₁ ⊕ Fin n₂ → K,Good z → r₁ d ≤ (evaluated A ell).rank)
    (hr₂ : ∀ d : Fin (a+1),∀ ell : Fin T → K,ell ≠ 0 →
      (∀ i v,covector ell (mu (Q i) v)=0) →
      finrank K (LinearMap.ker (relationMap mu ell))=d.val →
      ∀ z : Fin n₁ ⊕ Fin n₂ → K,Good z →
        evaluated A ell *ᵥ (fun i => z (Sum.inl i))=0 →
        r₂ d ≤ (evaluated B₂ (Sum.elim ell (fun i => z (Sum.inl i)))).rank) :
    ∃ P : MvPolynomial (Fin n₁ ⊕ Fin n₂) K,
      (∃ z : Fin n₁ ⊕ Fin n₂ → K,eval z P ≠ 0) ∧
      ∀ z,eval z P ≠ 0 → Good z → ∀ ell : Fin T → K,ell ≠ 0 →
        (∀ i v,covector ell (mu (Q i) v)=0) →
        let x := fun i => z (Sum.inl i)
        let y := fun j => z (Sum.inr j)
        evaluated A ell *ᵥ x ≠ 0 ∨ evaluated B₂ (Sum.elim ell x) *ᵥ y ≠ 0 := by
  classical
  choose P hP hgood using fun d : Fin (a+1) =>
    principal_open_two_stage (d := d.val) mu Q (Z d) (by omega) (hempty d)
      A B₂ hA hB (hcount d)
  have hPnz (d : Fin (a+1)) : P d ≠ 0 := by
    obtain ⟨z,hz⟩ := hP d
    intro h
    exact hz (by rw [h,map_zero])
  refine ⟨∏ d,P d,PolynomialImageAvoidance.exists_eval_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun d _ => hPnz d)),?_⟩
  intro z hz hGood ell hell hQ
  dsimp only
  by_contra! hbad
  have hdim : finrank K (LinearMap.ker (relationMap mu ell)) ≤ a := by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      (LinearMap.ker (relationMap mu ell)).finrank_le
  let d : Fin (a+1) := ⟨finrank K (LinearMap.ker (relationMap mu ell)),by omega⟩
  have hz' : eval z (P d) ≠ 0 := by
    rw [map_prod] at hz
    exact (Finset.prod_ne_zero_iff.mp hz) d (Finset.mem_univ d)
  have h := hgood d z hz' ell hell le_rfl hQ (hr₁ d ell hell hQ rfl z hGood)
    (hr₂ d ell hell hQ rfl z hGood hbad.1)
  exact h.elim (fun h => h hbad.1) (fun h => h hbad.2)

open ProfileCertificate UniformEndpoint ConvolutionClosedSlices

/-- Actual fixed-convolution closed covectors, with all profile boundaries,
feed the general dependent-motion theorem on one joint Q/slice open.
Only explicit pointwise rank and covector-scaling hypotheses remain on the
supplied motion matrices; the unsliced base has no assumed dimension. -/
theorem generic_actual_two_stage (m : ℕ) (hmlo : 28 ≤ m) (hmhi : m ≤ 40)
    (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (d : ℕ) (hd : d ≤ totalA m (mixedCount m upper))
    (A : Matrix (Fin a₁) (Fin n₁) (MvPolynomial (Fin (finrank K (Tgt K m upper))) K))
    (B₂ : Matrix (Fin a₂) (Fin n₂)
      (MvPolynomial (Fin (finrank K (Tgt K m upper)) ⊕ Fin n₁) K))
    (hA : ∀ (c : K) ell,evaluated A (c • ell)=c • evaluated A ell)
    (hB : ∀ (c : K) ell x,evaluated B₂ (Sum.elim (c • ell) x)=
      c • evaluated B₂ (Sum.elim ell x))
    (hcount : sliceCount m upper d ≤ r₁+r₂) :
    ∃ P : MvPolynomial (Fin (finrank K (SlicedInput K m upper d))) K,
      (∃ v : SlicedInput K m upper d,
        eval (PolynomialBilinearCoordinates.coordinates K _ v) P ≠ 0) ∧
      ∀ v : SlicedInput K m upper d,
        eval (PolynomialBilinearCoordinates.coordinates K _ v) P ≠ 0 →
        ∃ R : MvPolynomial (Fin n₁ ⊕ Fin n₂) K,
          (∃ z : Fin n₁ ⊕ Fin n₂ → K,eval z R ≠ 0) ∧
          ∀ z,eval z R ≠ 0 → ∀ ell : Fin (finrank K (Tgt K m upper)) → K,ell ≠ 0 →
            d ≤ finrank K (LinearMap.ker (relationMap (actualMu m upper ht) ell)) →
            (∀ i w,covector ell (actualMu m upper ht (v.1 i) w)=0) →
            let x := fun i => z (Sum.inl i)
            let y := fun j => z (Sum.inr j)
            r₁ ≤ (evaluated A ell).rank →
            r₂ ≤ (evaluated B₂ (Sum.elim ell x)).rank →
            evaluated A ell *ᵥ x ≠ 0 ∨ evaluated B₂ (Sum.elim ell x) *ᵥ y ≠ 0 := by
  obtain ⟨P,hP,hgood⟩ := principal_open_closed_sliced_empty (K := K) m hmlo hmhi upper ht d
  refine ⟨P,hP,?_⟩
  intro v hv
  have hd' : d ≤ ∑ i,blocks m upper i := by rw [blocks_sum]; exact hd
  exact principal_open_two_stage (actualMu m upper ht) v.1 v.2 hd'
    (hgood v hv) A B₂ hA hB hcount

end Quartic.ClosedCovectorMotionAvoidance
