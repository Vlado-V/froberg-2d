module

public import Froberg.SlicedPolynomialOpen
public import Froberg.ClosedKernelSlices

@[expose] public section

/-! Closed covector thresholds persist under an arbitrary polynomial change
of the presentation, in one fixed ambient target. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic BilinearCovectorCharts BilinearCoefficientKernel
variable {K I : Type*} [Field K] [IsAlgClosed K] {a b T c : ℕ}

theorem presentation_threshold_principal_open
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (A : (I → K) → Fin c → Fin T → K)
    (hA : ∀ i k,IsPolynomialFamily (fun p => A p i k))
    (r : Fin (a+1)) {s : ℕ} (Z : Fin s → Forms K T 1) (p₀ : I → K)
    (hempty : ∀ ell : Fin T → K,
      r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      (∀ i,covector ell (A p₀ i)=0) → (∀ i,aeval ell (Z i).val=0) → ell=0) :
    ∃ P : MvPolynomial I K,eval p₀ P ≠ 0 ∧ ∀ p,eval p P ≠ 0 →
      ∀ ell : Fin T → K,
        r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
        (∀ i,covector ell (A p i)=0) → (∀ i,aeval ell (Z i).val=0) → ell=0 := by
  let d := AmbientCovectorSpreading.finiteDegree a b 0 0 r.val
  let f := AmbientCovectorSpreading.finiteOriginalEquations (d := r.val) mu
    (0 : Fin 0 → Fin a → K) (0 : Fin 0 → Fin b → K)
  have heq (ell : Fin T → K) : (∀ i,aeval ell (f i).val=0) ↔
      r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) := by
    have h := AmbientCovectorSpreading.finite_original_equations_iff (d := r.val) mu
      (0 : Fin 0 → Fin a → K) (0 : Fin 0 → Fin b → K) (by omega) ell
    simpa only [f,aeval_eq_eval,Nat.add_zero,Fin.forall_fin_zero,true_and,and_true] using h
  let cuts : Fin (c+s) → (I → K) → Forms K T 1 :=
    Fin.addCases (fun i p => ClosedCovectorEquations.linearForm (A p i)) (fun i _ => Z i)
  have hcuts (i : Fin (c+s)) : IsPolynomialFamily (cuts i) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [cuts,Fin.addCases_left] using
        ClosedCovectorSpreading.linearForm_polynomial _ (hA j)
    · simpa only [cuts,Fin.addCases_right] using
        (isPolynomialFamily_const (Z j) : IsPolynomialFamily (fun _ : I → K => Z j))
  have hsplit (p : I → K) (ell : Fin T → K) :
      (∀ i,aeval ell (cuts i p).val=0) ↔
        (∀ i,covector ell (A p i)=0) ∧ (∀ i,aeval ell (Z i).val=0) := by
    constructor
    · intro h
      exact ⟨fun i => by simpa only [cuts,Fin.addCases_left,aeval_eq_eval,
        ClosedCovectorEquations.eval_linearForm] using h (Fin.castAdd s i),
        fun i => by simpa only [cuts,Fin.addCases_right] using h (Fin.natAdd c i)⟩
    · rintro ⟨hA,hZ⟩ i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [cuts,Fin.addCases_left,aeval_eq_eval,
          ClosedCovectorEquations.eval_linearForm] using hA j
      · simpa only [cuts,Fin.addCases_right] using hZ j
  obtain ⟨P,hP,hgood⟩ := principal_open_empty_slices (L := K) d (fun i _ => f i) cuts
    (fun _ => isPolynomialFamily_const _) hcuts p₀ (by
      intro ell hf hc
      have hc' := (hsplit p₀ ell).mp hc
      exact hempty ell ((heq ell).mp hf) hc'.1 hc'.2)
  exact ⟨P,hP,fun p hp ell hr hA hZ => hgood p hp ell
    ((heq ell).mpr hr) ((hsplit p ell).mpr ⟨hA,hZ⟩)⟩

theorem presentation_slices_principal_open
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (A : (I → K) → Fin c → Fin T → K)
    (hA : ∀ i k,IsPolynomialFamily (fun p => A p i k))
    (s : ℕ → ℕ) (Z : (r : Fin (a+1)) → Fin (s r.val) → Forms K T 1) (p₀ : I → K)
    (hempty : ∀ r (ell : Fin T → K),
      r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      (∀ i,covector ell (A p₀ i)=0) → (∀ i,aeval ell (Z r i).val=0) → ell=0) :
    ∃ P : MvPolynomial I K,eval p₀ P ≠ 0 ∧ ∀ p,eval p P ≠ 0 →
      ∀ r (ell : Fin T → K),
        r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
        (∀ i,covector ell (A p i)=0) → (∀ i,aeval ell (Z r i).val=0) → ell=0 := by
  classical
  have hx (r : Fin (a+1)) := presentation_threshold_principal_open mu A hA r (Z r) p₀ (hempty r)
  choose P hP hgood using hx
  refine ⟨∏ r,P r,by simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun r _ => hP r),?_⟩
  intro p hp r
  apply hgood r p
  have hall : ∀ r,eval p (P r) ≠ 0 := by
    simpa only [map_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const] using hp
  exact hall r

end Froberg
