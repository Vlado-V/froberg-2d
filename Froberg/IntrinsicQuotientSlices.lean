import Froberg.IntrinsicKernelAvoidance
import Froberg.QuotientSliceVectors

/-! Common scalar parameters for all positive kernel thresholds, followed
by descent to the actual target quotient. The zero threshold uses a basis
of that quotient and its actual dimension bound. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily QuotientCovectorKernel
variable {K P V W W₀ : Type} [Field K] [Infinite K]
  [AddCommGroup P] [Module K P] [FiniteDimensional K P]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W₀] [Module K W₀]
variable {q s : ℕ}

theorem exists_detecting_vectors {X : Type} [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] (hs : finrank K X ≤ s) :
    ∃ Z : Fin s → X,∀ ell : X →ₗ[K] K,(∀ i,ell (Z i)=0) → ell=0 := by
  classical
  let Z : Fin s → X := fun i => if hi : i.val<finrank K X then
    (Module.finBasis K X) ⟨i.val,hi⟩ else 0
  refine ⟨Z,?_⟩
  intro ell hell
  apply (Module.finBasis K X).ext
  intro i
  have hz := hell (i.castLE hs)
  simpa only [Z,Fin.coe_castLE,dif_pos i.isLt,LinearMap.zero_apply] using hz

theorem kernel_avoidance_quotient_slices
    (mu : P →ₗ[K] V →ₗ[K] W) (B : Fin q → V →ₗ[K] W)
    (bottom : (W →ₗ[K] K) →ₗ[K] (W₀ →ₗ[K] K))
    (A : (Fin q → P) → Submodule K W)
    (hA : ∀ Q i v,mu (Q i) v+B i v∈A Q)
    (slices : ℕ → ℕ)
    (E : MvPolynomial (Fin (finrank K (Fin q → P))) K)
    (hE : ∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) E≠0)
    (hdim : ∀ Q,eval ((Module.finBasis K _).equivFun Q) E≠0 →
      finrank K (W ⧸ A Q) ≤ slices 0)
    (hbottom : ∀ Q,eval ((Module.finBasis K _).equivFun Q) E≠0 →
      ∀ ell : W →ₗ[K] K,A Q ≤ ell.ker → bottom ell=0 → ell=0)
    (havoid : ∀ r : Fin (finrank K V+1),0<r.val →
      ∃ Z : Fin (slices r.val) → W,
      ∃ D : MvPolynomial (Fin (finrank K (Fin q → P))) K,
        (∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) D≠0) ∧
        ∀ Q,eval ((Module.finBasis K _).equivFun Q) D≠0 →
        ∀ ell : W →ₗ[K] K,bottom ell≠0 →
          r.val ≤ finrank K (relation mu ell).ker →
          ¬ ((∀ i v,ell (mu (Q i) v+B i v)=0) ∧ (∀ j,ell (Z j)=0))) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin q → P))) K,
      (∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) D≠0) ∧
      ∀ Q,eval ((Module.finBasis K _).equivFun Q) D≠0 →
        eval ((Module.finBasis K _).equivFun Q) E≠0 ∧
        HasClosedKernelSlices (targetPostcompose mu (A Q).mkQ) slices := by
  classical
  have hprofile (r : Fin (finrank K V+1)) :
      ∃ Z : Fin (slices r.val) → W,
      ∃ D : MvPolynomial (Fin (finrank K (Fin q → P))) K,
        (∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) D≠0) ∧
        ∀ Q,eval ((Module.finBasis K _).equivFun Q) D≠0 → 0<r.val →
        ∀ ell : W →ₗ[K] K,bottom ell≠0 →
          r.val ≤ finrank K (relation mu ell).ker →
          ¬ ((∀ i v,ell (mu (Q i) v+B i v)=0) ∧ (∀ j,ell (Z j)=0)) := by
    by_cases hr : 0<r.val
    · obtain ⟨Z,D,hD,hgood⟩ := havoid r hr
      exact ⟨Z,D,hD,fun Q hQ _ => hgood Q hQ⟩
    · exact ⟨0,1,⟨0,by simp⟩,fun _ _ h => (hr h).elim⟩
  choose Z D hD hgood using hprofile
  have hDn (r : Fin (finrank K V+1)) : D r≠0 := by
    obtain ⟨Q,hQ⟩ := hD r
    intro hz
    exact hQ (by rw [hz,map_zero])
  have hEn : E≠0 := by
    obtain ⟨Q,hQ⟩ := hE
    intro hz
    exact hQ (by rw [hz,map_zero])
  let T := E*∏ r,D r
  have hTn : T≠0 := mul_ne_zero hEn (Finset.prod_ne_zero_iff.mpr (fun r _ => hDn r))
  have hT : ∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) T≠0 := by
    by_contra hh
    push Not at hh
    apply hTn
    apply MvPolynomial.funext
    intro x
    have hx := hh ((Module.finBasis K (Fin q → P)).equivFun.symm x)
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using hx
  refine ⟨T,hT,?_⟩
  intro Q hQ
  have hQT : eval ((Module.finBasis K _).equivFun Q) E≠0 ∧
      eval ((Module.finBasis K _).equivFun Q) (∏ r,D r)≠0 := by
    simpa only [T,map_mul,mul_ne_zero_iff] using hQ
  refine ⟨hQT.1,?_⟩
  have hex (r : Fin (finrank K V+1)) :
      ∃ Y : Fin (slices r.val) → (W ⧸ A Q),∀ ell : (W ⧸ A Q) →ₗ[K] K,
        r.val ≤ finrank K (relation (targetPostcompose mu (A Q).mkQ) ell).ker →
        (∀ j,ell (Y j)=0) → ell=0 := by
    by_cases hr : r.val=0
    · obtain ⟨Y,hY⟩ := exists_detecting_vectors (K := K) (X := W ⧸ A Q)
        (show finrank K (W ⧸ A Q) ≤ slices r.val by rw [hr];exact hdim Q hQT.1)
      exact ⟨Y,fun ell _ => hY ell⟩
    · refine ⟨fun j => (A Q).mkQ (Z r j),?_⟩
      intro ell hk hcuts
      let lam := ell.comp (A Q).mkQ
      have hker : A Q ≤ lam.ker := by
        intro w hw
        change ell ((A Q).mkQ w)=0
        rw [show (A Q).mkQ w=0 from (Submodule.Quotient.mk_eq_zero (A Q)).mpr hw,map_zero]
      have hlam : lam=0 := by
        by_cases hb : bottom lam=0
        · exact hbottom Q hQT.1 lam hker hb
        · have hDr : eval ((Module.finBasis K _).equivFun Q) (D r)≠0 := by
            rw [map_prod] at hQT
            exact Finset.prod_ne_zero_iff.mp hQT.2 r (Finset.mem_univ _)
          apply (hgood r Q hDr (by omega) lam hb ?_ ⟨?_,hcuts⟩).elim
          · rwa [relation_targetPostcompose] at hk
          · intro i v
            exact hker (hA Q i v)
      apply LinearMap.ext
      intro w
      obtain ⟨v,rfl⟩ := (A Q).mkQ_surjective w
      exact LinearMap.congr_fun hlam v
  choose Y hY using hex
  exact (hasClosedKernelSlices_iff_vectors _ _).mpr ⟨Y,hY⟩

end Froberg
