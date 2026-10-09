module

public import Froberg.ActualThinSlices

@[expose] public section

/-! Actual quotient covectors and slices after scalar multiplication. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module Quartic QuotientCovectorKernel
variable {K F V W W' : Type*} [Field K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W'] [Module K W']
variable {q : ℕ}

def targetPostcompose (mu : F →ₗ[K] V →ₗ[K] W) (p : W →ₗ[K] W') :
    F →ₗ[K] V →ₗ[K] W' where
  toFun f := p.comp (mu f)
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

@[simp] lemma targetPostcompose_apply (mu : F →ₗ[K] V →ₗ[K] W)
    (p : W →ₗ[K] W') (f : F) (v : V) : targetPostcompose mu p f v=p (mu f v) := rfl

lemma relation_targetPostcompose (mu : F →ₗ[K] V →ₗ[K] W)
    (p : W →ₗ[K] W') (ell : W' →ₗ[K] K) :
    relation (targetPostcompose mu p) ell=relation mu (ell.comp p) := by
  ext v f
  rfl

abbrev ScalarQuotient (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F) :=
  W ⧸ (multiplication mu Q).range

def scalarQuotientBilinear (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F) :
    F →ₗ[K] V →ₗ[K] ScalarQuotient mu Q :=
  targetPostcompose mu (multiplication mu Q).range.mkQ

lemma scalar_product_mem_range (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F)
    (i : Fin q) (v : V) : mu (Q i) v ∈ (multiplication mu Q).range := by
  classical
  refine ⟨Pi.single i v,?_⟩
  simp [multiplication_apply,Pi.single_apply,apply_ite]

lemma scalarQuotient_product_zero (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F)
    (i : Fin q) (v : V) : scalarQuotientBilinear mu Q (Q i) v=0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr (scalar_product_mem_range mu Q i v)

theorem transport_scalar_quotient_slices (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F)
    (s : ℕ → ℕ) (Z : (r : Fin (finrank K V+1)) → Fin (s r.val) → W)
    (hZ : ∀ r : Fin (finrank K V+1),∀ ell : W →ₗ[K] K,
      r.val ≤ finrank K (LinearMap.ker (relation mu ell)) →
      (∀ i v,ell (mu (Q i) v)=0) → (∀ t,ell (Z r t)=0) → ell=0) :
    ∀ r : Fin (finrank K V+1),∀ ell : ScalarQuotient mu Q →ₗ[K] K,
      r.val ≤ finrank K (LinearMap.ker (relation (scalarQuotientBilinear mu Q) ell)) →
      (∀ t,ell ((multiplication mu Q).range.mkQ (Z r t))=0) → ell=0 := by
  intro r ell hr hcuts
  have hzero : ell.comp (multiplication mu Q).range.mkQ=0 := by
    apply hZ r
    · change r.val ≤ finrank K (LinearMap.ker (relation
        (targetPostcompose mu (multiplication mu Q).range.mkQ) ell)) at hr
      rw [relation_targetPostcompose] at hr
      exact hr
    · intro i v
      change ell (scalarQuotientBilinear mu Q (Q i) v)=0
      rw [scalarQuotient_product_zero,map_zero]
    · exact hcuts
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := (multiplication mu Q).range.mkQ_surjective w
  exact DFunLike.congr_fun hzero v

end Froberg.BilinearScalarFamily
