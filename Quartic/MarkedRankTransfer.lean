module

public import Quartic.DeformationRank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! A rank gain for the multiplication map with one additional fixed column
simultaneously proves maximal unaugmented rank and survival of that column
in the quotient. The additional source coordinate is constant in the pencil. -/
noncomputable section
namespace Quartic.MarkedRankTransfer
open Module MvPolynomial
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def augmented (M : V →ₗ[K] W) (z : W) : (V × K) →ₗ[K] W :=
  M.coprod (LinearMap.toSpanSingleton K W z)

@[simp] theorem augmented_apply (M : V →ₗ[K] W) (z : W) (v : V) (a : K) :
    augmented M z (v,a)=M v+a • z := rfl

theorem augmented_range (M : V →ₗ[K] W) (z : W) :
    (augmented M z).range=M.range ⊔ Submodule.span K {z} := by
  rw [augmented,LinearMap.range_coprod,LinearMap.range_toSpanSingleton]

theorem augmented_range_of_mem (M : V →ₗ[K] W) {z : W} (hz : z∈M.range) :
    (augmented M z).range=M.range := by
  rw [augmented_range]
  exact sup_eq_left.mpr (Submodule.span_le.mpr (by
    intro y hy
    rcases hy with rfl
    exact hz))

theorem rank_and_survival [FiniteDimensional K W] (M : V →ₗ[K] W) (z : W)
    (r : ℕ) (hupper : finrank K M.range≤r)
    (haug : r+1≤finrank K (augmented M z).range) :
    finrank K M.range=r ∧ z∉M.range ∧ finrank K (augmented M z).range=r+1 := by
  have hz : z∉M.range := by
    intro hz
    rw [augmented_range_of_mem M hz] at haug
    omega
  have heq : finrank K (augmented M z).range=finrank K M.range+1 := by
    rw [augmented_range,Submodule.finrank_sup_span_singleton hz]
  exact ⟨by omega,hz,by omega⟩

def perturbation (M₁ : V →ₗ[K] W) : (V × K) →ₗ[K] W :=
  M₁.comp (LinearMap.fst K V K)

@[simp] theorem perturbation_apply (M₁ : V →ₗ[K] W) (v : V) (a : K) :
    perturbation M₁ (v,a)=M₁ v := rfl

theorem pencil_eq (M₀ M₁ : V →ₗ[K] W) (z : W) (ε : K) :
    augmented (M₀+ε • M₁) z=augmented M₀ z+ε • perturbation M₁ := by
  apply LinearMap.ext
  rintro ⟨v,a⟩
  simp only [augmented_apply,LinearMap.add_apply,LinearMap.smul_apply,perturbation_apply]
  abel

/-- The added fixed column supplies precisely the extra split-kernel vector. -/
def extraCycle (M₀ : V →ₗ[K] W) (z : W) (b : V) (hb : M₀ b=z) :
    (augmented M₀ z).ker :=
  ⟨(b,-1),by change M₀ b+(-1 : K) • z=0; simp [hb]⟩

@[simp] theorem extra_first_response (M₀ M₁ : V →ₗ[K] W) (z : W)
    (b : V) (hb : M₀ b=z) :
    perturbation M₁ (extraCycle M₀ z b hb).val=M₁ b := rfl

theorem extra_pencil_response (M₀ M₁ : V →ₗ[K] W) (z : W)
    (b : V) (hb : M₀ b=z) (ε : K) :
    augmented (M₀+ε • M₁) z (extraCycle M₀ z b hb).val=ε • M₁ b := by
  rw [pencil_eq]
  exact deformation_first_response (augmented M₀ z) (perturbation M₁) ε
    (extraCycle M₀ z b hb).val (extraCycle M₀ z b hb).property

section Deformation
variable {J T : Type*} [Infinite K] [FiniteDimensional K V] [FiniteDimensional K W]
  [AddCommGroup J] [Module K J] [FiniteDimensional K J]
  [AddCommGroup T] [Module K T]

omit [Infinite K] [FiniteDimensional K V] [FiniteDimensional K W] [FiniteDimensional K J] in
theorem projection_annihilates (M₀ : V →ₗ[K] W) (z : W) (hz : z∈M₀.range)
    (π : W →ₗ[K] J) (hπ : π.comp M₀=0) : π.comp (augmented M₀ z)=0 := by
  obtain ⟨b,hb⟩ := hz
  have hzero : π z=0 := by rw [←hb]; exact LinearMap.congr_fun hπ b
  apply LinearMap.ext
  rintro ⟨v,a⟩
  change π (M₀ v+a • z)=0
  rw [map_add,map_smul,hzero,smul_zero,add_zero]
  exact LinearMap.congr_fun hπ v

/-- Exact corrected columns of the augmented pencil yield a common principal
open on which the original map has its prescribed rank and the marked column
survives. The rank premise is only the usual a priori upper bound. -/
theorem marked_principal_open_of_realizations
    (M₀ M₁ : V →ₗ[K] W) (z : W) (hz : z∈M₀.range)
    (π : W →ₗ[K] J) (N : T →ₗ[K] J) (hπ : π.comp M₀=0)
    (hreal : ∀ ξ : T,∃ a b : V × K,
      augmented M₀ z a=0 ∧ augmented M₀ z b= -perturbation M₁ a ∧
        π (perturbation M₁ b)=N ξ)
    (r : ℕ) (hcount : r+1≤finrank K M₀.range+finrank K N.range)
    (hupper : ∀ ε : K,ε≠0 → finrank K (M₀+ε • M₁).range≤r) :
    ∃ D : MvPolynomial (Fin 1) K,eval 0 D≠0 ∧
      ∀ ε : K,ε≠0 → eval (fun _ => ε) D≠0 →
        finrank K (M₀+ε • M₁).range=r ∧ z∉(M₀+ε • M₁).range := by
  obtain ⟨D,hD,hgain⟩ := DeformationRank.rank_gain_of_realizations_principal_open
    (augmented M₀ z) (perturbation M₁) π N (projection_annihilates M₀ z hz π hπ) hreal
  refine ⟨D,hD,?_⟩
  intro ε hε hDε
  have hg := hgain ε hε hDε
  rw [augmented_range_of_mem M₀ hz,←pencil_eq] at hg
  have h := rank_and_survival (M₀+ε • M₁) z r (hupper ε hε) (hcount.trans hg)
  exact ⟨h.1,h.2.1⟩

end Deformation
end Quartic.MarkedRankTransfer
