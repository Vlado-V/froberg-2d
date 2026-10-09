module

public import Froberg.IntrinsicProjectionOpen
public import Froberg.KernelCutoffOpen
public import Froberg.GenericDimensions

@[expose] public section

/-! One projection has both normalized image growth and a prescribed
surjective multiplication property of its kernel. The two conditions are
proved on nonempty opens in the same space of projection matrices. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic
variable {K F V W E T : Type*} [Field K] [Infinite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup T] [Module K T] [FiniteDimensional K T]

theorem exists_normalized_projection_with_cutoff {u b : ℕ}
    (ha : 0<finrank K V) (hW : finrank K W=u+b)
    (hmargin : finrank K V*finrank K V<u*b)
    (mu : F →ₗ[K] V →ₗ[K] W)
    (hmu : ∀ L : Submodule K V,
      finrank K W*finrank K L≤finrank K V*finrank K (BilinearImage.image mu L))
    (nu : E →ₗ[K] W →ₗ[K] T) (U : Submodule K W)
    (hU : finrank K U=u) (hcut : BilinearImage.image nu U=⊤) :
    ∃ P : W →ₗ[K] (Fin b → K),Function.Surjective P ∧ finrank K P.ker=u ∧
      (∀ L : Submodule K V,
        b*finrank K L≤finrank K V*finrank K ((BilinearImage.image mu L).map P)) ∧
      BilinearImage.image nu P.ker=⊤ := by
  have hdim : finrank K (W ⧸ U)=finrank K (Fin b → K) := by
    have hq := U.finrank_quotient_add_finrank
    simp only [Module.finrank_pi_fintype,finrank_self,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_one]
    omega
  let e : (W ⧸ U) ≃ₗ[K] (Fin b → K) := LinearEquiv.ofFinrankEq _ _ hdim
  let P₀ := e.toLinearMap.comp U.mkQ
  have hsurj : Function.Surjective P₀ := e.surjective.comp U.mkQ_surjective
  have hker : P₀.ker=U := by
    ext x
    change e (U.mkQ x)=0 ↔ x∈U
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero U
  obtain ⟨p₀,hp₀⟩ := coordinateProjection_surjective (K := K) (W := W) b P₀
  obtain ⟨D,hD,hgood⟩ := kernel_bilinear_surjective_open
    (coordinateProjection (K := K) (W := W) (b := b)) (coordinateProjection_polynomial b) p₀
    (by rwa [hp₀]) nu (by rwa [hp₀,hker])
  obtain ⟨G,hG,hgrowth⟩ := normalized_projection_principal_open ha hW hmargin mu hmu
  obtain ⟨p,hpD,hpG⟩ := principal_opens_intersect ⟨p₀,hD⟩ hG
  exact ⟨coordinateProjection p,(hgrowth p hpG).1,(hgrowth p hpG).2.1,
    (hgrowth p hpG).2.2,hgood p hpD⟩

end Froberg
