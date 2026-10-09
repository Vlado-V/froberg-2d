module

public import Froberg.BilinearProjection
public import Froberg.ProjectionCount

@[expose] public section

/-! A general projection preserves normalized bilinear-image growth.
This is the precise uniform projection observation used in C.3. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type*} [Field K] [Infinite K] {a B N b u : ℕ}

/-- Uniform normalized growth survives a general projection whenever the
explicit Schubert margin ub>a² is positive. -/
theorem normalized_projection_open (ha : 0 < a) (hN : N = u+b)
    (hmargin : a*a < u*b)
    (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin N → K))
    (hmu : ∀ L : Submodule K (Fin a → K),
      N * finrank K L ≤ a * finrank K (BilinearImage.image mu L)) :
    ∃ D : MvPolynomial (Fin (finrank K ((Fin N → K) →ₗ[K] (Fin b → K)))) K,
      (∃ x, eval x D ≠ 0) ∧
      ∀ x, eval x D ≠ 0 → ∀ L : Submodule K (Fin a → K),
        b * finrank K L ≤ a * finrank K ((BilinearImage.image mu L).map
          ((Module.finBasis K ((Fin N → K) →ₗ[K] (Fin b → K))).equivFun.symm x)) := by
  classical
  let C := Fin (a+1) × Fin (b+1) × Fin (N+1)
  let P (x : Fin (finrank K ((Fin N → K) →ₗ[K] (Fin b → K))) → K) :=
    (Module.finBasis K ((Fin N → K) →ₗ[K] (Fin b → K))).equivFun.symm x
  have hlocal (c : C) :
      ∃ D : MvPolynomial (Fin (finrank K ((Fin N → K) →ₗ[K] (Fin b → K)))) K,
        (∃ x, eval x D ≠ 0) ∧ ∀ x, eval x D ≠ 0 →
          c.1.val*(a-c.1.val)+c.2.1.val*(b-c.2.1.val) < c.2.2.val*(b-c.2.1.val) →
          ∀ L : Submodule K (Fin a → K), finrank K L=c.1.val →
            finrank K (BilinearImage.image mu L)=c.2.2.val →
            finrank K ((BilinearImage.image mu L).map (P x)) ≠ c.2.1.val := by
    by_cases hc : c.1.val*(a-c.1.val)+c.2.1.val*(b-c.2.1.val) < c.2.2.val*(b-c.2.1.val)
    · obtain ⟨D,hD,hgood⟩ := bilinear_projection_rank_open (b := b) mu hc
      exact ⟨D,hD,fun x hx _ L hL he => hgood x hx L hL (by omega)⟩
    · exact ⟨1,⟨0,by simp⟩,fun _ _ h => False.elim (hc h)⟩
  choose D hD hgood using hlocal
  have hnz (c : C) : D c ≠ 0 := by
    obtain ⟨x,hx⟩ := hD c
    intro h
    simp [h] at hx
  obtain ⟨x,hx⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ c, D c,⟨x,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun c _ => hx c)
  intro x hx L
  by_contra! hfail
  let ell := finrank K L
  let w := finrank K (BilinearImage.image mu L)
  let t := finrank K ((BilinearImage.image mu L).map (P x))
  have hla : ell ≤ a := by simpa [ell] using L.finrank_le
  have hwN : w ≤ N := by simpa [w] using (BilinearImage.image mu L).finrank_le
  have htb : t ≤ b := by simpa [t] using ((BilinearImage.image mu L).map (P x)).finrank_le
  have hl : 0 < ell := by change a*t < b*ell at hfail; nlinarith
  have hg : (u+b)*ell ≤ a*w := by simpa only [ell,w,← hN] using hmu L
  have hcount : ell*(a-ell)+t*(b-t) < w*(b-t) := by
    have hh := projection_failure_count_real
      (show (0 : ℝ)<a by exact_mod_cast ha)
      (show (0 : ℝ)≤u by positivity) (show (0 : ℝ)≤b by positivity)
      (show (0 : ℝ)<ell by exact_mod_cast hl)
      (show (ell : ℝ)≤a by exact_mod_cast hla)
      (show (0 : ℝ)≤t by positivity)
      (show ((u : ℝ)+b)*ell ≤ a*w by exact_mod_cast hg)
      (show (a : ℝ)*t < b*ell by exact_mod_cast hfail)
      (show (a : ℝ)*a < u*b by exact_mod_cast hmargin)
    have hc : ((ell*(a-ell)+t*(b-t) : ℕ) : ℝ) < (w*(b-t) : ℕ) := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hla,Nat.cast_sub htb] using hh
    exact_mod_cast hc
  let c : C := (⟨ell,by omega⟩,⟨t,by omega⟩,⟨w,by omega⟩)
  have hx' : eval x (D c) ≠ 0 := by
    have hh : ∏ c, eval x (D c) ≠ 0 := by simpa only [map_prod] using hx
    exact Finset.prod_ne_zero_iff.mp hh c (Finset.mem_univ _)
  exact hgood c x hx' hcount L rfl rfl rfl

end Froberg
