import Froberg.OuterMultiplication
import Froberg.SurjectiveImage

/-! Exact ambient interpretation of expansion for attached polynomial quotients. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module MvPolynomial
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] {n s d : ℕ}

lemma image_relationSpace (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s) :
    Quartic.BilinearImage.image (vectorMultiply (d := d)) (relationSpace (d := 0) e v he) =
      relationSpace (d := d) e v he := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro f
    rintro _ ⟨p,hp,rfl⟩
    exact vectorMultiply_relation e v he f p hp
  · rintro _ ⟨a,rfl⟩
    let g : I → J → Forms K n s := fun i j =>
      ⟨monomial (e i) (v i j),isHomogeneous_monomial _ (he i)⟩
    have hg (i : I) : g i ∈ relationSpace (d := 0) e v he := by
      let one : Forms K n 0 := ⟨monomial 0 1,isHomogeneous_monomial _ (by simp)⟩
      refine ⟨Pi.single i one,?_⟩
      funext j
      apply Subtype.ext
      simp [homogeneousMultiplication_val,multiplication,Pi.single_apply,g,one,apply_ite]
    have heq : homogeneousMultiplication e v he a = ∑ i,vectorMultiply (a i) (g i) := by
      funext j
      apply Subtype.ext
      simp only [homogeneousMultiplication_val,multiplication_apply,Finset.sum_apply,
        Submodule.coe_sum,vectorMultiply_val,g]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [heq]
    exact Submodule.sum_mem _ (fun i _ => Quartic.BilinearImage.product_mem _ _ _ _ (hg i))

lemma image_quotient_finrank_add (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s)
    (L : Submodule K ((J → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    finrank K (Quartic.BilinearImage.image (quotientMultiply (d := d) e v he) L)+
      finrank K (relationSpace (d := d) e v he) =
    finrank K (Quartic.BilinearImage.image (vectorMultiply (d := d))
      (L.comap (relationSpace (d := 0) e v he).mkQ)) := by
  rw [Quartic.QuotientBilinearImage.image_eq_map (vectorMultiply (d := d))
    (relationSpace (d := 0) e v he) (relationSpace (d := d) e v he)
    (quotientMultiply e v he) (quotientMultiply_mk e v he)]
  apply Quartic.QuotientBilinearImage.finrank_map_mkQ_add
  rw [← image_relationSpace e v he]
  exact Quartic.QuotientBilinearImage.image_mono _
    (Quartic.QuotientBilinearImage.le_preimage _ L)

lemma expansion_iff_ambient (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s) (ell q : ℕ) :
    (∀ L : Submodule K ((J → Forms K n s) ⧸ relationSpace (d := 0) e v he),
      finrank K L=ell → q ≤ finrank K (Quartic.BilinearImage.image (quotientMultiply (d := d) e v he) L)) ↔
    (∀ S : Submodule K (J → Forms K n s),relationSpace (d := 0) e v he ≤ S →
      finrank K S=ell+finrank K (relationSpace (d := 0) e v he) →
      q+finrank K (relationSpace (d := d) e v he) ≤
        finrank K (Quartic.BilinearImage.image (vectorMultiply (d := d)) S)) := by
  constructor
  · intro hb S hES hS
    let E := relationSpace (d := 0) e v he
    let L := S.map E.mkQ
    have hL : finrank K L=ell := by
      have hd := Quartic.QuotientBilinearImage.finrank_map_mkQ_add E S hES
      dsimp only [E] at hd
      change finrank K (S.map E.mkQ)=ell
      exact Nat.add_right_cancel (hd.trans hS)
    have hback : L.comap E.mkQ=S := by
      rw [Submodule.comap_map_mkQ,sup_eq_right.mpr hES]
    have hi := image_quotient_finrank_add (d := d) e v he L
    rw [hback] at hi
    exact hi ▸ Nat.add_le_add_right (hb L hL) _
  · intro hb L hL
    have hd := Quartic.QuotientBilinearImage.finrank_preimage (relationSpace (d := 0) e v he) L
    erw [hL] at hd
    have hh := hb _ (Quartic.QuotientBilinearImage.le_preimage _ L) hd
    have hi := image_quotient_finrank_add (d := d) e v he L
    exact Nat.le_of_add_le_add_right (hh.trans_eq hi.symm)

end Froberg.AttachedMultiplication
