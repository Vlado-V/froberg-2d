import Quartic.QuotientBilinearImage

/-! Exact source dimensions and image bounds for commuting surjective
linear maps. -/
noncomputable section
namespace Froberg.SurjectiveImage
open Module
variable {K F V V' W W' : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module K W]
  [AddCommGroup W'] [Module K W']

lemma image_eq_map (mu : F →ₗ[K] V →ₗ[K] W) (nu : F →ₗ[K] V' →ₗ[K] W')
    (p : V →ₗ[K] V') (q : W →ₗ[K] W') (hp : Function.Surjective p)
    (hc : ∀ f v,nu f (p v)=q (mu f v)) (L : Submodule K V') :
    Quartic.BilinearImage.image nu L =
      (Quartic.BilinearImage.image mu (L.comap p)).map q := by
  unfold Quartic.BilinearImage.image
  rw [Submodule.map_iSup]
  congr 1
  funext f
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,rfl⟩ := hp x
    exact ⟨mu f v,⟨v,hx,rfl⟩,(hc f v).symm⟩
  · rintro ⟨w,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨p v,hv,hc f v⟩

lemma finrank_map_add_ker [FiniteDimensional K V]
    (p : V →ₗ[K] V') (S : Submodule K V) (hk : LinearMap.ker p ≤ S) :
    finrank K (S.map p)+finrank K (LinearMap.ker p)=finrank K S := by
  have hn := (p.comp S.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.ker_comp,
    (Submodule.comapSubtypeEquivOfLe hk).finrank_eq] at hn
  exact hn

lemma finrank_preimage [FiniteDimensional K V]
    (p : V →ₗ[K] V') (hp : Function.Surjective p) (L : Submodule K V') :
    finrank K (L.comap p)=finrank K L+finrank K (LinearMap.ker p) := by
  have hk : LinearMap.ker p ≤ L.comap p := by
    intro v hv
    change p v ∈ L
    rw [LinearMap.mem_ker.mp hv]
    exact L.zero_mem
  have hn := finrank_map_add_ker p (L.comap p) hk
  rw [Submodule.map_comap_eq_of_surjective hp] at hn
  exact hn.symm

lemma finrank_le_map_add_ker [FiniteDimensional K V]
    (p : V →ₗ[K] V') (S : Submodule K V) :
    finrank K S ≤ finrank K (S.map p)+finrank K (LinearMap.ker p) := by
  let e : LinearMap.ker (p.comp S.subtype) →ₗ[K] LinearMap.ker p :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : Function.Injective e := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : LinearMap.ker p => x.val) hh
  have hdim := LinearMap.finrank_le_finrank_of_injective he
  have hn := (p.comp S.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp,Submodule.range_subtype] at hn
  omega

lemma image_finrank_le [FiniteDimensional K W]
    (mu : F →ₗ[K] V →ₗ[K] W) (nu : F →ₗ[K] V' →ₗ[K] W')
    (p : V →ₗ[K] V') (q : W →ₗ[K] W') (hp : Function.Surjective p)
    (hc : ∀ f v,nu f (p v)=q (mu f v)) (L : Submodule K V') :
    finrank K (Quartic.BilinearImage.image mu (L.comap p)) ≤
      finrank K (Quartic.BilinearImage.image nu L)+finrank K (LinearMap.ker q) := by
  rw [image_eq_map mu nu p q hp hc]
  exact finrank_le_map_add_ker q _

end Froberg.SurjectiveImage
