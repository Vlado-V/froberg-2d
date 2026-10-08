import Froberg.AllTargetElimination
import Froberg.Koszul
import Froberg.SurjectiveParameterOpen

/-! The simultaneous high-target conclusion is an ordinary rank-open
condition on the full generator family, in a fixed quotient of actual forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type} [Field K] {h m d r : ℕ}

def lowTargetSubspace : Submodule K (Forms K (h+m) (2*d)) :=
  ⨅ (b : ℕ) (_ : 2≤b) (_ : b≤2*d),
    ((coreComponent h m b).comp (Forms K (h+m) (2*d)).subtype).ker

@[simp] theorem mem_lowTargetSubspace (p : Forms K (h+m) (2*d)) :
    p∈lowTargetSubspace (K := K) (h := h) (m := m) (d := d) ↔
      ∀ b,2≤b → b≤2*d → coreComponent h m b p.val=0 := by
  simp only [lowTargetSubspace,Submodule.mem_iInf,LinearMap.mem_ker,
    LinearMap.comp_apply,Submodule.subtype_apply]

def upperTargetMap (q : Fin r → Forms K (h+m) d) :
    (Fin r → Forms K (h+m) d) →ₗ[K]
      (Forms K (h+m) (2*d)) ⧸ lowTargetSubspace (K := K) (h := h) (m := m) (d := d) :=
  (lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ.comp (endpointMultiplication q)

theorem upperTargetMap_surjective_of_lifts (q : Fin r → Forms K (h+m) d)
    (hd : 0<d)
    (hlift : ∀ b,2≤b → b≤2*d →
      TargetLift ((Submodule.span K (Set.range (fun i => (q i).val)))*Forms K (h+m) d) d b) :
    Function.Surjective (upperTargetMap q) := by
  intro z
  obtain ⟨p,rfl⟩ := (lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ_surjective z
  obtain ⟨v,hv,hvlow⟩ := all_target_lifts_eliminate _ hd hlift p
  have hm : p-v∈(endpointMultiplication q).range := by
    rw [range_endpointMultiplication]
    exact hv
  obtain ⟨c,hc⟩ := hm
  refine ⟨c,?_⟩
  change (lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ (endpointMultiplication q c)=(lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ p
  have hz : (lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ v=0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ((mem_lowTargetSubspace v).mpr hvlow)
  rw [hc,map_sub,hz,sub_zero]

theorem upperTargetMap_surjective_representative (q : Fin r → Forms K (h+m) d)
    (hq : Function.Surjective (upperTargetMap q)) (p : Forms K (h+m) (2*d)) :
    ∃ v : Forms K (h+m) (2*d),
      p.val-v.val∈(Submodule.span K (Set.range (fun i => (q i).val)))*Forms K (h+m) d ∧
      ∀ b,2≤b → b≤2*d → coreComponent h m b v.val=0 := by
  obtain ⟨c,hc⟩ := hq ((lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ p)
  refine ⟨p-endpointMultiplication q c,?_,?_⟩
  · have hm : endpointMultiplication q c∈(endpointMultiplication q).range := ⟨c,rfl⟩
    rw [range_endpointMultiplication] at hm
    change (endpointMultiplication q c).val∈(Submodule.span K (Set.range (fun i => (q i).val)))*Forms K (h+m) d at hm
    simpa only [Submodule.coe_sub,sub_sub_cancel] using hm
  · apply (mem_lowTargetSubspace _).mp
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ (p-endpointMultiplication q c)=0
    change (lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ (endpointMultiplication q c)=(lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ p at hc
    rw [map_sub,hc,sub_self]

/-- A covector annihilating the actual product row is determined by its two
bottom X-degree components. -/
theorem upperTargetMap_annihilator (q : Fin r → Forms K (h+m) d)
    (hq : Function.Surjective (upperTargetMap q))
    (ell : Forms K (h+m) (2*d) →ₗ[K] K)
    (hproducts : ∀ c,ell (endpointMultiplication q c)=0)
    (hlow : ∀ p,p∈lowTargetSubspace (K := K) (h := h) (m := m) (d := d) → ell p=0) : ell=0 := by
  apply LinearMap.ext
  intro p
  obtain ⟨v,hpv,hv⟩ := upperTargetMap_surjective_representative q hq p
  have hm : p-v∈(endpointMultiplication q).range := by
    rw [range_endpointMultiplication]
    exact hpv
  obtain ⟨c,hc⟩ := hm
  have he : ell (p-v)=0 := by rw [←hc];exact hproducts c
  rw [map_sub,hlow v ((mem_lowTargetSubspace v).mpr hv),sub_zero] at he
  exact he

def endpointMultiplicationOperator : (Fin r → Forms K (h+m) d) →ₗ[K]
    ((Fin r → Forms K (h+m) d) →ₗ[K] Forms K (h+m) (2*d)) where
  toFun := endpointMultiplication
  map_add' q q' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    simp only [endpointMultiplication_val,Pi.add_apply,Submodule.coe_add,
      add_mul,Finset.sum_add_distrib,LinearMap.add_apply]
  map_smul' a q := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    simp only [endpointMultiplication_val,Pi.smul_apply,Submodule.coe_smul,
      smul_mul_assoc,Finset.smul_sum,LinearMap.smul_apply,RingHom.id_apply]

/-- One successful prepared family yields a nonempty principal open on the
full parameter space where every high target is generated simultaneously. -/
theorem upperTarget_principal_open [Infinite K] {P : Type*}
    (q : (P → K) → Fin r → Forms K (h+m) d) (hpoly : IsPolynomialFamily q)
    (a₀ : P → K) (hq : Function.Surjective (upperTargetMap (q a₀))) :
    ∃ D : MvPolynomial P K,eval a₀ D≠0 ∧
      ∀ a,eval a D≠0 → Function.Surjective (upperTargetMap (q a)) := by
  apply surjective_polynomial_principal_open (fun a => upperTargetMap (q a)) _ a₀ hq
  let post : ((Fin r → Forms K (h+m) d) →ₗ[K] Forms K (h+m) (2*d)) →ₗ[K]
      ((Fin r → Forms K (h+m) d) →ₗ[K]
        (Forms K (h+m) (2*d)) ⧸ lowTargetSubspace (K := K) (h := h) (m := m) (d := d)) :=
    LinearMap.llcomp K _ _ _ (lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ
  intro ell
  exact hpoly (ell.comp (post.comp endpointMultiplicationOperator))

end Froberg
