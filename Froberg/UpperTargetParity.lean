module

public import Froberg.OddBottomDetection
public import Froberg.OddBackgroundBottomDetection
public import Froberg.PureScalarCoordinates
public import Froberg.PreparedLayerTargets
public import Froberg.SupportedTargetDeletion

@[expose] public section

/-! The upper-target condition fills the even endpoint after deleting
only a complementary subspace of the old pure-scalar target. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {h m d r : ℕ}

theorem lowTarget_even_weight_zero (p : Forms K (h+m) (2*d))
    (hp : p∈lowTargetSubspace (K := K) (h := h) (m := m) (d := d)) :
    (parityForm (coreParity h m) 0 p).val.IsWeightedHomogeneous (coreWeight h m) 0 := by
  intro a ha
  have hcoeff : p.val.coeff a≠0 := by
    intro hz
    apply ha
    simp only [parityForm_val,coeff_weightedHomogeneousComponent,hz,ite_self]
  have hpar : Finsupp.weight (coreWeight h m) a%2=0 :=
    (parity_homogeneous_iff (coreWeight h m) _ 0 (by decide)).mp
      (parityForm_homogeneous (coreParity h m) 0 p) a ha
  have hdeg : a.degree=2*d := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using p.property hcoeff
  have hbound : Finsupp.weight (coreWeight h m) a≤2*d := by
    simpa only [hdeg] using weight_le_degree (coreWeight h m) coreWeight_le_one a
  by_contra hn
  have hge : 2≤Finsupp.weight (coreWeight h m) a := by omega
  have hz := (mem_lowTargetSubspace p).mp hp _ hge hbound
  have hc := congrArg (fun f : Poly K (h+m) => f.coeff a) hz
  change (weightedHomogeneousComponent (coreWeight h m)
    (Finsupp.weight (coreWeight h m) a) p.val).coeff a=0 at hc
  simp only [coeff_weightedHomogeneousComponent,ite_true] at hc
  exact hcoeff hc

theorem upperTarget_even_coverage
    (e : Fin r → ZMod 2) (q : Fin r → Forms K (h+m) d)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous (coreParity h m) (e i))
    (hupper : Function.Surjective (upperTargetMap q))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hscalar : ∀ p : Forms K (h+m) (2*d),
      p.val.IsWeightedHomogeneous (coreWeight h m) 0 →
        p∈D ⊔ (endpointMultiplication q).range) :
    ∀ p,parityForm (coreParity h m) 0 p∈D ⊔ (endpointMultiplication q).range := by
  intro p
  obtain ⟨v,hpv,hv⟩ := upperTargetMap_surjective_representative q hupper p
  have hm : p-v∈(endpointMultiplication q).range := by
    rw [range_endpointMultiplication]
    exact hpv
  obtain ⟨c,hc⟩ := hm
  have hzero := hscalar (parityForm (coreParity h m) 0 v)
    (lowTarget_even_weight_zero v ((mem_lowTargetSubspace v).mpr hv))
  have hprod : parityForm (coreParity h m) 0 (p-v)∈(endpointMultiplication q).range := by
    refine ⟨paritySource (coreParity h m) e 0 c,?_⟩
    rw [endpointMultiplication_paritySource _ _ _ hq,hc]
  have hh := (D ⊔ (endpointMultiplication q).range).add_mem hzero ((show (endpointMultiplication q).range≤D ⊔ (endpointMultiplication q).range from le_sup_right) hprod)
  rw [map_sub] at hh
  have he : parityForm (coreParity h m) 0 v +
      (parityForm (coreParity h m) 0 p-parityForm (coreParity h m) 0 v)=
        parityForm (coreParity h m) 0 p := by abel
  rwa [he] at hh

variable [Infinite K]

theorem core_weight_zero_mem_scalar_range {k : ℕ} (p : Forms K (h+m) k)
    (hp : p.val.IsWeightedHomogeneous (coreWeight h m) 0) :
    p∈(renameForm (K := K) (d := k) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  let v := rename (finSumFinEquiv.symm : Fin (h+m) → Fin h ⊕ Fin m) p.val
  have hv : v.IsWeightedHomogeneous (blockWeight h m) 0 := by
    apply weighted_homogeneous_rename finSumFinEquiv.symm.toEmbedding (blockWeight h m) p.val 0
    change p.val.IsWeightedHomogeneous (blockWeight h m ∘ finSumFinEquiv.symm) 0
    rw [←coreWeight_eq_blockWeight]
    exact hp
  obtain ⟨b,hb⟩ := homogeneous_output_zero_exists p.property.rename_isHomogeneous hv
  refine ⟨b,Subtype.ext ?_⟩
  have hh := congrArg (rename (finSumFinEquiv : Fin h ⊕ Fin m → Fin (h+m))) hb
  simp only [rename_rename,Function.comp_def,Equiv.apply_symm_apply] at hh
  change rename (Fin.natAdd h) b.val=rename id p.val at hh
  change rename (Fin.natAdd h) b.val=p.val
  simpa only [rename_id,AlgHom.id_apply] using hh

theorem scalar_range_odd_zero {k : ℕ}
    (p : Forms K (h+m) k)
    (hp : p∈(renameForm (K := K) (d := k) (Fin.natAdd h : Fin m → Fin (h+m))).range) :
    parityForm (coreParity h m) 1 p=0 := by
  obtain ⟨b,rfl⟩ := hp
  apply parityForm_other (coreParity h m) 1 0 _ _ (by decide)
  exact weighted_homogeneous_has_parity (coreWeight h m) _ (scalar_rename_core_weight_zero b)

/-- The exact supported deletion used by transfer automatically has no odd
part and fills every pure scalar target modulo the embedded old products. -/
theorem supported_scalar_deletion_properties {s : ℕ}
    (Q : Fin s → Forms K m d) (q : Fin r → Forms K (h+m) d)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hfill : (renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range.map D.mkQ=
      ((endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))).map D.mkQ)
    (hold : (endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))≤
      (endpointMultiplication q).range) :
    D≤(parityForm (coreParity h m) 1).ker ∧
      ∀ p : Forms K (h+m) (2*d),p.val.IsWeightedHomogeneous (coreWeight h m) 0 →
        p∈D ⊔ (endpointMultiplication q).range := by
  refine ⟨fun p hp => scalar_range_odd_zero p (hD hp),?_⟩
  intro p hp
  have hh : D.mkQ p∈((endpointMultiplication Q).range.map (renameForm (Fin.natAdd h))).map D.mkQ := by
    rw [←hfill]
    exact ⟨p,core_weight_zero_mem_scalar_range p hp,rfl⟩
  obtain ⟨b,hb,he⟩ := hh
  have hdiff : p-b∈D := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change D.mkQ (p-b)=0
    rw [map_sub,he,sub_self]
  have hh := Submodule.add_mem_sup hdiff (hold hb)
  simpa only [sub_add_cancel] using hh

end Froberg
