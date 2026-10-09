module

public import Froberg.EvenRestorationSpace
public import Froberg.ParityWeights
public import Froberg.WeightedRename

@[expose] public section

/-! Natural-weight restoration is independent of the finite names chosen
for variables; the positive projection detects precisely weight zero. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K : Type} [Field K] {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem weightedParity_rename_equiv (e : σ ≃ τ) (w : σ → ℕ)
    (f : MvPolynomial σ K) (hf : f∈weightedParitySpace w 0) :
    rename e f∈weightedParitySpace (w ∘ e.symm) 0 := by
  apply (mem_weightedParitySpace_iff _ _ _).mpr
  apply (parity_homogeneous_iff _ _ 0 (by omega)).mp
  apply weighted_homogeneous_rename e.toEmbedding _ f 0
  have hh := (parity_homogeneous_iff w f 0 (by omega)).mpr
    ((mem_weightedParitySpace_iff _ _ _).mp hf)
  simpa only [Function.comp_def,Equiv.coe_toEmbedding,Equiv.symm_apply_apply,Nat.cast_zero] using hh

def evenRestorationRenameEquiv (e : σ ≃ τ) (w : σ → ℕ) (d : ℕ) :
    evenRestorationSpace (K := K) w d ≃ₗ[K]
      evenRestorationSpace (K := K) (w ∘ e.symm) d where
  toFun f := ⟨rename e f.val,f.property.1.rename_isHomogeneous,
    weightedParity_rename_equiv e w f.val f.property.2⟩
  invFun f := ⟨rename e.symm f.val,f.property.1.rename_isHomogeneous,by
    change rename e.symm f.val∈weightedParitySpace w 0
    have hh := weightedParity_rename_equiv e.symm (w ∘ e.symm) f.val f.property.2
    simpa only [Equiv.symm_symm,Function.comp_def,Equiv.symm_apply_apply] using hh⟩
  left_inv f := Subtype.ext ((renameEquiv K e).left_inv f.val)
  right_inv f := Subtype.ext ((renameEquiv K e).right_inv f.val)
  map_add' f g := Subtype.ext (map_add (rename e) f.val g.val)
  map_smul' a f := Subtype.ext (map_smul (rename e) a f.val)

theorem positiveWeightProjection_eq_zero_iff {d : ℕ}
    (w : σ → ℕ) (hw : ∀ x,w x≤1) (f : MvPolynomial σ K)
    (hf : f.IsHomogeneous (2*d)) :
    positiveWeightProjection w d f=0 ↔ f.IsWeightedHomogeneous w 0 := by
  constructor
  · intro hproj a ha
    have hdeg : a.degree=2*d := by
      simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hf ha
    have hb : Finsupp.weight w a≤2*d := by
      simpa only [hdeg] using weight_le_degree w hw a
    by_contra hn
    have hp : 0<Finsupp.weight w a := by omega
    have hh := congrFun hproj ⟨Finsupp.weight w a,hp,hb⟩
    have hc := congrArg (fun p : MvPolynomial σ K => p.coeff a) hh
    change (weightedHomogeneousComponent w (Finsupp.weight w a) f).coeff a=0 at hc
    simp only [coeff_weightedHomogeneousComponent,ite_true] at hc
    exact ha hc
  · exact positiveWeightProjection_zero w d f


theorem restoration_reduction_rename (e : σ ≃ τ) (w : σ → ℕ)
    (hw : ∀ x,w x≤1) {d r : ℕ}
    (g : Fin r → evenRestorationSpace (K := K) w d) (degree : Fin r → ℕ)
    (hreduce : ∀ c : Fin r → evenRestorationSpace (K := K) w d,
      PolynomialRestoration.row (evenRestorationSpace w d).subtype
        (positiveWeightProjection w d) g c=0 →
      ∃ (M : Fin r → Fin r → K) (z : retainedScalarCoefficients (K := K) w d degree),
        c-coefficientBoundary g M=z.val) :
    ∀ c : Fin r → evenRestorationSpace (K := K) (w ∘ e.symm) d,
      PolynomialRestoration.row (evenRestorationSpace (w ∘ e.symm) d).subtype
        (positiveWeightProjection (w ∘ e.symm) d) (fun i => evenRestorationRenameEquiv e w d (g i)) c=0 →
      ∃ (M : Fin r → Fin r → K)
        (z : retainedScalarCoefficients (K := K) (w ∘ e.symm) d degree),
        c-coefficientBoundary (fun i => evenRestorationRenameEquiv e w d (g i)) M=z.val := by
  classical
  intro c hc
  let f := evenRestorationRenameEquiv (K := K) e w d
  let c₀ : Fin r → evenRestorationSpace (K := K) w d := fun i => f.symm (c i)
  let p := ∑ i,(f (g i)).val*(c i).val
  have hp : p.IsHomogeneous (2*d) := by
    apply (homogeneousSubmodule τ K (2*d)).sum_mem
    intro i _
    change ((f (g i)).val*(c i).val).IsHomogeneous (2*d)
    simpa only [two_mul] using ((f (g i)).property.1.mul (c i).property.1)
  have hpzero : p.IsWeightedHomogeneous (w ∘ e.symm) 0 :=
    (positiveWeightProjection_eq_zero_iff (w ∘ e.symm) (fun x => hw _) p hp).mp hc
  have hsum : (∑ i,(g i).val*(c₀ i).val)=rename e.symm p := by
    simp only [p,map_sum,map_mul,c₀,f,evenRestorationRenameEquiv,
      LinearEquiv.symm_apply_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ((renameEquiv K e).left_inv (g i).val).symm
  have hc₀ : PolynomialRestoration.row (evenRestorationSpace w d).subtype
      (positiveWeightProjection w d) g c₀=0 := by
    apply positiveWeightProjection_zero
    change (∑ i,(g i).val*(c₀ i).val).IsWeightedHomogeneous w 0
    rw [hsum]
    exact weighted_homogeneous_rename e.symm.toEmbedding w p 0 hpzero
  obtain ⟨M,z,hz⟩ := hreduce c₀ hc₀
  let z' : Fin r → evenRestorationSpace (K := K) (w ∘ e.symm) d := fun i => f (z.val i)
  have hz' : z'∈retainedScalarCoefficients (K := K) (w ∘ e.symm) d degree := by
    constructor
    · intro i hi
      change f (z.val i)=0
      rw [z.property.1 i hi,map_zero]
    · intro i
      apply weighted_homogeneous_rename e.toEmbedding (w ∘ e.symm) (z.val i).val 0
      simpa only [Function.comp_def,Equiv.coe_toEmbedding,Equiv.symm_apply_apply]
        using z.property.2 i
  refine ⟨M,⟨z',hz'⟩,?_⟩
  funext i
  have hh := congrArg f (congrFun hz i)
  simpa only [Pi.sub_apply,coefficientBoundary,map_sub,map_sum,map_smul,c₀,
    LinearEquiv.apply_symm_apply,z',f] using hh

end Froberg
