module

public import Froberg.UpperTargetOpen
public import Froberg.OddQuotientProduct
public import Froberg.ParityWeights
public import Froberg.OddSplitElimination

@[expose] public section

/-! B.7 excludes a nonzero odd endpoint covector with zero bottom row.
The target here is the actual endpoint quotient, not a larger row model. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {h m d r n : ℕ}

def coreParity (h m : ℕ) : Fin (h+m) → ZMod 2 :=
  fun i => (coreWeight h m i : ZMod 2)

theorem coreWeight_le_one (i : Fin (h+m)) : coreWeight h m i≤1 := by
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [coreWeight]

/-- On a form supported in X-degrees zero and one, odd projection is
supported in X-degree one. -/
theorem lowTarget_odd_weight_one (p : Forms K (h+m) (2*d))
    (hp : p∈lowTargetSubspace (K := K) (h := h) (m := m) (d := d)) :
    (parityForm (coreParity h m) 1 p).val.IsWeightedHomogeneous (coreWeight h m) 1 := by
  intro a ha
  have hcoeff : p.val.coeff a≠0 := by
    intro hz
    apply ha
    simp only [parityForm_val,coeff_weightedHomogeneousComponent,hz,ite_self]
  have hpar : Finsupp.weight (coreWeight h m) a%2=1 :=
    (parity_homogeneous_iff (coreWeight h m) _ 1 (by decide)).mp
      (parityForm_homogeneous (coreParity h m) 1 p) a ha
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

/-- Projection to the actual odd endpoint quotient. -/
def oddTargetClass (w : Fin n → ZMod 2) (q : Fin r → Forms K n d) :
    Forms K n (2*d) →ₗ[K] oddTargetSpace w q :=
  ((projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ.comp
    (parityForm w 1)).rangeRestrict

theorem oddTargetClass_surjective (w : Fin n → ZMod 2) (q : Fin r → Forms K n d) :
    Function.Surjective (oddTargetClass w q) := by
  intro z
  obtain ⟨p,hp⟩ := z.property
  exact ⟨p,Subtype.ext hp⟩

theorem oddTargetClass_parity (w : Fin n → ZMod 2) (q : Fin r → Forms K n d)
    (p : Forms K n (2*d)) :
    oddTargetClass w q (parityForm w 1 p)=oddTargetClass w q p := by
  apply Subtype.ext
  change (projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ
    (parityForm w 1 (parityForm w 1 p))=_
  rw [parityForm_same w 1 _ (parityForm_homogeneous w 1 p)]
  rfl

theorem oddTargetClass_product (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (c : Fin r → Forms K n d) : oddTargetClass w q (endpointMultiplication q c)=0 := by
  apply Subtype.ext
  change (projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ
    (parityForm w 1 (endpointMultiplication q c))=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨paritySource w e 1 c,?_⟩
  exact endpointMultiplication_paritySource w e q hq 1 c

/-- An odd covector is determined by its X-degree-one component whenever
the actual generator products fill all target rows of X-degree at least two. -/
theorem oddTarget_bottom_detects (e : Fin r → ZMod 2)
    (q : Fin r → Forms K (h+m) d)
    (hpar : ∀ i,(q i).val.IsWeightedHomogeneous (coreParity h m) (e i))
    (hupper : Function.Surjective (upperTargetMap q))
    (ell : oddTargetSpace (coreParity h m) q →ₗ[K] K)
    (hbottom : ∀ p : Forms K (h+m) (2*d),
      p.val.IsWeightedHomogeneous (coreWeight h m) 1 →
        ell (oddTargetClass (coreParity h m) q p)=0) : ell=0 := by
  have hext : ell.comp (oddTargetClass (coreParity h m) q)=0 := by
    apply upperTargetMap_annihilator q hupper
    · intro c
      change ell (oddTargetClass (coreParity h m) q (endpointMultiplication q c))=0
      rw [oddTargetClass_product (coreParity h m) e q hpar,map_zero]
    · intro p hp
      change ell (oddTargetClass (coreParity h m) q p)=0
      rw [←oddTargetClass_parity (coreParity h m) q p]
      exact hbottom _ (lowTarget_odd_weight_one p hp)
  apply LinearMap.ext
  intro z
  obtain ⟨p,rfl⟩ := oddTargetClass_surjective (coreParity h m) q z
  exact LinearMap.congr_fun hext p

end Froberg
