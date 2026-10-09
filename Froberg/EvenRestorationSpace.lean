module

public import Froberg.WeightedParitySpace
public import Froberg.PolynomialFamilyRestoration
public import Froberg.HomogeneousOutputCoordinates

@[expose] public section

/-! The actual coefficient and target spaces for restoring pure forms in even
degree. The target remembers every positive output-weight component. -/
noncomputable section
namespace Froberg
open MvPolynomial Module
variable {K : Type} {σ : Type*} [Field K] [Fintype σ]

def evenRestorationSpace (w : σ → ℕ) (d : ℕ) : Submodule K (MvPolynomial σ K) :=
  homogeneousSubmodule σ K d ⊓ weightedParitySpace w 0

instance evenRestorationSpace_finite (w : σ → ℕ) (d : ℕ) :
    Module.Finite K (evenRestorationSpace (K := K) w d) := by
  letI : Module.Finite K (homogeneousSubmodule σ K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ d)
  exact Submodule.finiteDimensional_of_le inf_le_left

def positiveWeightProjection (w : σ → ℕ) (d : ℕ) :
    MvPolynomial σ K →ₗ[K] ({r : ℕ // 0<r ∧ r≤2*d} → MvPolynomial σ K) :=
  LinearMap.pi (fun r => weightedHomogeneousComponent w r.val)

theorem positiveWeightProjection_zero (w : σ → ℕ) (d : ℕ)
    (f : MvPolynomial σ K) (hf : f.IsWeightedHomogeneous w 0) :
    positiveWeightProjection w d f=0 := by
  funext r
  exact hf.weightedHomogeneousComponent_ne r.val (by omega)

/-- The retained coefficients have output weight zero and occur only on old
scalar labels. No equation on their scalar products is imposed here. -/
def retainedScalarCoefficients {r : ℕ} (w : σ → ℕ) (d : ℕ)
    (degree : Fin r → ℕ) : Submodule K (Fin r → evenRestorationSpace (K := K) w d) where
  carrier := {z | (∀ i,0<degree i → z i=0) ∧
    ∀ i,(z i).val.IsWeightedHomogeneous w 0}
  zero_mem' := ⟨by simp,fun _ => (weightedHomogeneousSubmodule K w 0).zero_mem⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i hi
      simp only [Pi.add_apply,hx.1 i hi,hy.1 i hi,zero_add]
    · intro i
      exact (weightedHomogeneousSubmodule K w 0).add_mem (hx.2 i) (hy.2 i)
  smul_mem' := by
    intro a x hx
    constructor
    · intro i hi
      simp only [Pi.smul_apply,hx.1 i hi,smul_zero]
    · intro i
      exact (weightedHomogeneousSubmodule K w 0).smul_mem a (hx.2 i)

theorem retainedScalarCoefficients_row_zero {r : ℕ} (w : σ → ℕ) (d : ℕ)
    (degree : Fin r → ℕ) (q : Fin r → evenRestorationSpace (K := K) w d)
    (hq : ∀ i,degree i=0 → (q i).val.IsWeightedHomogeneous w 0)
    (z : retainedScalarCoefficients (K := K) w d degree) :
    PolynomialRestoration.row (evenRestorationSpace w d).subtype
      (positiveWeightProjection w d) q z.val=0 := by
  apply positiveWeightProjection_zero
  apply (weightedHomogeneousSubmodule K w 0).sum_mem
  intro i _
  change ((q i).val*(z.val i).val).IsWeightedHomogeneous w 0
  by_cases hi : 0<degree i
  · simp only [z.property.1 i hi,Submodule.coe_zero,mul_zero]
    exact (weightedHomogeneousSubmodule K w 0).zero_mem
  · have hprod := (hq i (by omega)).mul (z.property.2 i)
    simpa only [zero_add] using hprod

theorem pureShift_eq_zero_away {U V : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {u r : ℕ} (embed : U →ₗ[K] V) (slot : Fin u → Fin r)
    (v : Fin u → U) (i : Fin r) (hi : ∀ k,slot k≠i) :
    PolynomialRestoration.pureShift (K := K) (V := V) embed slot v i=0 := by
  classical
  simp only [PolynomialRestoration.pureShift,LinearMap.sum_apply,Finset.sum_apply,
    LinearMap.comp_apply,LinearMap.proj_apply]
  apply Finset.sum_eq_zero
  intro k _
  simp [LinearMap.single_apply,Pi.single_eq_of_ne (hi k).symm]

theorem pureShift_at_slot {U V : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {u r : ℕ} (embed : U →ₗ[K] V) (slot : Fin u → Fin r)
    (hslot : Function.Injective slot) (v : Fin u → U) (k : Fin u) :
    PolynomialRestoration.pureShift (K := K) (V := V) embed slot v (slot k)=embed (v k) := by
  classical
  simp [PolynomialRestoration.pureShift,LinearMap.single_apply,Pi.single_apply,hslot.eq_iff]

end Froberg
