module

public import Froberg.PolynomialFamilyRestoration

@[expose] public section

/-! A two-parity coefficient complex has an open exactness locus even
when both alternating boundary maps have kernels. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.SplitRestoration
open Module MvPolynomial Quartic PolynomialRestoration
variable {K : Type} {σ I V W Z S : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup Z] [Module K Z]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
variable {r b : ℕ}

def row (j : V →ₗ[K] MvPolynomial σ K) (k : W →ₗ[K] MvPolynomial σ K)
    (pi : MvPolynomial σ K →ₗ[K] Z) (g : Fin r → V) (p : Fin b → W) :
    ((Fin r → V) × (Fin b → W)) →ₗ[K] Z :=
  (PolynomialRestoration.row j pi g).coprod (PolynomialRestoration.row k pi p)

def boundary (g : Fin r → V) (p : Fin b → W) (T : S →ₗ[K] (Fin r → V)) :
    (((Fin r → Fin r → K) × S) × (Fin b → Fin b → K)) →ₗ[K]
      ((Fin r → V) × (Fin b → W)) :=
  ((PolynomialRestoration.boundary g).coprod T).prodMap (PolynomialRestoration.boundary p)

theorem split_restoration_open
    (j : V →ₗ[K] MvPolynomial σ K) (k : W →ₗ[K] MvPolynomial σ K)
    (pi : MvPolynomial σ K →ₗ[K] Z)
    (g : (I → K) → Fin r → V) (p : (I → K) → Fin b → W)
    (hg : IsPolynomialFamily g) (hp : IsPolynomialFamily p)
    (T : S →ₗ[K] (Fin r → V))
    (hT : ∀ a z,PolynomialRestoration.row j pi (g a) (T z)=0)
    (a₀ : I → K)
    (hreduce : ∀ c v,row j k pi (g a₀) (p a₀) (c,v)=0 →
      ∃ (M : Fin r → Fin r → K) (C : Fin b → Fin b → K) (z : S),
        c-coefficientBoundary (g a₀) M=T z ∧ v=coefficientBoundary (p a₀) C) :
    ∃ D : MvPolynomial I K,eval a₀ D≠0 ∧
      ∀ a,eval a D≠0 → ∀ c v,row j k pi (g a) (p a) (c,v)=0 →
        ∃ (M : Fin r → Fin r → K) (C : Fin b → Fin b → K) (z : S),
          c-coefficientBoundary (g a) M=T z ∧ v=coefficientBoundary (p a) C := by
  let A := fun a => row j k pi (g a) (p a)
  let B := fun a => boundary (g a) (p a) T
  have hA : IsPolynomialFamily A := by
    apply isPolynomialFamily_linearMap
    intro x
    exact ((row_polynomial j pi g hg).linear_comp (LinearMap.applyₗ (R := K) x.1)).add
      ((row_polynomial k pi p hp).linear_comp (LinearMap.applyₗ (R := K) x.2))
  have hB : IsPolynomialFamily B := by
    apply isPolynomialFamily_linearMap
    intro x
    exact ((hg.linear_comp (boundaryInFamily x.1.1)).add (isPolynomialFamily_const (T x.1.2))).prod_mk
      (hp.linear_comp (boundaryInFamily x.2))
  have hAB : ∀ a,(A a).comp (B a)=0 := by
    intro a
    apply LinearMap.ext
    rintro ⟨⟨M,z⟩,C⟩
    change PolynomialRestoration.row j pi (g a) (PolynomialRestoration.boundary (g a) M+T z)+
      PolynomialRestoration.row k pi (p a) (PolynomialRestoration.boundary (p a) C)=0
    rw [map_add,row_boundary,row_boundary,hT,add_zero,zero_add]
  have hexact : (A a₀).ker=(B a₀).range := by
    apply le_antisymm
    · rintro ⟨c,v⟩ hv
      obtain ⟨M,C,z,hc,hv⟩ := hreduce c v hv
      refine ⟨((M,z),C),?_⟩
      apply Prod.ext
      · change coefficientBoundary (g a₀) M+T z=c
        exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hc).symm
      · exact hv.symm
    · rintro _ ⟨x,rfl⟩
      exact LinearMap.congr_fun (hAB a₀) x
  obtain ⟨D,hD,hgood⟩ := complex_general_exact_principal_open A B hA hB hAB a₀ hexact
  refine ⟨D,hD,?_⟩
  intro a ha c v hcv
  have hmem : (c,v)∈(B a).range := (hgood a ha) ▸ (show (c,v)∈(A a).ker from hcv)
  obtain ⟨⟨⟨M,z⟩,C⟩,hMC⟩ := hmem
  refine ⟨M,C,z,?_,?_⟩
  · have hc := congrArg Prod.fst hMC
    change coefficientBoundary (g a) M+T z=c at hc
    rw [←hc,add_sub_cancel_left]
  · exact (congrArg Prod.snd hMC).symm

end Froberg.SplitRestoration
