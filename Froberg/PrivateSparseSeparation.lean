import Froberg.PrivateCoreCoefficients
import Froberg.SparseOutputQuotients
import Froberg.PrivateLowerInjection

/-! Separation of the sparse new layer from fixed private powers. Projected
linear-coefficient injectivity is used only where a private power can occur. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PrivateColumns
open MvPolynomial Module Quartic.FreeCoefficients
variable {K : Type*} [Field K] [Infinite K] {a z s b h c m r : ℕ}

lemma privateExponent_le_merge (ι : Fin b ↪ Fin z) (i : Fin b)
    (α : Fin a →₀ ℕ) (β : Fin z →₀ ℕ) :
    privateExponent a s ι i ≤ mergeExponent α β ↔ s ≤ β (ι i) := by
  rw [privateExponent_le_iff]
  simp

lemma private_unique_of_small_free_degree (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (β : Fin z →₀ ℕ) (hβ : β.degree ≤ s+1) (i j : Fin b)
    (hi : s ≤ β (ι i)) (hj : s ≤ β (ι j)) : i=j := by
  let B := mergeExponent (0 : Fin 0 →₀ ℕ) β
  have hb : B.degree=β.degree := by simp [B]
  have hd := privateDivisors_degree_bound (a := 0) (s := s) ι B
  have hcard : (privateDivisors (s := s) ι B).card ≤ 1 := by
    rw [hb] at hd
    nlinarith
  apply Finset.card_le_one.mp hcard
  · simp only [privateDivisors,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (privateExponent_le_merge ι i 0 β).mpr hi
  · simp only [privateDivisors,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (privateExponent_le_merge ι j 0 β).mpr hj

/-- A polynomial tuple has no monomial divisible by any private power. -/
def avoidsPrivatePowers (ι : Fin b ↪ Fin z) (f : Fin c → Poly K (a+z)) : Prop :=
  ∀ k δ i,privateExponent a s ι i ≤ δ → (f k).coeff δ=0

/-- The scalar/existing-product side avoids private powers whenever all of
its private coefficient polynomials above degree s−1 vanish. -/
theorem avoidsPrivatePowers_of_free_degree_lt (ι : Fin b ↪ Fin z)
    (f : Fin c → Poly K (a+z))
    (hf : ∀ k β,s ≤ β.degree → freeCoeff β (f k)=0) :
    avoidsPrivatePowers (s := s) ι f := by
  intro k δ i hi
  have hval : s ≤ (freeExponent δ) (ι i) := by
    simpa [freeExponent] using (privateExponent_le_iff ι i δ).mp hi
  have hd : s ≤ (freeExponent δ).degree := hval.trans (Finsupp.le_degree (ι i) (freeExponent δ))
  have hh := congrArg (fun p : Poly K a => p.coeff (coreExponent δ)) (hf k _ hd)
  simpa only [freeCoeff_coeff,merge_core_free,MvPolynomial.coeff_zero,Finsupp.zero_apply] using hh

/-- A private target coefficient with only one eligible private power lies
in exactly that column's output image. -/
theorem private_coefficient_mem_range (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (v : Fin b → Fin h → Forms K (a+z) r)
    (β : Fin z →₀ ℕ) (hβ : β.degree ≤ s+1) (i : Fin b) (hi : s ≤ β (ι i))
    (α : Fin a →₀ ℕ) :
    (fun k => (privatePolynomialMapAt (s := s) ι A v k).coeff (mergeExponent α β))∈(A i).range := by
  refine ⟨privateSourceCoefficient v i (mergeExponent α β-privateExponent a s ι i),?_⟩
  funext k
  rw [privatePolynomialMapAt_coefficient]
  unfold privateCoefficient
  rw [Finset.sum_eq_single i]
  · simp only [(privateExponent_le_merge ι i α β).mpr hi,ite_true]
  · intro j _ hji
    rw [if_neg]
    intro hj
    exact hji (private_unique_of_small_free_degree hs ι β hβ j i
      ((privateExponent_le_merge ι j α β).mp hj) hi)
  · simp

/-- Projected linear and constant injectivity separate the new sparse layer
from every private column, even with arbitrary private-variable coefficients. -/
theorem private_sparse_separation (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin c → K)
    (hprojected : ∀ j d,d ≤ 1 → ∀ u : Fin m → Forms K a d,
      (∀ α,sparseOutputCoefficient e v u α∈(A j).range) → u=0)
    (p : Fin m → Forms K (a+z) (s+1))
    (w : Fin b → Fin h → Forms K (a+z) r)
    (res : Fin c → Poly K (a+z)) (hres : avoidsPrivatePowers (s := s) ι res)
    (hrel : extendedCorePolynomialMatrix (fun k i => monomial (e i) (v i k)) p+
      privatePolynomialMapAt (s := s) ι A w+res=0) :
    privatePolynomialMapAt (s := s) ι A w=0 := by
  classical
  let H := extendedCorePolynomialMatrix (fun k i => monomial (e i) (v i k)) p
  let P := privatePolynomialMapAt (s := s) ι A w
  have hpβ (β : Fin z →₀ ℕ) (j : Fin b) (hj : s ≤ β (ι j)) :
      ∀ i,freeCoeff β (p i).val=0 := by
    by_cases hb : β.degree ≤ s+1
    · let u : Fin m → Forms K a (s+1-β.degree) := fun i =>
        ⟨freeCoeff β (p i).val,freeCoeff_homogeneous _ (p i).property β⟩
      have hlow : s+1-β.degree ≤ 1 := by
        have hd := hj.trans (Finsupp.le_degree (ι j) β)
        omega
      have hu : u=0 := by
        apply hprojected j _ hlow u
        intro α
        have hP := private_coefficient_mem_range hs ι A w β hb j hj α
        have hcoeff : sparseOutputCoefficient e v u α=
            -(fun k => (P k).coeff (mergeExponent α β)) := by
          funext k
          have hh := congrArg (fun f : Fin c → Poly K (a+z) =>
            (freeCoeff β (f k)).coeff α) hrel
          have hzero := hres k (mergeExponent α β) j
            ((privateExponent_le_merge ι j α β).mpr hj)
          have hE : freeCoeff β (H k)=AttachedMultiplication.multiplication e v u k := by
            simp only [H,extendedCorePolynomialMatrix,LinearMap.coe_mk,AddHom.coe_mk,
              map_sum,freeCoeff_rename_mul,AttachedMultiplication.multiplication_apply,u]
          change (freeCoeff β (H k+P k+res k)).coeff α=(freeCoeff β 0).coeff α at hh
          rw [map_add,map_add,hE] at hh
          simp only [MvPolynomial.coeff_add,AttachedMultiplication.coefficient_formula,freeCoeff_coeff,map_zero,MvPolynomial.coeff_zero,
            Finsupp.zero_apply,hzero,add_zero] at hh
          simpa only [sparseOutputCoefficient,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply]
            using eq_neg_of_add_eq_zero_left hh
        rw [hcoeff]
        exact (A j).range.neg_mem hP
      intro i
      exact congrArg Subtype.val (congrFun hu i)
    · intro i
      exact freeCoeff_eq_zero_of_degree_lt _ (p i).property β (by omega)
  have hH : avoidsPrivatePowers (s := s) ι H := by
    intro k δ j hj
    let β := freeExponent δ
    have hj' : s ≤ β (ι j) := by
      simpa [β,freeExponent] using (privateExponent_le_iff ι j δ).mp hj
    have hz : freeCoeff β (H k)=0 := by
      simp only [H,extendedCorePolynomialMatrix,LinearMap.coe_mk,AddHom.coe_mk,
        map_sum,freeCoeff_rename_mul,hpβ β j hj',mul_zero,Finset.sum_const_zero]
    have hh := congrArg (fun f : Poly K a => f.coeff (coreExponent δ)) hz
    simpa only [β,freeCoeff_coeff,merge_core_free,MvPolynomial.coeff_zero,Finsupp.zero_apply] using hh
  funext k
  apply MvPolynomial.ext
  intro δ
  by_cases hd : ∃ j,privateExponent a s ι j ≤ δ
  · obtain ⟨j,hj⟩ := hd
    have hh := congrArg (fun f : Fin c → Poly K (a+z) => (f k).coeff δ) hrel
    change (H k+P k+res k).coeff δ=(0 : Poly K (a+z)).coeff δ at hh
    simpa only [MvPolynomial.coeff_add,hH k δ j hj,hres k δ j hj,zero_add,add_zero,
      P,Pi.zero_apply,MvPolynomial.coeff_zero,Finsupp.zero_apply] using hh
  · rw [privatePolynomialMapAt_coefficient]
    simp only [privateCoefficient,Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (fun hj => hd ⟨j,hj⟩)]
    rfl

/-- In every later row there is no private coefficient at all; only row
two can reach the first pairwise private-power overlap. -/
theorem private_sparse_lower_zero (hs : 2 ≤ s) (hr : r < s) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i,Function.Injective (A i))
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin c → K)
    (hprojected : ∀ j d,d ≤ 1 → ∀ u : Fin m → Forms K a d,
      (∀ α,sparseOutputCoefficient e v u α∈(A j).range) → u=0)
    (p : Fin m → Forms K (a+z) (s+1))
    (w : Fin b → Fin h → Forms K (a+z) r)
    (res : Fin c → Poly K (a+z)) (hres : avoidsPrivatePowers (s := s) ι res)
    (hrel : extendedCorePolynomialMatrix (fun k i => monomial (e i) (v i k)) p+
      privatePolynomialMapAt (s := s) ι A w+res=0) : w=0 := by
  apply privatePolynomialMapAt_injective hr ι A hA
  rw [map_zero]
  exact private_sparse_separation hs ι A e v hprojected p w res hres hrel

end Froberg.PrivateColumns
