import Froberg.ProductRowGluing
import Froberg.ParityProfileGrowth
import Froberg.PairedScalarSeparation

/-! All products in a row are supported in the removed parity and at most
one additional scalar half-degree. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial MonomialExpansion
variable {K : Type} [Field K] {σ : Type*}

def assignedScalarDegree (R d j : ℕ) : ℕ :=
  if 2*j<R then d-j else if 2*j=R then (d-j)/2 else 0

/-- The scalar half-degree of each actual formal product. -/
theorem products_scalar_weighted (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (w : σ → ℕ) {J : Finset ℕ} {R d : ℕ}
    (hq : ∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedScalarDegree R d j))
    (r : Row J R) (c : Columns e r) :
    (products e q r c).IsWeightedHomogeneous w
      (if r.val.val=R-r.val.val then 2*((d-r.val.val)/2) else d-r.val.val) := by
  classical
  have hj := r.property
  by_cases hd : r.val.val=R-r.val.val
  · have htwo : 2*r.val.val=R := by omega
    have ht : assignedScalarDegree R d r.val.val = (d-r.val.val)/2 := by
      simp [assignedScalarDegree,htwo]
    unfold products
    simp only [dif_pos hd,if_pos hd]
    generalize hc : cast (if_pos hd) c = p
    induction p using Sym2.inductionOn with
    | _ a b =>
      have h := (hq _ hj.1 a).mul (hq _ hj.1 b)
      simpa only [pairProducts_mk,ht,← two_mul] using h
  · have hsmall : 2*r.val.val<R := by omega
    have hlarge : R<2*(R-r.val.val) := by omega
    have hl : assignedScalarDegree R d r.val.val=d-r.val.val := by
      simp [assignedScalarDegree,hsmall]
    have hr : assignedScalarDegree R d (R-r.val.val)=0 := by
      simp [assignedScalarDegree,show ¬2*(R-r.val.val)<R by omega,
        show ¬2*(R-r.val.val)=R by omega]
    unfold products
    simp only [dif_neg hd,if_neg hd]
    let p : Fin (e r.val.val) × Fin (e (R-r.val.val)) := cast (if_neg hd) c
    change (q r.val.val p.1 * q (R-r.val.val) p.2).IsWeightedHomogeneous w (d-r.val.val)
    simpa only [hl,hr,add_zero] using (hq _ hj.1 p.1).mul (hq _ hj.2.1 p.2)

/-- An arbitrary property stable under zero is preserved by the common
family assembly, including degree and output-subspace constraints. -/
theorem assembledFamily_property (e : ℕ → ℕ) {J : Finset ℕ} {R : ℕ}
    (q : (r : Row J R) → (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (P : ℕ → MvPolynomial σ K → Prop) (hzero : ∀ j, P j 0)
    (hq : ∀ r j, ∀ i, P j (q r j i)) :
    ∀ j i, P j (assembledFamily e q j i) := by
  intro j i
  unfold assembledFamily
  split_ifs with h
  · exact hq h.choose j i
  · exact hzero j

/-- A scalar half-degree is measured by the first coordinate of splitWeight. -/
def halfWeight {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℕ :=
  (splitWeight S i).1

theorem weight_halfWeight {n : ℕ} (S : Finset (Fin n)) (a : Fin n →₀ ℕ) :
    Finsupp.weight (halfWeight S) a = partialDegree S a := by
  rw [← fst_weight_splitWeight]
  change Finsupp.weight (fun i => (splitWeight S i).1) a =
    (Finsupp.weight (splitWeight S) a).1
  change Finsupp.weight (fun i => (splitWeight S i).1) a =
    (AddMonoidHom.fst ℕ ℕ) (Finsupp.weight (splitWeight S) a)
  rw [Finsupp.weight_eq_sum,Finsupp.weight_eq_sum,map_sum]
  rfl

/-- A homogeneous scalar half-degree in the excluded set vanishes under
retention. -/
theorem retained_profile_zero {n k p j : ℕ} (S : Finset (Fin n))
    (f : Poly K n) (hf : f.IsWeightedHomogeneous (halfWeight S) k)
    (hk : k%2=p ∨ k=j) :
    retainMonomials (parityProfileRetained S p j) f = 0 := by
  ext a
  rw [coeff_retainMonomials]
  by_cases hP : parityProfileRetained S p j a
  · rw [if_pos hP]
    by_contra hc
    have h := hf hc
    rw [weight_halfWeight] at h
    rcases hk with hk | hk
    · exact hP.1 (h ▸ hk)
    · exact hP.2 (h ▸ hk)
  · simp [hP]

/-- Every formal product is killed by the same parity-plus-one-profile
projection, which is independent of the pair block. -/
theorem products_retained_zero {n : ℕ} (S : Finset (Fin n)) (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → Poly K n) {J : Finset ℕ} {R d : ℕ}
    (heven : ∀ j ∈ J, Even j) (hdegree : ∀ j ∈ J, j≤d)
    (hq : ∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous (halfWeight S) (assignedScalarDegree R d j))
    (r : Row J R) (c : Columns e r) :
    retainMonomials (parityProfileRetained S (d%2) (2*((d-R/2)/2))) (products e q r c)=0 := by
  apply retained_profile_zero S _ (products_scalar_weighted e q _ hq r c)
  split_ifs with h
  · right
    have hj := r.property.2.2
    have heq : r.val.val=R/2 := by omega
    simp [heq]
  · left
    have hjd := hdegree _ r.property.1
    have hje := heven _ r.property.1
    obtain ⟨k,hk⟩ := hje
    omega

/-- Hence the whole actual product image is contained in the deleted
coordinate subspace. -/
theorem multiplication_range_le_retention_kernel {n : ℕ} (S : Finset (Fin n))
    (e : ℕ → ℕ) (q : (j : ℕ) → Fin (e j) → Poly K n) {J : Finset ℕ} {R d : ℕ}
    (heven : ∀ j ∈ J, Even j) (hdegree : ∀ j ∈ J, j≤d)
    (hq : ∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous (halfWeight S) (assignedScalarDegree R d j)) :
    (multiplication e q J R).range ≤
      (retainMonomials (K := K) (parityProfileRetained S (d%2) (2*((d-R/2)/2)))).ker := by
  rw [multiplication,Finsupp.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro f ⟨⟨r,c⟩,rfl⟩
  exact products_retained_zero S e q heven hdegree hq r c

end Froberg.ProductRows
