module

public import Froberg.GradedProductAssembly

@[expose] public section

/-! Actual polynomial multiplication on the formal cross and diagonal source
blocks of the product row Π_R. Distinct half-degrees assemble all its blocks. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg Module MvPolynomial
variable {K : Type} [Field K]

/-- An unordered active pair is determined by its smaller layer index. -/
def Row (J : Finset ℕ) (R : ℕ) :=
  {j : Fin (R+1) // j.val ∈ J ∧ R-j.val ∈ J ∧ 2*j.val ≤ R}

instance (J : Finset ℕ) (R : ℕ) : Fintype (Row J R) := by
  unfold Row
  infer_instance

instance (J : Finset ℕ) (R : ℕ) : DecidableEq (Row J R) := Classical.decEq _

/-- Each formal block has its ordinary tensor-product basis, or the
unordered-pair basis in the diagonal case. -/
def Columns (e : ℕ → ℕ) {J R} (j : Row J R) :=
  if j.val.val = R-j.val.val then Sym2 (Fin (e j.val.val))
  else Fin (e j.val.val) × Fin (e (R-j.val.val))

instance (e : ℕ → ℕ) {J R} (j : Row J R) : Fintype (Columns e j) := by
  unfold Columns
  split <;> infer_instance

/-- The output half-degree assigned to a layer in one fixed product row. -/
def assignedDegree (R j : ℕ) : ℕ :=
  if 2*j<R then j else if 2*j=R then j/2 else 0

variable {σ : Type*}

def products (e : ℕ → ℕ) (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    {J R} (j : Row J R) : Columns e j → MvPolynomial σ K :=
  if h : j.val.val = R-j.val.val then
    fun c => pairProducts (q j.val.val) (cast (if_pos h) c)
  else fun c =>
    let p : Fin (e j.val.val) × Fin (e (R-j.val.val)) := cast (if_neg h) c
    q j.val.val p.1 * q (R-j.val.val) p.2

/-- The polynomial multiplication matrix on all formal product blocks. -/
def multiplication (e : ℕ → ℕ) (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (J : Finset ℕ) (R : ℕ) :
    ((Σ j : Row J R, Columns e j) →₀ K) →ₗ[K] MvPolynomial σ K :=
  Finsupp.linearCombination K (fun p => products e q p.1 p.2)

/-- For even active layers, every product block has the smaller layer index
as its output half-degree, so distinct blocks cannot cancel. -/
theorem products_weighted (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (w : σ → ℕ) {J R} (heven : ∀ j ∈ J, Even j)
    (hq : ∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedDegree R j))
    (j : Row J R) (c : Columns e j) :
    (products e q j c).IsWeightedHomogeneous w j.val.val := by
  classical
  have hj := j.property
  have hjle : j.val.val ≤ R := by omega
  by_cases hd : j.val.val = R-j.val.val
  · have htwo : 2*j.val.val=R := by omega
    have ht : assignedDegree R j.val.val = j.val.val/2 := by
      simp [assignedDegree,htwo]
    have hev : 2*(j.val.val/2)=j.val.val := Nat.two_mul_div_two_of_even (heven _ hj.1)
    unfold products
    simp only [dif_pos hd]
    generalize hc : cast (if_pos hd) c = p
    induction p using Sym2.inductionOn with
    | _ a b =>
      have h := (hq _ hj.1 a).mul (hq _ hj.1 b)
      simpa only [pairProducts_mk,ht,← two_mul,hev] using h
  · have hsmall : 2*j.val.val<R := by omega
    have hlarge : R<2*(R-j.val.val) := by omega
    have hl : assignedDegree R j.val.val = j.val.val := by simp [assignedDegree,hsmall]
    have hr : assignedDegree R (R-j.val.val) = 0 := by
      simp [assignedDegree,show ¬2*(R-j.val.val)<R by omega,show ¬2*(R-j.val.val)=R by omega]
    unfold products
    simp only [dif_neg hd]
    let p : Fin (e j.val.val) × Fin (e (R-j.val.val)) := cast (if_neg hd) c
    change (q j.val.val p.1 * q (R-j.val.val) p.2).IsWeightedHomogeneous w j.val.val
    have h := (hq _ hj.1 p.1).mul (hq _ hj.2.1 p.2)
    simpa only [hl,hr,add_zero] using h

/-- Independence in each cross/diagonal block implies injectivity of the
whole formal product multiplication map Π_R. -/
theorem multiplication_injective (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (w : σ → ℕ) (J : Finset ℕ) (R : ℕ)
    (heven : ∀ j ∈ J, Even j)
    (hq : ∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedDegree R j))
    (hblocks : ∀ j : Row J R, LinearIndependent K (products e q j)) :
    Function.Injective (multiplication e q J R) := by
  apply linearIndependent_weighted_fibers w (fun j : Row J R => j.val.val)
    (fun _ _ h => Subtype.ext (Fin.ext h)) (products e q) hblocks
  exact products_weighted e q w heven hq

end Froberg.ProductRows
