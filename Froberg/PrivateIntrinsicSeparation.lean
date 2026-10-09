module

public import Froberg.PrivateBiformRow
public import Froberg.IntrinsicBiformRow

@[expose] public section

/-! Private-row separation in the fixed intrinsic coefficient spaces used
by the combined prepared-row matrix. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K] {σ : Type*} [Fintype σ]
variable {a z d R b q m hi ho g : ℕ}

 theorem private_intrinsic_row_zero (hd : 3≤d) (hR : 2≤R) (hRd : R+1≤d)
    (bi : Basis (Fin hi) K (homogeneousSubmodule σ K R))
    (bo : Basis (Fin ho) K (homogeneousSubmodule σ K (R+1)))
    (w : Fin b → homogeneousSubmodule σ K 1) (hw : ∀ i,w i≠0)
    (ι : Fin b ↪ Fin z)
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin ho → K)
    (hproj : ∀ l c,c≤1 → ∀ p : Fin m → Forms K a c,
      (∀ α,sparseOutputCoefficient e v p α∈(privateOutputMatrix bi bo (w l)).range) → p=0)
    (Q : Fin q → Forms K a d)
    (x : Fin q → FullBiform K σ (a+z) (R+1) (d-(R+1)))
    (p : Fin m → Forms K (a+z) d)
    (C : FullBiform K σ a (R+1) g)
    (u : Fin b → FullBiform K σ (a+z) R (d-R))
    (hrel : (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i).val)*(x i).val)+
      (∑ i,rename (Sum.map id (Fin.castAdd z))
        (attachedPolynomialFamily (fun j => (bo j).val) e v i)*rename Sum.inr (p i).val)+
      rename (Sum.map id (Fin.castAdd z)) C.val+
      (∑ i,(rename Sum.inl (w i).val*
        rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))*(u i).val)=0) :
    u=0 := by
  let p' : Fin m → Forms K (a+z) ((d-1)+1) := fun i =>
    ⟨(p i).val,by simpa only [Nat.sub_add_cancel (by omega : 1≤d)] using (p i).property⟩
  have hh := private_biform_row_zero (s := d-1) (r := d-R) (t := d-(R+1))
    (by omega) (by omega) (by omega) bi bo w hw ι e v hproj
    (fun i => (Q i).val) (fun i => (x i).val) (fun i => (x i).property)
    C.val C.property p' (fun i => (u i).val) (fun i => (u i).property) (by
      simpa only [attachedPolynomialFamily,polynomialVector_core_extension,p'] using hrel)
  funext i
  apply Subtype.ext
  exact congrFun hh i

end Froberg
