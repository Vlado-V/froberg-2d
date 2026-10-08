import Froberg.PrivateMixedRow
import Froberg.PreparedCoreExtension

/-! Private separation for actual homogeneous biforms. Output coordinates
are constructed here, so the row consumer supplies only polynomial data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z s b h c m q r t g R : ℕ}

lemma polynomialVector_core_extension (o : Fin c → MvPolynomial σ K)
    (p : Fin c → Poly K a) :
    rename (Sum.map id (Fin.castAdd z)) (polynomialVector o p)=
      polynomialVector o (fun k => rename (Fin.castAdd z) (p k)) := by
  simp only [polynomialVector_apply,map_sum,map_mul,rename_rename]
  rfl

theorem private_biform_row_zero (hs : 2 ≤ s) (hr : r<s) (ht : t<s)
    (bi : Basis (Fin h) K (homogeneousSubmodule σ K R))
    (bo : Basis (Fin c) K (homogeneousSubmodule σ K (R+1)))
    (w : Fin b → homogeneousSubmodule σ K 1) (hw : ∀ i,w i≠0)
    (ι : Fin b ↪ Fin z)
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin c → K)
    (hprojected : ∀ j d,d≤1 → ∀ p : Fin m → Forms K a d,
      (∀ α,sparseOutputCoefficient e v p α∈(privateOutputMatrix bi bo (w j)).range) → p=0)
    (Q : Fin q → Poly K a)
    (x : Fin q → MvPolynomial (σ ⊕ Fin (a+z)) K)
    (hx : ∀ i,x i∈biformImage (homogeneousSubmodule σ K (R+1)) (Forms K (a+z) t))
    (C : MvPolynomial (σ ⊕ Fin a) K)
    (hC : C∈biformImage (homogeneousSubmodule σ K (R+1)) (Forms K a g))
    (p : Fin m → Forms K (a+z) (s+1))
    (u : Fin b → MvPolynomial (σ ⊕ Fin (a+z)) K)
    (hu : ∀ i,u i∈biformImage (homogeneousSubmodule σ K R) (Forms K (a+z) r))
    (hrel : (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i))*x i)+
      (∑ i,polynomialVector (fun k => (bo k).val) (fun k =>
        rename (Fin.castAdd z) (monomial (e i) (v i k)))*rename Sum.inr (p i).val)+
      rename (Sum.map id (Fin.castAdd z)) C+
      (∑ i,(rename Sum.inl (w i).val*rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*u i)=0) :
    u=0 := by
  have hx' (i : Fin q) : x i∈(polynomialFormVector (fun k => (bo k).val) t).range := by
    rw [polynomialFormVector_range_basis]
    exact hx i
  choose xp hxp using hx'
  have hu' (i : Fin b) : u i∈(polynomialFormVector (fun k => (bi k).val) r).range := by
    rw [polynomialFormVector_range_basis]
    exact hu i
  choose up hup using hu'
  have hC' : C∈(polynomialFormVector (fun k => (bo k).val) g).range := by
    rw [polynomialFormVector_range_basis]
    exact hC
  obtain ⟨cp,hcp⟩ := hC'
  have hres : polynomialVector (fun k => (bo k).val) (fun k =>
      (∑ i,rename (Fin.castAdd z) (Q i)*(xp i k).val)+rename (Fin.castAdd z) (cp k).val)=
      (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i))*x i)+
        rename (Sum.map id (Fin.castAdd z)) C := by
    have heq : (fun k => (∑ i,rename (Fin.castAdd z) (Q i)*(xp i k).val)+
        rename (Fin.castAdd z) (cp k).val)=
        (∑ i,(fun k => rename (Fin.castAdd z) (Q i)*(xp i k).val))+
          (fun k => rename (Fin.castAdd z) (cp k).val) := by
      funext k
      simp only [Pi.add_apply,Finset.sum_apply]
    rw [heq,map_add,map_sum]
    simp_rw [polynomialVector_scalar_mul]
    have hxval (i) : polynomialVector (fun k => (bo k).val) (fun k => (xp i k).val)=x i := hxp i
    simp_rw [hxval]
    rw [←polynomialVector_core_extension]
    congr 1
    exact congrArg (rename (Sum.map id (Fin.castAdd z))) hcp
  have hlinout : LinearIndependent K (fun k => (bo k).val) :=
    bo.linearIndependent.map' (homogeneousSubmodule σ K (R+1)).subtype
      (LinearMap.ker_eq_bot.mpr (homogeneousSubmodule σ K (R+1)).subtype_injective)
  have hlinin : LinearIndependent K (fun k => (bi k).val) :=
    bi.linearIndependent.map' (homogeneousSubmodule σ K R).subtype
      (LinearMap.ker_eq_bot.mpr (homogeneousSubmodule σ K R).subtype_injective)
  have hz : up=0 := private_mixed_polynomial_row_zero hs hr ht
    (fun k => (bo k).val) hlinout (fun k => (bi k).val) hlinin
    (fun i => (w i).val) (fun i hz => hw i (Subtype.ext hz)) ι
    (fun i => privateOutputMatrix bi bo (w i)) (fun i => privateOutputMatrix_column bi bo (w i))
    e v hprojected Q xp (fun k => (cp k).val) p up (by
      rw [hres]
      have hup' (i) : polynomialVector (fun k => (bi k).val) (fun k => (up i k).val)=u i := hup i
      simp_rw [hup']
      convert hrel using 1 <;> abel)
  funext i
  rw [←hup i,hz]
  exact map_zero _

/-- A core-only term cannot cancel a private-power row below its endpoint. -/
theorem private_biform_core_zero (hs : 2 ≤ s) (hr : r<s)
    (bi : Basis (Fin h) K (homogeneousSubmodule σ K R))
    (bo : Basis (Fin c) K (homogeneousSubmodule σ K (R+1)))
    (w : Fin b → homogeneousSubmodule σ K 1) (hw : ∀ i,w i≠0)
    (ι : Fin b ↪ Fin z)
    (C : MvPolynomial (σ ⊕ Fin a) K)
    (hC : C∈biformImage (homogeneousSubmodule σ K (R+1)) (Forms K a g))
    (u : Fin b → MvPolynomial (σ ⊕ Fin (a+z)) K)
    (hu : ∀ i,u i∈biformImage (homogeneousSubmodule σ K R) (Forms K (a+z) r))
    (hrel : rename (Sum.map id (Fin.castAdd z)) C+
      (∑ i,(rename Sum.inl (w i).val*rename Sum.inr
        (monomial (privateExponent a s ι i) (1:K)))*u i)=0) : u=0 := by
  apply private_biform_row_zero (m := 0) (q := 0) (t := 0) hs hr (by omega)
    bi bo w hw ι Fin.elim0 Fin.elim0
    (fun _ _ _ p _ => Subsingleton.elim p 0) Fin.elim0 Fin.elim0
    (fun i => Fin.elim0 i) C hC Fin.elim0 u hu
  simpa only [Fin.sum_univ_zero,zero_add] using hrel

end Froberg
