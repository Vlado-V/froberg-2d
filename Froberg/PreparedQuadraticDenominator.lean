import Froberg.PreparedQuadraticDetector
import Froberg.QuadraticSeparationRow

/-! The low-degree prepared denominator maps into the literal scalar/private
coefficient row. This keeps the C.2 certificate uniform in scalar deletions. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {h m d t c q b : ℕ}

theorem mem_scalarCoefficientRow_range
    (Q : Fin q → Forms K m d) (g : Fin c → Poly K m)
    (hg : ∀ k,g k∈familySpace Q*Forms K m t) :
    g∈(scalarCoefficientRow (t := t) Q).range := by
  have hx (k : Fin c) : ∃ x : Fin q → Forms K m t,
      (prefixMultiplication Q t x).val=g k := by
    have hh := hg k
    rw [←range_ambient_prefixMultiplication Q] at hh
    exact hh
  choose x hx using hx
  refine ⟨fun i k => x k i,?_⟩
  funext k
  simpa only [scalarCoefficientRow,LinearMap.coe_mk,AddHom.coe_mk,prefixMultiplication_val] using hx k

theorem polynomialTensorSpace_product_scalar_range
    (T : Poly K h →ₗ[K] (Fin c → K)) (Q : Fin q → Forms K m d)
    (A C : Submodule K (Poly K h)) (B D : Submodule K (Poly K m))
    (hBD : B*D≤familySpace Q*Forms K m t) :
    polynomialTensorSpace A B*polynomialTensorSpace C D≤
      (scalarCoefficientRow (t := t) Q).range.comap (preparedQuadraticDetector T) := by
  apply Submodule.mul_le.mpr
  rintro _ ⟨v,rfl⟩ _ ⟨w,rfl⟩
  change preparedQuadraticDetector T (polynomialTensorMap A B v*polynomialTensorMap C D w)∈
    (scalarCoefficientRow (t := t) Q).range
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      apply mem_scalarCoefficientRow_range Q
      intro k
      rw [polynomialTensorMap_tmul,polynomialTensorMap_tmul,←map_mul,
        Algebra.TensorProduct.tmul_mul_tmul,preparedQuadraticDetector_tmul]
      exact Submodule.smul_mem _ _ (hBD (Submodule.mul_mem_mul b.property y.property))
    | add u v hu hv =>
      simpa only [map_add,mul_add] using Submodule.add_mem _ hu hv
  | add u v hu hv =>
    simpa only [map_add,add_mul] using Submodule.add_mem _ hu hv

theorem polynomialTensorSpace_rename_back
    (A : Submodule K (Poly K h)) (B : Submodule K (Poly K m))
    {p : Poly K (h+m)} (hp : p∈polynomialTensorSpace A B) :
    rename finSumFinEquiv.symm p∈biformImage A B := by
  obtain ⟨v,rfl⟩ := hp
  induction v using TensorProduct.inductionOn with
  | tmul a b =>
    refine ⟨a.val ⊗ₜ[K] b.val,⟨a ⊗ₜ[K] b,rfl⟩,?_⟩
    rw [polynomialTensorMap_tmul,splitPolynomialEquiv_tmul,map_mul,
      rename_rename,rename_rename]
    change tensorEquivSum K (Fin h) (Fin m) K (a.val ⊗ₜ[K] b.val)=_
    rw [tensorEquivSum_tmul]
    have hl : (finSumFinEquiv.symm ∘ Fin.castAdd m : Fin h → Fin h ⊕ Fin m)=Sum.inl :=
      funext fun i => finSumFinEquiv_symm_apply_castAdd i
    have hr : (finSumFinEquiv.symm ∘ Fin.natAdd h : Fin m → Fin h ⊕ Fin m)=Sum.inr :=
      funext fun i => finSumFinEquiv_symm_apply_natAdd i
    rw [hl,hr]
  | add x y hx hy =>
    simpa only [map_add] using (biformImage A B).add_mem hx hy

theorem private_product_mem_quadratic_row
    (T : Poly K h →ₗ[K] (Fin c → K))
    (P : Fin b → FullBiform K (Fin h) m 1 (d-1)) :
    Submodule.span K (Set.range (fun i => rename finSumFinEquiv (P i).val))*
      polynomialTensorSpace (Forms K h 1) (Forms K m (d-1))≤
      (PolynomialRestoration.row (FullBiform K (Fin h) m 1 (d-1)).subtype
        (biformVectorDetector T) P).range.comap (preparedQuadraticDetector T) := by
  classical
  apply Submodule.mul_le.mpr
  intro p hp a ha
  change preparedQuadraticDetector T (p*a)∈
    (PolynomialRestoration.row (FullBiform K (Fin h) m 1 (d-1)).subtype
      (biformVectorDetector T) P).range
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i,rfl⟩ := hp
    let aa : FullBiform K (Fin h) m 1 (d-1) :=
      ⟨rename finSumFinEquiv.symm a,polynomialTensorSpace_rename_back _ _ ha⟩
    let v : Fin b → FullBiform K (Fin h) m 1 (d-1) := Pi.single i aa
    refine ⟨v,?_⟩
    change biformVectorDetector T (∑ k,(P k).val*(v k).val)=
      preparedQuadraticDetector T (rename finSumFinEquiv (P i).val*a)
    rw [Finset.sum_eq_single i]
    · simp only [v,Pi.single_eq_same]
      change biformVectorDetector T ((P i).val*aa.val)=
        biformVectorDetector T (rename finSumFinEquiv.symm (rename finSumFinEquiv (P i).val*a))
      apply congrArg (biformVectorDetector T)
      have hback : rename finSumFinEquiv.symm (rename finSumFinEquiv (P i).val)=(P i).val :=
        (renameEquiv K finSumFinEquiv).left_inv (P i).val
      simp only [map_mul,hback,aa]
    · intro k _ hki
      simp only [v,Pi.single_eq_of_ne hki,Submodule.coe_zero,mul_zero]
    · simp
  | zero => simp
  | add p r hp hr ihp ihr =>
    simpa only [add_mul,map_add] using Submodule.add_mem _ ihp ihr
  | smul r p hp ih =>
    simpa only [smul_mul_assoc,map_smul] using Submodule.smul_mem _ r ih

theorem prepared_denominator_mem_quadratic_row
    (hd : 2≤d) (T : Poly K h →ₗ[K] (Fin c → K))
    (Q : Fin q → Forms K m d) (P : Fin b → FullBiform K (Fin h) m 1 (d-1))
    (D : Submodule K (Poly K h)) (hD : D≤T.ker) :
    preparedProductDenominator (d := d)
      (polynomialTensorSpace (Forms K h 0) (familySpace Q))
      (Submodule.span K (Set.range (fun i => rename finSumFinEquiv (P i).val)))
      (polynomialTensorSpace D (Forms K m (d-2)))≤
      (quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
        (biformVectorDetector T) Q P).range.comap (preparedQuadraticDetector T) := by
  let A := quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
    (biformVectorDetector T) Q P
  have hscalar : (scalarCoefficientRow (t := d-2) (c := c) Q).range≤A.range := by
    rintro y ⟨x,rfl⟩
    refine ⟨(x,0),?_⟩
    simp only [A,quadraticNuisanceRow,addRow_apply,map_zero,add_zero]
  have hprivate : (PolynomialRestoration.row
      (FullBiform K (Fin h) m 1 (d-1)).subtype (biformVectorDetector T) P).range≤A.range := by
    rintro y ⟨u,rfl⟩
    refine ⟨(0,u),?_⟩
    simp only [A,quadraticNuisanceRow,addRow_apply,map_zero,zero_add]
  have hc2 : coreCoefficientSpace K h m d 2=
      polynomialTensorSpace (Forms K h 2) (Forms K m (d-2)) := by
    have hh : 2+(d-2)=d := by omega
    simpa only [hh] using
      (coreCoefficientSpace_eq_polynomialTensorSpace (K := K) (h := h) (m := m) 2 (d-2))
  have hc1 : coreCoefficientSpace K h m d 1=
      polynomialTensorSpace (Forms K h 1) (Forms K m (d-1)) := by
    have hh : 1+(d-1)=d := by omega
    simpa only [hh] using
      (coreCoefficientSpace_eq_polynomialTensorSpace (K := K) (h := h) (m := m) 1 (d-1))
  unfold preparedProductDenominator
  apply sup_le (sup_le ?_ ?_) ?_
  · rw [hc2]
    exact (polynomialTensorSpace_product_scalar_range T Q (Forms K h 0)
      (Forms K h 2) (familySpace Q) (Forms K m (d-2)) le_rfl).trans
        (Submodule.comap_mono hscalar)
  · rw [hc1]
    exact (private_product_mem_quadratic_row T P).trans (Submodule.comap_mono hprivate)
  · intro y hy
    have hz : preparedQuadraticDetector T y=0 :=
      preparedQuadraticDetector_quadratic_product T D hD hy
    change preparedQuadraticDetector T y∈A.range
    rw [hz]
    exact Submodule.zero_mem _

theorem prepared_background_mem_quadratic_row
    (hd : 2≤d) (T : Poly K h →ₗ[K] (Fin c → K))
    (hT : T.comp (homogeneousComponent 2)=T)
    (Q : Fin q → Forms K m d) (P : Fin b → FullBiform K (Fin h) m 1 (d-1))
    (D : Submodule K (Poly K h)) (hD : D≤T.ker)
    (W : Submodule K (Forms K (h+m) d))
    (H : PreparedLowComponents W (polynomialTensorSpace (Forms K h 0) (familySpace Q))
      (Submodule.span K (Set.range (fun i => rename finSumFinEquiv (P i).val)))
      (polynomialTensorSpace D (Forms K m (d-2)))) :
    ∀ w : Forms K (h+m) d,w∈W → ∀ a : Forms K (h+m) d,
      preparedQuadraticDetector T (w.val*a.val)∈
        (quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
          (biformVectorDetector T) Q P).range := by
  let A := quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
    (biformVectorDetector T) Q P
  let R := A.range.mkQ.comp (preparedQuadraticDetector T)
  have hs : R.comp (coreComponent h m 2)=R := by
    dsimp only [R]
    rw [LinearMap.comp_assoc,preparedQuadraticDetector_supported T hT]
  have hz := prepared_background_annihilated W _ _ _ H R hs (by
    intro y hy
    exact (Submodule.Quotient.mk_eq_zero A.range).mpr
      (prepared_denominator_mem_quadratic_row hd T Q P D hD hy))
  intro w hw a
  exact (Submodule.Quotient.mk_eq_zero A.range).mp (hz w hw a)

end Froberg
