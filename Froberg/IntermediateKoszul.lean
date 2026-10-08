import Froberg.OuterMultiplication
import Froberg.BilinearScalarFamily

/-! Injectivity in the new-layer quotient is equivalent to the exact
constant scalar-layer Koszul kernel before taking the quotient. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg.AttachedMultiplication
open Module MvPolynomial
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
variable {n s d q : ℕ}

/-- Multiply a degree-zero coefficient by a fixed homogeneous form. -/
def constantMul (f : Forms K n d) : Forms K n 0 →ₗ[K] Forms K n d where
  toFun c := ⟨f.val*c.val,by simpa using f.property.mul c.property⟩
  map_add' a b := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' k a := by apply Subtype.ext; exact mul_smul_comm _ _ _

@[simp] theorem constantMul_val (f : Forms K n d) (c : Forms K n 0) :
    (constantMul f c).val=f.val*c.val := rfl

theorem vectorMultiply_constantRelation (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree=s) (f : Forms K n d) (c : I → Forms K n 0) :
    vectorMultiply f (homogeneousMultiplication (d := 0) e v he c) =
      homogeneousMultiplication e v he (fun i => constantMul f (c i)) := by
  funext j
  apply Subtype.ext
  simp only [vectorMultiply_val,homogeneousMultiplication_val,multiplication_apply,constantMul_val,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The scalar part plus the new-layer part of a single polynomial row. -/
def intermediateRow (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree=s) (Q : Fin q → Forms K n d) :
    ((Fin q → J → Forms K n s) × (I → Forms K n d)) →ₗ[K] (J → Forms K n (s+d)) where
  toFun x := BilinearScalarFamily.multiplication vectorMultiply Q x.1 +
    homogeneousMultiplication e v he x.2
  map_add' x y := by
    change BilinearScalarFamily.multiplication vectorMultiply Q (x.1+y.1) +
      homogeneousMultiplication e v he (x.2+y.2) = _
    rw [map_add,map_add]
    change _ = (BilinearScalarFamily.multiplication vectorMultiply Q x.1 + homogeneousMultiplication e v he x.2) +
      (BilinearScalarFamily.multiplication vectorMultiply Q y.1 + homogeneousMultiplication e v he y.2)
    abel
  map_smul' c x := by
    change BilinearScalarFamily.multiplication vectorMultiply Q (c • x.1) +
      homogeneousMultiplication e v he (c • x.2) = _
    rw [map_smul,map_smul]
    exact (smul_add c _ _).symm

/-- The literal constant scalar-layer Koszul map. -/
def intermediateKoszul (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree=s) (Q : Fin q → Forms K n d) :
    (Fin q → I → Forms K n 0) →ₗ[K]
      ((Fin q → J → Forms K n s) × (I → Forms K n d)) where
  toFun c := (fun i => homogeneousMultiplication (d := 0) e v he (c i),
    -∑ i, fun a => constantMul (Q i) (c i a))
  map_add' c c' := by
    apply Prod.ext
    · funext i
      change homogeneousMultiplication e v he (c i+c' i) = _
      exact map_add _ _ _
    · funext a
      simp only [Prod.snd_add,Pi.add_apply,Pi.neg_apply,Finset.sum_apply,
        map_add,Finset.sum_add_distrib,neg_add]
  map_smul' k c := by
    apply Prod.ext
    · funext i
      change homogeneousMultiplication e v he (k • c i) = k • homogeneousMultiplication e v he (c i)
      exact map_smul _ _ _
    · funext a
      simp only [Prod.smul_snd,Pi.smul_apply,Pi.neg_apply,Finset.sum_apply,RingHom.id_apply,
        map_smul,← Finset.smul_sum,smul_neg]

/-- Every prescribed constant Koszul vector is an actual polynomial relation. -/
theorem intermediateRow_koszul (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree=s) (Q : Fin q → Forms K n d)
    (c : Fin q → I → Forms K n 0) :
    intermediateRow e v he Q (intermediateKoszul e v he Q c)=0 := by
  change BilinearScalarFamily.multiplication vectorMultiply Q
    (fun i => homogeneousMultiplication (d := 0) e v he (c i)) +
      homogeneousMultiplication e v he (-∑ i, fun a => constantMul (Q i) (c i a))=0
  rw [BilinearScalarFamily.multiplication_apply,map_neg,map_sum]
  simp_rw [vectorMultiply_constantRelation]
  exact add_neg_cancel _

/-- Scalar injectivity in the quotient and layer injectivity give precisely
the constant Koszul kernel, with no other relations. -/
theorem intermediateRow_ker_eq_koszul (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree=s) (Q : Fin q → Forms K n d)
    (hE : Function.Injective (multiplication (d := d) e v))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply e v he) Q)) :
    (intermediateRow e v he Q).ker = (intermediateKoszul e v he Q).range := by
  apply le_antisymm
  · rintro x hx
    have hquot : BilinearScalarFamily.multiplication (quotientMultiply e v he) Q
        (fun i => (relationSpace (d := 0) e v he).mkQ (x.1 i))=0 := by
      have hz := congrArg (relationSpace (d := d) e v he).mkQ hx
      change (relationSpace (d := d) e v he).mkQ
        (BilinearScalarFamily.multiplication vectorMultiply Q x.1 + homogeneousMultiplication e v he x.2) = _ at hz
      rw [map_add] at hz
      have he0 : (relationSpace (d := d) e v he).mkQ (homogeneousMultiplication e v he x.2)=0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨x.2,rfl⟩
      rw [he0,add_zero,map_zero] at hz
      simpa only [BilinearScalarFamily.multiplication_apply,map_sum,quotientMultiply_mk] using hz
    have hxzero : (fun i => (relationSpace (d := 0) e v he).mkQ (x.1 i))=0 :=
      hQ (hquot.trans (map_zero _).symm)
    have hconst (i : Fin q) : ∃ c : I → Forms K n 0,
        homogeneousMultiplication e v he c=x.1 i := by
      exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun hxzero i)
    choose c hc using hconst
    refine ⟨c,?_⟩
    apply Prod.ext
    · funext i
      exact hc i
    · have hz := intermediateRow_koszul e v he Q c
      have hfirst : (intermediateKoszul e v he Q c).1=x.1 := funext hc
      change BilinearScalarFamily.multiplication vectorMultiply Q (intermediateKoszul e v he Q c).1 +
        homogeneousMultiplication e v he (intermediateKoszul e v he Q c).2=0 at hz
      rw [hfirst] at hz
      change BilinearScalarFamily.multiplication vectorMultiply Q x.1 +
        homogeneousMultiplication e v he x.2=0 at hx
      apply homogeneousMultiplication_injective e v he hE
      exact add_left_cancel (hz.trans hx.symm)
  · rintro x ⟨c,rfl⟩
    exact intermediateRow_koszul e v he Q c

/-- Independence of the layer at coefficient degree zero also proves that
the prescribed constant Koszul source has its stated dimension. -/
theorem intermediateKoszul_injective (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree=s) (Q : Fin q → Forms K n d)
    (hE : Function.Injective (multiplication (d := 0) e v)) :
    Function.Injective (intermediateKoszul e v he Q) := by
  intro c c' h
  have hfirst := congrArg Prod.fst h
  funext i
  exact homogeneousMultiplication_injective e v he hE (congrFun hfirst i)

end Froberg.AttachedMultiplication
