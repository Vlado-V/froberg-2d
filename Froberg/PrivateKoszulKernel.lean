import Froberg.PrivateAlternatingKernel

/-! The endpoint kernel of the private-power row is exactly its constant
Koszul space, once the actual quadratic detector preserves pair overlaps. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PrivateColumns
open MvPolynomial Module
variable {K : Type*} [Field K] {a z s b h c : ℕ}

/-- A private generator in vector-valued scalar-polynomial coordinates. -/
def privateGenerator (ι : Fin b ↪ Fin z) (w : Fin b → Fin h → K)
    (i : Fin b) : Fin h → Forms K (a+z) s := fun j =>
  ⟨monomial (privateExponent a s ι i) (w i j),
    isHomogeneous_monomial _ (privateExponent_degree ι i)⟩

lemma privateGenerator_coefficient (hs : 0<s) (ι : Fin b ↪ Fin z)
    (w : Fin b → Fin h → K) (i j : Fin b) :
    (fun k => (privateGenerator (a := a) (s := s) ι w j k).val.coeff
      (privateExponent a s ι i)) = if i=j then w i else 0 := by
  classical
  funext k
  change (monomial (privateExponent a s ι j) (w j k)).coeff
    (privateExponent a s ι i) = _
  by_cases hij : i=j
  · subst j
    simp only [coeff_monomial,ite_true]
  · have he : privateExponent a s ι j ≠ privateExponent a s ι i :=
      fun he => hij ((privateExponent_injective hs ι he).symm)
    simp [coeff_monomial,he,hij]

lemma privateGenerator_linearIndependent (hs : 0<s) (ι : Fin b ↪ Fin z)
    (w : Fin b → Fin h → K) (dual : Fin b → (Fin h → K) →ₗ[K] K)
    (hdual : ∀ i, dual i (w i)=1) :
    LinearIndependent K (privateGenerator (a := a) (s := s) ι w) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro t ht i
  have hh := congrArg (fun v : Fin h → Forms K (a+z) s =>
    dual i (fun k => (v k).val.coeff (privateExponent a s ι i))) ht
  have hcoeff : (fun k => ((∑ j, t j • privateGenerator (a := a) (s := s) ι w j) k).val.coeff
      (privateExponent a s ι i)) = t i • w i := by
    funext k
    simp only [Finset.sum_apply,Pi.smul_apply,Submodule.coe_sum,Submodule.coe_smul,
      coeff_sum,coeff_smul]
    have hc (j : Fin b) := congrFun (privateGenerator_coefficient (a := a) hs ι w i j) k
    simp only [ite_apply,Pi.zero_apply] at hc
    simp_rw [hc]
    simp
  rw [hcoeff,map_smul,hdual,smul_eq_mul,mul_one] at hh
  simp only [Pi.zero_apply,Submodule.coe_zero,MvPolynomial.coeff_zero,Finsupp.zero_apply] at hh
  change t i=dual i 0 at hh
  simpa only [map_zero] using hh

lemma private_product_expansion (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K)) (w : Fin b → Fin h → K)
    (i j : Fin b) (k : Fin c) :
    (∑ l, monomial (privateExponent a s ι i) (A i (Pi.single l 1) k) *
      (privateGenerator (a := a) (s := s) ι w j l).val) =
      monomial (privateExponent a s ι i+privateExponent a s ι j) (A i (w j) k) := by
  change (∑ l, monomial _ _ * monomial _ _) = _
  simp_rw [monomial_mul]
  rw [← map_sum]
  congr 1
  rw [pi_linear_expansion]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

lemma privatePolynomialMap_single (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (i : Fin b) (v : Fin h → Forms K (a+z) s) (k : Fin c) :
    privatePolynomialMap ι A (Pi.single i v) k =
      ∑ l,monomial (privateExponent a s ι i) (A i (Pi.single l 1) k)*(v l).val := by
  classical
  dsimp only [privatePolynomialMap,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_apply,hji]
  · simp

/-- Commutativity of the detected output products gives actual private-row boundaries. -/
theorem privatePolynomialMap_koszul (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K)) (w : Fin b → Fin h → K)
    (hcomm : ∀ i j, A i (w j)=A j (w i)) (p : GeneratorPair b) :
    privatePolynomialMap (a := a) (s := s) ι A
      (koszulVector (privateGenerator (a := a) (s := s) ι w) p)=0 := by
  classical
  have hk : koszulVector (privateGenerator (a := a) (s := s) ι w) p =
      Pi.single p.val.1 (privateGenerator (a := a) (s := s) ι w p.val.2)-
        Pi.single p.val.2 (privateGenerator (a := a) (s := s) ι w p.val.1) := by
    funext i
    simp only [koszulVector,Pi.sub_apply,Pi.single_apply]
  rw [hk,map_sub]
  funext k
  simp only [Pi.sub_apply,Pi.zero_apply,privatePolynomialMap_single,
    private_product_expansion]
  rw [hcomm p.val.1 p.val.2,
    add_comm (privateExponent a s ι p.val.1) (privateExponent a s ι p.val.2)]
  exact sub_self _

/-- Exact endpoint kernel of the private-power row. -/
theorem privatePolynomialMap_kernel_eq_koszul (hs : 0<s) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i, Function.Injective (A i)) (w : Fin b → Fin h → K)
    (dual : Fin b → (Fin h → K) →ₗ[K] K) (hdual : ∀ i, dual i (w i)=1)
    (hcomm : ∀ i j, A i (w j)=A j (w i))
    (hpair : ∀ p : GeneratorPair b, ∀ x y,
      A p.val.1 x+A p.val.2 y=0 → ∃ t : K,
        x=t • w p.val.2 ∧ y=(-t) • w p.val.1) :
    (privatePolynomialMap (a := a) (s := s) ι A).ker =
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := s) ι w))) := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    exact privatePolynomialMap_koszul ι A w hcomm p
  · have hdim := privatePolynomialMap_kernel_finrank_le (a := a) hs ι A hA w dual hdual hpair
    rw [finrank_span_eq_card (koszulVector_linearIndependent _
      (privateGenerator_linearIndependent hs ι w dual hdual)),card_generatorPair]
    exact hdim

/-- Explicit alternating coefficient vector for every private-row cycle. -/
theorem privatePolynomialMap_cycle_coefficients (hs : 0<s) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i, Function.Injective (A i)) (w : Fin b → Fin h → K)
    (dual : Fin b → (Fin h → K) →ₗ[K] K) (hdual : ∀ i, dual i (w i)=1)
    (hcomm : ∀ i j, A i (w j)=A j (w i))
    (hpair : ∀ p : GeneratorPair b, ∀ x y,
      A p.val.1 x+A p.val.2 y=0 → ∃ t : K,
        x=t • w p.val.2 ∧ y=(-t) • w p.val.1)
    (v : Fin b → Fin h → Forms K (a+z) s)
    (hv : privatePolynomialMap ι A v=0) :
    ∃ c : GeneratorPair b → K,
      v=∑ p, c p • koszulVector (privateGenerator (a := a) (s := s) ι w) p := by
  have hmem : v ∈ (privatePolynomialMap (a := a) (s := s) ι A).ker := hv
  rw [privatePolynomialMap_kernel_eq_koszul hs ι A hA w dual hdual hcomm hpair] at hmem
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  exact ⟨c,hc.symm⟩

end Froberg.PrivateColumns
