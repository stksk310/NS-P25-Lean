import NS25Lean.P2MixedKoszulLayers
import NS25Lean.P2MixedCornerCount

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.PrincipalTensorColonLayers
open L5A2BFinalRepair L5A2BFinalRepair.MixedLayers MvPolynomial
variable {k A B : Type*} [Field k] [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B]

/-- The tensor cohomology formula follows from the actual three multiplication
operators. No homological dimension or rank is a hypothesis. -/
theorem cohomology_finrank_of_operators [Module.Finite k A] [Module.Finite k B]
    (D : ℕ) (hD : 0<D) (g : Fin 3 → A) (y z : B)
    (e : A ≃ₗ[k] (Fin D → B))
    (he : ∀ t,
      e (g 0*t)=truncatedLayerShift (k:=k) D (e t) ∧
      e (g 1*t)=layerMultiply (k:=k) D y (e t) ∧
      e (g 2*t)=layerMultiply (k:=k) D z (e t)) :
    Module.finrank k (ThreeKoszulH1 (k:=k) g)=
      2*Module.finrank k (LinearMap.ker (threeKoszulD0 (k:=k) g))+
        Module.finrank k (TwoKoszulH2 (k:=k) y z) := by
  cases D with
  | zero => omega
  | succ n =>
    rw [truncatedLayerShift_eq] at he
    let e3 := LinearEquiv.piCongrRight (fun _ : Fin 3 => e)
    have c0 : ∀ t, d0 (k:=k) n y z (e t)=e3 (threeKoszulD0 (k:=k) g t) := by
      intro t
      apply funext
      intro i
      fin_cases i
      · exact (he t).1.symm
      · exact (he t).2.1.symm
      · exact (he t).2.2.symm
    have c1 : ∀ t, d1 (k:=k) n y z (e3 t)=e3 (threeKoszulD1 (k:=k) g t) := by
      intro t
      apply funext
      intro i
      fin_cases i
      · change multiply (k:=k) n y (e (t 0))-shift (k:=k) n (e (t 1))=e (g 1*t 0-g 0*t 1)
        rw [map_sub,(he (t 0)).2.1,(he (t 1)).1]
        rfl
      · change multiply (k:=k) n z (e (t 0))-shift (k:=k) n (e (t 2))=e (g 2*t 0-g 0*t 2)
        rw [map_sub,(he (t 0)).2.2,(he (t 2)).1]
        rfl
      · change multiply (k:=k) n z (e (t 1))-multiply (k:=k) n y (e (t 2))=e (g 2*t 1-g 1*t 2)
        rw [map_sub,(he (t 1)).2.2,(he (t 2)).2.1]
        rfl
    have hh1 := (cochainH1Equiv (threeKoszulD0 (k:=k) g) (threeKoszulD1 (k:=k) g)
      (d0 n y z) (d1 n y z) e e3 e3 c0 c1).finrank_eq
    have hh0 := (kernelEquiv (threeKoszulD0 (k:=k) g) (d0 n y z) e e3 c0).finrank_eq
    change Module.finrank k (ThreeKoszulH1 (k:=k) g)=
      Module.finrank k (H1 (k:=k) n y z) at hh1
    rw [hh1,hh0,cohomology_finrank_h0]

/-- The colon socle and the bivariate socle have equal dimension. -/
theorem h0_finrank_of_operators [Module.Finite k A] [Module.Finite k B]
    (D : ℕ) (hD : 0<D) (g : Fin 3 → A) (y z : B)
    (e : A ≃ₗ[k] (Fin D → B))
    (he : ∀ t,
      e (g 0*t)=truncatedLayerShift (k:=k) D (e t) ∧
      e (g 1*t)=layerMultiply (k:=k) D y (e t) ∧
      e (g 2*t)=layerMultiply (k:=k) D z (e t)) :
    Module.finrank k (LinearMap.ker (threeKoszulD0 (k:=k) g))=
      Module.finrank k (TwoKoszulH0 (k:=k) y z) := by
  cases D with
  | zero => omega
  | succ n =>
    rw [truncatedLayerShift_eq] at he
    let e3 := LinearEquiv.piCongrRight (fun _ : Fin 3 => e)
    have c0 : ∀ t, d0 (k:=k) n y z (e t)=e3 (threeKoszulD0 (k:=k) g t) := by
      intro t
      apply funext
      intro i
      fin_cases i
      · exact (he t).1.symm
      · exact (he t).2.1.symm
      · exact (he t).2.2.symm
    exact (kernelEquiv (threeKoszulD0 (k:=k) g) (d0 n y z) e e3 c0).finrank_eq.trans
      (h0Equiv (k:=k) n y z).finrank_eq

section Plane
variable (J : Ideal (MvPolynomial (Fin 3) k))

def planeGenerator (i : Fin 2) : MvPolynomial (Fin 3) k ⧸ J := Ideal.Quotient.mkₐ k J (X i.succ)

theorem plane_X_zero (hplane : ∀ a∈L3A.standardExponents J, a 0=0) :
    Ideal.Quotient.mkₐ k J (X 0)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  by_contra hn
  have hs : Finsupp.single 0 1∈L3A.standardExponents J := by
    simpa only [L3A.standardExponents,Set.mem_setOf_eq,← X_pow_eq_monomial,pow_one] using hn
  have he := hplane _ hs
  simp at he

theorem plane_H0_eq_socle (hplane : ∀ a∈L3A.standardExponents J, a 0=0) :
    TwoKoszulH0 (k:=k) (planeGenerator J 0) (planeGenerator J 1)=L3A.socle J := by
  ext z
  constructor
  · intro hz i
    have hc : ![planeGenerator J 0*z,planeGenerator J 1*z]=0 := hz
    fin_cases i
    · change Ideal.Quotient.mkₐ k J (X 0)*z=0
      rw [plane_X_zero J hplane,zero_mul]
    · exact congrFun hc 0
    · exact congrFun hc 1
  · intro hz
    change ![planeGenerator J 0*z,planeGenerator J 1*z]=0
    ext i
    fin_cases i
    · exact hz 1
    · exact hz 2

theorem monomial_le_augmentation (hmono : L2B.IsMonomialIdeal k J) (hproper : (1:MvPolynomial (Fin 3) k)∉J) :
    J≤RingHom.ker (aeval (0:Fin 3→k)).toRingHom := by
  obtain ⟨S,hS⟩ := hmono
  rw [hS]
  apply Ideal.span_le.mpr
  rintro p ⟨a,ha,rfl⟩
  have hne : a≠0 := by
    intro hz
    apply hproper
    rw [hS]
    simpa [hz] using (Ideal.subset_span (show monomial a (1:k)∈(fun b => monomial b (1:k)) '' S from ⟨a,ha,rfl⟩))
  change aeval (0:Fin 3→k) (monomial a 1)=0
  rw [aeval_zero]
  change coeff 0 (monomial a (1:k))=0
  simp [coeff_monomial,hne,Ne.symm hne]

def augmentation (hmono : L2B.IsMonomialIdeal k J) (hproper : (1:MvPolynomial (Fin 3) k)∉J) :
    (MvPolynomial (Fin 3) k ⧸ J) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (aeval (0:Fin 3→k)) (fun p hp => monomial_le_augmentation J hmono hproper hp)

theorem plane_H2_finrank (hmono : L2B.IsMonomialIdeal k J)
    (hproper : (1:MvPolynomial (Fin 3) k)∉J)
    (hplane : ∀ a∈L3A.standardExponents J, a 0=0) :
    Module.finrank k (TwoKoszulH2 (k:=k) (planeGenerator J 0) (planeGenerator J 1))=1 := by
  let q := Ideal.Quotient.mkₐ k J
  let eps := augmentation J hmono hproper
  let y := planeGenerator J 0
  let z := planeGenerator J 1
  have hy : eps y=0 := by change aeval (0:Fin 3→k) (X 1)=0; simp
  have hz : eps z=0 := by change aeval (0:Fin 3→k) (X 2)=0; simp
  have hr : LinearMap.range (twoKoszulD1 (k:=k) y z)=LinearMap.ker eps.toLinearMap := by
    apply le_antisymm
    · rintro _ ⟨a,rfl⟩
      change eps (z*a 0-y*a 1)=0
      simp [hy,hz]
    · intro b hb
      obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective k J b
      have hd : ∀ p, q p-q (C (aeval (0:Fin 3→k) p))∈LinearMap.range (twoKoszulD1 (k:=k) y z) := by
        intro p
        induction p using MvPolynomial.induction_on with
        | C a => simp [q]
        | add p r hp hr => simpa only [map_add,add_sub_add_comm] using Submodule.add_mem _ hp hr
        | mul_X p i hp =>
          simp only [map_mul,aeval_X,Pi.zero_apply,mul_zero,map_zero,sub_zero]
          fin_cases i
          · have hx : q (X 0)=0 := plane_X_zero J hplane
            change q p*q (X 0)∈_
            rw [hx,mul_zero]; exact Submodule.zero_mem _
          · exact ⟨![0,-q p],by change z*0-y*(-q p)=q p*y; ring⟩
          · exact ⟨![q p,0],by change z*q p-y*0=q p*z; ring⟩
      have he : aeval (0:Fin 3→k) p=0 := hb
      simpa only [he,map_zero,sub_zero] using hd p
  have heps : Function.Surjective eps := by
    intro a
    exact ⟨q (C a),by simp [eps,q,augmentation]⟩
  unfold TwoKoszulH2
  change Module.finrank k ((MvPolynomial (Fin 3) k ⧸ J) ⧸ LinearMap.range (twoKoszulD1 (k:=k) y z))=1
  rw [hr]
  exact (eps.toLinearMap.quotKerEquivOfSurjective heps).finrank_eq.trans (Module.finrank_self k)
end Plane

#print axioms cohomology_finrank_of_operators
#print axioms h0_finrank_of_operators
#print axioms plane_H2_finrank
end NS25Lean.PrincipalTensorColonLayers
