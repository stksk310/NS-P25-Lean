import NS25Lean.P2BranchBMixedKoszul

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair.MixedLayers
variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]

def shift (n : ℕ) : (Fin (n+1) → B) →ₗ[k] (Fin (n+1) → B) where
  toFun f := Fin.cons 0 (fun i => f i.castSucc)
  map_add' := by intro f g; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' := by intro a f; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

def multiply (n : ℕ) (b : B) : (Fin (n+1) → B) →ₗ[k] (Fin (n+1) → B) where
  toFun f i := b*f i
  map_add' := by intro f g; ext i; simp [mul_add]
  map_smul' := by intro a f; ext i; simp

def d0 (n : ℕ) (y z : B) : (Fin (n+1) → B) →ₗ[k] (Fin 3 → Fin (n+1) → B) where
  toFun f := ![shift (k:=k) n f,multiply (k:=k) n y f,multiply (k:=k) n z f]
  map_add' := by intro f g; ext i j; fin_cases i <;> simp
  map_smul' := by intro a f; ext i j; fin_cases i <;> simp

def d1 (n : ℕ) (y z : B) : (Fin 3 → Fin (n+1) → B) →ₗ[k] (Fin 3 → Fin (n+1) → B) where
  toFun f := ![multiply (k:=k) n y (f 0)-shift (k:=k) n (f 1),
    multiply (k:=k) n z (f 0)-shift (k:=k) n (f 2),
    multiply (k:=k) n z (f 1)-multiply (k:=k) n y (f 2)]
  map_add' := by intro f g; ext i j; fin_cases i <;> simp [sub_add_sub_comm]
  map_smul' := by intro a f; ext i j; fin_cases i <;> simp [smul_sub]

theorem boundaries_are_cycles (n : ℕ) (y z : B) :
    LinearMap.range (d0 (k:=k) n y z) ≤ LinearMap.ker (d1 n y z) := by
  rintro _ ⟨f,rfl⟩
  ext i j
  fin_cases i
  · refine Fin.cases ?_ (fun t => ?_) j <;> simp [d0,d1,multiply,shift]
  · refine Fin.cases ?_ (fun t => ?_) j <;> simp [d0,d1,multiply,shift]
  · simp [d0,d1,multiply]; ring

abbrev Cycles (n : ℕ) (y z : B) := LinearMap.ker (d1 (k:=k) n y z)
abbrev Boundaries (n : ℕ) (y z : B) :=
  (LinearMap.range (d0 (k:=k) n y z)).comap (Cycles (k:=k) n y z).subtype
abbrev H1 (n : ℕ) (y z : B) := Cycles (k:=k) n y z ⧸ Boundaries (k:=k) n y z

theorem cycle_y (n : ℕ) (y z : B) (f : Cycles (k:=k) n y z) (i : Fin (n+1)) :
    y*f.val 0 i=(shift (k:=k) n (f.val 1)) i := by
  have h := congrFun (congrFun f.property (0 : Fin 3)) i
  simpa [d1,multiply,sub_eq_zero] using h

theorem cycle_z (n : ℕ) (y z : B) (f : Cycles (k:=k) n y z) (i : Fin (n+1)) :
    z*f.val 0 i=(shift (k:=k) n (f.val 2)) i := by
  have h := congrFun (congrFun f.property (1 : Fin 3)) i
  simpa [d1,multiply,sub_eq_zero] using h

def cycleHead (n : ℕ) (y z : B) : Cycles (k:=k) n y z →ₗ[k] TwoKoszulH0 (k:=k) y z where
  toFun f := ⟨f.val 0 0,by
    ext i
    fin_cases i
    · simpa [twoKoszulD0,shift] using cycle_y n y z f 0
    · simpa [twoKoszulD0,shift] using cycle_z n y z f 0⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def cycleTop (n : ℕ) (y z : B) : Cycles (k:=k) n y z →ₗ[k] LinearMap.ker (twoKoszulD1 (k:=k) y z) where
  toFun f := ⟨![f.val 1 (Fin.last n),f.val 2 (Fin.last n)],by
    have h := congrFun (congrFun f.property (2 : Fin 3)) (Fin.last n)
    simpa [d1,multiply,twoKoszulD1] using h⟩
  map_add' := by intros; apply Subtype.ext; ext i; fin_cases i <;> rfl
  map_smul' := by intros; apply Subtype.ext; ext i; fin_cases i <;> rfl

def cycleProjection (n : ℕ) (y z : B) : Cycles (k:=k) n y z →ₗ[k]
    TwoKoszulH0 (k:=k) y z × TwoKoszulH1 (k:=k) y z :=
  (cycleHead n y z).prod
    (((LinearMap.range (twoKoszulD0 (k:=k) y z)).comap (LinearMap.ker (twoKoszulD1 y z)).subtype).mkQ.comp
      (cycleTop n y z))

theorem projection_boundary_zero (n : ℕ) (y z : B) (f : Cycles (k:=k) n y z)
    (hf : f ∈ Boundaries (k:=k) n y z) : cycleProjection n y z f=0 := by
  obtain ⟨w,hw⟩ := hf
  have he : d0 (k:=k) n y z w=f.val := hw
  apply Prod.ext
  · apply Subtype.ext
    change f.val 0 0=0
    rw [← he]
    simp [d0,shift]
  · apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (cycleTop n y z f).val ∈ LinearMap.range (twoKoszulD0 (k:=k) y z)
    refine ⟨w (Fin.last n),?_⟩
    ext i
    fin_cases i <;> simp [twoKoszulD0,cycleTop,← he,d0,multiply]

def cohomologyProjection (n : ℕ) (y z : B) : H1 (k:=k) n y z →ₗ[k]
    TwoKoszulH0 (k:=k) y z × TwoKoszulH1 (k:=k) y z :=
  (Boundaries (k:=k) n y z).liftQ (cycleProjection n y z) (projection_boundary_zero n y z)

theorem projection_kernel (n : ℕ) (y z : B) (f : Cycles (k:=k) n y z)
    (hf : cycleProjection n y z f=0) : f ∈ Boundaries (k:=k) n y z := by
  have hhead : f.val 0 0=0 := congrArg Subtype.val (congrArg Prod.fst hf)
  have htop := congrArg Prod.snd hf
  change Submodule.Quotient.mk (cycleTop n y z f)=0 at htop
  have ht := (Submodule.Quotient.mk_eq_zero _).mp htop
  obtain ⟨b,hb⟩ := ht
  have hb' : twoKoszulD0 (k:=k) y z b=(cycleTop n y z f).val := hb
  let w : Fin (n+1) → B := Fin.snoc (fun i => f.val 0 i.succ) b
  refine ⟨w,?_⟩
  change d0 (k:=k) n y z w=f.val
  ext i j
  fin_cases i
  · refine Fin.cases ?_ (fun t => ?_) j
    · simpa [d0,shift] using hhead.symm
    · simp [d0,shift,w]
  · refine Fin.lastCases ?_ (fun t => ?_) j
    · have h := congrFun hb' (0 : Fin 2)
      simpa [twoKoszulD0,cycleTop,d0,multiply,w] using h
    · have h := cycle_y n y z f t.succ
      simpa [d0,multiply,shift,w] using h
  · refine Fin.lastCases ?_ (fun t => ?_) j
    · have h := congrFun hb' (1 : Fin 2)
      simpa [twoKoszulD0,cycleTop,d0,multiply,w] using h
    · have h := cycle_z n y z f t.succ
      simpa [d0,multiply,shift,w] using h

def faceCycle (n : ℕ) (y z : B) (a : TwoKoszulH0 (k:=k) y z)
    (b : LinearMap.ker (twoKoszulD1 (k:=k) y z)) : Cycles (k:=k) n y z :=
  ⟨![Fin.cons a.val (fun _ => 0),Fin.snoc (fun _ => 0) (b.val 0),
    Fin.snoc (fun _ => 0) (b.val 1)],by
    ext i j
    fin_cases i
    · refine Fin.cases ?_ (fun t => ?_) j
      · have h := congrFun a.property (0 : Fin 2)
        simpa [d1,multiply,shift,twoKoszulD0] using h
      · simp [d1,multiply,shift]
    · refine Fin.cases ?_ (fun t => ?_) j
      · have h := congrFun a.property (1 : Fin 2)
        simpa [d1,multiply,shift,twoKoszulD0] using h
      · simp [d1,multiply,shift]
    · refine Fin.lastCases ?_ (fun t => ?_) j
      · simpa [d1,multiply,twoKoszulD1] using b.property
      · simp [d1,multiply]⟩

theorem projection_faceCycle (n : ℕ) (y z : B) (a : TwoKoszulH0 (k:=k) y z)
    (b : LinearMap.ker (twoKoszulD1 (k:=k) y z)) :
    cycleProjection n y z (faceCycle n y z a b)=(a,Submodule.Quotient.mk b) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [cycleProjection,cycleHead,faceCycle]
  · change Submodule.Quotient.mk (cycleTop n y z (faceCycle n y z a b))=Submodule.Quotient.mk b
    congr 1
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [cycleTop,faceCycle]

theorem cohomologyProjection_surjective (n : ℕ) (y z : B) :
    Function.Surjective (cohomologyProjection (k:=k) n y z) := by
  rintro ⟨a,b⟩
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact ⟨Submodule.Quotient.mk (faceCycle n y z a c),projection_faceCycle n y z a c⟩

theorem cohomologyProjection_injective (n : ℕ) (y z : B) :
    Function.Injective (cohomologyProjection (k:=k) n y z) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro a ha
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ a
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact projection_kernel n y z f ha

/-- The local degree-one product splitting, proved by explicit cycles and
coboundaries rather than a supplied Künneth hypothesis. -/
def cohomologyEquiv (n : ℕ) (y z : B) : H1 (k:=k) n y z ≃ₗ[k]
    TwoKoszulH0 (k:=k) y z × TwoKoszulH1 (k:=k) y z :=
  LinearEquiv.ofBijective (cohomologyProjection n y z)
    ⟨cohomologyProjection_injective n y z,cohomologyProjection_surjective n y z⟩

theorem cohomology_finrank [Module.Finite k B] (n : ℕ) (y z : B) :
    Module.finrank k (H1 (k:=k) n y z)=
      2*Module.finrank k (TwoKoszulH0 (k:=k) y z)+Module.finrank k (TwoKoszulH2 (k:=k) y z) := by
  rw [(cohomologyEquiv (k:=k) n y z).finrank_eq,Module.finrank_prod,twoKoszul_finrank_euler]
  omega

def h0Equiv (n : ℕ) (y z : B) :
    LinearMap.ker (d0 (k:=k) n y z) ≃ₗ[k] TwoKoszulH0 (k:=k) y z where
  toFun f := ⟨f.val (Fin.last n),by
    ext i
    fin_cases i
    · have h := congrFun (congrFun f.property (1 : Fin 3)) (Fin.last n)
      simpa [d0,multiply,twoKoszulD0] using h
    · have h := congrFun (congrFun f.property (2 : Fin 3)) (Fin.last n)
      simpa [d0,multiply,twoKoszulD0] using h⟩
  invFun a := ⟨Fin.snoc (fun _ => 0) a.val,by
    ext i j
    fin_cases i
    · refine Fin.cases ?_ (fun t => ?_) j <;> simp [d0,shift]
    · refine Fin.lastCases ?_ (fun t => ?_) j
      · simpa [d0,multiply,twoKoszulD0] using congrFun a.property (0 : Fin 2)
      · simp [d0,multiply]
    · refine Fin.lastCases ?_ (fun t => ?_) j
      · simpa [d0,multiply,twoKoszulD0] using congrFun a.property (1 : Fin 2)
      · simp [d0,multiply]⟩
  left_inv f := by
    apply Subtype.ext
    ext j
    refine Fin.lastCases ?_ (fun t => ?_) j
    · simp
    · have h := congrFun (congrFun f.property (0 : Fin 3)) t.succ
      simpa [d0,shift] using h.symm
  right_inv a := by apply Subtype.ext; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem cohomology_finrank_h0 [Module.Finite k B] (n : ℕ) (y z : B) :
    Module.finrank k (H1 (k:=k) n y z)=
      2*Module.finrank k (LinearMap.ker (d0 (k:=k) n y z))+
        Module.finrank k (TwoKoszulH2 (k:=k) y z) := by
  rw [(h0Equiv (k:=k) n y z).finrank_eq]
  exact cohomology_finrank n y z

section Transport
variable {V W V' W' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

def kernelEquiv (f : V →ₗ[k] W) (g : V' →ₗ[k] W') (e : V ≃ₗ[k] V') (h : W ≃ₗ[k] W')
    (commute : ∀ x, g (e x)=h (f x)) : LinearMap.ker f ≃ₗ[k] LinearMap.ker g where
  toFun x := ⟨e x.val,by change g (e x.val)=0; rw [commute,x.property,map_zero]⟩
  invFun y := ⟨e.symm y.val,by
    apply h.injective
    rw [← commute,e.apply_symm_apply,map_zero]
    exact y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply _
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply _
  map_add' := by intros; apply Subtype.ext; exact e.map_add _ _
  map_smul' := by intros; apply Subtype.ext; exact e.map_smul _ _

variable {U U' : Type*} [AddCommGroup U] [Module k U] [AddCommGroup U'] [Module k U']

theorem boundary_map (f0 : U →ₗ[k] V) (f1 : V →ₗ[k] W)
    (g0 : U' →ₗ[k] V') (g1 : V' →ₗ[k] W')
    (e0 : U ≃ₗ[k] U') (e1 : V ≃ₗ[k] V') (e2 : W ≃ₗ[k] W')
    (c0 : ∀ x, g0 (e0 x)=e1 (f0 x)) (c1 : ∀ x, g1 (e1 x)=e2 (f1 x)) :
    ((LinearMap.range f0).comap (LinearMap.ker f1).subtype).map
      (kernelEquiv f1 g1 e1 e2 c1).toLinearMap =
    (LinearMap.range g0).comap (LinearMap.ker g1).subtype := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨u,hu⟩ := hx
    refine ⟨e0 u,?_⟩
    change g0 (e0 u)=e1 x.val
    rw [c0,hu]
    rfl
  · intro y hy
    refine ⟨(kernelEquiv f1 g1 e1 e2 c1).symm y,?_,?_⟩
    · obtain ⟨u,hu⟩ := hy
      refine ⟨e0.symm u,?_⟩
      change f0 (e0.symm u)=e1.symm y.val
      apply e1.injective
      rw [← c0,e0.apply_symm_apply,hu,e1.apply_symm_apply]
      rfl
    · exact (kernelEquiv f1 g1 e1 e2 c1).apply_symm_apply y

def cochainH1Equiv (f0 : U →ₗ[k] V) (f1 : V →ₗ[k] W)
    (g0 : U' →ₗ[k] V') (g1 : V' →ₗ[k] W')
    (e0 : U ≃ₗ[k] U') (e1 : V ≃ₗ[k] V') (e2 : W ≃ₗ[k] W')
    (c0 : ∀ x, g0 (e0 x)=e1 (f0 x)) (c1 : ∀ x, g1 (e1 x)=e2 (f1 x)) :
    (LinearMap.ker f1 ⧸ (LinearMap.range f0).comap (LinearMap.ker f1).subtype) ≃ₗ[k]
    (LinearMap.ker g1 ⧸ (LinearMap.range g0).comap (LinearMap.ker g1).subtype) :=
  Submodule.Quotient.equiv _ _ (kernelEquiv f1 g1 e1 e2 c1)
    (boundary_map f0 f1 g0 g1 e0 e1 e2 c0 c1)
end Transport

theorem truncatedLayerShift_eq (n : ℕ) :
    truncatedLayerShift (k:=k) (V:=B) (n+1)=shift (k:=k) n := by
  apply LinearMap.ext
  intro f
  apply funext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [truncatedLayerShift,shift]
  · simp [truncatedLayerShift,shift]
    rfl

end NS25Lean.L5A2BFinalRepair.MixedLayers

namespace NS25Lean.L5A2BFinalRepair
open L5A1 L5A2B4AR1 L5A2B4AR4R1 MixedLayers ToricPresentation
variable {k : Type*} [Field k] {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Actual mixed colon formula. Neither BAL nor a supplied tensor/cohomology
formula is a premise: actual tail actions were proved on the standard basis. -/
theorem nonsymmetric_principal_colon_koszulH1_finrank
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (nonsymmetricPrincipalColonH1 (k:=k) R hQ)=
      2*Module.finrank k (nonsymmetricPrincipalColonH0 (k:=k) R hQ)+1 := by
  letI := nonsymmetric_colon_finite (k:=k) R hQ
  letI := nonsymmetric_bivariate_finite (k:=k) R hB hQ
  have packet := nonsymmetric_layer_operator_packet (k:=k) R hB hQ
  generalize hD : nonsymmetricDa R hB hQ=D at packet
  cases D with
  | zero => have := nonsymmetricDa_positive R hB hQ; omega
  | succ n =>
    obtain ⟨e,he⟩ := packet
    rw [truncatedLayerShift_eq] at he
    let y := nonsymmetricBivariateGenerator (k:=k) R hB hQ 0
    let z := nonsymmetricBivariateGenerator (k:=k) R hB hQ 1
    let g := nonsymmetricColonGenerators (k:=k) R hQ
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
    change Module.finrank k (nonsymmetricPrincipalColonH1 (k:=k) R hQ)=
      Module.finrank k (H1 (k:=k) n y z) at hh1
    change Module.finrank k (nonsymmetricPrincipalColonH0 (k:=k) R hQ)=
      Module.finrank k (LinearMap.ker (d0 (k:=k) n y z)) at hh0
    rw [hh1,hh0,cohomology_finrank_h0]
    exact congrArg (fun a => 2*Module.finrank k (LinearMap.ker (d0 (k:=k) n y z))+a)
      (nonsymmetric_bivariate_koszulH2_finrank R hB hQ)

abbrev nonsymmetricPrincipalPrefixQuotient
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  SemigroupAlgebra k (nsH R).toAddSubmonoid ⧸ carrierMonomialIdeal k (nonsymmetricPrefixIdeal R hQ)

def nonsymmetricPrincipalInjection
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrincipalColonQuotient k R hQ →ₗ[k] nonsymmetricPrincipalPrefixQuotient (k:=k) R hQ :=
  principalColonInjection (carrierMonomialIdeal k (nonsymmetricPrefixIdeal R hQ))
    (AddMonoidAlgebra.single (nonsymmetricPrincipalDegree R) 1)

theorem nonsymmetricPrincipalInjection_injective
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricPrincipalInjection (k:=k) R hQ) :=
  principalColonInjection_injective _ _

def nonsymmetricPrefixGenerators
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) :
    nonsymmetricPrincipalPrefixQuotient (k:=k) R hQ :=
  Ideal.Quotient.mkₐ k (carrierMonomialIdeal k (nonsymmetricPrefixIdeal R hQ))
    (AddMonoidAlgebra.single (nonsymmetricTailMonomialDegree R i) 1)

theorem nonsymmetricPrincipalInjection_generator
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3)
    (z : nonsymmetricPrincipalColonQuotient k R hQ) :
    nonsymmetricPrincipalInjection (k:=k) R hQ (nonsymmetricColonGenerators R hQ i*z)=
      nonsymmetricPrefixGenerators R hQ i*nonsymmetricPrincipalInjection R hQ z := by
  refine Quotient.inductionOn' z ?_
  intro p
  change Ideal.Quotient.mk _ (_*(_*p))=Ideal.Quotient.mk _ (_*(_*p))
  congr 1
  ring

abbrev nonsymmetricPrincipalPrefixH1
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  ThreeKoszulH1 (k:=k) (nonsymmetricPrefixGenerators (k:=k) R hQ)

def nonsymmetricPrincipalComparisonCycles
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.ker (threeKoszulD1 (k:=k) (nonsymmetricColonGenerators (k:=k) R hQ)) →ₗ[k]
      LinearMap.ker (threeKoszulD1 (k:=k) (nonsymmetricPrefixGenerators (k:=k) R hQ)) where
  toFun z := ⟨fun i => nonsymmetricPrincipalInjection R hQ (z.val i),by
    have hc := z.property
    ext i
    fin_cases i
    · simpa [threeKoszulD1,map_sub,nonsymmetricPrincipalInjection_generator] using
        congrArg (nonsymmetricPrincipalInjection (k:=k) R hQ) (congrFun hc (0 : Fin 3))
    · simpa [threeKoszulD1,map_sub,nonsymmetricPrincipalInjection_generator] using
        congrArg (nonsymmetricPrincipalInjection (k:=k) R hQ) (congrFun hc (1 : Fin 3))
    · simpa [threeKoszulD1,map_sub,nonsymmetricPrincipalInjection_generator] using
        congrArg (nonsymmetricPrincipalInjection (k:=k) R hQ) (congrFun hc (2 : Fin 3))
    ⟩
  map_add' := by
    intro z w; apply Subtype.ext; ext i
    exact (nonsymmetricPrincipalInjection (k:=k) R hQ).map_add (z.val i) (w.val i)
  map_smul' := by
    intro a z; apply Subtype.ext; ext i
    exact (nonsymmetricPrincipalInjection (k:=k) R hQ).map_smul a (z.val i)

def nonsymmetricPrincipalComparisonPre
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.ker (threeKoszulD1 (k:=k) (nonsymmetricColonGenerators (k:=k) R hQ)) →ₗ[k]
      nonsymmetricPrincipalPrefixH1 (k:=k) R hQ :=
  (((LinearMap.range (threeKoszulD0 (k:=k) (nonsymmetricPrefixGenerators R hQ))).comap
    (LinearMap.ker (threeKoszulD1 (k:=k) (nonsymmetricPrefixGenerators R hQ))).subtype).mkQ).comp
      (nonsymmetricPrincipalComparisonCycles R hQ)

theorem nonsymmetricPrincipalComparisonPre_boundary_zero
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base)
    (z : LinearMap.ker (threeKoszulD1 (k:=k) (nonsymmetricColonGenerators R hQ)))
    (hz : z ∈ (LinearMap.range (threeKoszulD0 (k:=k) (nonsymmetricColonGenerators R hQ))).comap
      (LinearMap.ker (threeKoszulD1 (k:=k) (nonsymmetricColonGenerators R hQ))).subtype) :
    nonsymmetricPrincipalComparisonPre (k:=k) R hQ z=0 := by
  obtain ⟨w,hw⟩ := hz
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (fun i => nonsymmetricPrincipalInjection R hQ (z.val i)) ∈
    LinearMap.range (threeKoszulD0 (k:=k) (nonsymmetricPrefixGenerators R hQ))
  refine ⟨nonsymmetricPrincipalInjection R hQ w,?_⟩
  have he : threeKoszulD0 (k:=k) (nonsymmetricColonGenerators R hQ) w=z.val := hw
  rw [← he]
  ext i
  exact (nonsymmetricPrincipalInjection_generator R hQ i w).symm

/-- The actual comparison H1(T) → H1(Bminus) induced by multiplication
by the actual principal monomial Q*m. No rank bound is stored in its data. -/
def nonsymmetricPrincipalComparisonH1
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrincipalColonH1 (k:=k) R hQ →ₗ[k] nonsymmetricPrincipalPrefixH1 (k:=k) R hQ :=
  ((LinearMap.range (threeKoszulD0 (k:=k) (nonsymmetricColonGenerators R hQ))).comap
    (LinearMap.ker (threeKoszulD1 (k:=k) (nonsymmetricColonGenerators R hQ))).subtype).liftQ
      (nonsymmetricPrincipalComparisonPre R hQ)
      (nonsymmetricPrincipalComparisonPre_boundary_zero R hQ)

theorem nonsymmetric_principal_colon_koszulH0_bivariate_finrank
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (nonsymmetricPrincipalColonH0 (k:=k) R hQ)=
      Module.finrank k (nonsymmetricBivariateH0 (k:=k) R hB hQ) := by
  have packet := nonsymmetric_layer_operator_packet (k:=k) R hB hQ
  generalize hD : nonsymmetricDa R hB hQ=D at packet
  cases D with
  | zero => have := nonsymmetricDa_positive R hB hQ; omega
  | succ n =>
    obtain ⟨e,he⟩ := packet
    rw [truncatedLayerShift_eq] at he
    let y := nonsymmetricBivariateGenerator (k:=k) R hB hQ 0
    let z := nonsymmetricBivariateGenerator (k:=k) R hB hQ 1
    let g := nonsymmetricColonGenerators (k:=k) R hQ
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

section CornerDetection
variable {H : NumericalSemigroup}

def carrierRawCoefficient (h : H.toAddSubmonoid) : SemigroupAlgebra k H.toAddSubmonoid →ₗ[k] k where
  toFun p := p.coeff h
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Homogeneous coefficient on an actual surviving degree, descended through
the carrier ideal rather than chosen on polynomial representatives. -/
def carrierCoefficient (I : RelativeIdeal H) (h : H.toAddSubmonoid) (hh : (h.val : ℤ) ∉ I) :
    (SemigroupAlgebra k H.toAddSubmonoid ⧸ carrierMonomialIdeal k I) →ₗ[k] k :=
  ((carrierMonomialIdeal k I).restrictScalars k).liftQ (carrierRawCoefficient h) (by
    intro p hp
    change p.coeff h=0
    by_contra hn
    exact hh ((carrierMonomialIdeal_mem_iff I p).mp hp h (Finsupp.mem_support_iff.mpr hn)))

theorem carrierCoefficient_mul (I : RelativeIdeal H) (h g : H.toAddSubmonoid)
    (hh : (h.val : ℤ) ∉ I) (hg : ((h+g).val : ℤ) ∉ I)
    (w : SemigroupAlgebra k H.toAddSubmonoid ⧸ carrierMonomialIdeal k I) :
    carrierCoefficient (k:=k) I (h+g) hg
      (carrierMonomialClass (k:=k) I g*w)=carrierCoefficient (k:=k) I h hh w := by
  refine Quotient.inductionOn' w ?_
  intro p
  change (AddMonoidAlgebra.single g (1 : k)*p).coeff (h+g)=p.coeff h
  rw [add_comm,AddMonoidAlgebra.coeff_single_mul_add,one_mul]

theorem carrierCoefficient_class (I : RelativeIdeal H) (h t : H.toAddSubmonoid)
    (hh : (h.val : ℤ) ∉ I) :
    carrierCoefficient (k:=k) I h hh (carrierMonomialClass (k:=k) I t)=
      if t=h then 1 else 0 := by
  classical
  change (AddMonoidAlgebra.single t (1 : k)).coeff h=_
  change (Finsupp.single t (1 : k)) h=_
  simp only [Finsupp.single_apply]

def carrierCornerDetectionPre (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid)
    (h : H.toAddSubmonoid) (hb : ((h+g 1).val : ℤ) ∉ I) (hc : ((h+g 2).val : ℤ) ∉ I) :
    LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g)) →ₗ[k] k :=
  ((carrierCoefficient (k:=k) I (h+g 2) hc).comp
      ((LinearMap.proj 2).comp (LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g))).subtype)) -
    ((carrierCoefficient (k:=k) I (h+g 1) hb).comp
      ((LinearMap.proj 1).comp (LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g))).subtype))

theorem carrierCornerDetectionPre_boundary_zero (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid)
    (h : H.toAddSubmonoid) (hh : (h.val : ℤ) ∉ I)
    (hb : ((h+g 1).val : ℤ) ∉ I) (hc : ((h+g 2).val : ℤ) ∉ I)
    (z : LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g)))
    (hz : z ∈ (LinearMap.range (threeKoszulD0 (k:=k) (carrierGenerators (k:=k) I g))).comap
      (LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g))).subtype) :
    carrierCornerDetectionPre (k:=k) I g h hb hc z=0 := by
  obtain ⟨w,hw⟩ := hz
  have he : threeKoszulD0 (k:=k) (carrierGenerators (k:=k) I g) w=z.val := hw
  change carrierCoefficient (k:=k) I (h+g 2) hc (z.val 2)-
    carrierCoefficient (k:=k) I (h+g 1) hb (z.val 1)=0
  rw [← he]
  change carrierCoefficient (k:=k) I (h+g 2) hc (carrierMonomialClass I (g 2)*w)-
    carrierCoefficient (k:=k) I (h+g 1) hb (carrierMonomialClass I (g 1)*w)=0
  rw [carrierCoefficient_mul I h (g 2) hh hc,carrierCoefficient_mul I h (g 1) hh hb,sub_self]

/-- The K5 homogeneous detector: it annihilates actual D0 boundaries. -/
def carrierCornerDetection (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid)
    (h : H.toAddSubmonoid) (hh : (h.val : ℤ) ∉ I)
    (hb : ((h+g 1).val : ℤ) ∉ I) (hc : ((h+g 2).val : ℤ) ∉ I) :
    ThreeKoszulH1 (k:=k) (carrierGenerators (k:=k) I g) →ₗ[k] k :=
  ((LinearMap.range (threeKoszulD0 (k:=k) (carrierGenerators (k:=k) I g))).comap
    (LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g))).subtype).liftQ
      (carrierCornerDetectionPre I g h hb hc)
      (carrierCornerDetectionPre_boundary_zero I g h hh hb hc)

theorem carrierCornerDetection_nonzero (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid)
    (h : H.toAddSubmonoid) (hh : (h.val : ℤ) ∉ I)
    (hb : ((h+g 1).val : ℤ) ∉ I) (hc : ((h+g 2).val : ℤ) ∉ I)
    (z : LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g)))
    (hz1 : z.val 1=0) (hz2 : z.val 2=carrierMonomialClass (k:=k) I (h+g 2)) :
    (Submodule.Quotient.mk z : ThreeKoszulH1 (k:=k) (carrierGenerators (k:=k) I g))≠0 := by
  intro he
  have hd := congrArg (carrierCornerDetection (k:=k) I g h hh hb hc) he
  rw [map_zero] at hd
  change carrierCoefficient (k:=k) I (h+g 2) hc (z.val 2)-
    carrierCoefficient (k:=k) I (h+g 1) hb (z.val 1)=0 at hd
  rw [hz1,hz2,carrierCoefficient_class,map_zero] at hd
  simp at hd
end CornerDetection

end NS25Lean.L5A2BFinalRepair
