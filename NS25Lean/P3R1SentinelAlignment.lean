import NS25Lean.P3R1FinalCarrierR65
import NS25Lean.P3R3MixedCountR67
import NS25Lean.P3R3StaircaseCountR67

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R65
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open P3R61 P3R67 CombinatorialCore
variable {Gamma : NumericalSemigroup}

/-- CU.07/CU.11: the exact final LT floor and its real pure-principal top
sentinel give one total merge per ordinary floor minimum. No endpoint or
exceptional-status persistence is used. -/
theorem actual_lt_sentinel_merge_count (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hlevels : ∀ n, 0<n → n<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
      ∃ i j d, LTLevel M hp e n i j d)
    (k : ℕ) (hk : 0<k) (hkC : k<criticalExponent M.base (e 2))
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=
      k*routingC M.base e)
    (hdeep : ∀ n i j d, 0<n →
      n<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
      LTLevel M hp e n i j d → j<k) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    (coordinateMinima (ltFloorPoints M hp e)).card ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e)) := by
  classical
  let E := coordinateMinima (ltFloorPoints M hp e)
  let P := P3R57.roleCoefficient M hp e 0 1
  have hpB : P < criticalExponent M.base (e 1) :=
    P3R57.roleCoefficient_lt_critical M hp e 0 1 (by decide)
  have hP : 0<P := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  apply floor_staircase_sentinel_bound M hp e P (k+1) k E hpB.le (by omega)
    (Or.inl le_rfl) hP hk (by omega)
  · intro p hpE q hqE hq1 hq2
    exact ((mem_coordinateMinima _ p).mp hpE).2 q
      ((mem_coordinateMinima _ q).mp hqE).1 hq1 hq2
  · intro p hpE
    have hpL := ((mem_coordinateMinima _ p).mp hpE).1
    have hb := ltFloorPoints_bounds M hp e p hpL
    obtain ⟨n,d,hn,hnQ,hl⟩ := (mem_ltFloorPoints M hp e p).mp hpL
    exact ⟨hb.1,hb.2.2.1,hb.2.1,hdeep n p.1 p.2 d hn hnQ hl⟩
  · intro i j hi hj
    rw [final_lt_canonical_membership M hp e hQ hlevels k ht i j
      (by omega) (by omega) (Or.inl hi)]
    constructor
    · rintro (hkj | ⟨n,x,y,d,hn,hnQ,hl,hxi,hyj⟩)
      · exact ⟨(0,k),Finset.mem_insert_self _ _,by omega,hkj⟩
      · have hm : (x,y) ∈ ltFloorPoints M hp e :=
          (mem_ltFloorPoints M hp e _).mpr ⟨n,d,hn,hnQ,hl⟩
        obtain ⟨p,hpE,hpx,hpy⟩ := coordinate_minima_cover (ltFloorPoints M hp e) (x,y) hm
        exact ⟨p,Finset.mem_insert_of_mem hpE,le_trans hpx hxi,le_trans hpy hyj⟩
    · rintro ⟨p,hpS,hpi,hpj⟩
      rcases Finset.mem_insert.mp hpS with rfl | hpE
      · exact Or.inl hpj
      · have hpL := ((mem_coordinateMinima _ p).mp hpE).1
        obtain ⟨n,d,hn,hnQ,hl⟩ := (mem_ltFloorPoints M hp e p).mp hpL
        exact Or.inr ⟨n,p.1,p.2,d,hn,hnQ,hl,hpi,hpj⟩
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local notation "Z" => P3R57.roleCoefficient M hp e 2 1
local notation "W" => P3R57.roleCoefficient M hp e 2 0
local notation "B" => criticalExponent M.base (e 1)
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

/-- CU.11 applies to all actual X-target branches, independently of their
exceptional status or run length: the same bottom height crosses only once. -/
theorem actual_lt_x_target_unique (k : ℕ) (hkC : k<criticalExponent M.base (e 2))
    (hprincipal : ((k*c:ℕ):ℤ) ∈ routingI M.base e)
    (s t : ResidueData.CSourceTargetBranches (routingData M.base e))
    (hs : ∃ n i j d, LTLevel M hp e n i j d ∧
      (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s.val)=
        ltAxisA M hp e i j d)
    (ht : ∃ n i j d, LTLevel M hp e n i j d ∧
      (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget t.val)=
        ltAxisA M hp e i j d) : s=t := by
  obtain ⟨n,i,j,d,hl,hsrep⟩ := hs
  obtain ⟨n',i',j',d',hl',htrep⟩ := ht
  have hsx := routing_x_target_crossing M hp e n i j d k hl hkC hprincipal s hsrep
  have htx := routing_x_target_crossing M hp e n' i' j' d' k hl' hkC hprincipal t htrep
  have sums := P3R58.p3_coefficient_sums M hp e
  have hiB : Z+i<B := by have := hl.2.2.2.1; omega
  have hiB' : Z+i'<B := by have := hl'.2.2.2.1; omega
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hcan : ∀ q : ℕ, q<B →
      (routingH M.base e).asRelativeIdeal.aperyRepresentative a ((q*b:ℕ):ZMod a)=(q*b:ℕ) := by
    intro q hq
    have hc := P3R60.canonical_grid_value M.base e q 0
      (P3R58.p3_lshape_canonical M hp e q 0 hq (by
        have := (criticalExponent_spec M.base (e 2)).1; omega) (Or.inr hT))
    simpa only [P3R60.CanonicalValue,L5A2C4OR3.physicalAlpha,Nat.cast_zero,
      zero_mul,add_zero,Nat.cast_mul,Int.cast_natCast,Int.cast_mul] using hc
  have hidx : Z+i=Z+i' := by
    rcases lt_trichotomy (Z+i) (Z+i') with hij | heq | hji
    · have hm := bottom_height_antitone (routingI M.base e) a b (routingHB M.base e)
        (P3R63.routing_ideal_subset M.base e) (Z+i) (Z+i'-1) (by omega)
        (hcan _ hiB) (hcan _ (by omega))
      rw [htx.1] at hm
      omega
    · exact heq
    · have hm := bottom_height_antitone (routingI M.base e) a b (routingHB M.base e)
        (P3R63.routing_ideal_subset M.base e) (Z+i') (Z+i-1) (by omega)
        (hcan _ hiB') (hcan _ (by omega))
      rw [hsx.1] at hm
      omega
  have target (u : ResidueData.CSourceTargetBranches (routingData M.base e))
      (ii jj dd : ℕ)
      (hu : (routingI M.base e).aperyRepresentative a
        ((routingData M.base e).branchTarget u.val)=ltAxisA M hp e ii jj dd) :
      (routingData M.base e).branchTarget u.val=(((Z+ii)*b:ℕ):ZMod a) := by
    have hh := (routingI M.base e).aperyRepresentative_mod a
      ((routingData M.base e).branchTarget u.val)
    rw [hu] at hh
    have haZero : (a:ZMod a)=0 := ZMod.natCast_self a
    simpa only [ltAxisA,Nat.cast_add,Nat.cast_mul,Int.cast_add,Int.cast_sub,
      Int.cast_mul,Int.cast_natCast,Int.cast_zero,haZero,mul_zero,zero_mul,
      zero_add,add_zero,add_comm] using hh.symm
  apply Subtype.ext
  apply (routingData M.base e).branchTarget_injective
  rw [target s i j d hsrep,target t i' j' d' htrep,hidx]

/-- Actual final target exhaustion labels an F target by an ALL-floor minimum
and an X target by one extra label. Principal and Y targets are excluded
geometrically; the count makes no reference to exceptional branches. -/
theorem actual_lt_target_count (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, LTLevel M hp e n i j d)
    (k : ℕ) (hkC : k<criticalExponent M.base (e 2))
    (hkT : P3R57.roleCoefficient M hp e 0 2<k)
    (hkV : k≤P3R57.roleCoefficient M hp e 1 2)
    (ht : Q*M.base.q.val=k*c)
    (hdeep : ∀ n i j d, 0<n → n<Q → LTLevel M hp e n i j d → j<k) :
    ResidueData.sourceTargetBranchCount (routingData M.base e) ≤
      (coordinateMinima (ltFloorPoints M hp e)).card+1 := by
  classical
  let E := coordinateMinima (ltFloorPoints M hp e)
  let ST := ResidueData.CSourceTargetBranches (routingData M.base e)
  let IsX : ST → Prop := fun s => ∃ n i j d, LTLevel M hp e n i j d ∧
    (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s.val)=
      ltAxisA M hp e i j d
  let Spec : ST → Option {p // p∈E} → Prop := fun s z => match z with
    | none => IsX s
    | some p => (routingI M.base e).aperyRepresentative a
        ((routingData M.base e).branchTarget s.val)=(p.val.1:ℤ)*b+p.val.2*c
  have hex : ∀ s : ST, ∃ z, Spec s z := by
    intro s
    have hmin := (P3R62.routing_source_iff_minimal M.base e _).mp s.property.2
    rcases final_lt_generator_cover M hp e hQ hlevels _ hmin with hprincipalTarget | ⟨n,i,j,d,hn,hnQ,hl,hr⟩
    · exact (final_principal_not_target M hp e hQ k hkT hkV ht
        (by intro n hn hnQ; obtain ⟨i,j,d,hl⟩ := hlevels n hn hnQ
            exact ⟨i,j,d,hl,hdeep n i j d hn hnQ hl⟩) s.val s.property hprincipalTarget).elim
    · rcases hr with hF | hX | hY
      · have hpL : (i,j)∈ltFloorPoints M hp e :=
          (mem_ltFloorPoints M hp e _).mpr ⟨n,d,hn,hnQ,hl⟩
        have hmin' : (routingI M.base e).IsMinimalGenerator ((i:ℤ)*b+j*c) := hF ▸ hmin
        exact ⟨some ⟨(i,j),lt_floorpoint_minimal_coordinates M hp e _ hpL hmin'⟩,hF⟩
      · exact ⟨none,n,i,j,d,hl,hX⟩
      · exact (final_y_not_target M hp e hQ k ht hlevels n i j d hn hnQ hl
          (hdeep n i j d hn hnQ hl) s.val s.property hY).elim
  choose f hf using hex
  have hprincipal : ((k*c:ℕ):ℤ) ∈ routingI M.base e := by
    simpa [ht] using (P3R62.routing_principal_isMinimalGenerator M.base e).1
  have hinj : Function.Injective f := by
    intro s t he
    cases hfs : f s with
    | none =>
      have hft : f t=none := he.symm.trans hfs
      exact actual_lt_x_target_unique M hp e k hkC hprincipal s t
        (by simpa only [hfs,Spec] using hf s) (by simpa only [hft,Spec] using hf t)
    | some p =>
      have hft : f t=some p := he.symm.trans hfs
      have hsrep : (routingI M.base e).aperyRepresentative a
          ((routingData M.base e).branchTarget s.val)=(p.val.1:ℤ)*b+p.val.2*c := by
        simpa only [hfs,Spec] using hf s
      have htrep : (routingI M.base e).aperyRepresentative a
          ((routingData M.base e).branchTarget t.val)=(p.val.1:ℤ)*b+p.val.2*c := by
        simpa only [hft,Spec] using hf t
      have hmod := congrArg (fun z : ℤ => (z:ZMod a)) (hsrep.trans htrep.symm)
      rw [(routingI M.base e).aperyRepresentative_mod,
        (routingI M.base e).aperyRepresentative_mod] at hmod
      exact Subtype.ext ((routingData M.base e).branchTarget_injective hmod)
  have hc := Nat.card_le_card_of_injective f hinj
  change Nat.card ST ≤ E.card+1
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_coe] using hc
end

/-- The reduced R1 original-type route uses all final floor minima plus the
real top sentinel and the unique X target. No directional exceptional-count
bound is a dependency of this theorem. -/
theorem r1_original_type_via_final_sentinel (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR1 : (P3R51.internalDegrees M).card=1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma-2 := by
  obtain ⟨e,hlive,hbound,_,k,hk,hkC,ht⟩ := P3R64.r1_principal_pure_c_exists M hp hR1
  let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have htotal : ResidueData.sourceTargetBranchCount (routingData M.base e) ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e))+1 := by
    by_cases hQ : Q=1
    · have hc := P3R54.sourceTargetBranchCount_le_sourceCount (routingData M.base e)
      have hmin := normalizedSemigroup_minimal (chosenBase_minimalFour M.base e)
      have hb : routingB M.base e≠0 := by
        intro hz; apply hmin.2.2.1; simpa only [routingB,hz] using AddSubmonoid.zero_mem _
      have hcc : routingC M.base e≠0 := by
        intro hz; apply hmin.2.2.2; simpa only [routingC,hz] using AddSubmonoid.zero_mem _
      have hs := (routingI M.base e).concrete_sourceCount_eq_generatorCount
        (routingA M.base e) (routingB M.base e) (routingC M.base e) hmin.1
        (routingHB M.base e) (routingHC M.base e) hb hcc
      change (routingData M.base e).sourceCount=(routingI M.base e).generatorCount at hs
      rw [hs,P3R64.q1_routing_generatorCount M e hQ] at hc
      omega
    have hQpos := (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive).1
    have hQgt : 1<Q := by omega
    have hlevels : ∀ n, 0<n → n<Q → ∃ i j d, LTLevel M hp e n i j d := by
      intro n hn hnQ
      exact lt_level_exists M hp e n
        (all_nonprincipal_lt M hp e (hbound 1 (by decide)) (hbound 2 (by decide))
          hlive k hk ht n hn hnQ)
    have hdeep : ∀ n i j d, 0<n → n<Q → LTLevel M hp e n i j d → j<k := by
      intro n i j d hn hnQ hl
      exact (deep_lt_level M hp e (hbound 1 (by decide)) (hbound 2 (by decide))
        hlive k hk ht n i j d hn hnQ hl).2
    have hwindow := principal_window M hp e (hbound 1 (by decide)) hlive k hk ht
    have hST := actual_lt_target_count M hp e hQgt hlevels k hkC hwindow.1 hwindow.2 ht hdeep
    have hUM := actual_lt_sentinel_merge_count M hp e hQgt hlevels k hk hkC ht hdeep
    omega
  have ht' := P3R52Bridge.type_le_source_add_one_of_total_compensation M e htotal
  have hr := sourceCount_add_defect M.base
  omega
end NS25Lean.P3R65
