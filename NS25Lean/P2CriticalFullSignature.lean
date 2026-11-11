import NS25Lean.P2GenericCriticalCompensation
import NS25Lean.P2CriticalModeBounds
import NS25Lean.SharedTailModePresentation

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalFullSignature
open Classical FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen
  ReturnSourceRigidity ReturnPresentationAdapter PureInternalTransverse CriticalNormalForm
  CriticalShortFibers CriticalCapGeometry CriticalPresentationModes CriticalForwardExchange
  CriticalCapSources CriticalReverseExchange CriticalCapAttainment GenericCriticalCompensation

/-- The actual surviving boundary side; `true` selects the positive mixed side. -/
def endpoint {H : NumericalSemigroup} {B : Base H} (D : Mode B) (mixed : Bool) : Exponent :=
  match D with
  | .positive _ _ w z _ _ _ _ _ _ _ _ _ => if mixed then vector w z 0 else vector 0 0 B.L
  | .purePair _ => vector 0 0 B.L

def boundaryGuards {H : NumericalSemigroup} {B : Base H} (D : Mode B) (mixed : Bool) : Prop :=
  match D with
  | .positive _ _ w z _ _ _ _ _ _ _ _ _ =>
      if mixed then (B.L-1)*B.triple.g 2∈B.K ∧
        B.triple.weight (vector (w-1) z 0)∉B.K ∧ B.triple.weight (vector w (z-1) 0)∉B.K
      else (B.L-1)*B.triple.g 2∉B.K ∧ boundaryKilled D
  | .purePair _ => mixed=false ∧ (B.L-1)*B.triple.g 2∉B.K

/-- Local critical predecessor signs, all in the actual cyclic cut.
No normal uniqueness, cap, rectangle, attainment, or count is input. -/
structure Front {H : NumericalSemigroup} (B : Base H) (D : Mode B) where
  mixed : Bool
  axis_killed : (B.R-1)*B.triple.g 0∈B.K
  pure_b_live : (B.C-1)*B.triple.g 1∉B.K
  mixed_x_live : (B.u-1)*B.triple.g 0+B.v*B.triple.g 2∉B.K
  mixed_z_live : B.u*B.triple.g 0+(B.v-1)*B.triple.g 2∉B.K
  inactive_killed : inactiveKilled D
  boundary : boundaryGuards D mixed

theorem Front.coefficient_bounds {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : B.u<B.R ∧ B.v<B.L := by
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary => omega
  | purePair hpair =>
    have hv := CriticalModeBounds.pure_pair_v_lt B.triple B.m B.R B.L B.u B.v
      (B.critical.positive 0) B.u_pos hpair F.axis_killed F.mixed_x_live
    obtain ⟨s,a,hap,haR,ha⟩ := B.axis_source F.axis_killed
    have hu : B.u<a := by
      by_contra hn
      have hle : a≤B.u := by omega
      have hk := weight_cut_upward B.triple B.m ((B.norm_degree s).symm ▸ s.property.1)
        (show B.norm s≤vector B.u 0 (B.v-1) by
          rw [ha]; intro i; fin_cases i <;> simp_all)
      exact F.mixed_z_live (by simpa [vector_weight,Triple.grid] using hk)
    exact ⟨lt_trans hu haR,hv⟩

theorem Front.boundary_degree_proper {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : ∃ p∈B.K, ∃ g∈H, 0<g ∧ B.L*B.triple.g 2=p+g := by
  have hL : 0<B.L := B.critical.positive 2
  cases D with
  | positive p q w z hp hq hw hz hR hC hLsum hcenter hboundary =>
    cases hm : F.mixed with
    | true =>
      have hb : (B.L-1)*B.triple.g 2∈B.K ∧
          B.triple.weight (vector (w-1) z 0)∉B.K ∧ B.triple.weight (vector w (z-1) 0)∉B.K := by
        simpa [boundaryGuards,hm] using F.boundary
      have hk := hb.1
      refine ⟨(B.L-1)*B.triple.g 2,hk,B.triple.g 2,?_,B.triple.positive 2,?_⟩
      · simpa [B.triple.weight_single] using B.triple.member (Finsupp.single 2 1)
      · have h := congrArg (fun n => n*B.triple.g 2) (Nat.sub_add_cancel hL)
        simpa [Nat.add_mul] using h.symm
    | false =>
      have hb : (B.L-1)*B.triple.g 2∉B.K ∧
          boundaryKilled (.positive p q w z hp hq hw hz hR hC hLsum hcenter hboundary : Mode B) := by
        simpa [boundaryGuards,hm] using F.boundary
      have hk := hb.2
      rcases hk with hk | hk
      · refine ⟨B.triple.weight (vector (w-1) z 0),hk,B.triple.g 0,?_,B.triple.positive 0,?_⟩
        · simpa [B.triple.weight_single] using B.triple.member (Finsupp.single 0 1)
        · rw [vector_weight,Triple.grid]
          have h := congrArg (fun n => n*B.triple.g 0) (Nat.sub_add_cancel hw)
          simp only [Nat.add_mul,one_mul] at h
          nlinarith only [hboundary,h]
      · refine ⟨B.triple.weight (vector w (z-1) 0),hk,B.triple.g 1,?_,B.triple.positive 1,?_⟩
        · simpa [B.triple.weight_single] using B.triple.member (Finsupp.single 1 1)
        · rw [vector_weight,Triple.grid]
          have h := congrArg (fun n => n*B.triple.g 1) (Nat.sub_add_cancel hz)
          simp only [Nat.add_mul,one_mul] at h
          nlinarith only [hboundary,h]
  | purePair hpair =>
    refine ⟨(B.R-1)*B.triple.g 0,F.axis_killed,B.triple.g 0,?_,B.triple.positive 0,?_⟩
    · simpa [B.triple.weight_single] using B.triple.member (Finsupp.single 0 1)
    · have hR : 0<B.R := B.critical.positive 0
      have h := congrArg (fun n => n*B.triple.g 0) (show B.R-1+1=B.R by omega)
      simp only [Nat.add_mul,one_mul] at h
      omega

theorem Front.normal_unique {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (s : B.Source) (e : Exponent) (he : B.triple.weight e=s.val) :
    normal B.C B.u B.v e=B.norm s := by
  have hR : 0<B.R := B.critical.positive 0
  have hr : ∃ p∈B.K, ∃ g∈H, 0<g ∧ B.R*B.triple.g 0=p+g := by
    refine ⟨(B.R-1)*B.triple.g 0,F.axis_killed,B.triple.g 0,?_,B.triple.positive 0,?_⟩
    · simpa [B.triple.weight_single] using B.triple.member (Finsupp.single 0 1)
    · have h := congrArg (fun n => n*B.triple.g 0) (show B.R-1+1=B.R by omega)
      simpa [Nat.add_mul] using h.symm
  have hl := F.boundary_degree_proper
  apply (sourceNormal_spec B.triple B.m B.C B.u B.v (B.critical.positive 1) B.tie
    D.relations (SharedTail.mode_genuine D) ?_ ?_ s).2.2 e he
  · intro lr h
    rcases h with h | h
    · exact D.relation_weight lr h
    · exact (D.relation_weight (lr.2,lr.1) h).symm
  · intro lr h ha
    cases D with
    | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
      rcases h with h | h
      · rcases h with rfl | rfl | rfl
        · simpa only [vector_weight,Triple.grid,zero_mul,add_zero] using hr
        · exact (ha (Or.inl rfl)).elim
        · simpa only [vector_weight,Triple.grid,zero_mul,zero_add] using hl
      · rcases h with h | h | h
        · have heq : lr=(vector 0 p q,vector B.R 0 0) := Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
          subst lr
          simpa only [vector_weight,Triple.grid,zero_mul,zero_add,←hcenter] using hr
        · have heq : lr=(vector B.u 0 B.v,vector 0 B.C 0) := Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
          subst lr
          exact (ha (Or.inr rfl)).elim
        · have heq : lr=(vector w z 0,vector 0 0 B.L) := Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
          subst lr
          simpa only [vector_weight,Triple.grid,zero_mul,add_zero,←hboundary] using hl
    | purePair hpair =>
      rcases h with h | h
      · rcases h with rfl | rfl
        · simpa only [vector_weight,Triple.grid,zero_mul,add_zero] using hr
        · exact (ha (Or.inl rfl)).elim
      · rcases h with h | h
        · have heq : lr=(vector 0 0 B.L,vector B.R 0 0) := Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
          subst lr
          simpa only [vector_weight,Triple.grid,zero_mul,zero_add] using hl
        · have heq : lr=(vector B.u 0 B.v,vector 0 B.C 0) := Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
          subst lr
          exact (ha (Or.inr rfl)).elim

theorem Front.internal_cut_first_y_zero {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hk : B.C*B.triple.g 1∈B.K) : B.norm B.first 1=0 := by
  have hC : 0<B.C := B.critical.positive 1
  have hu := B.u_pos
  have hv := B.v_pos
  let p : Fin 3→ℕ := ![(B.u-1)*B.triple.g 0+B.v*B.triple.g 2,
    (B.C-1)*B.triple.g 1,B.u*B.triple.g 0+(B.v-1)*B.triple.g 2]
  have hp : ∀ i, p i∉B.K := by intro i; fin_cases i <;> first | exact F.mixed_x_live | exact F.pure_b_live | exact F.mixed_z_live
  have hdegree : ∀ i, B.C*B.triple.g 1=p i+B.triple.g i := by
    intro i
    fin_cases i <;> dsimp [p]
    · have h := congrArg (fun n => n*B.triple.g 0) (show B.u-1+1=B.u by omega)
      simp only [Nat.add_mul,one_mul] at h
      nlinarith only [B.tie,h]
    · have h := congrArg (fun n => n*B.triple.g 1) (show B.C-1+1=B.C by omega)
      simpa [Nat.add_mul] using h.symm
    · have h := congrArg (fun n => n*B.triple.g 2) (show B.v-1+1=B.v by omega)
      simp only [Nat.add_mul,one_mul] at h
      nlinarith only [B.tie,h]
  have hs : IsMinimalTailGenerator H.toAddSubmonoid B.K (B.C*B.triple.g 1) := by
    apply (minimal_iff_literal H B.K _).mpr
    refine ⟨hk,?_⟩
    intro t d ht hd he
    by_contra hzero
    obtain ⟨i,e,hei,hed⟩ := B.triple.D_nonempty hd (Nat.pos_of_ne_zero hzero)
    have hcut := ErasedSourceScreen.cut_add H ht hei
    exact hp i (by have hh := hdegree i; convert hcut using 1 <;> omega)
  let s : B.Source := ⟨B.C*B.triple.g 1,hs⟩
  have hfull : FullSupport B.triple s.val := by
    intro i
    fin_cases i
    · simpa [s,vector_weight,Triple.grid,←B.tie] using B.triple.D_of_coordinate (vector B.u 0 B.v) 0 (by simpa using hu)
    · simpa [s,vector_weight,Triple.grid] using B.triple.D_of_coordinate (vector 0 B.C 0) 1 (by simpa using hC)
    · simpa [s,vector_weight,Triple.grid,←B.tie] using B.triple.D_of_coordinate (vector B.u 0 B.v) 2 (by simpa using hv)
  have hfirst : s=B.first := Subtype.ext (full_support_source_is_first B.triple B.m B.m_pos s hfull)
  have he : B.triple.weight (vector B.u 0 B.v)=s.val := by simpa [vector_weight,Triple.grid] using B.tie.symm
  have hn := F.normal_unique s (vector B.u 0 B.v) he
  have hny := congrArg (fun e : Exponent => e 1) hn
  rw [hfirst] at hny
  simpa [normal] using hny.symm

theorem pure_c_source {H : NumericalSemigroup} (B : Base H)
    (hk : (B.L-1)*B.triple.g 2∈B.K) :
    ∃ s : B.Source, ∃ a : ℕ, 0<a ∧ a<B.L ∧ B.norm s=vector 0 0 a := by
  have hL : 0<B.L := B.critical.positive 2
  obtain ⟨s,hs⟩ := subcritical_axis_source_divisor B.triple B.critical B.m B.C B.u B.v
    B.tie 2 (B.L-1) (by change B.L-1<B.L; omega) hk
  change B.norm s≤Finsupp.single 2 (B.L-1) at hs
  have hx := hs 0
  have hy := hs 1
  have hz := hs 2
  simp only [Finsupp.single_eq_same,Finsupp.single_eq_of_ne (by decide : (0:Fin 3)≠2),
    Finsupp.single_eq_of_ne (by decide : (1:Fin 3)≠2)] at hx hy hz
  have he : B.norm s=vector 0 0 (B.norm s 2) := by
    ext i
    fin_cases i <;> simp_all
  have hp : 0<B.norm s 2 := by
    by_contra hh
    have h0 : B.norm s 2=0 := by omega
    have hsdeg := B.norm_degree s
    rw [he,h0,vector_weight,Triple.grid] at hsdeg
    obtain ⟨_,n,hn,r,_,hr⟩ := s.property.1
    simp at hsdeg
    have hm := B.m_pos
    nlinarith
  exact ⟨s,B.norm s 2,hp,by omega,he⟩

theorem mixed_alive_first_y_zero {H : NumericalSemigroup} (B : Base H)
    (w z : ℕ) (hw : 0<w) (hz : 0<z)
    (hboundary : B.L*B.triple.g 2=w*B.triple.g 0+z*B.triple.g 1)
    (hkill : (B.L-1)*B.triple.g 2∈B.K)
    (hlx : B.triple.weight (vector (w-1) z 0)∉B.K)
    (hly : B.triple.weight (vector w (z-1) 0)∉B.K) : B.norm B.first 1=0 := by
  obtain ⟨s,a,hap,haL,hs⟩ := pure_c_source B hkill
  have hdiv : ∃ d∈H, B.L*B.triple.g 2=s.val+d := by
    have hle : B.norm s≤vector 0 0 B.L := by
      rw [hs]; intro i; fin_cases i <;> simp_all <;> omega
    simpa [vector_weight,Triple.grid] using source_divides_monomial_degree B s (vector 0 0 B.L) hle
  have hfirst : s=B.first := by
    by_contra hnf
    obtain ⟨n,r,hn,_,hr,hrp,hret⟩ := nonfirst_source_small_return H B.m B.m_pos s
      (fun h => hnf (Subtype.ext h))
    obtain ⟨i,e,hei,her⟩ := B.triple.D_nonempty hr hrp
    obtain ⟨d,hd,hdiv⟩ := hdiv
    fin_cases i
    · change r=e+B.triple.g 0 at her
      apply hlx
      apply guarded_live_reflection H B.m n s.val r (B.L*B.triple.g 2) (B.triple.g 0)
        d e (B.triple.weight (vector (w-1) z 0)) hn hret hd hei (B.triple.member _) hdiv (by omega)
      rw [vector_weight,Triple.grid]
      have h := congrArg (fun n => n*B.triple.g 0) (show w-1+1=w by omega)
      simp only [Nat.add_mul,one_mul] at h
      nlinarith only [hboundary,h]
    · change r=e+B.triple.g 1 at her
      apply hly
      apply guarded_live_reflection H B.m n s.val r (B.L*B.triple.g 2) (B.triple.g 1)
        d e (B.triple.weight (vector w (z-1) 0)) hn hret hd hei (B.triple.member _) hdiv (by omega)
      rw [vector_weight,Triple.grid]
      have h := congrArg (fun n => n*B.triple.g 1) (show z-1+1=z by omega)
      simp only [Nat.add_mul,one_mul] at h
      nlinarith only [hboundary,h]
    · let se : Sources H B.m Set.univ := ⟨s.val,by simpa only [returnCut_univ] using s.property⟩
      apply source_remainder_support_disjoint B.triple B.m Set.univ se (Set.mem_univ n) hn hret
        ?_ ⟨e,hei,her⟩
      have hsdeg : B.triple.weight (vector 0 0 a)=s.val := hs ▸ B.norm_degree s
      exact hsdeg ▸ B.triple.D_of_coordinate (vector 0 0 a) 2 (by simpa using hap)
  have hy := congrArg (fun e : Exponent => e 1) hs
  rw [hfirst] at hy
  simpa using hy

theorem Front.mixed_first_y_zero {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hm : F.mixed=true) : B.norm B.first 1=0 := by
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
    have hb : (B.L-1)*B.triple.g 2∈B.K ∧
        B.triple.weight (vector (w-1) z 0)∉B.K ∧ B.triple.weight (vector w (z-1) 0)∉B.K := by
      simpa [boundaryGuards,hm] using F.boundary
    exact mixed_alive_first_y_zero B w z hw hz hboundary hb.1 hb.2.1 hb.2.2
  | purePair hpair =>
    have hb : F.mixed=false ∧ (B.L-1)*B.triple.g 2∉B.K := F.boundary
    simp [hm] at hb

end NS25Lean.CriticalFullSignature
