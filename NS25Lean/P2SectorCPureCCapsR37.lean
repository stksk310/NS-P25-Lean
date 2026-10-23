import NS25Lean.P2SectorCM8SourceRigidityR36
set_option linter.style.header false
noncomputable section
open Classical
namespace NS25Lean.L5A2C4OR37
open L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR29
  L5A2C4OR32 L5A2C4OR33 L5A2C4OR35 L5A2C4OR36 FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Original y-zero monomials, BEFORE adding wraps (authority §§E/F/G/J). -/
def OriginalZeroGenerators (R : ActualRolePacket P) : Set Monomial :=
  {g | g ∈ Set.range (sourceNormal R) ∪ {boundaryAliveMonomial R} ∧ g.2.1=0}

def OriginalZeroIdeal (R : ActualRolePacket P) (x z : ℕ) : Prop :=
  (x,0,z) ∈ monomialClosure (OriginalZeroGenerators R)

/-- The full M4 zero-plane section is deliberately a different predicate. -/
def M4ZeroSection (R : ActualRolePacket P) (x z : ℕ) : Prop :=
  (x,0,z) ∈ monomialClosure (M4Generators R)

theorem originalZero_le_M4 (R : ActualRolePacket P) {x z : ℕ}
    (h : OriginalZeroIdeal R x z) : M4ZeroSection R x z := by
  obtain ⟨g,hg,hd⟩ := h
  exact ⟨g,Or.inl hg.1,hd⟩

theorem originalZero_upward (R : ActualRolePacket P) {x z x' z' : ℕ}
    (h : OriginalZeroIdeal R x z) (hx : x≤x') (hz : z≤z') :
    OriginalZeroIdeal R x' z' := monomialClosure_upward h hx le_rfl hz

theorem originalZero_neck_out (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ¬OriginalZeroIdeal R (cr21 R.HD) (cr23 R.HD) := by
  intro h
  have hc := (strip_mem_iff_cut R (cr21 R.HD,0,cr23 R.HD)
    (herzogC_positive _ _ 1)).mp (originalZero_le_M4 R h)
  apply hn
  have he : monomialDegree P.M.base R.e (cr21 R.HD,0,cr23 R.HD)=
      c2 P.M.base R.e*routingB P.M.base R.e := by
    simpa [monomialDegree,normalizedGrid] using
      (coherent_normalized_relations _ _ R.HD).2.1.symm
  rwa [he] at hc

/-- A y-zero source containing the mixed F2 side has full union support,
hence is first; no uniqueness assumption on first-source fibers is used. -/
theorem zero_source_containing_neck_is_first (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (hy : (sourceNormal R s).2.1=0)
    (hx : cr21 R.HD≤(sourceNormal R s).1)
    (hz : cr23 R.HD≤(sourceNormal R s).2.2) : s=firstSource R := by
  apply Subtype.ext
  apply model_full_support_source_is_first
  have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
  have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  have hp := monomial_positive_predecessors R (sourceNormal R s)
  have hC := herzogC_positive P.M.base R.e 1
  let t : Monomial := ((sourceNormal R s).1-cr21 R.HD,c2 P.M.base R.e,
    (sourceNormal R s).2.2-cr23 R.HD)
  have ht : monomialDegree P.M.base R.e t=s.val := by
    have ha := congrArg (fun n => n*routingA P.M.base R.e) (Nat.sub_add_cancel hx)
    have hc := congrArg (fun n => n*routingC P.M.base R.e) (Nat.sub_add_cancel hz)
    have hs := (sourceNormal_spec R s).1
    have hr := (coherent_normalized_relations _ _ R.HD).2.1
    simp only [Nat.add_mul] at ha hc
    simp only [monomialDegree,normalizedGrid,hy,zero_mul,add_zero] at hs
    dsimp [t,monomialDegree,normalizedGrid]
    omega
  refine ⟨?_,?_,?_⟩
  · rw [←(sourceNormal_spec R s).1]; exact hp.1 (by omega)
  · rw [←ht]; exact (monomial_positive_predecessors R t).2.1 hC
  · rw [←(sourceNormal_spec R s).1]; exact hp.2.2 (by omega)

theorem pure_c_alive_boundary (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    boundaryAliveMonomial R=(0,0,c3 P.M.base R.e) := by
  classical
  simp [boundaryAliveMonomial,hlive]

/-- Every ORIGINAL zero-plane generator lies strictly left/up or right/down.
This is not asserted for an additional surviving full-source wrap. -/
theorem originalZero_generator_regions (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (g : Monomial) (hg : g ∈ OriginalZeroGenerators R) :
    (g.1<cr21 R.HD ∧ cr23 R.HD<g.2.2) ∨
      (cr21 R.HD<g.1 ∧ g.2.2<cr23 R.HD) := by
  have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
  have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  have hs := (coherent_coefficients P.M.base R.e R.HD).2.2
  have hq := (coherent_coefficients_positive _ _ R.HD).2.1
  have hnot : ¬(g.1≤cr21 R.HD ∧ g.2.2≤cr23 R.HD) := by
    rintro ⟨hx,hz⟩
    apply originalZero_neck_out R hn
    exact ⟨g,hg,hx,by simpa [hg.2],hz⟩
  rcases hg.1 with ⟨s,rfl⟩ | hb
  · have hnot' : ¬(cr21 R.HD≤(sourceNormal R s).1 ∧
        cr23 R.HD≤(sourceNormal R s).2.2) := by
      rintro ⟨hx,hz⟩
      have he := zero_source_containing_neck_is_first R s hg.2 hx hz
      have := hg.2
      rw [he] at this
      omega
    omega
  · have he : g=(0,0,c3 P.M.base R.e) := hb.trans (pure_c_alive_boundary R hlive)
    rw [he]
    exact Or.inl ⟨hu,by dsimp; omega⟩

theorem originalZero_axes (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    (∃ A, 0<A ∧ A<c1 P.M.base R.e ∧ OriginalZeroIdeal R A 0) ∧
      OriginalZeroIdeal R 0 (c3 P.M.base R.e) := by
  obtain ⟨s,A,hA,hAc,hs⟩ := actual_pure_a_source R
  constructor
  · exact ⟨A,hA,hAc,(A,0,0),⟨Or.inl ⟨s,hs⟩,rfl⟩,le_rfl,le_rfl,le_rfl⟩
  · refine ⟨(0,0,c3 P.M.base R.e),⟨Or.inr ?_,rfl⟩,le_rfl,le_rfl,le_rfl⟩
    exact (pure_c_alive_boundary R hlive).symm

theorem rightCap_exists (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ∃ A, OriginalZeroIdeal R A (cr23 R.HD-1) := by
  obtain ⟨⟨A,_,_,hA⟩,_⟩ := originalZero_axes R hlive
  exact ⟨A,originalZero_upward R hA le_rfl (Nat.zero_le _)⟩

theorem leftCap_exists (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ∃ D, OriginalZeroIdeal R (cr21 R.HD-1) D :=
  ⟨c3 P.M.base R.e,originalZero_upward R (originalZero_axes R hlive).2
    (Nat.zero_le _) le_rfl⟩

def rightCap (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) : ℕ :=
  Nat.find (rightCap_exists R hlive)

def leftCap (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) : ℕ :=
  Nat.find (leftCap_exists R hlive)

theorem rightCap_spec (R : ActualRolePacket P) (hlive) :
    OriginalZeroIdeal R (rightCap R hlive) (cr23 R.HD-1) :=
  Nat.find_spec (rightCap_exists R hlive)

theorem leftCap_spec (R : ActualRolePacket P) (hlive) :
    OriginalZeroIdeal R (cr21 R.HD-1) (leftCap R hlive) :=
  Nat.find_spec (leftCap_exists R hlive)

theorem rightCap_le (R : ActualRolePacket P) (hlive) {x z : ℕ}
    (hz : z<cr23 R.HD) (h : OriginalZeroIdeal R x z) : rightCap R hlive≤x :=
  Nat.find_min' (rightCap_exists R hlive)
    (originalZero_upward R h le_rfl (by omega))

theorem leftCap_le (R : ActualRolePacket P) (hlive) {x z : ℕ}
    (hx : x<cr21 R.HD) (h : OriginalZeroIdeal R x z) : leftCap R hlive≤z :=
  Nat.find_min' (leftCap_exists R hlive)
    (originalZero_upward R h (by omega) le_rfl)

theorem centralCaps_bounds (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    cr21 R.HD<rightCap R hlive ∧ rightCap R hlive<c1 P.M.base R.e ∧
      cr23 R.HD<leftCap R hlive ∧ leftCap R hlive≤c3 P.M.base R.e := by
  have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
  have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  obtain ⟨⟨A,_,hAc,hA⟩,hD⟩ := originalZero_axes R hlive
  have hAr : rightCap R hlive≤A := rightCap_le R hlive hv hA
  have hDl : leftCap R hlive≤c3 P.M.base R.e := leftCap_le R hlive hu hD
  have hr : cr21 R.HD<rightCap R hlive := by
    by_contra hh
    exact originalZero_neck_out R hn
      (originalZero_upward R (rightCap_spec R hlive) (by omega) (by omega))
  have hl : cr23 R.HD<leftCap R hlive := by
    by_contra hh
    exact originalZero_neck_out R hn
      (originalZero_upward R (leftCap_spec R hlive) (by omega) (by omega))
  exact ⟨hr,by omega,hl,hDl⟩

theorem originalZero_rectangle_empty (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {x z : ℕ} (hx : x<rightCap R hlive) (hz : z<leftCap R hlive) :
    ¬OriginalZeroIdeal R x z := by
  rintro ⟨g,hg,hgx,hgy,hgz⟩
  change g.1≤x at hgx
  change g.2.2≤z at hgz
  have hmem : OriginalZeroIdeal R g.1 g.2.2 :=
    ⟨g,hg,le_rfl,by simpa [hg.2],le_rfl⟩
  rcases originalZero_generator_regions R hn hy hlive g hg with h | h
  · have := leftCap_le R hlive h.1 hmem
    omega
  · have := rightCap_le R hlive h.2 hmem
    omega

theorem originalZero_central_rectangle (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {x z : ℕ} (hx : cr21 R.HD≤x) (hz : cr23 R.HD≤z) :
    ¬OriginalZeroIdeal R x z ↔ x<rightCap R hlive ∧ z<leftCap R hlive := by
  constructor
  · intro h
    constructor
    · by_contra hh
      exact h (originalZero_upward R (rightCap_spec R hlive) (by omega) (by omega))
    · by_contra hh
      exact h (originalZero_upward R (leftCap_spec R hlive) (by omega) (by omega))
  · rintro ⟨h,h'⟩
    exact originalZero_rectangle_empty R hn hy hlive h h'

/-- Full zero-plane membership has precisely the original contribution and
genuinely surviving wraps; the latter must not be silently discarded. -/
theorem M4ZeroSection_iff_original_or_surviving (R : ActualRolePacket P) (x z : ℕ) :
    M4ZeroSection R x z ↔ OriginalZeroIdeal R x z ∨
      ∃ g : survivingSourceWraps R, Divides g.val (x,0,z) := by
  constructor
  · intro hm
    have hi := (initial_mem_iff R (x,0,z)).mpr (Or.inr hm)
    obtain ⟨g,hg,hmin,hd⟩ := closure_has_minimal_divisor (initialGenerators R) (x,0,z) hi
    have hp : g ∈ rawGenerators R ∪ survivingSourceWraps R := by
      rw [←initial_minimal_partition]
      exact ⟨hg,hmin⟩
    rcases hp with hr | hw
    · rcases hr with (he | hs) | hb
      · have hC := herzogC_positive P.M.base R.e 1
        change 0<c2 P.M.base R.e at hC
        have hdy := hd.2.1
        rw [he] at hdy
        change c2 P.M.base R.e≤0 at hdy
        omega
      · exact Or.inl ⟨g,⟨Or.inl hs,by have := hd.2.1; change g.2.1≤0 at this; omega⟩,hd⟩
      · exact Or.inl ⟨g,⟨Or.inr hb,by have := hd.2.1; change g.2.1≤0 at this; omega⟩,hd⟩
    · exact Or.inr ⟨⟨g,hw⟩,hd⟩
  · rintro (hn | ⟨g,hd⟩)
    · exact originalZero_le_M4 R hn
    · obtain ⟨s,hs,he⟩ := g.property.1
      refine ⟨g.val,Or.inr ⟨s,hs,he⟩,hd⟩

theorem M4ZeroSection_iff_original_or_first_wrap (R : ActualRolePacket P) (x z : ℕ) :
    M4ZeroSection R x z ↔ OriginalZeroIdeal R x z ∨
      (Nonempty (survivingSourceWraps R) ∧
        Divides (sourceWrap R (sourceNormal R (firstSource R))) (x,0,z)) := by
  rw [M4ZeroSection_iff_original_or_surviving]
  constructor
  · rintro (h | ⟨g,hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨g⟩,by rwa [surviving_wrap_eq_first_wrap R g] at hd⟩
  · rintro (h | ⟨⟨g⟩,hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨g,by rwa [surviving_wrap_eq_first_wrap R g]⟩

/-- At top y all wrap multiples are already covered by their original
source. This statement does not discard wraps at y=0. -/
theorem top_M4_iff_original (R : ActualRolePacket P) (x z : ℕ) :
    (x,c2 P.M.base R.e-1,z) ∈ monomialClosure (M4Generators R) ↔
      ∃ g ∈ Set.range (sourceNormal R) ∪ {boundaryAliveMonomial R},
        Divides g (x,c2 P.M.base R.e-1,z) := by
  constructor
  · rintro ⟨g,hg,hd⟩
    rcases hg with hg | ⟨s,hs,rfl⟩
    · exact ⟨g,hg,hd⟩
    · have hy := (sourceNormal_spec R s).2.1
      refine ⟨sourceNormal R s,Or.inl ⟨s,rfl⟩,?_,by dsimp; omega,?_⟩
      · have := hd.1; dsimp [sourceWrap] at this ⊢; omega
      · have := hd.2.2; dsimp [sourceWrap] at this ⊢; omega
  · rintro ⟨g,hg,hd⟩
    exact ⟨g,Or.inl hg,hd⟩

theorem rightCap_actual_source (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ∃ s : ModelSources P.M.base R.e, ∃ z, z<cr23 R.HD ∧
      sourceNormal R s=(rightCap R hlive,0,z) := by
  obtain ⟨g,hg,hx,hy,hz⟩ := rightCap_spec R hlive
  change g.1≤rightCap R hlive at hx
  change g.2.2≤cr23 R.HD-1 at hz
  have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  have hlt : g.2.2<cr23 R.HD := by omega
  have hm : OriginalZeroIdeal R g.1 g.2.2 :=
    ⟨g,hg,le_rfl,by simpa [hg.2],le_rfl⟩
  have hx' := rightCap_le R hlive hlt hm
  have hxEq : g.1=rightCap R hlive := by omega
  rcases hg.1 with ⟨s,he⟩ | hb
  · refine ⟨s,g.2.2,hlt,?_⟩
    rw [he]
    exact Prod.ext hxEq (Prod.ext hg.2 rfl)
  · have he : g=(0,0,c3 P.M.base R.e) := hb.trans (pure_c_alive_boundary R hlive)
    have hc := (coherent_coefficients P.M.base R.e R.HD).2.2
    rw [he] at hlt
    dsimp at hlt
    omega

theorem leftCap_actual_source_or_boundary (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    leftCap R hlive=c3 P.M.base R.e ∨
      ∃ s : ModelSources P.M.base R.e, ∃ x, x<cr21 R.HD ∧
        sourceNormal R s=(x,0,leftCap R hlive) := by
  obtain ⟨g,hg,hx,hy,hz⟩ := leftCap_spec R hlive
  change g.1≤cr21 R.HD-1 at hx
  change g.2.2≤leftCap R hlive at hz
  have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
  have hlt : g.1<cr21 R.HD := by omega
  have hm : OriginalZeroIdeal R g.1 g.2.2 :=
    ⟨g,hg,le_rfl,by simpa [hg.2],le_rfl⟩
  have hz' := leftCap_le R hlive hlt hm
  have hzEq : g.2.2=leftCap R hlive := by omega
  rcases hg.1 with ⟨s,he⟩ | hb
  · exact Or.inr ⟨s,g.1,hlt,he.trans (Prod.ext rfl (Prod.ext hg.2 hzEq))⟩
  · have he : g=(0,0,c3 P.M.base R.e) := hb.trans (pure_c_alive_boundary R hlive)
    rw [he] at hzEq
    exact Or.inl hzEq.symm

theorem M4ZeroSection_iff_original_off_neck (R : ActualRolePacket P) {x z : ℕ}
    (h : x<cr21 R.HD ∨ z<cr23 R.HD) :
    M4ZeroSection R x z ↔ OriginalZeroIdeal R x z := by
  rw [M4ZeroSection_iff_original_or_first_wrap]
  constructor
  · rintro (hn | ⟨_,hd⟩)
    · exact hn
    · dsimp [Divides,sourceWrap] at hd
      rcases h with h | h <;> omega
  · exact Or.inl

/-- A selected nonfirst XZ-source return is genuinely positive pure-b,
and its b exponent is below the internal critical exponent. -/
theorem nonfirst_xz_small_return (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e)
    (hfirst : s≠firstSource R)
    (hx : 0<(sourceNormal R s).1) (hz : 0<(sourceNormal R s).2.2) :
    ∃ n k, 0<n ∧ n<firstPrincipal (routingH P.M.base R.e)
      (routingM P.M.base R.e) (routingM_pos P.M.base R.e) ∧
      0<k ∧ k<c2 P.M.base R.e ∧ s.val=n*routingM P.M.base R.e+k*routingB P.M.base R.e := by
  have hfirst' : s.val≠firstSourceDegree R := fun h => hfirst (Subtype.ext h)
  obtain ⟨n,t,hn,hn0,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ s hfirst'
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base R.e (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation R s (sourceNormal R s) (x,y,z)
    (sourceNormal_spec R s).1 hn (he.trans (by rw [hd]))
  have hx0 : x=0 := sep.1 hx
  have hz0 : z=0 := sep.2.2 hz
  have hty : t=y*routingB P.M.base R.e := by simpa [monomialDegree,normalizedGrid,hx0,hz0] using hd.symm
  have hyp : 0<y := by
    by_contra h
    have hy0 : y=0 := by omega
    rw [hy0,zero_mul] at hty
    omega
  have hyC : y<c2 P.M.base R.e := by
    by_contra hh
    have hle : c2 P.M.base R.e≤y := by omega
    let t' : Monomial := (cr21 R.HD,y-c2 P.M.base R.e,cr23 R.HD)
    have ht' : monomialDegree P.M.base R.e t'=t := by
      have hm := congrArg (fun k => k*routingB P.M.base R.e) (Nat.sub_add_cancel hle)
      have hr := (coherent_normalized_relations _ _ R.HD).2.1
      simp only [Nat.add_mul] at hm
      dsimp [t',monomialDegree,normalizedGrid]
      omega
    have sep' := source_return_coordinate_separation R s (sourceNormal R s) t'
      (sourceNormal_spec R s).1 hn (he.trans (by rw [ht']))
    have := sep'.1 hx
    have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
    change cr21 R.HD=0 at this
    omega
  exact ⟨n,y,hn,hn0,hyp,hyC,by omega⟩

theorem nonfirst_xy_strict_predecessor (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (hfirst : s≠firstSource R)
    (hx : 0<(sourceNormal R s).1) (hy : 0<(sourceNormal R s).2.1) :
    OriginalZeroIdeal R ((sourceNormal R s).1+cr21 R.HD) (cr23 R.HD-1) := by
  have hfirst' : s.val≠firstSourceDegree R := fun h => hfirst (Subtype.ext h)
  obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ s hfirst'
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base R.e (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation R s (sourceNormal R s) (x,y,z)
    (sourceNormal_spec R s).1 hn (he.trans (by rw [hd]))
  have hx0 : x=0 := sep.1 hx
  have hy0 : y=0 := sep.2.1 hy
  have hzpos : 0<z := by
    by_contra hh
    have hz0 : z=0 := by omega
    simp [monomialDegree,normalizedGrid,hx0,hy0,hz0] at hd
    omega
  have hsz : (sourceNormal R s).2.2=0 := by
    by_contra hh
    have := sep.2.2 (by omega)
    change z=0 at this
    omega
  let p : Monomial := ((sourceNormal R s).1+cr21 R.HD,0,cr23 R.HD-1)
  have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  have hC := (sourceNormal_spec R s).2.1
  have hs := (sourceNormal_spec R s).1
  have hr := (coherent_normalized_relations _ _ R.HD).2.1
  have hsub := congrArg (fun k => k*routingB P.M.base R.e) (Nat.sub_add_cancel (Nat.le_of_lt hC))
  have hzm := congrArg (fun k => k*routingC P.M.base R.e) (show z-1+1=z by omega)
  have hvm := congrArg (fun k => k*routingC P.M.base R.e) (show cr23 R.HD-1+1=cr23 R.HD by omega)
  have hpcut : monomialDegree P.M.base R.e p ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    refine ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ (0,c2 P.M.base R.e-(sourceNormal R s).2.1,z-1),?_⟩
    simp only [monomialDegree,normalizedGrid,hx0,hy0,hsz,zero_mul,zero_add,add_zero] at hs hd
    simp only [Nat.add_mul,one_mul] at hsub hzm hvm
    simp only [p,monomialDegree,normalizedGrid,zero_mul,zero_add,Nat.add_mul]
    nlinarith only [hs,hd,he,hr,hsub,hzm,hvm]
  have hm := (strip_mem_iff_cut R p (herzogC_positive _ _ 1)).mpr hpcut
  exact (M4ZeroSection_iff_original_off_neck R (Or.inr (by omega))).mp hm

theorem nonfirst_yz_strict_predecessor (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (hfirst : s≠firstSource R)
    (hy : 0<(sourceNormal R s).2.1) (hz : 0<(sourceNormal R s).2.2) :
    OriginalZeroIdeal R (cr21 R.HD-1) ((sourceNormal R s).2.2+cr23 R.HD) := by
  have hfirst' : s.val≠firstSourceDegree R := fun h => hfirst (Subtype.ext h)
  obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ s hfirst'
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base R.e (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation R s (sourceNormal R s) (x,y,z)
    (sourceNormal_spec R s).1 hn (he.trans (by rw [hd]))
  have hy0 : y=0 := sep.2.1 hy
  have hz0 : z=0 := sep.2.2 hz
  have hxpos : 0<x := by
    by_contra hh
    have hx0 : x=0 := by omega
    simp [monomialDegree,normalizedGrid,hx0,hy0,hz0] at hd
    omega
  have hsx : (sourceNormal R s).1=0 := by
    by_contra hh
    have := sep.1 (by omega)
    change x=0 at this
    omega
  let p : Monomial := (cr21 R.HD-1,0,(sourceNormal R s).2.2+cr23 R.HD)
  have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
  have hC := (sourceNormal_spec R s).2.1
  have hs := (sourceNormal_spec R s).1
  have hr := (coherent_normalized_relations _ _ R.HD).2.1
  have hsub := congrArg (fun k => k*routingB P.M.base R.e) (Nat.sub_add_cancel (Nat.le_of_lt hC))
  have hxm := congrArg (fun k => k*routingA P.M.base R.e) (show x-1+1=x by omega)
  have hum := congrArg (fun k => k*routingA P.M.base R.e) (show cr21 R.HD-1+1=cr21 R.HD by omega)
  have hpcut : monomialDegree P.M.base R.e p ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    refine ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ (x-1,c2 P.M.base R.e-(sourceNormal R s).2.1,0),?_⟩
    simp only [monomialDegree,normalizedGrid,hsx,hy0,hz0,zero_mul,zero_add,add_zero] at hs hd
    simp only [Nat.add_mul,one_mul] at hsub hxm hum
    simp only [p,monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero,Nat.add_mul]
    nlinarith only [hs,hd,he,hr,hsub,hxm,hum]
  have hm := (strip_mem_iff_cut R p (herzogC_positive _ _ 1)).mpr hpcut
  exact (M4ZeroSection_iff_original_off_neck R (Or.inl (by omega))).mp hm

theorem nonfirst_xy_cap_lower (R : ActualRolePacket P) (hlive)
    (s : ModelSources P.M.base R.e) (hf : s≠firstSource R)
    (hx : 0<(sourceNormal R s).1) (hy : 0<(sourceNormal R s).2.1) :
    rightCap R hlive-cr21 R.HD≤(sourceNormal R s).1 := by
  have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  have := rightCap_le R hlive (show cr23 R.HD-1<cr23 R.HD by omega)
    (nonfirst_xy_strict_predecessor R s hf hx hy)
  omega

theorem nonfirst_yz_cap_lower (R : ActualRolePacket P) (hlive)
    (s : ModelSources P.M.base R.e) (hf : s≠firstSource R)
    (hy : 0<(sourceNormal R s).2.1) (hz : 0<(sourceNormal R s).2.2) :
    leftCap R hlive-cr23 R.HD≤(sourceNormal R s).2.2 := by
  have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
  have := leftCap_le R hlive (show cr21 R.HD-1<cr21 R.HD by omega)
    (nonfirst_yz_strict_predecessor R s hf hy hz)
  omega

theorem pure_c_xy_cut_source (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {x y : ℕ} (hy : y<c2 P.M.base R.e)
    (hcut : monomialDegree P.M.base R.e (x,y,0) ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ∃ s : ModelSources P.M.base R.e,
      Divides (sourceNormal R s) (x,y,0) ∧ 0<(sourceNormal R s).1 := by
  obtain ⟨g,hg,hd⟩ := (strip_mem_iff_cut R (x,y,0) hy).mpr hcut
  rcases hg with (⟨s,rfl⟩ | hb) | ⟨s,hs,rfl⟩
  · refine ⟨s,hd,?_⟩
    by_contra hh
    apply source_not_divides_yC R s
    dsimp [Divides] at hd ⊢
    omega
  · have he : g=(0,0,c3 P.M.base R.e) := hb.trans (pure_c_alive_boundary R hlive)
    have hc := herzogC_positive P.M.base R.e 2
    change 0<c3 P.M.base R.e at hc
    rw [he] at hd
    dsimp [Divides] at hd
    omega
  · have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
    dsimp [Divides,sourceWrap] at hd
    omega

theorem pure_c_yz_cut_source (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {y z : ℕ} (hy : y<c2 P.M.base R.e) (hz : z<c3 P.M.base R.e)
    (hcut : monomialDegree P.M.base R.e (0,y,z) ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ∃ s : ModelSources P.M.base R.e,
      Divides (sourceNormal R s) (0,y,z) ∧ 0<(sourceNormal R s).2.2 := by
  obtain ⟨g,hg,hd⟩ := (strip_mem_iff_cut R (0,y,z) hy).mpr hcut
  rcases hg with (⟨s,rfl⟩ | hb) | ⟨s,hs,rfl⟩
  · refine ⟨s,hd,?_⟩
    by_contra hh
    apply source_not_divides_yC R s
    dsimp [Divides] at hd ⊢
    omega
  · have he : g=(0,0,c3 P.M.base R.e) := hb.trans (pure_c_alive_boundary R hlive)
    rw [he] at hd
    dsimp [Divides] at hd
    omega
  · have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
    dsimp [Divides,sourceWrap] at hd
    omega

/-- The return is an actual source return, not a desired cap equality. -/
theorem rightCap_forcing_of_selected_return (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hfirstZ : 0<(sourceNormal R (firstSource R)).2.2)
    (s : ModelSources P.M.base R.e) {e n k r : ℕ}
    (hs : sourceNormal R s=(rightCap R hlive,0,e)) (he : e<cr23 R.HD)
    (hns : 0<n) (hk : 0<k) (hkC : k<c2 P.M.base R.e)
    (hret : s.val=n*routingM P.M.base R.e+k*routingB P.M.base R.e+r*routingC P.M.base R.e) :
    ∃ t : ModelSources P.M.base R.e,
      (sourceNormal R t).1=rightCap R hlive-cr21 R.HD ∧
      0<(sourceNormal R t).2.1 ∧ (sourceNormal R t).2.2=0 := by
  have hb := centralCaps_bounds R hn hlive
  have hC : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
  let g : Monomial := (rightCap R hlive-cr21 R.HD,c2 P.M.base R.e-k,0)
  have hcut : monomialDegree P.M.base R.e g ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    refine ⟨grid_mem_H _ _ _,n,hns,_,grid_mem_H _ _ (0,0,cr23 R.HD+r-e),?_⟩
    have hd := (sourceNormal_spec R s).1
    rw [hs] at hd
    have hA := congrArg (fun t => t*routingA P.M.base R.e) (Nat.sub_add_cancel (Nat.le_of_lt hb.1))
    have hB := congrArg (fun t => t*routingB P.M.base R.e) (Nat.sub_add_cancel (Nat.le_of_lt hkC))
    have hV := congrArg (fun t => t*routingC P.M.base R.e) (Nat.sub_add_cancel (show e≤cr23 R.HD+r by omega))
    have hr := (coherent_normalized_relations _ _ R.HD).2.1
    simp only [Nat.add_mul] at hA hB hV
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero] at hd
    simp only [g,monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero]
    nlinarith only [hd,hret,hA,hB,hV,hr]
  obtain ⟨t,ht,hx⟩ := pure_c_xy_cut_source R hlive (by omega) hcut
  have htz : (sourceNormal R t).2.2=0 := by have := ht.2.2; change (sourceNormal R t).2.2≤0 at this; omega
  have htx : (sourceNormal R t).1≤rightCap R hlive-cr21 R.HD := ht.1
  have hty : 0<(sourceNormal R t).2.1 := by
    by_contra hh
    have hy0 : (sourceNormal R t).2.1=0 := by omega
    have hm : OriginalZeroIdeal R (sourceNormal R t).1 0 :=
      ⟨sourceNormal R t,⟨Or.inl ⟨t,rfl⟩,hy0⟩,le_rfl,by simp [hy0],by simp [htz]⟩
    have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
    have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
    have := rightCap_le R hlive hv hm
    omega
  have htf : t≠firstSource R := by intro heq; rw [heq] at htz; omega
  have hlow := nonfirst_xy_cap_lower R hlive t htf hx hty
  exact ⟨t,by omega,hty,htz⟩

theorem leftCap_forcing_of_selected_return (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hfirstX : 0<(sourceNormal R (firstSource R)).1)
    (s : ModelSources P.M.base R.e) {f n k r : ℕ}
    (hs : sourceNormal R s=(f,0,leftCap R hlive)) (hf : f<cr21 R.HD)
    (hns : 0<n) (hk : 0<k) (hkC : k<c2 P.M.base R.e)
    (hret : s.val=n*routingM P.M.base R.e+k*routingB P.M.base R.e+r*routingA P.M.base R.e) :
    ∃ t : ModelSources P.M.base R.e,
      (sourceNormal R t).2.2=leftCap R hlive-cr23 R.HD ∧
      0<(sourceNormal R t).2.1 ∧ (sourceNormal R t).1=0 := by
  have hb := centralCaps_bounds R hn hlive
  have hC : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
  have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  let g : Monomial := (0,c2 P.M.base R.e-k,leftCap R hlive-cr23 R.HD)
  have hcut : monomialDegree P.M.base R.e g ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    refine ⟨grid_mem_H _ _ _,n,hns,_,grid_mem_H _ _ (cr21 R.HD+r-f,0,0),?_⟩
    have hd := (sourceNormal_spec R s).1
    rw [hs] at hd
    have hA := congrArg (fun t => t*routingA P.M.base R.e) (Nat.sub_add_cancel (show f≤cr21 R.HD+r by omega))
    have hB := congrArg (fun t => t*routingB P.M.base R.e) (Nat.sub_add_cancel (Nat.le_of_lt hkC))
    have hV := congrArg (fun t => t*routingC P.M.base R.e) (Nat.sub_add_cancel (Nat.le_of_lt hb.2.2.1))
    have hr := (coherent_normalized_relations _ _ R.HD).2.1
    simp only [Nat.add_mul] at hA hB hV
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero] at hd
    simp only [g,monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero]
    nlinarith only [hd,hret,hA,hB,hV,hr]
  obtain ⟨t,ht,hz⟩ := pure_c_yz_cut_source R hlive (by omega) (by omega) hcut
  have htx : (sourceNormal R t).1=0 := by have := ht.1; change (sourceNormal R t).1≤0 at this; omega
  have htz : (sourceNormal R t).2.2≤leftCap R hlive-cr23 R.HD := ht.2.2
  have hty : 0<(sourceNormal R t).2.1 := by
    by_contra hh
    have hy0 : (sourceNormal R t).2.1=0 := by omega
    have hm : OriginalZeroIdeal R 0 (sourceNormal R t).2.2 :=
      ⟨sourceNormal R t,⟨Or.inl ⟨t,rfl⟩,hy0⟩,by simp [htx],by simp [hy0],le_rfl⟩
    have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
    have := leftCap_le R hlive hu hm
    omega
  have htf : t≠firstSource R := by intro heq; rw [heq] at htx; omega
  have hlow := nonfirst_yz_cap_lower R hlive t htf hty hz
  exact ⟨t,by omega,hty,htx⟩

theorem pure_c_alive_excludes_pure_c_return (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {X Y n Z : ℕ} (hX : X≤cr31 R.HD) (hY : Y≤cr32 R.HD)
    (hn : 0<n) (hZ : 0<Z)
    (he : monomialDegree P.M.base R.e (X,Y,0)=
      n*routingM P.M.base R.e+Z*routingC P.M.base R.e) : False := by
  have hr := (coherent_normalized_relations _ _ R.HD).2.2
  have hm := routingM_pos P.M.base R.e
  have hc := routingC_positive P.M.base R.e
  have hXa := Nat.mul_le_mul_right (routingA P.M.base R.e) hX
  have hYb := Nat.mul_le_mul_right (routingB P.M.base R.e) hY
  have hZc : Z<c3 P.M.base R.e := by
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero] at he
    nlinarith
  have hcut : monomialDegree P.M.base R.e (0,0,c3 P.M.base R.e-Z) ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    refine ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ (cr31 R.HD-X,cr32 R.HD-Y,0),?_⟩
    have hA := congrArg (fun t => t*routingA P.M.base R.e) (Nat.sub_add_cancel hX)
    have hB := congrArg (fun t => t*routingB P.M.base R.e) (Nat.sub_add_cancel hY)
    have hC := congrArg (fun t => t*routingC P.M.base R.e) (Nat.sub_add_cancel (Nat.le_of_lt hZc))
    simp only [Nat.add_mul] at hA hB hC
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero,zero_add] at he ⊢
    omega
  have ht := monomial_cut_upward P.M.base R.e
    (show Divides (0,0,c3 P.M.base R.e-Z) (0,0,c3 P.M.base R.e-1) from
      ⟨le_rfl,le_rfl,by dsimp; omega⟩) hcut
  apply hlive
  simpa only [monomialDegree,normalizedGrid,zero_mul,zero_add,Nat.sub_mul,one_mul] using ht

theorem pure_c_alive_killed_mixed_forces_pure_x (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hfirstZ : 0<(sourceNormal R (firstSource R)).2.2) :
    ∃ s : ModelSources P.M.base R.e, ∃ A,
      0<A ∧ A≤cr31 R.HD ∧ sourceNormal R s=(A,0,0) := by
  have hp := coherent_coefficients_positive _ _ R.HD
  have hw : 0<cr31 R.HD := hp.2.2.2.2.1
  have hq : 0<cr32 R.HD := hp.2.2.2.2.2
  have hqC : cr32 R.HD<c2 P.M.base R.e := by
    have hc := (coherent_coefficients _ _ R.HD).2.1
    omega
  have hr := (coherent_normalized_relations _ _ R.HD).2.2
  have hex : ∃ X Y, X≤cr31 R.HD ∧ Y≤cr32 R.HD ∧
      monomialDegree P.M.base R.e (X,Y,0) ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    rcases actual_normalized_boundary_dichotomy R with h | h
    · exact (hlive h.1).elim
    · rcases h.2 with ha | hb
      · refine ⟨cr31 R.HD-1,cr32 R.HD,by omega,le_rfl,?_⟩
        have hm := congrArg (fun k => k*routingA P.M.base R.e) (show cr31 R.HD-1+1=cr31 R.HD by omega)
        simp only [Nat.add_mul,one_mul] at hm
        convert ha using 1 <;> simp only [monomialDegree,normalizedGrid,zero_mul,add_zero] <;> omega
      · refine ⟨cr31 R.HD,cr32 R.HD-1,le_rfl,by omega,?_⟩
        have hm := congrArg (fun k => k*routingB P.M.base R.e) (show cr32 R.HD-1+1=cr32 R.HD by omega)
        simp only [Nat.add_mul,one_mul] at hm
        convert hb using 1 <;> simp only [monomialDegree,normalizedGrid,zero_mul,add_zero] <;> omega
  obtain ⟨X,Y,hX,hY,hK⟩ := hex
  obtain ⟨s,hs,hx⟩ := pure_c_xy_cut_source R hlive (by omega) hK
  have hsx : (sourceNormal R s).1≤cr31 R.HD := hs.1.trans hX
  have hsy : (sourceNormal R s).2.1≤cr32 R.HD := hs.2.1.trans hY
  have hsz : (sourceNormal R s).2.2=0 := by have := hs.2.2; change (sourceNormal R s).2.2≤0 at this; omega
  have hsf : s≠firstSource R := by intro hh; rw [hh] at hsz; omega
  have hsy0 : (sourceNormal R s).2.1=0 := by
    by_contra hh
    have hy : 0<(sourceNormal R s).2.1 := by omega
    have hsf' : s.val≠firstSourceDegree R := fun h => hsf (Subtype.ext h)
    obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ s hsf'
    obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
    have hd : monomialDegree P.M.base R.e (x,y,z)=t := hfac.symm
    have sep := source_return_coordinate_separation R s (sourceNormal R s) (x,y,z)
      (sourceNormal_spec R s).1 hn (he.trans (by rw [hd]))
    have hx0 : x=0 := sep.1 hx
    have hy0 : y=0 := sep.2.1 hy
    have htz : t=z*routingC P.M.base R.e := by simpa [monomialDegree,normalizedGrid,hx0,hy0] using hd.symm
    have hz : 0<z := by
      by_contra h
      have hz0 : z=0 := by omega
      rw [hz0,zero_mul] at htz
      omega
    apply pure_c_alive_excludes_pure_c_return R hlive hsx hsy hn hz
    have hsd := (sourceNormal_spec R s).1
    have hg : sourceNormal R s=((sourceNormal R s).1,(sourceNormal R s).2.1,0) :=
      Prod.ext rfl (Prod.ext rfl hsz)
    rw [hg] at hsd
    exact hsd.trans (he.trans (by rw [htz]))
  exact ⟨s,(sourceNormal R s).1,hx,hsx,Prod.ext rfl (Prod.ext hsy0 hsz)⟩

theorem pure_x_small_return_b_positive (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hfirstZ : 0<(sourceNormal R (firstSource R)).2.2)
    (s : ModelSources P.M.base R.e) {A : ℕ}
    (hs : sourceNormal R s=(A,0,0)) (hA : 0<A) (hAw : A≤cr31 R.HD) :
    ∃ n k r, 0<n ∧ n<firstPrincipal (routingH P.M.base R.e)
      (routingM P.M.base R.e) (routingM_pos P.M.base R.e) ∧
      0<k ∧ k<c2 P.M.base R.e ∧
      s.val=n*routingM P.M.base R.e+k*routingB P.M.base R.e+r*routingC P.M.base R.e := by
  have hsf : s.val≠firstSourceDegree R := by
    intro hh
    have heq : s=firstSource R := Subtype.ext hh
    have hz := congrArg (fun g : Monomial => g.2.2) hs
    rw [heq] at hz
    dsimp at hz
    omega
  obtain ⟨n,t,hn,hn0,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ s hsf
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base R.e (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation R s (sourceNormal R s) (x,y,z)
    (sourceNormal_spec R s).1 hn (he.trans (by rw [hd]))
  have hx0 : x=0 := sep.1 (by simpa [hs] using hA)
  have hret : s.val=n*routingM P.M.base R.e+y*routingB P.M.base R.e+z*routingC P.M.base R.e := by
    simp only [monomialDegree,normalizedGrid,hx0,zero_mul,zero_add] at hd
    omega
  have hyp : 0<y := by
    by_contra hh
    have hy0 : y=0 := by omega
    have htz : t=z*routingC P.M.base R.e := by simpa [monomialDegree,normalizedGrid,hx0,hy0] using hd.symm
    have hz : 0<z := by
      by_contra h
      have hz0 : z=0 := by omega
      rw [hz0,zero_mul] at htz
      omega
    apply pure_c_alive_excludes_pure_c_return R hlive hAw (Nat.zero_le _) hn hz
    have hsd := (sourceNormal_spec R s).1
    rw [hs] at hsd
    simpa [hy0] using hsd.trans hret
  have hyC : y<c2 P.M.base R.e := by
    by_contra hh
    have hle : c2 P.M.base R.e≤y := by omega
    let t' : Monomial := (cr21 R.HD,y-c2 P.M.base R.e,z+cr23 R.HD)
    have ht' : monomialDegree P.M.base R.e t'=t := by
      have hm := congrArg (fun k => k*routingB P.M.base R.e) (Nat.sub_add_cancel hle)
      have hr := (coherent_normalized_relations _ _ R.HD).2.1
      simp only [Nat.add_mul] at hm
      simp only [monomialDegree,normalizedGrid,hx0,zero_mul,zero_add] at hd
      dsimp [t',monomialDegree,normalizedGrid]
      simp only [Nat.add_mul]
      omega
    have sep' := source_return_coordinate_separation R s (sourceNormal R s) t'
      (sourceNormal_spec R s).1 hn (he.trans (by rw [ht']))
    have := sep'.1 (by simpa [hs] using hA)
    have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
    change cr21 R.HD=0 at this
    omega
  exact ⟨n,y,z,hn,hn0,hyp,hyC,hret⟩

theorem actual_right_cap_forced (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hfirstZ : 0<(sourceNormal R (firstSource R)).2.2) :
    ∃ t : ModelSources P.M.base R.e,
      (sourceNormal R t).1=rightCap R hlive-cr21 R.HD ∧
      0<(sourceNormal R t).2.1 ∧ (sourceNormal R t).2.2=0 := by
  obtain ⟨s,e,he,hs⟩ := rightCap_actual_source R hlive
  have hb := centralCaps_bounds R hn hlive
  have hsf : s≠firstSource R := by
    intro hh
    have := congrArg (fun g : Monomial => g.2.1) hs
    rw [hh] at this
    dsimp at this
    omega
  by_cases he0 : e=0
  · obtain ⟨t,A,hA,hAw,ht⟩ := pure_c_alive_killed_mixed_forces_pure_x R hlive hfirstZ
    have hm : OriginalZeroIdeal R A 0 :=
      ⟨(A,0,0),⟨Or.inl ⟨t,ht⟩,rfl⟩,le_rfl,le_rfl,le_rfl⟩
    have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
    have hAw' := (rightCap_le R hlive hv hm).trans hAw
    have hs' : sourceNormal R s=(rightCap R hlive,0,0) := by simpa [he0] using hs
    obtain ⟨n,k,r,hns,_,hk,hkC,hret⟩ := pure_x_small_return_b_positive R hlive hfirstZ s hs' (by omega) hAw'
    exact rightCap_forcing_of_selected_return R hn hlive hfirstZ s hs he hns hk hkC hret
  · obtain ⟨n,k,hns,_,hk,hkC,hret⟩ := nonfirst_xz_small_return R s hsf
      (by simpa [hs] using (show 0<rightCap R hlive by omega)) (by simp [hs]; omega)
    exact rightCap_forcing_of_selected_return R hn hlive hfirstZ s (r := 0) hs he hns hk hkC
      (by simpa using hret)

theorem pure_c_alive_no_low_pure_c_source (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (s : ModelSources P.M.base R.e) {D : ℕ}
    (hs : sourceNormal R s=(0,0,D)) (hD : D<c3 P.M.base R.e) : False := by
  have hc : monomialDegree P.M.base R.e (0,0,D) ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    rw [←hs,(sourceNormal_spec R s).1]
    exact ((minimalTail_iff_literal _ _ _).mp s.property).1
  have ht := monomial_cut_upward P.M.base R.e
    (show Divides (0,0,D) (0,0,c3 P.M.base R.e-1) from ⟨le_rfl,le_rfl,by dsimp; omega⟩) hc
  apply hlive
  simpa only [monomialDegree,normalizedGrid,zero_mul,zero_add,Nat.sub_mul,one_mul] using ht

theorem actual_left_cap_strict_forced (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hfirstX : 0<(sourceNormal R (firstSource R)).1)
    (hD : leftCap R hlive<c3 P.M.base R.e) :
    ∃ t : ModelSources P.M.base R.e,
      (sourceNormal R t).2.2=leftCap R hlive-cr23 R.HD ∧
      0<(sourceNormal R t).2.1 ∧ (sourceNormal R t).1=0 := by
  obtain he | ⟨s,f,hf,hs⟩ := leftCap_actual_source_or_boundary R hlive
  · omega
  have hb := centralCaps_bounds R hn hlive
  have hsf : s≠firstSource R := by
    intro hh
    have := congrArg (fun g : Monomial => g.2.1) hs
    rw [hh] at this
    dsimp at this
    omega
  have hfp : 0<f := by
    by_contra hh
    have hf0 : f=0 := by omega
    exact pure_c_alive_no_low_pure_c_source R hlive s (by simpa [hf0] using hs) hD
  obtain ⟨n,k,hns,_,hk,hkC,hret⟩ := nonfirst_xz_small_return R s hsf
    (by simpa [hs] using hfp) (by simpa [hs] using (show 0<leftCap R hlive by omega))
  exact leftCap_forcing_of_selected_return R hn hlive hfirstX s (r := 0) hs hf hns hk hkC
    (by simpa using hret)

theorem actual_left_cap_equality_forced (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hfirstX : 0<(sourceNormal R (firstSource R)).1)
    (hD : leftCap R hlive=c3 P.M.base R.e) :
    ∃ t : ModelSources P.M.base R.e,
      (sourceNormal R t).2.2=cr13 R.HD ∧
      0<(sourceNormal R t).2.1 ∧ (sourceNormal R t).1=0 := by
  have hp := coherent_coefficients_positive _ _ R.HD
  have hp' : 0<cr12 R.HD := hp.1
  have hq : 0<cr13 R.HD := hp.2.1
  have hpC : cr12 R.HD<c2 P.M.base R.e := by
    have hc := (coherent_coefficients _ _ R.HD).2.1
    have hz := hp.2.2.2.2.2
    omega
  have hqc : cr13 R.HD<c3 P.M.base R.e := by
    have hc := (coherent_coefficients _ _ R.HD).2.2
    have hv := hp.2.2.2.1
    omega
  have hr := (coherent_normalized_relations _ _ R.HD).1
  have hex : ∃ Y Z, Y≤cr12 R.HD ∧ Z≤cr13 R.HD ∧
      monomialDegree P.M.base R.e (0,Y,Z) ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    rcases (actual_normalized_inactive_killed R).2 with hb | hc
    · refine ⟨cr12 R.HD-1,cr13 R.HD,by omega,le_rfl,?_⟩
      have hm := congrArg (fun k => k*routingB P.M.base R.e) (show cr12 R.HD-1+1=cr12 R.HD by omega)
      simp only [Nat.add_mul,one_mul] at hm
      convert hb using 1 <;> simp only [monomialDegree,normalizedGrid,zero_mul,zero_add] <;> omega
    · refine ⟨cr12 R.HD,cr13 R.HD-1,le_rfl,by omega,?_⟩
      have hm := congrArg (fun k => k*routingC P.M.base R.e) (show cr13 R.HD-1+1=cr13 R.HD by omega)
      simp only [Nat.add_mul,one_mul] at hm
      convert hc using 1 <;> simp only [monomialDegree,normalizedGrid,zero_mul,zero_add] <;> omega
  obtain ⟨Y,Z,hY,hZ,hK⟩ := hex
  obtain ⟨s,hs,hz⟩ := pure_c_yz_cut_source R hlive (by omega) (by omega) hK
  have hsx : (sourceNormal R s).1=0 := by have := hs.1; change (sourceNormal R s).1≤0 at this; omega
  have hsz : (sourceNormal R s).2.2≤cr13 R.HD := hs.2.2.trans hZ
  have hsy : 0<(sourceNormal R s).2.1 := by
    by_contra hh
    have hy0 : (sourceNormal R s).2.1=0 := by omega
    apply pure_c_alive_no_low_pure_c_source R hlive s (D := (sourceNormal R s).2.2)
      (Prod.ext hsx (Prod.ext hy0 rfl))
    exact hsz.trans_lt hqc
  have hsf : s≠firstSource R := by intro hh; rw [hh] at hsx; omega
  have hlow := nonfirst_yz_cap_lower R hlive s hsf hsy hz
  have hc := (coherent_coefficients _ _ R.HD).2.2
  rw [hD] at hlow
  exact ⟨s,by omega,hsy,hsx⟩

theorem actual_left_cap_forced (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hfirstX : 0<(sourceNormal R (firstSource R)).1) :
    ∃ t : ModelSources P.M.base R.e,
      (sourceNormal R t).2.2=leftCap R hlive-cr23 R.HD ∧
      0<(sourceNormal R t).2.1 ∧ (sourceNormal R t).1=0 := by
  have hb := centralCaps_bounds R hn hlive
  by_cases hD : leftCap R hlive=c3 P.M.base R.e
  · obtain ⟨s,hs,hy,hr⟩ := actual_left_cap_equality_forced R hlive hfirstX hD
    have hc := (coherent_coefficients _ _ R.HD).2.2
    exact ⟨s,by omega,hy,hr⟩
  · exact actual_left_cap_strict_forced R hn hy hlive hfirstX (by omega)

theorem surviving_first_wrap_outside_original (R : ActualRolePacket P)
    (g : survivingSourceWraps R) :
    ¬OriginalZeroIdeal R ((sourceNormal R (firstSource R)).1+cr21 R.HD)
      ((sourceNormal R (firstSource R)).2.2+cr23 R.HD) := by
  rintro ⟨h,hh,hd⟩
  have he := surviving_wrap_eq_first_wrap R g
  have hi : h ∈ monomialClosure (initialGenerators R) :=
    ⟨h,Or.inr (Or.inl hh.1),le_rfl,le_rfl,le_rfl⟩
  have hd' : Divides h g.val := by rw [he]; exact hd
  have heq := g.property.2.1.2 h hi hd'
  apply g.property.2.2
  rw [←heq]
  rcases hh.1 with hs | hb
  · exact Or.inl (Or.inr hs)
  · exact Or.inr hb

theorem surviving_first_wrap_cap_bounds (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (g : survivingSourceWraps R) :
    (sourceNormal R (firstSource R)).1<rightCap R hlive-cr21 R.HD ∧
      (sourceNormal R (firstSource R)).2.2<leftCap R hlive-cr23 R.HD := by
  have hb := (originalZero_central_rectangle R hn hy hlive
    (show cr21 R.HD≤(sourceNormal R (firstSource R)).1+cr21 R.HD by omega)
    (show cr23 R.HD≤(sourceNormal R (firstSource R)).2.2+cr23 R.HD by omega)).mp
      (surviving_first_wrap_outside_original R g)
  omega

theorem top_outside_of_caps (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {x z : ℕ} (hx : x<rightCap R hlive-cr21 R.HD)
    (hz : z<leftCap R hlive-cr23 R.HD)
    (hmiss : x<(sourceNormal R (firstSource R)).1 ∨ z<(sourceNormal R (firstSource R)).2.2) :
    (x,c2 P.M.base R.e-1,z) ∉ monomialClosure (M4Generators R) := by
  have hb := centralCaps_bounds R hn hlive
  rw [top_M4_iff_original]
  rintro ⟨g,hg,hd⟩
  rcases hg with ⟨s,rfl⟩ | hbound
  · have hsx : (sourceNormal R s).1≤x := hd.1
    have hsz : (sourceNormal R s).2.2≤z := hd.2.2
    by_cases hsy : (sourceNormal R s).2.1=0
    · apply originalZero_rectangle_empty R hn hy hlive (x := x) (z := z) (by omega) (by omega)
      exact ⟨sourceNormal R s,⟨Or.inl ⟨s,rfl⟩,hsy⟩,hsx,by simp [hsy],hsz⟩
    · have hsp : 0<(sourceNormal R s).2.1 := by omega
      by_cases hsf : s=firstSource R
      · rw [hsf] at hsx hsz
        rcases hmiss with h | h <;> omega
      · by_cases hsx0 : (sourceNormal R s).1=0
        · have hszp : 0<(sourceNormal R s).2.2 := by
            by_contra hh
            apply source_not_divides_yC R s
            dsimp [Divides]
            have hc := (sourceNormal_spec R s).2.1
            omega
          have := nonfirst_yz_cap_lower R hlive s hsf hsp hszp
          omega
        · have hsxp : 0<(sourceNormal R s).1 := by omega
          have := nonfirst_xy_cap_lower R hlive s hsf hsxp hsp
          omega
  · have he : g=(0,0,c3 P.M.base R.e) := hbound.trans (pure_c_alive_boundary R hlive)
    rw [he] at hd
    have hdz := hd.2.2
    change c3 P.M.base R.e≤z at hdz
    omega

theorem wrapped_outside_of_caps (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {x z : ℕ} (hx : x<rightCap R hlive-cr21 R.HD)
    (hz : z<leftCap R hlive-cr23 R.HD)
    (hmiss : x<(sourceNormal R (firstSource R)).1 ∨ z<(sourceNormal R (firstSource R)).2.2) :
    sourceWrap R (x,c2 P.M.base R.e-1,z) ∉ monomialClosure (M4Generators R) := by
  change ¬M4ZeroSection R (x+cr21 R.HD) (z+cr23 R.HD)
  rw [M4ZeroSection_iff_original_or_first_wrap]
  rintro (h | ⟨_,hd⟩)
  · exact originalZero_rectangle_empty R hn hy hlive (by omega) (by omega) h
  · dsimp [Divides,sourceWrap] at hd
    rcases hmiss with h | h <;> omega

theorem border_of_cap_cell (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {x z : ℕ} (hx : x<rightCap R hlive-cr21 R.HD)
    (hz : z<leftCap R hlive-cr23 R.HD)
    (hmiss : x<(sourceNormal R (firstSource R)).1 ∨ z<(sourceNormal R (firstSource R)).2.2)
    (hxs : (x+1,c2 P.M.base R.e-1,z) ∈ monomialClosure (M4Generators R))
    (hzs : (x,c2 P.M.base R.e-1,z+1) ∈ monomialClosure (M4Generators R)) :
    (x,c2 P.M.base R.e-1,z) ∈ borderExceptional R := by
  have hC : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
  have htop : c2 P.M.base R.e-1+1=c2 P.M.base R.e := by omega
  have hlt : c2 P.M.base R.e-1<c2 P.M.base R.e := by omega
  have hout := top_outside_of_caps R hn hy hlive hx hz hmiss
  refine ⟨⟨(standardStrip_iff R _).mp ⟨hlt,hout⟩,
    (initial_mem_iff R _).mpr (Or.inr hxs),
    (initial_mem_iff R _).mpr (Or.inl (by change c2 P.M.base R.e≤c2 P.M.base R.e-1+1; omega)),
    (initial_mem_iff R _).mpr (Or.inr hzs)⟩,htop,?_⟩
  exact wrapped_outside_of_caps R hn hy hlive hx hz hmiss

theorem top_source_multiple (R : ActualRolePacket P) (s : ModelSources P.M.base R.e)
    {x z : ℕ} (hx : (sourceNormal R s).1≤x) (hz : (sourceNormal R s).2.2≤z) :
    (x,c2 P.M.base R.e-1,z) ∈ monomialClosure (M4Generators R) := by
  refine ⟨sourceNormal R s,Or.inl (Or.inl ⟨s,rfl⟩),hx,?_,hz⟩
  have := (sourceNormal_spec R s).2.1
  change (sourceNormal R s).2.1≤c2 P.M.base R.e-1
  omega

theorem borderExceptional_finite (R : ActualRolePacket P) : (borderExceptional R).Finite := by
  obtain ⟨a,b,c,_,_,_,ha,hb,hc⟩ := initial_axes R
  exact (L5A2C4OR23.monomialSocle_finite (initialGenerators R) a b c ha hb hc).subset (fun _ h => h.1)

theorem border_card_one (R : ActualRolePacket P) {g : Monomial}
    (hg : g ∈ borderExceptional R) : 1≤Nat.card {z // z ∈ borderExceptional R} := by
  letI := (borderExceptional_finite R).to_subtype
  have := Nat.card_le_card_of_injective (fun _ : Unit => (⟨g,hg⟩ : {z // z ∈ borderExceptional R}))
    (fun _ _ _ => Subsingleton.elim _ _)
  simpa using this

theorem border_card_two (R : ActualRolePacket P) {g h : Monomial}
    (hg : g ∈ borderExceptional R) (hh : h ∈ borderExceptional R) (hne : g≠h) :
    2≤Nat.card {z // z ∈ borderExceptional R} := by
  letI := (borderExceptional_finite R).to_subtype
  let f : Bool → {z // z ∈ borderExceptional R} := fun b => if b then ⟨g,hg⟩ else ⟨h,hh⟩
  have hi : Function.Injective f := by
    intro x y he
    cases x <;> cases y
    · rfl
    · exact (hne (congrArg Subtype.val he).symm).elim
    · exact (hne (congrArg Subtype.val he)).elim
    · rfl
  simpa using Nat.card_le_card_of_injective f hi

/-- The two literal E seats in the full-source inner-quadrant case. -/
theorem full_source_two_border_witnesses (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hf : FullySupported (sourceNormal R (firstSource R)))
    (hα : (sourceNormal R (firstSource R)).1<rightCap R hlive-cr21 R.HD)
    (hγ : (sourceNormal R (firstSource R)).2.2<leftCap R hlive-cr23 R.HD) :
    ((sourceNormal R (firstSource R)).1-1,c2 P.M.base R.e-1,leftCap R hlive-cr23 R.HD-1) ∈ borderExceptional R ∧
    (rightCap R hlive-cr21 R.HD-1,c2 P.M.base R.e-1,(sourceNormal R (firstSource R)).2.2-1) ∈ borderExceptional R ∧
    ((sourceNormal R (firstSource R)).1-1,c2 P.M.base R.e-1,leftCap R hlive-cr23 R.HD-1) ≠
      (rightCap R hlive-cr21 R.HD-1,c2 P.M.base R.e-1,(sourceNormal R (firstSource R)).2.2-1) := by
  have hαp : 0<(sourceNormal R (firstSource R)).1 := hf.1
  have hγp : 0<(sourceNormal R (firstSource R)).2.2 := hf.2.2
  obtain ⟨sx,hsx,hsy,hsz⟩ := actual_right_cap_forced R hn hf.2.1 hlive hf.2.2
  obtain ⟨sz,hsz',hszy,hszx⟩ := actual_left_cap_forced R hn hf.2.1 hlive hf.1
  have hb := centralCaps_bounds R hn hlive
  have hleft : ((sourceNormal R (firstSource R)).1-1,c2 P.M.base R.e-1,leftCap R hlive-cr23 R.HD-1) ∈ borderExceptional R := by
    apply border_of_cap_cell R hn hf.2.1 hlive (by omega) (by omega) (Or.inl (by omega))
    · exact top_source_multiple R (firstSource R) (by omega) (by omega)
    · exact top_source_multiple R sz (by omega) (by omega)
  have hright : (rightCap R hlive-cr21 R.HD-1,c2 P.M.base R.e-1,(sourceNormal R (firstSource R)).2.2-1) ∈ borderExceptional R := by
    apply border_of_cap_cell R hn hf.2.1 hlive (by omega) (by omega) (Or.inr (by omega))
    · exact top_source_multiple R sx (by omega) (by omega)
    · exact top_source_multiple R (firstSource R) (by omega) (by omega)
  refine ⟨hleft,hright,?_⟩
  intro he
  have hx := congrArg (fun g : Monomial => g.1) he
  dsimp at hx
  omega

theorem full_source_outer_border_witness (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hf : FullySupported (sourceNormal R (firstSource R)))
    (hout : rightCap R hlive-cr21 R.HD≤(sourceNormal R (firstSource R)).1 ∨
      leftCap R hlive-cr23 R.HD≤(sourceNormal R (firstSource R)).2.2) :
    (rightCap R hlive-cr21 R.HD-1,c2 P.M.base R.e-1,leftCap R hlive-cr23 R.HD-1) ∈ borderExceptional R := by
  obtain ⟨sx,hsx,hsy,hsz⟩ := actual_right_cap_forced R hn hf.2.1 hlive hf.2.2
  obtain ⟨sz,hsz',hszy,hszx⟩ := actual_left_cap_forced R hn hf.2.1 hlive hf.1
  have hb := centralCaps_bounds R hn hlive
  apply border_of_cap_cell R hn hf.2.1 hlive (by omega) (by omega)
  · rcases hout with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · exact top_source_multiple R sx (by omega) (by omega)
  · exact top_source_multiple R sz (by omega) (by omega)

theorem full_source_compensation (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hf : FullySupported (sourceNormal R (firstSource R))) :
    survivingWrapCount R + Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
      Nat.card {z // z ∈ borderExceptional R} := by
  by_cases hinner : (sourceNormal R (firstSource R)).1<rightCap R hlive-cr21 R.HD ∧
      (sourceNormal R (firstSource R)).2.2<leftCap R hlive-cr23 R.HD
  · obtain ⟨hl,hr,hne⟩ := full_source_two_border_witnesses R hn hlive hf hinner.1 hinner.2
    have hc := border_card_two R hl hr hne
    have hb := wrap_and_full_support_count_le_two R
    omega
  · have hout : rightCap R hlive-cr21 R.HD≤(sourceNormal R (firstSource R)).1 ∨
        leftCap R hlive-cr23 R.HD≤(sourceNormal R (firstSource R)).2.2 := by omega
    haveI : IsEmpty (survivingSourceWraps R) := ⟨fun g => hinner (surviving_first_wrap_cap_bounds R hn hf.2.1 hlive g)⟩
    have hB : survivingWrapCount R=0 := by simp [survivingWrapCount]
    have hc := border_card_one R (full_source_outer_border_witness R hn hlive hf hout)
    have hk := fullSupportSourceCount_le_one R
    omega

theorem first_yz_border_witness (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hx0 : (sourceNormal R (firstSource R)).1=0)
    (hzp : 0<(sourceNormal R (firstSource R)).2.2)
    (g : survivingSourceWraps R) :
    (rightCap R hlive-cr21 R.HD-1,c2 P.M.base R.e-1,(sourceNormal R (firstSource R)).2.2-1) ∈ borderExceptional R := by
  have hb := centralCaps_bounds R hn hlive
  have hcap := surviving_first_wrap_cap_bounds R hn hy hlive g
  obtain ⟨sx,hsx,hsy,hsz⟩ := actual_right_cap_forced R hn hy hlive hzp
  apply border_of_cap_cell R hn hy hlive (by omega) (by omega) (Or.inr (by omega))
  · exact top_source_multiple R sx (by omega) (by omega)
  · exact top_source_multiple R (firstSource R) (by omega) (by omega)

theorem first_xy_border_witness (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hz0 : (sourceNormal R (firstSource R)).2.2=0)
    (hxp : 0<(sourceNormal R (firstSource R)).1)
    (g : survivingSourceWraps R) :
    ((sourceNormal R (firstSource R)).1-1,c2 P.M.base R.e-1,leftCap R hlive-cr23 R.HD-1) ∈ borderExceptional R := by
  have hb := centralCaps_bounds R hn hlive
  have hcap := surviving_first_wrap_cap_bounds R hn hy hlive g
  obtain ⟨sz,hsz,hszy,hszx⟩ := actual_left_cap_forced R hn hy hlive hxp
  apply border_of_cap_cell R hn hy hlive (by omega) (by omega) (Or.inl (by omega))
  · exact top_source_multiple R (firstSource R) (by omega) (by omega)
  · exact top_source_multiple R sz (by omega) (by omega)

theorem full_count_zero_of_first_not_full (R : ActualRolePacket P)
    (hf : ¬FullySupported (sourceNormal R (firstSource R))) :
    Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}=0 := by
  haveI : IsEmpty {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} := ⟨fun s => by
    have he := full_support_source_eq_first R s.val s.property
    exact hf (he ▸ s.property)⟩
  simp

theorem pure_c_alive_compensation (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    survivingWrapCount R + Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
      Nat.card {z // z ∈ borderExceptional R} := by
  by_cases hy0 : (sourceNormal R (firstSource R)).2.1=0
  · exact compensation_of_first_source_y_zero R hy0
  have hy : 0<(sourceNormal R (firstSource R)).2.1 := by omega
  by_cases hf : FullySupported (sourceNormal R (firstSource R))
  · exact full_source_compensation R hn hlive hf
  have hk := full_count_zero_of_first_not_full R hf
  by_cases hne : Nonempty (survivingSourceWraps R)
  · obtain ⟨g⟩ := hne
    have hB := survivingWrapCount_le_one R
    by_cases hx0 : (sourceNormal R (firstSource R)).1=0
    · have hzp : 0<(sourceNormal R (firstSource R)).2.2 := by
        by_contra hh
        apply source_not_divides_yC R (firstSource R)
        have hc := (sourceNormal_spec R (firstSource R)).2.1
        dsimp [Divides]
        omega
      have hc := border_card_one R (first_yz_border_witness R hn hy hlive hx0 hzp g)
      omega
    · have hxp : 0<(sourceNormal R (firstSource R)).1 := by omega
      have hz0 : (sourceNormal R (firstSource R)).2.2=0 := by
        by_contra hh
        exact hf ⟨hxp,hy,by omega⟩
      have hc := border_card_one R (first_xy_border_witness R hn hy hlive hz0 hxp g)
      omega
  · haveI : IsEmpty (survivingSourceWraps R) := ⟨fun g => hne ⟨g⟩⟩
    have hB : survivingWrapCount R=0 := by simp [survivingWrapCount]
    simp [hB,hk]

/-- M9 at arbitrary actual role packet; no DirectPF/notch/owner premise. -/
theorem actual_role_packet_compensation (R : ActualRolePacket P) :
    survivingWrapCount R + Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
      Nat.card {z // z ∈ borderExceptional R} := by
  by_cases hcut : c2 P.M.base R.e*routingB P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
  · exact internal_cut_compensation R hcut
  · rcases actual_normalized_boundary_dichotomy R with h | h
    · exact mixed_alive_compensation R h.2
    · exact pure_c_alive_compensation R hcut h.1

/-- Literal original M9 binder, with the original DirectPF predicate. -/
theorem actual_border_compensation (R : ActualRolePacket P)
    (_hDP : L5A2C4G.DirectPFBranch P.M.base R.e R.HD) :
    survivingWrapCount R + Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
      Nat.card {z // z ∈ borderExceptional R} := actual_role_packet_compensation R

theorem actual_directPF_type_bound (R : ActualRolePacket P)
    (hDP : L5A2C4G.DirectPFBranch P.M.base R.e R.HD) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  have hM9 := actual_border_compensation R hDP
  have hM6M7 := actual_M6_M7_bound R
  omega

end NS25Lean.L5A2C4OR37
