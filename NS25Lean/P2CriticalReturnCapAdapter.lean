import NS25Lean.P2CriticalReturnDuality
import NS25Lean.AttainedCapCompensation
import NS25Lean.P2ActualGenericDualityCounts

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalReturnCapAdapter
open ChosenBase FourGeneratedBridge L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H
  L5A2C4OR1 L5A2C4OR5 L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33 L5A2C4OR35 L5A2C4OR36
  L5A2C4OR37 CriticalReturnDuality
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

def positiveOriginals (R : ActualRolePacket P) : Set Monomial :=
  Set.range (sourceNormal R)∪{boundaryAliveMonomial R}

theorem positive_source_shape (R : ActualRolePacket P)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    {g : Monomial} (hg : g∈positiveOriginals R)
    (hnf : g≠sourceNormal R (firstSource R)) (hy : 0<g.2.1) :
    (rightCap R hlive-cr21 R.HD≤g.1 ∧ g.2.2=0) ∨
      (leftCap R hlive-cr23 R.HD≤g.2.2 ∧ g.1=0) := by
  rcases hg with ⟨s,rfl⟩ | hg
  · have hs : s≠firstSource R := fun h => hnf (congrArg (sourceNormal R) h)
    by_cases hx : 0<(sourceNormal R s).1
    · have hz : (sourceNormal R s).2.2=0 := by
        by_contra h
        exact hs (full_support_source_eq_first R s ⟨hx,hy,by omega⟩)
      exact Or.inl ⟨nonfirst_xy_cap_lower R hlive s hs hx hy,hz⟩
    · have hx0 : (sourceNormal R s).1=0 := by omega
      have hz : 0<(sourceNormal R s).2.2 := by
        by_contra h
        apply source_not_divides_yC R s
        dsimp [Divides]
        have hb := (sourceNormal_spec R s).2.1
        exact ⟨by omega,by omega,by omega⟩
      exact Or.inr ⟨nonfirst_yz_cap_lower R hlive s hs hy hz,hx0⟩
  · have hb := pure_c_alive_boundary R hlive
    have hg' : g=(0,0,c3 P.M.base R.e) := hg.trans hb
    simp [hg'] at hy

/-- Every field is derived from the original packet and its branch guards.
In particular neither cap-attainment nor compensation is an input. -/
def positiveCapData (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) : SharedCap.Data where
  C := c2 P.M.base R.e
  u := cr21 R.HD
  v := cr23 R.HD
  U := rightCap R hlive-cr21 R.HD
  V := leftCap R hlive-cr23 R.HD
  C_pos := herzogC_positive _ _ 1
  u_pos := (coherent_coefficients_positive _ _ R.HD).2.2.1
  v_pos := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  U_pos := by have := (centralCaps_bounds R hn hlive).1; omega
  V_pos := by have := (centralCaps_bounds R hn hlive).2.2.1; omega
  originals := positiveOriginals R
  originals_finite := by
    letI := actual_model_sources_finite R
    exact (Set.finite_range _).union (Set.finite_singleton _)
  first := sourceNormal R (firstSource R)
  first_mem := Or.inl ⟨firstSource R,rfl⟩
  first_y_pos := hy
  first_transverse_pos := by
    by_contra h
    apply source_not_divides_yC R (firstSource R)
    dsimp [Divides]
    have hb := (sourceNormal_spec R (firstSource R)).2.1
    exact ⟨by omega,by omega,by omega⟩
  normal := by
    intro g hg
    rcases hg with ⟨s,rfl⟩ | hg
    · exact (sourceNormal_spec R s).2.1
    · rw [hg,pure_c_alive_boundary R hlive]
      exact herzogC_positive _ _ 1
  shape := by
    intro g hg hg0 hgY
    exact positive_source_shape R hlive hg hg0 hgY
  other_wraps := by
    intro g hg hg0 hgY
    rcases hg with ⟨s,rfl⟩ | hg
    · exact positive_nonfirst_wrap_in_original R s
        (fun h => hg0 (congrArg (sourceNormal R) h)) hgY
    · rw [hg,pure_c_alive_boundary R hlive] at hgY
      simp at hgY
  rectangle := by
    intro i k hi hk
    have hb := centralCaps_bounds R hn hlive
    exact originalZero_rectangle_empty R hn hy hlive (by omega) (by omega)
  central := by
    intro i k hi hk
    change ¬OriginalZeroIdeal R i k ↔
      i<cr21 R.HD+(rightCap R hlive-cr21 R.HD) ∧
      k<cr23 R.HD+(leftCap R hlive-cr23 R.HD)
    have hb := centralCaps_bounds R hn hlive
    simpa only [Nat.add_sub_cancel' hb.1.le,Nat.add_sub_cancel' hb.2.2.1.le] using
      (originalZero_central_rectangle R hn hy hlive hi hk)
  attained_x := by
    intro hz
    obtain ⟨t,hx,hty,htz⟩ := actual_right_cap_forced R hn hy hlive hz
    refine ⟨sourceNormal R t,Or.inl ⟨t,rfl⟩,?_,hx,hty,htz⟩
    intro h
    have := congrArg (fun g : Monomial => g.2.2) h
    omega
  attained_z := by
    intro hx
    obtain ⟨t,hz,hty,htx⟩ := actual_left_cap_forced R hn hy hlive hx
    refine ⟨sourceNormal R t,Or.inl ⟨t,rfl⟩,?_,htx,hty,hz⟩
    intro h
    have := congrArg (fun g : Monomial => g.1) h
    omega

theorem positive_MGenerators_eq (R : ActualRolePacket P) (hn hy hlive) :
    SharedCap.MGenerators (positiveCapData R hn hy hlive).originals
      (positiveCapData R hn hy hlive).u (positiveCapData R hn hy hlive).v=M4Generators R := by
  ext g
  change (g∈positiveOriginals R ∨ ∃ w∈positiveOriginals R, 0<w.2.1 ∧
    g=sourceWrap R w) ↔ g∈M4Generators R
  constructor
  · rintro (hg | ⟨w,hw,hy,hg⟩)
    · exact Or.inl hg
    · rcases hw with ⟨s,rfl⟩ | hw
      · exact Or.inr ⟨s,hy,hg⟩
      · rw [hw,pure_c_alive_boundary R hlive] at hy
        simp at hy
  · rintro (hg | ⟨s,hs,hg⟩)
    · exact Or.inl hg
    · exact Or.inr ⟨sourceNormal R s,Or.inl ⟨s,rfl⟩,hs,hg⟩

theorem positive_LGenerators_eq (R : ActualRolePacket P) (hn hy hlive) :
    SharedCap.LGenerators (positiveCapData R hn hy hlive).originals
      (positiveCapData R hn hy hlive).C (positiveCapData R hn hy hlive).u
      (positiveCapData R hn hy hlive).v=initialGenerators R := by
  unfold SharedCap.LGenerators
  rw [positive_MGenerators_eq]
  rfl

theorem positive_exceptional_eq (R : ActualRolePacket P) (hn hy hlive) :
    (positiveCapData R hn hy hlive).exceptional=borderExceptional R := by
  ext g
  unfold SharedCap.Data.exceptional
  rw [positive_LGenerators_eq,positive_MGenerators_eq]
  rfl

theorem positive_additional_wraps_eq (R : ActualRolePacket P) (hn hy hlive) :
    (positiveCapData R hn hy hlive).additionalWraps=survivingSourceWraps R := by
  ext g
  unfold SharedCap.Data.additionalWraps
  rw [positive_LGenerators_eq]
  change (InitialMinimal R g ∧ g∉positiveOriginals R ∧
      ∃ w∈positiveOriginals R, 0<w.2.1 ∧ g=sourceWrap R w) ↔
    g∈sourceWraps R ∧ InitialMinimal R g ∧ g∉rawGenerators R
  constructor
  · rintro ⟨hmin,hnot,w,hw,hwy,hg⟩
    have hsource : g∈sourceWraps R := by
      rcases hw with ⟨s,rfl⟩ | hw
      · exact ⟨s,hwy,hg⟩
      · rw [hw,pure_c_alive_boundary R hlive] at hwy
        simp at hwy
    refine ⟨hsource,hmin,?_⟩
    rintro ((hgY | hgS) | hgB)
    · have hgY' : g=(0,c2 P.M.base R.e,0) := hgY
      have hy0 : g.2.1=0 := by rw [hg]; rfl
      rw [hgY'] at hy0
      change c2 P.M.base R.e=0 at hy0
      have hp := herzogC_positive P.M.base R.e 1
      exact hp.ne' hy0
    · exact hnot (Or.inl hgS)
    · exact hnot (Or.inr hgB)
  · rintro ⟨⟨s,hsy,hg⟩,hmin,hnot⟩
    refine ⟨hmin,?_,sourceNormal R s,Or.inl ⟨s,rfl⟩,hsy,hg⟩
    intro ho
    rcases ho with hs | hb
    · exact hnot (Or.inl (Or.inr hs))
    · exact hnot (Or.inr hb)

theorem positive_full_support_count (R : ActualRolePacket P) (hn hy hlive) :
    (positiveCapData R hn hy hlive).fullSupport=
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} := by
  classical
  letI := actual_model_sources_finite R
  by_cases hf : 0<(sourceNormal R (firstSource R)).1 ∧
      0<(sourceNormal R (firstSource R)).2.2
  · have hp : 0<Nat.card {s : ModelSources P.M.base R.e //
        FullySupported (sourceNormal R s)} := Nat.card_pos_iff.mpr
        ⟨⟨⟨firstSource R,hf.1,hy,hf.2⟩⟩,inferInstance⟩
    have hl := fullSupportSourceCount_le_one R
    change (if 0<(sourceNormal R (firstSource R)).1 ∧
      0<(sourceNormal R (firstSource R)).2.2 then 1 else 0)=_
    rw [if_pos hf]
    omega
  · have hz := full_count_zero_of_first_not_full R
      (fun h => hf ⟨h.1,h.2.2⟩)
    change (if 0<(sourceNormal R (firstSource R)).1 ∧
      0<(sourceNormal R (firstSource R)).2.2 then 1 else 0)=_
    rw [if_neg hf,hz]

/-- The original actual compensation endpoint now follows from the proved
shared cap theorem, with all three count dictionaries explicit. -/
theorem positive_compensation (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    survivingWrapCount R+
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
        Nat.card {z // z∈borderExceptional R} := by
  have h := SharedCap.compensation (positiveCapData R hn hy hlive)
  rw [positive_additional_wraps_eq,positive_full_support_count,positive_exceptional_eq] at h
  exact h

/-- All original actual role packets, with no dispatcher/cap/DirectPF input. -/
theorem actual_packet_compensation_shared (R : ActualRolePacket P) :
    survivingWrapCount R+
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
        Nat.card {z // z∈borderExceptional R} := by
  exact ActualGenericDualityAdapter.actual_packet_compensation R

theorem actual_packet_type_bound_shared (R : ActualRolePacket P) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  have hc := actual_packet_compensation_shared R
  have hb := actual_M6_M7_bound R
  omega

theorem actual_nonsymmetric_type_bound_shared (P : P2Data Gamma)
    (hNS : L5A2C4G.NonsymmetricSectorC P) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  obtain ⟨R,_⟩ := actual_role_gate_dispatcher P hNS
  exact actual_packet_type_bound_shared R

end NS25Lean.CriticalReturnCapAdapter
