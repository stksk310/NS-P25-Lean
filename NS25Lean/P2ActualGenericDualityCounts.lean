import NS25Lean.P2ActualGenericDualityAdapter

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.ActualGenericDualityAdapter
open Classical ChosenBase FourGeneratedBridge L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H
  L5A2C4OR1 L5A2C4OR5 L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33 L5A2C4OR35 L5A2C4OR36 L5A2C4OR37
  ErasedSourceScreen PureInternalTransverse CriticalCapGeometry
  CriticalPresentationModes CriticalFullSignature GenericCriticalCompensation
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

theorem actual_boundary_wrap_zero (R : ActualRolePacket P) (hy : 0<(boundaryAliveMonomial R).2.1) :
    sourceWrap R (boundaryAliveMonomial R)∈SharedCap.Closure (SharedCap.ZeroGenerators (actualOriginals R)) := by
  have he := GenericCriticalDuality.endpoint_wrap_redundant (actualFront R)
    (by simpa only [←actual_endpoint_tuple R,tuple] using hy)
  rw [actual_family,actual_endpoint_tuple] at he
  exact he

theorem zero_original_to_M4 (R : ActualRolePacket P) {g : Monomial}
    (hg : g∈SharedCap.Closure (SharedCap.ZeroGenerators (actualOriginals R))) :
    g∈monomialClosure (M4Generators R) := by
  obtain ⟨w,hw,hle⟩ := hg
  exact ⟨w,Or.inl hw.1,hle⟩

theorem actual_MClosure (R : ActualRolePacket P) :
    SharedCap.Closure (SharedCap.MGenerators (GenericCriticalDuality.family (actualFront R))
      (actualBase R).u (actualBase R).v)=monomialClosure (M4Generators R) := by
  rw [actual_family]
  ext g
  constructor
  · rintro ⟨w,(hw | ⟨z,hz,hy,hw⟩),hle⟩
    · exact ⟨w,Or.inl hw,hle⟩
    · change w=sourceWrap R z at hw
      rcases hz with ⟨s,rfl⟩ | rfl
      · exact ⟨w,Or.inr ⟨s,hy,hw⟩,hle⟩
      · exact monomialClosure_upward (zero_original_to_M4 R (hw ▸ actual_boundary_wrap_zero R hy))
          hle.1 hle.2.1 hle.2.2
  · rintro ⟨w,(hw | ⟨s,hy,hw⟩),hle⟩
    · exact ⟨w,Or.inl hw,hle⟩
    · exact ⟨w,Or.inr ⟨sourceNormal R s,Or.inl ⟨s,rfl⟩,hy,hw⟩,hle⟩

theorem closure_insert_eq {G J : Set SharedCap.Monomial}
    (heq : SharedCap.Closure G=SharedCap.Closure J) (a : SharedCap.Monomial) :
    SharedCap.Closure (insert a G)=SharedCap.Closure (insert a J) := by
  ext p
  constructor
  · rintro ⟨g,(hg | hg),hle⟩
    · exact ⟨g,Or.inl hg,hle⟩
    · have hm : p∈SharedCap.Closure J := heq ▸ (show p∈SharedCap.Closure G from ⟨g,hg,hle⟩)
      obtain ⟨g,hg,hle⟩ := hm
      exact ⟨g,Or.inr hg,hle⟩
  · rintro ⟨g,(hg | hg),hle⟩
    · exact ⟨g,Or.inl hg,hle⟩
    · have hm : p∈SharedCap.Closure G := heq.symm ▸ (show p∈SharedCap.Closure J from ⟨g,hg,hle⟩)
      obtain ⟨g,hg,hle⟩ := hm
      exact ⟨g,Or.inr hg,hle⟩

theorem actual_LClosure (R : ActualRolePacket P) :
    SharedCap.Closure (SharedCap.LGenerators (GenericCriticalDuality.family (actualFront R))
      (actualBase R).C (actualBase R).u (actualBase R).v)=monomialClosure (initialGenerators R) :=
  closure_insert_eq (actual_MClosure R) _

theorem actual_minimal (R : ActualRolePacket P) (g : Monomial) :
    SharedCap.MinimalGenerator (SharedCap.LGenerators (GenericCriticalDuality.family (actualFront R))
      (actualBase R).C (actualBase R).u (actualBase R).v) g ↔ InitialMinimal R g := by
  unfold SharedCap.MinimalGenerator
  rw [actual_LClosure]
  rfl

theorem actual_exceptional (R : ActualRolePacket P) :
    GenericCriticalDuality.exceptional (actualFront R)=borderExceptional R := by
  ext g
  unfold GenericCriticalDuality.exceptional SharedCap.Socle
  rw [actual_LClosure,actual_MClosure]
  rfl

theorem actual_additional (R : ActualRolePacket P) :
    GenericCriticalDuality.additional (actualFront R)=survivingSourceWraps R := by
  ext g
  constructor
  · rintro ⟨hmin,hnot,z,hz,hy,hg⟩
    have hm := (actual_minimal R g).mp hmin
    rw [actual_family] at hnot hz
    have hsource : g∈sourceWraps R := by
      rcases hz with ⟨s,rfl⟩ | rfl
      · exact ⟨s,hy,hg⟩
      · have hzero := actual_boundary_wrap_zero R hy
        have ho := GenericCriticalDuality.minimal_zero_original
          (GenericCriticalDuality.family (actualFront R)) (actualBase R).C (actualBase R).u
          (actualBase R).v g hmin
          (by rw [actual_family]; exact hg ▸ hzero)
        exact (hnot (by rw [actual_family] at ho; exact ho)).elim
    refine ⟨hsource,hm,?_⟩
    rintro ((hgY | hgS) | hgB)
    · have hgY' : g=(0,c2 P.M.base R.e,0) := hgY
      have hgy : g.2.1=0 := by rw [hg]; rfl
      rw [hgY'] at hgy
      exact (herzogC_positive P.M.base R.e 1).ne' hgy
    · exact hnot (Or.inl hgS)
    · exact hnot (Or.inr hgB)
  · rintro ⟨⟨s,hy,hg⟩,hmin,hnot⟩
    refine ⟨(actual_minimal R g).mpr hmin,?_,sourceNormal R s,?_,hy,hg⟩
    · rw [actual_family]
      rintro (hs | hb)
      · exact hnot (Or.inl (Or.inr hs))
      · exact hnot (Or.inr hb)
    · rw [actual_family]
      exact Or.inl ⟨s,rfl⟩

theorem actual_full_source_count (R : ActualRolePacket P) :
    GenericCriticalDuality.fullSupport (actualFront R)=
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} := by
  rw [GenericCriticalDuality.fullSupport_source_count]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun s => ?_)
  change (0<((actualBase R).norm s) 0 ∧ 0<((actualBase R).norm s) 1 ∧ 0<((actualBase R).norm s) 2) ↔
    (0<(sourceNormal R s).1 ∧ 0<(sourceNormal R s).2.1 ∧ 0<(sourceNormal R s).2.2)
  rw [←actual_normal_tuple R s]
  rfl

/-- The original actual packet theorem is a literal instance of the full
common critical-return duality, including internal-cut and mixed-alive cases. -/
theorem actual_packet_compensation (R : ActualRolePacket P) :
    survivingWrapCount R+Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
      Nat.card {z // z∈borderExceptional R} := by
  have h := GenericCriticalDuality.compensation (actualFront R)
  rw [actual_additional,actual_full_source_count,actual_exceptional] at h
  exact h

end NS25Lean.ActualGenericDualityAdapter
