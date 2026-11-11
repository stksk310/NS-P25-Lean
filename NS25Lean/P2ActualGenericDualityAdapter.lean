import NS25Lean.P2GenericCriticalDuality
import NS25Lean.P2ErasureActualAdapters
import NS25Lean.P2SectorCPureCCapsR37

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.ActualGenericDualityAdapter
open Classical ChosenBase FourGeneratedBridge L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H
  L5A2C4OR1 L5A2C4OR5 L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33 L5A2C4OR35 L5A2C4OR36 L5A2C4OR37
  ErasedSourceScreen ErasureActualAdapters PureInternalTransverse CriticalCapGeometry
  CriticalPresentationModes CriticalFullSignature GenericCriticalCompensation
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

def actualBase (R : ActualRolePacket P) : Base (routingH P.M.base R.e) where
  triple := actualTriple P.M.base R.e
  critical := actualCritical P.M.base R.e
  m := routingM P.M.base R.e
  m_pos := routingM_pos P.M.base R.e
  u := cr21 R.HD
  v := cr23 R.HD
  u_pos := (coherent_coefficients_positive _ _ R.HD).2.2.1
  v_pos := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  tie := by simpa [actualCritical,L5A2C4A.herzogC] using (coherent_normalized_relations _ _ R.HD).2.1

def actualMode (R : ActualRolePacket P) : Mode (actualBase R) :=
  .positive (cr12 R.HD) (cr13 R.HD) (cr31 R.HD) (cr32 R.HD)
    (coherent_coefficients_positive _ _ R.HD).1
    (coherent_coefficients_positive _ _ R.HD).2.1
    (coherent_coefficients_positive _ _ R.HD).2.2.2.2.1
    (coherent_coefficients_positive _ _ R.HD).2.2.2.2.2
    (coherent_coefficients _ _ R.HD).1
    (coherent_coefficients _ _ R.HD).2.1
    (coherent_coefficients _ _ R.HD).2.2
    (by simpa [actualBase,actualCritical,L5A2C4A.herzogC] using (coherent_normalized_relations _ _ R.HD).1)
    (by simpa [actualBase,actualCritical,L5A2C4A.herzogC] using (coherent_normalized_relations _ _ R.HD).2.2)

def actualMixed (R : ActualRolePacket P) : Bool :=
  decide (c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e∈
    cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))

theorem actual_pred_equalities (R : ActualRolePacket P) :
    (cr21 R.HD-1)*routingA P.M.base R.e+cr23 R.HD*routingC P.M.base R.e=
      c2 P.M.base R.e*routingB P.M.base R.e-routingA P.M.base R.e ∧
    cr21 R.HD*routingA P.M.base R.e+(cr23 R.HD-1)*routingC P.M.base R.e=
      c2 P.M.base R.e*routingB P.M.base R.e-routingC P.M.base R.e ∧
    (cr12 R.HD-1)*routingB P.M.base R.e+cr13 R.HD*routingC P.M.base R.e=
      c1 P.M.base R.e*routingA P.M.base R.e-routingB P.M.base R.e ∧
    cr12 R.HD*routingB P.M.base R.e+(cr13 R.HD-1)*routingC P.M.base R.e=
      c1 P.M.base R.e*routingA P.M.base R.e-routingC P.M.base R.e ∧
    (cr31 R.HD-1)*routingA P.M.base R.e+cr32 R.HD*routingB P.M.base R.e=
      c3 P.M.base R.e*routingC P.M.base R.e-routingA P.M.base R.e ∧
    cr31 R.HD*routingA P.M.base R.e+(cr32 R.HD-1)*routingB P.M.base R.e=
      c3 P.M.base R.e*routingC P.M.base R.e-routingB P.M.base R.e := by
  have hp := coherent_coefficients_positive _ _ R.HD
  rcases coherent_normalized_relations _ _ R.HD with ⟨hrA,hrB,hrC⟩
  have hu := congrArg (fun n => n*routingA P.M.base R.e) (show cr21 R.HD-1+1=cr21 R.HD by omega)
  have hv := congrArg (fun n => n*routingC P.M.base R.e) (show cr23 R.HD-1+1=cr23 R.HD by omega)
  have hpp := congrArg (fun n => n*routingB P.M.base R.e) (show cr12 R.HD-1+1=cr12 R.HD by omega)
  have hq := congrArg (fun n => n*routingC P.M.base R.e) (show cr13 R.HD-1+1=cr13 R.HD by omega)
  have hw := congrArg (fun n => n*routingA P.M.base R.e) (show cr31 R.HD-1+1=cr31 R.HD by omega)
  have hz := congrArg (fun n => n*routingB P.M.base R.e) (show cr32 R.HD-1+1=cr32 R.HD by omega)
  simp only [Nat.add_mul,one_mul] at hu hv hpp hq hw hz
  omega

def actualFront (R : ActualRolePacket P) : Front (actualBase R) (actualMode R) where
  mixed := actualMixed R
  axis_killed := by
    simpa [actualBase,actualCritical,L5A2C4A.herzogC,Nat.sub_mul] using (actual_normalized_inactive_killed R).1
  pure_b_live := by
    simpa [actualBase,actualCritical,L5A2C4A.herzogC,Nat.sub_mul] using (actual_normalized_internal_live R).2.1
  mixed_x_live := by
    simpa only [actualBase,actual_g_zero,actual_g_two,(actual_pred_equalities R).1] using
      (actual_normalized_internal_live R).1
  mixed_z_live := by
    simpa only [actualBase,actual_g_zero,actual_g_two,(actual_pred_equalities R).2.1] using
      (actual_normalized_internal_live R).2.2
  inactive_killed := by
    change (actualTriple P.M.base R.e).weight (vector 0 (cr12 R.HD-1) (cr13 R.HD))∈(actualBase R).K ∨
      (actualTriple P.M.base R.e).weight (vector 0 (cr12 R.HD) (cr13 R.HD-1))∈(actualBase R).K
    simpa only [Base.K,actualBase,vector_weight,Triple.grid,actual_g_one,actual_g_two,zero_mul,zero_add,
      (actual_pred_equalities R).2.2.1,(actual_pred_equalities R).2.2.2.1] using
      (actual_normalized_inactive_killed R).2
  boundary := by
    have hpred := actual_pred_equalities R
    rcases actual_normalized_boundary_dichotomy R with h | h
    · have hm : actualMixed R=true := by simp [actualMixed,h.1]
      simp only [actualMode,boundaryGuards,hm,ite_true]
      simp only [Base.L,actualBase,actualCritical,actual_g_two]
      change (c3 P.M.base R.e-1)*routingC P.M.base R.e∈(actualBase R).K ∧
        (actualTriple P.M.base R.e).weight (vector (cr31 R.HD-1) (cr32 R.HD) 0)∉(actualBase R).K ∧
        (actualTriple P.M.base R.e).weight (vector (cr31 R.HD) (cr32 R.HD-1) 0)∉(actualBase R).K
      simp only [vector_weight,Triple.grid,actual_g_zero,actual_g_one,actual_g_two,zero_mul,add_zero,
        hpred.2.2.2.2.1,hpred.2.2.2.2.2]
      simpa [Base.K,actualBase,Nat.sub_mul] using h
    · have hm : actualMixed R=false := by simp [actualMixed,h.1]
      simp only [actualMode,boundaryGuards,hm,Bool.false_eq_true,ite_false]
      simp only [CriticalReverseExchange.boundaryKilled,Base.L,actualBase,actualCritical,actual_g_two]
      change (c3 P.M.base R.e-1)*routingC P.M.base R.e∉(actualBase R).K ∧
        ((actualTriple P.M.base R.e).weight (vector (cr31 R.HD-1) (cr32 R.HD) 0)∈(actualBase R).K ∨
        (actualTriple P.M.base R.e).weight (vector (cr31 R.HD) (cr32 R.HD-1) 0)∈(actualBase R).K)
      simp only [vector_weight,Triple.grid,actual_g_zero,actual_g_one,actual_g_two,zero_mul,add_zero,
        hpred.2.2.2.2.1,hpred.2.2.2.2.2]
      simpa [Base.K,actualBase,Nat.sub_mul] using h

theorem actual_normal_tuple (R : ActualRolePacket P) (s : ModelSources P.M.base R.e) :
    tuple ((actualBase R).norm s)=sourceNormal R s := by
  have hd : monomialDegree P.M.base R.e (tuple ((actualBase R).norm s))=s.val :=
    (actualBase R).norm_degree s
  have hy : (tuple ((actualBase R).norm s)).2.1<c2 P.M.base R.e := (actualBase R).norm_y_lt s
  have hn := (sourceNormal_spec R s).2.2 (tuple ((actualBase R).norm s)) hd
  simpa only [f2Normal,Nat.div_eq_of_lt hy,Nat.mod_eq_of_lt hy,mul_zero,add_zero] using hn

theorem actual_endpoint_tuple (R : ActualRolePacket P) :
    tuple (endpoint (actualMode R) (actualFront R).mixed)=boundaryAliveMonomial R := by
  by_cases hk : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
  · simp only [c3,L5A2C4A.herzogC] at hk
    simp [actualMode,actualFront,actualMixed,endpoint,boundaryAliveMonomial,hk,tuple,
      c3,L5A2C4A.herzogC]
  · simp only [c3,L5A2C4A.herzogC] at hk
    simp [actualMode,actualFront,actualMixed,endpoint,boundaryAliveMonomial,hk,tuple,
      Base.L,actualBase,actualCritical,c3,L5A2C4A.herzogC]

def actualOriginals (R : ActualRolePacket P) : Set Monomial :=
  Set.range (sourceNormal R)∪{boundaryAliveMonomial R}

theorem actual_family (R : ActualRolePacket P) :
    GenericCriticalDuality.family (actualFront R)=actualOriginals R := by
  ext g
  constructor
  · rintro ⟨e,(⟨s,rfl⟩ | rfl),rfl⟩
    · exact Or.inl ⟨s,(actual_normal_tuple R s).symm⟩
    · exact Or.inr (actual_endpoint_tuple R)
  · rintro (⟨s,rfl⟩ | rfl)
    · exact ⟨(actualBase R).norm s,Or.inl ⟨s,rfl⟩,actual_normal_tuple R s⟩
    · exact ⟨endpoint (actualMode R) (actualFront R).mixed,Or.inr rfl,actual_endpoint_tuple R⟩

end NS25Lean.ActualGenericDualityAdapter
