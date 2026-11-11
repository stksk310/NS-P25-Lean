import NS25Lean.P2ReturnPresentationAdapter
import NS25Lean.P2PureInternalTransverse

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalNormalForm
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen
  ReturnSourceRigidity ReturnPresentationAdapter PureInternalTransverse

def normal (C u v : ℕ) (e : Exponent) : Exponent :=
  vector (e 0+u*(e 1/C)) (e 1%C) (e 2+v*(e 1/C))

theorem normal_y_lt (C u v : ℕ) (hC : 0<C) (e : Exponent) : normal C u v e 1<C := by
  simpa only [normal,vector_one] using Nat.mod_lt (e 1) hC

theorem normal_fixed (C u v : ℕ) {e : Exponent} (he : e 1<C) : normal C u v e=e := by
  ext i
  fin_cases i <;> simp [normal,Nat.div_eq_of_lt he,Nat.mod_eq_of_lt he]

theorem normal_idempotent (C u v : ℕ) (hC : 0<C) (e : Exponent) :
    normal C u v (normal C u v e)=normal C u v e :=
  normal_fixed C u v (normal_y_lt C u v hC e)

theorem normal_degree {H : NumericalSemigroup} (T : Triple H)
    (C u v : ℕ) (hrel : C*T.g 1=u*T.g 0+v*T.g 2) (e : Exponent) :
    T.weight (normal C u v e)=T.weight e := by
  have hr := congrArg (fun n => n*(e 1/C)) hrel
  have hd := congrArg (fun n => n*T.g 1) (Nat.div_add_mod (e 1) C)
  rw [normal,vector_weight,T.weight_three]
  dsimp [Triple.grid]
  nlinarith only [hr,hd]

theorem normal_active (C u v : ℕ) (hC : 0<C) (d : Exponent) :
    normal C u v (vector 0 C 0+d)=normal C u v (vector u 0 v+d) := by
  have hd : (C+d 1)/C=d 1/C+1 := by
    simpa only [Nat.add_comm] using Nat.add_div_right (d 1) hC
  have hm : (C+d 1)%C=d 1%C := by
    simpa only [Nat.add_comm] using Nat.add_mod_right (d 1) C
  ext i
  fin_cases i <;> simp [normal,hd,hm,Nat.mul_add] <;> omega

def Active (C u v : ℕ) (lr : Exponent×Exponent) : Prop :=
  lr=(vector 0 C 0,vector u 0 v) ∨ lr=(vector u 0 v,vector 0 C 0)

theorem normal_active_step (C u v : ℕ) (hC : 0<C)
    (S : Set (Exponent×Exponent)) {e f : Exponent}
    (hs : Move {lr | lr∈S ∧ Active C u v lr} e f) :
    normal C u v e=normal C u v f := by
  obtain ⟨l,r,⟨_,hact⟩,d,rfl,rfl⟩ := hs
  rcases hact with h | h
  · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
    exact normal_active C u v hC d
  · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
    exact (normal_active C u v hC d).symm

theorem normal_active_path (C u v : ℕ) (hC : 0<C)
    (S : Set (Exponent×Exponent)) {e f : Exponent}
    (hp : Relation.ReflTransGen (Move {lr | lr∈S ∧ Active C u v lr}) e f) :
    normal C u v e=normal C u v f := by
  induction hp with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (normal_active_step C u v hC S hs)

/-- F-normal uniqueness at every actual source degree, derived from the
genuine toric presentation and proper K-predecessors of all inactive moves. -/
theorem source_f_normal_unique {H : NumericalSemigroup} (T : Triple H)
    (m C u v : ℕ) (hC : 0<C) (S : Set (Exponent×Exponent))
    (hgen : Presentation.relationIdeal ℚ S=
      Presentation.relationIdeal ℚ {lr : Exponent×Exponent | T.weight lr.1=T.weight lr.2})
    (hrel : ∀ lr∈symmetricRelations S, T.weight lr.1=T.weight lr.2)
    (hinactive : ∀ lr∈symmetricRelations S, ¬Active C u v lr →
      ∃ p∈cyclicCut H m, ∃ g∈H, 0<g ∧ T.weight lr.1=p+g)
    (s : IdealSources H (cyclicCut H m))
    {e f : Exponent} (he : T.weight e=s.val) (hf : T.weight f=s.val) :
    normal C u v e=normal C u v f := by
  have hp := move_connected_of_relationIdeal_eq T S hgen e f (he.trans hf.symm)
  have ha := source_path_uses_active T m (symmetricRelations S) (Active C u v)
    hrel hinactive s he hp
  exact normal_active_path C u v hC (symmetricRelations S) ha

def sourceNormal {H : NumericalSemigroup} (T : Triple H) (m C u v : ℕ)
    (s : IdealSources H (cyclicCut H m)) : Exponent :=
  normal C u v (Classical.choose (T.factor s.val s.property.1.1))

theorem sourceNormal_degree {H : NumericalSemigroup} (T : Triple H)
    (m C u v : ℕ) (hrel : C*T.g 1=u*T.g 0+v*T.g 2)
    (s : IdealSources H (cyclicCut H m)) :
    T.weight (sourceNormal T m C u v s)=s.val := by
  rw [sourceNormal,normal_degree T C u v hrel]
  exact Classical.choose_spec (T.factor s.val s.property.1.1)

theorem sourceNormal_spec {H : NumericalSemigroup} (T : Triple H)
    (m C u v : ℕ) (hC : 0<C) (htie : C*T.g 1=u*T.g 0+v*T.g 2)
    (S : Set (Exponent×Exponent))
    (hgen : Presentation.relationIdeal ℚ S=
      Presentation.relationIdeal ℚ {lr : Exponent×Exponent | T.weight lr.1=T.weight lr.2})
    (hrel : ∀ lr∈symmetricRelations S, T.weight lr.1=T.weight lr.2)
    (hinactive : ∀ lr∈symmetricRelations S, ¬Active C u v lr →
      ∃ p∈cyclicCut H m, ∃ g∈H, 0<g ∧ T.weight lr.1=p+g)
    (s : IdealSources H (cyclicCut H m)) :
    T.weight (sourceNormal T m C u v s)=s.val ∧
      sourceNormal T m C u v s 1<C ∧
      ∀ e : Exponent, T.weight e=s.val → normal C u v e=sourceNormal T m C u v s := by
  refine ⟨sourceNormal_degree T m C u v htie s,normal_y_lt C u v hC _,?_⟩
  intro e he
  exact source_f_normal_unique T m C u v hC S hgen hrel hinactive s he
    (Classical.choose_spec (T.factor s.val s.property.1.1))

end NS25Lean.CriticalNormalForm
