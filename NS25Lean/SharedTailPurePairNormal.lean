import NS25Lean.SharedTailPurePair

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse L4A L3C

structure PurePair.Reduced {H : NumericalSemigroup} (D : PurePair H) where
  r : ℕ
  s : ℕ
  s_bound : s<D.alpha
  relation : D.c=r*D.alpha+s*D.beta

def PurePair.reduced {H : NumericalSemigroup} (D : PurePair H) : D.Reduced := by
  classical
  exact Classical.choice (show Nonempty D.Reduced from by
    obtain ⟨r,s,hs,he⟩ := D.reduced_witness_exists
    exact ⟨⟨r,s,hs,he⟩⟩)

def PurePair.Reduced.relations {H : NumericalSemigroup} {D : PurePair H} (R : D.Reduced) :
    Set (Exponent×Exponent) :=
  {(vector 0 D.alpha 0,vector D.beta 0 0),(vector 0 0 D.d,vector R.r R.s 0)}

theorem PurePair.Reduced.pure_relation {H : NumericalSemigroup} {D : PurePair H} (R : D.Reduced) :
    D.alpha*D.b=D.beta*D.a := by rw [D.scale_a,D.scale_b]; ring
theorem PurePair.Reduced.mixed_relation {H : NumericalSemigroup} {D : PurePair H} (R : D.Reduced) :
    D.d*D.c=R.r*D.a+R.s*D.b := by rw [R.relation,D.scale_a,D.scale_b]; ring

theorem PurePair.Reduced.relation_weight {H : NumericalSemigroup} {D : PurePair H}
    (R : D.Reduced) (lr : Exponent×Exponent) (h : lr∈R.relations) :
    D.triple.weight lr.1=D.triple.weight lr.2 := by
  rcases h with rfl | rfl <;> simp only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero]
  · exact R.pure_relation
  · exact R.mixed_relation

theorem context_path_weight {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent)) (hrel : ∀ lr∈S, T.weight lr.1=T.weight lr.2)
    {e f : Exponent} (hp : ContextPath S e f) : T.weight e=T.weight f := by
  induction hp with
  | refl => rfl
  | @tail v w _ hstep ih =>
    obtain ⟨lr,hlr,t,h⟩ := hstep
    have hw : T.weight v=T.weight w := by
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rw [map_add,map_add,hrel lr hlr]
    exact ih.trans hw

/-- The reduced pair coordinates are unique modulo the omitted a-axis. -/
theorem PurePair.rectangle_modEq_unique {H : NumericalSemigroup} (D : PurePair H)
    {i j i' j' : ℕ} (hi : i<D.alpha) (hj : j<D.d)
    (hi' : i'<D.alpha) (hj' : j'<D.d)
    (hmod : Nat.ModEq D.a (i*D.b+j*D.c) (i'*D.b+j'*D.c)) : i=i' ∧ j=j' := by
  rw [D.scale_a,D.scale_b] at hmod
  have hmodd : Nat.ModEq D.d (i*(D.d*D.beta)+j*D.c)
      (i'*(D.d*D.beta)+j'*D.c) := hmod.of_mul_right D.alpha
  have hib : Nat.ModEq D.d (i*(D.d*D.beta)) (i'*(D.d*D.beta)) := by
    have h0 : Nat.ModEq D.d (i*(D.d*D.beta)) 0 := by
      rw [Nat.modEq_zero_iff_dvd]; exact ⟨i*D.beta,by ring⟩
    have h1 : Nat.ModEq D.d (i'*(D.d*D.beta)) 0 := by
      rw [Nat.modEq_zero_iff_dvd]; exact ⟨i'*D.beta,by ring⟩
    exact h0.trans h1.symm
  have hjc := hib.add_left_cancel hmodd
  have hjmod : Nat.ModEq D.d j j' := hjc.cancel_right_of_coprime D.d_c_coprime
  have hjEq : j=j' := hjmod.eq_of_lt_of_lt hj hj'
  subst j'
  have himul : Nat.ModEq (D.d*D.alpha) (i*(D.d*D.beta)) (i'*(D.d*D.beta)) :=
    (Nat.ModEq.refl (j*D.c)).add_right_cancel hmod
  have hid : Nat.ModEq (D.d*D.alpha) (D.d*(i*D.beta)) (D.d*(i'*D.beta)) := by
    simpa [mul_assoc,mul_left_comm,mul_comm] using himul
  have hibeta : Nat.ModEq D.alpha (i*D.beta) (i'*D.beta) :=
    hid.mul_left_cancel' D.d_pos.ne'
  have himod : Nat.ModEq D.alpha i i' :=
    hibeta.cancel_right_of_coprime D.alpha_beta_coprime
  exact ⟨himod.eq_of_lt_of_lt hi hi',rfl⟩

theorem PurePair.normal_unique {H : NumericalSemigroup} (D : PurePair H)
    (e f : Exponent) (hey : e 1<D.alpha) (hez : e 2<D.d)
    (hfy : f 1<D.alpha) (hfz : f 2<D.d) (he : D.triple.weight e=D.triple.weight f) : e=f := by
  have hew := D.triple.weight_three e
  have hfw := D.triple.weight_three f
  dsimp [Triple.grid] at hew hfw
  have hmod : Nat.ModEq D.a (e 1*D.b+e 2*D.c) (f 1*D.b+f 2*D.c) := by
    have h0 : Nat.ModEq D.a (D.triple.weight e) (e 1*D.b+e 2*D.c) := by
      rw [hew]
      simp [Nat.ModEq,Nat.add_mod,Nat.mul_mod]
    have h1 : Nat.ModEq D.a (D.triple.weight f) (f 1*D.b+f 2*D.c) := by
      rw [hfw]
      simp [Nat.ModEq,Nat.add_mod,Nat.mul_mod]
    exact h0.symm.trans (he ▸ h1)
  obtain ⟨hy,hz⟩ := D.rectangle_modEq_unique hey hez hfy hfz hmod
  have h0 : e 0=f 0 := by
    have hp := D.triple.positive 0
    change 0<D.a at hp
    nlinarith
  ext i
  fin_cases i <;> assumption

/-- Two-stage nonnegative reduction, first in z and then in y. -/
theorem PurePair.Reduced.normal_exists {H : NumericalSemigroup} {D : PurePair H}
    (R : D.Reduced) (e : Exponent) :
    ∃ f : Exponent, f 1<D.alpha ∧ f 2<D.d ∧ ContextPath R.relations e f := by
  classical
  suffices hall : ∀ z x y : ℕ, ∃ f : Exponent,
      f 1<D.alpha ∧ f 2<D.d ∧ ContextPath R.relations (vector x y z) f by
    obtain ⟨f,hy,hz,hp⟩ := hall (e 2) (e 0) (e 1)
    exact ⟨f,hy,hz,(exponent_eq_vector e).symm ▸ hp⟩
  intro z
  induction z using Nat.strong_induction_on with
  | h z ih =>
    intro x y
    by_cases hz : D.d≤z
    · obtain ⟨f,hyf,hzf,hp⟩ := ih (z-D.d) (by have := D.d_pos; omega) (x+R.r) (y+R.s)
      have hstep : ContextPath R.relations (vector x y z)
          (vector (x+R.r) (y+R.s) (z-D.d)) := by
        have hc := context_step_of_relation R.relations (vector 0 0 D.d)
          (vector R.r R.s 0) (vector x y (z-D.d)) (by simp [PurePair.Reduced.relations])
        have h0 : vector 0 0 D.d+vector x y (z-D.d)=vector x y z := by
          ext i; fin_cases i <;> simp <;> omega
        have h1 : vector R.r R.s 0+vector x y (z-D.d)=vector (x+R.r) (y+R.s) (z-D.d) := by
          ext i; fin_cases i <;> simp <;> omega
        rwa [h0,h1] at hc
      exact ⟨f,hyf,hzf,hstep.trans hp⟩
    · have hzlt : z<D.d := by omega
      induction y using Nat.strong_induction_on generalizing x with
      | h y ihy =>
        by_cases hy : D.alpha≤y
        · obtain ⟨f,hyf,hzf,hp⟩ := ihy (y-D.alpha) (by have := D.alpha_pos; omega) (x+D.beta)
          have hstep : ContextPath R.relations (vector x y z) (vector (x+D.beta) (y-D.alpha) z) := by
            have hc := context_step_of_relation R.relations (vector 0 D.alpha 0)
              (vector D.beta 0 0) (vector x (y-D.alpha) z) (by simp [PurePair.Reduced.relations])
            have h0 : vector 0 D.alpha 0+vector x (y-D.alpha) z=vector x y z := by
              ext i; fin_cases i <;> simp <;> omega
            have h1 : vector D.beta 0 0+vector x (y-D.alpha) z=
                vector (x+D.beta) (y-D.alpha) z := by
              ext i; fin_cases i <;> simp <;> omega
            rwa [h0,h1] at hc
          exact ⟨f,hyf,hzf,hstep.trans hp⟩
        · exact ⟨vector x y z,by simpa using Nat.lt_of_not_ge hy,by simpa using hzlt,.refl⟩

theorem PurePair.Reduced.connected {H : NumericalSemigroup} {D : PurePair H} (R : D.Reduced)
    (e f : Exponent) (he : D.triple.weight e=D.triple.weight f) : ContextPath R.relations e f := by
  obtain ⟨e',hey,hez,hpe⟩ := R.normal_exists e
  obtain ⟨f',hfy,hfz,hpf⟩ := R.normal_exists f
  have hew := context_path_weight D.triple R.relations R.relation_weight hpe
  have hfw := context_path_weight D.triple R.relations R.relation_weight hpf
  have heq := D.normal_unique e' f' hey hez hfy hfz (hew.symm.trans (he.trans hfw))
  exact hpe.trans (heq.symm ▸ contextPath_symm R.relations hpf)

theorem PurePair.Reduced.exact_ideal {H : NumericalSemigroup} {D : PurePair H}
    (R : D.Reduced) (k : Type*) [Field k] : Presentation.relationIdeal k R.relations=
      Presentation.relationIdeal k {lr : Exponent×Exponent | D.triple.weight lr.1=D.triple.weight lr.2} :=
  ideal_eq_of_connected D.triple R.relations R.relation_weight R.connected k

end NS25Lean.SharedTail
