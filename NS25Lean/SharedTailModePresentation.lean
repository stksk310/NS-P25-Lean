import NS25Lean.SharedTailConnectivity

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse CriticalCapGeometry CriticalPresentationModes L3C

def Bridge {H : NumericalSemigroup} (T : Triple H) (S : Set (Exponent×Exponent))
    (e f : Exponent) : Prop := ∃ u v : Exponent,
    ContextPath S e u ∧ ContextPath S f v ∧ T.weight u=T.weight e ∧
    T.weight v=T.weight f ∧ ∃ j, 0<u j ∧ 0<v j

theorem bridge_symm {H : NumericalSemigroup} {T : Triple H}
    {S : Set (Exponent×Exponent)} {e f : Exponent} (h : Bridge T S e f) : Bridge T S f e := by
  obtain ⟨u,v,he,hf,hu,hv,j,huj,hvj⟩ := h
  exact ⟨v,u,hf,he,hv,hu,j,hvj,huj⟩

theorem critical_coordinate_bridge {H : NumericalSemigroup} (T : Triple H)
    (C : Critical T) (S : Set (Exponent×Exponent)) (i : Fin 3) (n : ℕ)
    (f r : Exponent) (hn : 0<n) (hfi : f i=0)
    (hf : T.weight f=n*T.g i) (hr : T.weight r=C.exponent i*T.g i)
    (hstep : ContextPath S (Finsupp.single i (C.exponent i)) r)
    (j : Fin 3) (hfj : 0<f j) (hrj : 0<r j) :
    Bridge T S (Finsupp.single i n) f := by
  have hCn := C.least i n f hn hfi hf.symm
  let d := Finsupp.single i (n-C.exponent i)
  have he : d+Finsupp.single i (C.exponent i)=Finsupp.single i n := by
    simp only [d,←Finsupp.single_add,Nat.sub_add_cancel hCn]
  have hp := contextPath_add S hstep d
  refine ⟨d+r,f,by simpa only [he] using hp,.refl,?_,rfl,j,?_,hfj⟩
  · rw [map_add,T.weight_single,T.weight_single,hr]
    have hh := congrArg (fun t => t*T.g i) (Nat.sub_add_cancel hCn)
    simp only [Nat.add_mul] at hh
    simpa only [d,T.weight_single] using hh
  · simp only [Finsupp.add_apply]
    omega

theorem mode_pure_bridge {H : NumericalSemigroup} {B : Base H} (D : Mode B)
    (i : Fin 3) (n : ℕ) (f : Exponent) (hn : 0<n) (hfn : f≠0)
    (hfi : f i=0) (hf : B.triple.weight f=n*B.triple.g i) :
    Bridge B.triple D.relations (Finsupp.single i n) f := by
  classical
  have vec (x y z : ℕ) := vector_weight B.triple x y z
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
    let D : Mode B := .positive p q w z hp hq hw hz hR hC hL hcenter hboundary
    obtain ⟨j,hfj⟩ : ∃ j : Fin 3, 0<f j := by
      by_contra h
      push Not at h
      exact hfn (by ext j; exact Nat.eq_zero_of_le_zero (h j))
    have hji : j≠i := by intro he; subst j; omega
    have s0 : ContextPath D.relations (Finsupp.single 0 B.R) (vector 0 p q) := by
      simpa [vector] using context_step_of_relation D.relations
        (vector B.R 0 0) (vector 0 p q) 0 (by simp [D,Mode.relations])
    have s1 : ContextPath D.relations (Finsupp.single 1 B.C) (vector B.u 0 B.v) := by
      simpa [vector] using context_step_of_relation D.relations
        (vector 0 B.C 0) (vector B.u 0 B.v) 0 (by simp [D,Mode.relations])
    have s2 : ContextPath D.relations (Finsupp.single 2 B.L) (vector w z 0) := by
      simpa [vector] using context_step_of_relation D.relations
        (vector 0 0 B.L) (vector w z 0) 0 (by simp [D,Mode.relations])
    fin_cases i
    · apply critical_coordinate_bridge B.triple B.critical D.relations 0 n f (vector 0 p q)
        hn hfi hf (by simpa [vector_weight,Triple.grid] using hcenter.symm) s0 j hfj
      fin_cases j <;> simp_all
    · apply critical_coordinate_bridge B.triple B.critical D.relations 1 n f (vector B.u 0 B.v)
        hn hfi hf (by simpa [vector_weight,Triple.grid] using B.tie.symm) s1 j hfj
      fin_cases j <;> simp_all [B.u_pos,B.v_pos]
    · apply critical_coordinate_bridge B.triple B.critical D.relations 2 n f (vector w z 0)
        hn hfi hf (by simpa [vector_weight,Triple.grid] using hboundary.symm) s2 j hfj
      fin_cases j <;> simp_all
  | purePair hpair =>
    let D : Mode B := .purePair hpair
    have s0 : ContextPath D.relations (Finsupp.single 0 B.R) (Finsupp.single 2 B.L) := by
      simpa [vector] using context_step_of_relation D.relations
        (vector B.R 0 0) (vector 0 0 B.L) 0 (by simp [D,Mode.relations])
    have s1 : ContextPath D.relations (Finsupp.single 1 B.C) (vector B.u 0 B.v) := by
      simpa [vector] using context_step_of_relation D.relations
        (vector 0 B.C 0) (vector B.u 0 B.v) 0 (by simp [D,Mode.relations])
    have s2 := contextPath_symm D.relations s0
    have swap (i : Fin 3) (hi : i=0 ∨ i=2) (n : ℕ) (f : Exponent)
        (hn : 0<n) (hfi : f i=0) (hf : B.triple.weight f=n*B.triple.g i)
        (hfother : ∀ j, j≠1 → f j=0) :
        Bridge B.triple D.relations (Finsupp.single i n) f := by
      have ff : f=Finsupp.single 1 (f 1) := by
        ext j
        by_cases hj : j=1
        · subst j; simp
        · simp [hj,hfother j hj]
      have hfy : 0<f 1 := by
        have hp := B.triple.positive i
        change 0<B.triple.g i at hp
        rw [ff,B.triple.weight_single] at hf
        nlinarith
      apply bridge_symm
      rw [ff]
      apply critical_coordinate_bridge B.triple B.critical D.relations 1 (f 1)
        (Finsupp.single i n) (vector B.u 0 B.v) hfy
        (by rcases hi with rfl | rfl <;> simp)
        (by rw [B.triple.weight_single,←hf,ff,B.triple.weight_single]; simp)
        (by simpa [vector_weight,Triple.grid] using B.tie.symm) s1 i
        (by simpa using hn)
      rcases hi with rfl | rfl <;> simp [B.u_pos,B.v_pos]
    fin_cases i
    · by_cases hfz : 0<f 2
      · exact critical_coordinate_bridge B.triple B.critical D.relations 0 n f
          (Finsupp.single 2 B.L) hn hfi hf
          (by simpa [B.triple.weight_single] using hpair.symm) s0 2 hfz
          (by simpa using B.critical.positive 2)
      · apply swap 0 (Or.inl rfl) n f hn hfi hf
        intro j hj
        fin_cases j <;> simp_all <;> omega
    · obtain ⟨j,hfj⟩ : ∃ j : Fin 3, 0<f j := by
        by_contra h
        push Not at h
        exact hfn (by ext j; exact Nat.eq_zero_of_le_zero (h j))
      have hj : j≠1 := by
        intro he
        subst j
        have hz : f 1=0 := hfi
        omega
      apply critical_coordinate_bridge B.triple B.critical D.relations 1 n f (vector B.u 0 B.v)
        hn hfi hf (by simpa [vector_weight,Triple.grid] using B.tie.symm) s1 j hfj
      fin_cases j <;> simp_all [B.u_pos,B.v_pos]
    · by_cases hfx : 0<f 0
      · exact critical_coordinate_bridge B.triple B.critical D.relations 2 n f
          (Finsupp.single 0 B.R) hn hfi hf
          (by simpa [B.triple.weight_single] using hpair) s2 0 hfx
          (by simpa using B.critical.positive 0)
      · apply swap 2 (Or.inr rfl) n f hn hfi hf
        intro j hj
        fin_cases j <;> simp_all <;> omega

/-- Both critical presentation modes generate every whole fiber. -/
theorem mode_connected {H : NumericalSemigroup} {B : Base H} (D : Mode B) :
    ∀ e f : Exponent, B.triple.weight e=B.triple.weight f → ContextPath D.relations e f := by
  apply connected_of_disjoint_bridges B.triple D.relations
  intro e f he hf hef hdis
  rcases disjoint_one_pure e f he hf hdis with ⟨i,n,hn,rfl⟩ | ⟨i,n,hn,rfl⟩
  · apply mode_pure_bridge D i n f hn hf
    · rcases hdis i with h | h
      · simp at h; omega
      · exact h
    · simpa only [B.triple.weight_single] using hef.symm
  · apply bridge_symm
    apply mode_pure_bridge D i n e hn he
    · rcases hdis i with h | h
      · exact h
      · simp at h; omega
    · simpa only [B.triple.weight_single] using hef

/-- Exact polynomial ideal generation over every field is derived here from
the true critical exponents; it is not a presentation field or assumption. -/
theorem mode_exact_ideal {H : NumericalSemigroup} {B : Base H} (D : Mode B)
    (k : Type*) [Field k] : Presentation.relationIdeal k D.relations=
      Presentation.relationIdeal k {lr : Exponent×Exponent |
        B.triple.weight lr.1=B.triple.weight lr.2} :=
  ideal_eq_of_connected B.triple D.relations D.relation_weight (mode_connected D) k

theorem mode_genuine {H : NumericalSemigroup} {B : Base H} (D : Mode B) : D.Genuine :=
  mode_exact_ideal D ℚ

end NS25Lean.SharedTail
