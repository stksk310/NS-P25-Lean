import NS25Lean.SharedTailPurePairInteger

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse L3C FourGeneratedBridge

theorem PurePair.Reduced.r_pos {H : NumericalSemigroup} {D : PurePair H} (R : D.Reduced) :
    0<R.r := by
  by_contra hn
  have hr : R.r=0 := by omega
  have hcpos := D.triple.positive 2
  change 0<D.c at hcpos
  have he : D.c=R.s*D.beta := by simpa [hr] using R.relation
  have hs : 0<R.s := by nlinarith
  have hm := D.critical.least 1 R.s (vector 0 0 D.d) hs (by simp) (by
    rw [vector_weight,Triple.grid]
    change R.s*D.b=0*D.a+0*D.b+D.d*D.c
    rw [D.scale_b,he]
    ring)
  rw [D.pure_exponents.2] at hm
  have hbound := R.s_bound
  omega

theorem PurePair.Reduced.rectangle_factorization_unique {H : NumericalSemigroup} {D : PurePair H}
    (R : D.Reduced) (j k : ℕ) (hj : j<D.alpha) (hk : k<D.d)
    (e : Exponent) (he : D.triple.weight e=j*D.b+k*D.c) : e=vector 0 j k := by
  apply CriticalShortFibers.unique_of_no_toric_side D.triple R.relations (R.exact_ideal ℚ)
    (vector 0 j k)
  · intro lr hlr
    rcases hlr with rfl | rfl
    · constructor
      · intro h; have hh := h 1; simp at hh; omega
      · intro h; have hh := h 0; simp at hh; have hp := D.beta_pos; omega
    · constructor
      · intro h; have hh := h 2; simp at hh; omega
      · intro h; have hh := h 0; simp at hh; have hp := R.r_pos; omega
  · simpa [vector_weight,Triple.grid] using he

theorem PurePair.Reduced.rectangle_apery {H : NumericalSemigroup} {D : PurePair H}
    (R : D.Reduced) (j k : ℕ) (hj : j<D.alpha) (hk : k<D.d) :
    j*D.b+k*D.c∈aperySet H.toAddSubmonoid D.a := by
  have hm : j*D.b+k*D.c∈H := by
    simpa [vector_weight,Triple.grid] using D.triple.member (vector 0 j k)
  refine ⟨hm,?_⟩
  by_cases hlt : j*D.b+k*D.c<D.a
  · exact Or.inl hlt
  · right
    intro hcut
    obtain ⟨e,hew⟩ := D.triple.factor _ hcut
    have hw : D.triple.weight (Finsupp.single 0 1+e)=j*D.b+k*D.c := by
      rw [map_add,D.triple.weight_single,one_mul,hew]
      change D.a+(j*D.b+k*D.c-D.a)=j*D.b+k*D.c
      omega
    have hu := R.rectangle_factorization_unique j k hj hk _ hw
    have h0 := congrArg (fun e : Exponent => e 0) hu
    simp at h0

theorem PurePair.Reduced.apery_rectangle_iff {H : NumericalSemigroup} {D : PurePair H}
    (R : D.Reduced) (h : ℕ) : h∈aperySet H.toAddSubmonoid D.a ↔
    ∃ j k : ℕ, j<D.alpha ∧ k<D.d ∧ h=j*D.b+k*D.c := by
  constructor
  · intro hh
    obtain ⟨e,hew⟩ := D.triple.factor h hh.1
    obtain ⟨f,hy,hz,hpath⟩ := R.normal_exists e
    have hfw := context_path_weight D.triple R.relations R.relation_weight hpath
    have hthree := D.triple.weight_three f
    change D.triple.weight f=f 0*D.a+f 1*D.b+f 2*D.c at hthree
    have hf0 : f 0=0 := by
      by_contra hn
      have hp : 0<f 0 := Nat.pos_of_ne_zero hn
      have hd := congrArg (fun n => n*D.a) (Nat.sub_add_cancel hp)
      have hd' : (f 0-1)*D.a+D.a=f 0*D.a := by simpa [Nat.add_mul] using hd
      have hge : D.a≤h := by omega
      have hsub := Nat.sub_add_cancel hge
      have hm : h-D.a∈H := by
        have hx := D.triple.member (vector (f 0-1) (f 1) (f 2))
        have hw : D.triple.weight (vector (f 0-1) (f 1) (f 2))=h-D.a := by
          rw [vector_weight,Triple.grid]
          change (f 0-1)*D.a+f 1*D.b+f 2*D.c=h-D.a
          omega
        exact hw ▸ hx
      rcases hh.2 with hlt | hnot
      · omega
      · exact hnot hm
    refine ⟨f 1,f 2,hy,hz,?_⟩
    rw [hf0,zero_mul,zero_add] at hthree
    omega
  · rintro ⟨j,k,hj,hk,rfl⟩
    exact R.rectangle_apery j k hj hk

end NS25Lean.SharedTail
