import NS25Lean.SharedTailPurePairNormal

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse L4A L3C FourGeneratedBridge

theorem PurePair.integer_normal_exists {H : NumericalSemigroup} (D : PurePair H) (z : ℤ) :
    ∃ i j k : ℤ, 0 ≤ j ∧ j < D.alpha ∧ 0 ≤ k ∧ k < D.d ∧ z=i*D.a+j*D.b+k*D.c := by
  obtain ⟨k,l,hk,hkd,hl⟩ := two_generator_normal_form D.d D.c D.d_pos D.d_c_coprime z
  obtain ⟨j,i,hj,hja,hi⟩ := two_generator_normal_form D.alpha D.beta D.alpha_pos D.alpha_beta_coprime l
  refine ⟨i,j,k,hj,hja,hk,hkd,?_⟩
  have ha : (D.a:ℤ)=D.d*D.alpha := by exact_mod_cast D.scale_a
  have hb : (D.b:ℤ)=D.d*D.beta := by exact_mod_cast D.scale_b
  rw [hl,hi,ha,hb]
  ring

theorem PurePair.integer_normal_unique {H : NumericalSemigroup} (D : PurePair H)
    (i j k i' j' k' : ℤ) (hj : 0 ≤ j) (hja : j < D.alpha) (hk : 0 ≤ k) (hkd : k < D.d)
    (hj' : 0 ≤ j') (hja' : j' < D.alpha) (hk' : 0 ≤ k') (hkd' : k' < D.d)
    (he : i*D.a+j*D.b+k*D.c=i'*D.a+j'*D.b+k'*D.c) : i=i' ∧ j=j' ∧ k=k' := by
  let t : ℤ := max (-i) (-i')
  have hi0 : 0 ≤ i+t := by dsimp [t]; omega
  have hi0' : 0 ≤ i'+t := by dsimp [t]; omega
  let e := vector (i+t).toNat j.toNat k.toNat
  let f := vector (i'+t).toNat j'.toNat k'.toNat
  have hey : e 1 < D.alpha := by simp only [e,vector_one]; omega
  have hez : e 2 < D.d := by simp only [e,vector_two]; omega
  have hfy : f 1 < D.alpha := by simp only [f,vector_one]; omega
  have hfz : f 2 < D.d := by simp only [f,vector_two]; omega
  have hw : D.triple.weight e=D.triple.weight f := by
    simp only [e,f,vector_weight,Triple.grid]
    apply Int.ofNat_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg hi0,Int.toNat_of_nonneg hi0',Int.toNat_of_nonneg hj,
      Int.toNat_of_nonneg hk,Int.toNat_of_nonneg hj',Int.toNat_of_nonneg hk']
    nlinarith
  have hu := D.normal_unique e f hey hez hfy hfz hw
  have h0 := congrArg (fun e : Exponent => (e 0:ℤ)) hu
  have h1 := congrArg (fun e : Exponent => (e 1:ℤ)) hu
  have h2 := congrArg (fun e : Exponent => (e 2:ℤ)) hu
  simp only [e,f,vector_zero,vector_one,vector_two,Int.toNat_of_nonneg hi0,
    Int.toNat_of_nonneg hi0',Int.toNat_of_nonneg hj,Int.toNat_of_nonneg hk,
    Int.toNat_of_nonneg hj',Int.toNat_of_nonneg hk'] at h0 h1 h2
  exact ⟨by omega,h1,h2⟩

theorem PurePair.integer_normal_membership {H : NumericalSemigroup} (D : PurePair H)
    (i j k : ℤ) (hj : 0 ≤ j) (hja : j < D.alpha) (hk : 0 ≤ k) (hkd : k < D.d) :
    IntMem H.toAddSubmonoid (i*D.a+j*D.b+k*D.c) ↔ 0 ≤ i := by
  constructor
  · rintro ⟨n,hn,he⟩
    obtain ⟨e,hew⟩ := D.triple.factor n hn
    obtain ⟨f,hy,hz,hp⟩ := D.reduced.normal_exists e
    have hfw := context_path_weight D.triple D.reduced.relations D.reduced.relation_weight hp
    have hthree := D.triple.weight_three f
    dsimp [Triple.grid] at hthree
    change D.triple.weight f=f 0*D.a+f 1*D.b+f 2*D.c at hthree
    have heq : i*D.a+j*D.b+k*D.c=(f 0:ℤ)*D.a+(f 1:ℤ)*D.b+(f 2:ℤ)*D.c := by
      rw [he]
      exact_mod_cast (show n=f 0*D.a+f 1*D.b+f 2*D.c by omega)
    have hx := D.integer_normal_unique i j k (f 0) (f 1) (f 2) hj hja hk hkd
      (by positivity) (by exact_mod_cast hy) (by positivity) (by exact_mod_cast hz) heq
    rw [hx.1]
    positivity
  · intro hi
    refine ⟨D.triple.weight (vector i.toNat j.toNat k.toNat),D.triple.member _,?_⟩
    simp only [vector_weight,Triple.grid]
    push_cast
    rw [Int.toNat_of_nonneg hi,Int.toNat_of_nonneg hj,Int.toNat_of_nonneg hk]

/-- Exact symmetry of the primitive pure-pair semigroup, for every integer. -/
theorem PurePair.integer_symmetry {H : NumericalSemigroup} (D : PurePair H) (z : ℤ) :
    let F : ℤ := ((D.alpha:ℤ)-1)*D.b+((D.d:ℤ)-1)*D.c-D.a
    IntMem H.toAddSubmonoid (F-z) ↔ ¬IntMem H.toAddSubmonoid z := by
  dsimp only
  obtain ⟨i,j,k,hj,hja,hk,hkd,he⟩ := D.integer_normal_exists z
  have hF : ((D.alpha:ℤ)-1)*D.b+((D.d:ℤ)-1)*D.c-D.a-z=
      (-1-i)*D.a+((D.alpha:ℤ)-1-j)*D.b+((D.d:ℤ)-1-k)*D.c := by rw [he]; ring
  rw [he,D.integer_normal_membership i j k hj hja hk hkd]
  have hmem := D.integer_normal_membership (-1-i) ((D.alpha:ℤ)-1-j) ((D.d:ℤ)-1-k)
    (by omega) (by omega) (by omega) (by omega)
  have hF' : ((D.alpha:ℤ)-1)*D.b+((D.d:ℤ)-1)*D.c-D.a-
      (i*D.a+j*D.b+k*D.c)=(-1-i)*D.a+((D.alpha:ℤ)-1-j)*D.b+((D.d:ℤ)-1-k)*D.c := by ring
  rw [hF',hmem]
  omega

theorem PurePair.Reduced.b_seam {H : NumericalSemigroup} {D : PurePair H} (R : D.Reduced)
    (k : ℕ) : (D.alpha-1)*D.b+k*D.c+D.b=D.beta*D.a+k*D.c := by
  have ha := Nat.sub_add_cancel D.alpha_pos
  nlinarith [R.pure_relation]

theorem PurePair.Reduced.c_seam {H : NumericalSemigroup} {D : PurePair H} (R : D.Reduced)
    (j : ℕ) : j*D.b+(D.d-1)*D.c+D.c=
      (R.r+(j+R.s)/D.alpha*D.beta)*D.a+((j+R.s)%D.alpha)*D.b := by
  have hd := Nat.sub_add_cancel D.d_pos
  have hdiv := Nat.div_add_mod (j+R.s) D.alpha
  have hdivb := congrArg (fun n => n*D.b) hdiv
  have hdc := congrArg (fun n => n*D.c) hd
  have hpair := congrArg (fun n => n*((j+R.s)/D.alpha)) R.pure_relation
  nlinarith only [hdivb,hdc,hpair,R.mixed_relation]

end NS25Lean.SharedTail
