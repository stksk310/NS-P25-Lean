import NS25Lean.P2BranchBPrefixSignedAccounting

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-! N2's values in the actual inactive chart. O is eligible only in CENTER.
The arm branches include equality with p/q, hence their axis degeneration. -/
abbrev nonsymmetricF (R : SectorBCriticalRoleBranchB P) (i j : ℕ) := i*nsB R+j*nsC R
abbrev nonsymmetricO (R : SectorBCriticalRoleBranchB P) (depth : ℕ) := (nsC1 R-depth)*nsA R
def nonsymmetricX (R : SectorBCriticalRoleBranchB P) (i depth : ℕ) : ℕ :=
  if i < nsP R then (nsW R-depth)*nsA R+(i+nsZ R)*nsB R
  else (nsC1 R-depth)*nsA R+(i-nsP R)*nsB R
def nonsymmetricY (R : SectorBCriticalRoleBranchB P) (j depth : ℕ) : ℕ :=
  if j < nsQ R then (nsU R-depth)*nsA R+(j+nsV R)*nsC R
  else (nsC1 R-depth)*nsA R+(j-nsQ R)*nsC R

private theorem add_int_mem {H : NumericalSemigroup} (I : RelativeIdeal H)
    {z t : ℤ} (hz : z ∈ I) (ht : t ∈ H.asRelativeIdeal) : z+t ∈ I := by
  obtain ⟨n,hn,rfl⟩ := ht
  exact I.add_mem hz hn

theorem nonsymmetric_return_depth_lt_c1 (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hdom : NonsymmetricLDomain R i j)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    depth < nsC1 R := by
  have ha := nonsymmetric_single_return_admission R hB hp hdom hb
  have hc := nonsymmetric_coefficients R
  rcases hdom.2.2 with hi | hj
  · have := ha.2.2.1 hi; omega
  · have := ha.2.2.2 hj; omega

/-- Exact numerical differences, not a symbolic eta/envelope identification. -/
theorem nonsymmetric_single_return_source_differences (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hdom : NonsymmetricLDomain R i j)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    (nonsymmetricF R i j : ℤ)-(ell*normalizedM P.M.base : ℕ)=(depth*nsA R : ℕ) ∧
    (nonsymmetricX R i depth : ℤ)-(ell*normalizedM P.M.base : ℕ)=
      ((if i < nsP R then nsC3 R-j else nsQ R-j)*nsC R : ℕ) ∧
    (nonsymmetricY R j depth : ℤ)-(ell*normalizedM P.M.base : ℕ)=
      ((if j < nsQ R then nsC2 R-i else nsP R-i)*nsB R : ℕ) ∧
    (i < nsP R → j < nsQ R →
      (nonsymmetricO R depth : ℤ)-(ell*normalizedM P.M.base : ℕ)=
        ((nsP R-i)*nsB R+(nsQ R-j)*nsC R : ℕ)) := by
  have ha := nonsymmetric_single_return_admission R hB hp hdom hb
  have hd := nonsymmetric_return_depth_lt_c1 R hB hp hdom hb
  have hr := nonsymmetric_normalized_relations R
  have hbZ : (i : ℤ)*nsB R+j*nsC R=(ell*normalizedM P.M.base : ℕ)+(depth : ℤ)*nsA R := by exact_mod_cast hb
  simp only [Nat.cast_mul] at hbZ
  have r1 : (nsC1 R : ℤ)*nsA R=nsP R*nsB R+nsQ R*nsC R := by exact_mod_cast hr.1
  have r2 : (nsC2 R : ℤ)*nsB R=nsU R*nsA R+nsV R*nsC R := by exact_mod_cast hr.2.1
  have r3 : (nsC3 R : ℤ)*nsC R=nsW R*nsA R+nsZ R*nsB R := by exact_mod_cast hr.2.2
  have sub (a b : ℕ) (h : b ≤ a) : ((a-b : ℕ) : ℤ)+(b : ℤ)=a := by exact_mod_cast Nat.sub_add_cancel h
  refine ⟨?_,?_,?_,?_⟩
  · simp only [nonsymmetricF,Nat.cast_add,Nat.cast_mul]; nlinarith only [hbZ]
  · by_cases hi : i < nsP R
    · have h1 := sub (nsW R) depth (le_of_lt (ha.2.2.1 hi))
      have h2 := sub (nsC3 R) j (le_of_lt hdom.2.1)
      simp only [nonsymmetricX,if_pos hi,Nat.cast_add,Nat.cast_mul]
      nlinarith only [hbZ,r3,h1,h2]
    · have hj : j < nsQ R := by rcases hdom.2.2 with h | h; exact (hi h).elim; exact h
      have h1 := sub (nsC1 R) depth (le_of_lt hd)
      have h2 := sub i (nsP R) (by omega)
      have h3 := sub (nsQ R) j (le_of_lt hj)
      simp only [nonsymmetricX,if_neg hi,Nat.cast_add,Nat.cast_mul]
      nlinarith only [hbZ,r1,h1,h2,h3]
  · by_cases hj : j < nsQ R
    · have h1 := sub (nsU R) depth (le_of_lt (ha.2.2.2 hj))
      have h2 := sub (nsC2 R) i (le_of_lt hdom.1)
      simp only [nonsymmetricY,if_pos hj,Nat.cast_add,Nat.cast_mul]
      nlinarith only [hbZ,r2,h1,h2]
    · have hi : i < nsP R := by rcases hdom.2.2 with h | h; exact h; exact (hj h).elim
      have h1 := sub (nsC1 R) depth (le_of_lt hd)
      have h2 := sub j (nsQ R) (by omega)
      have h3 := sub (nsP R) i (le_of_lt hi)
      simp only [nonsymmetricY,if_neg hj,Nat.cast_add,Nat.cast_mul]
      nlinarith only [hbZ,r1,h1,h2,h3]
  · intro hi hj
    have h1 := sub (nsC1 R) depth (le_of_lt hd)
    have h2 := sub (nsP R) i (le_of_lt hi)
    have h3 := sub (nsQ R) j (le_of_lt hj)
    simp only [nonsymmetricO,Nat.cast_add,Nat.cast_mul]
    nlinarith only [hbZ,r1,h1,h2,h3]

theorem nonsymmetric_single_return_sources_mem (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hdom : NonsymmetricLDomain R i j)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    (nonsymmetricF R i j : ℤ) ∈ returnIdeal (nsH R) (ell*normalizedM P.M.base) ∧
    (nonsymmetricX R i depth : ℤ) ∈ returnIdeal (nsH R) (ell*normalizedM P.M.base) ∧
    (nonsymmetricY R j depth : ℤ) ∈ returnIdeal (nsH R) (ell*normalizedM P.M.base) ∧
    (i < nsP R → j < nsQ R →
      (nonsymmetricO R depth : ℤ) ∈ returnIdeal (nsH R) (ell*normalizedM P.M.base)) := by
  have hs := nonsymmetric_single_return_source_differences R hB hp hdom hb
  have hx : (nonsymmetricX R i depth : ℤ) ∈ (nsH R).asRelativeIdeal := by
    unfold nonsymmetricX; split_ifs with hi
    · simpa only [zero_mul,add_zero] using nonsymmetric_grid_mem R (nsW R-depth) (i+nsZ R) 0
    · simpa only [zero_mul,add_zero] using nonsymmetric_grid_mem R (nsC1 R-depth) (i-nsP R) 0
  have hy : (nonsymmetricY R j depth : ℤ) ∈ (nsH R).asRelativeIdeal := by
    unfold nonsymmetricY; split_ifs with hj
    · simpa only [zero_mul,zero_add,add_zero] using nonsymmetric_grid_mem R (nsU R-depth) 0 (j+nsV R)
    · simpa only [zero_mul,zero_add,add_zero] using nonsymmetric_grid_mem R (nsC1 R-depth) 0 (j-nsQ R)
  refine ⟨⟨?_,?_⟩,⟨hx,?_⟩,⟨hy,?_⟩,?_⟩
  · simpa only [zero_mul,zero_add] using nonsymmetric_grid_mem R 0 i j
  · change _ - _ ∈ (nsH R).asRelativeIdeal; rw [hs.1]
    simpa only [zero_mul,add_zero] using nonsymmetric_grid_mem R depth 0 0
  · change _ - _ ∈ (nsH R).asRelativeIdeal; rw [hs.2.1]
    simpa only [zero_mul,zero_add] using nonsymmetric_grid_mem R 0 0 (if i < nsP R then nsC3 R-j else nsQ R-j)
  · change _ - _ ∈ (nsH R).asRelativeIdeal; rw [hs.2.2.1]
    simpa only [zero_mul,zero_add,add_zero] using nonsymmetric_grid_mem R 0 (if j < nsQ R then nsC2 R-i else nsP R-i) 0
  · intro hi hj
    refine ⟨?_,?_⟩
    · simpa only [zero_mul,add_zero] using nonsymmetric_grid_mem R (nsC1 R-depth) 0 0
    · change _ - _ ∈ (nsH R).asRelativeIdeal; rw [hs.2.2.2 hi hj]
      simpa only [zero_mul,zero_add] using nonsymmetric_grid_mem R 0 (nsP R-i) (nsQ R-j)

/-- N2: exact generation of the individual return ideal. This includes the
arm axis degenerations; O is excluded on both strict arms. -/
theorem nonsymmetric_single_return_four_sources (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hdom : NonsymmetricLDomain R i j)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) (z : ℤ) :
    z ∈ returnIdeal (nsH R) (ell*normalizedM P.M.base) ↔
    z-(nonsymmetricF R i j : ℕ) ∈ (nsH R).asRelativeIdeal ∨
    z-(nonsymmetricX R i depth : ℕ) ∈ (nsH R).asRelativeIdeal ∨
    z-(nonsymmetricY R j depth : ℕ) ∈ (nsH R).asRelativeIdeal ∨
    (i < nsP R ∧ j < nsQ R ∧ z-(nonsymmetricO R depth : ℕ) ∈ (nsH R).asRelativeIdeal) := by
  have hs := nonsymmetric_single_return_source_differences R hB hp hdom hb
  constructor
  · rintro ⟨hzH,hret⟩
    change z-(ell*normalizedM P.M.base : ℕ) ∈ (nsH R).asRelativeIdeal at hret
    obtain ⟨w,hw,he⟩ := hret
    obtain ⟨a,b,c,hf⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) hw
    change w=a*nsA R+b*nsB R+c*nsC R at hf
    have heZ : z=(ell*normalizedM P.M.base : ℕ)+(a : ℤ)*nsA R+b*nsB R+c*nsC R := by
      rw [hf] at he; simp only [Nat.cast_add,Nat.cast_mul] at he; omega
    simp only [Nat.cast_mul] at heZ
    have ht := (nonsymmetric_single_return_colon_threshold R hB (x:=b) (y:=c) (height:=a) hp hdom hb).mp
      (show ((a*nsA R+b*nsB R+c*nsC R : ℕ) : ℤ)+(ell*normalizedM P.M.base : ℕ) ∈ (nsH R).asRelativeIdeal from by
        convert hzH using 1; simp only [Nat.cast_add,Nat.cast_mul]; linarith [heZ])
    have divBC (s tb tc : ℕ)
        (hd : (s : ℤ)-(ell*normalizedM P.M.base : ℕ)=(tb*nsB R+tc*nsC R : ℕ))
        (hb' : tb ≤ b) (hc' : tc ≤ c) : z-(s : ℕ) ∈ (nsH R).asRelativeIdeal := by
      have h1 : ((b-tb : ℕ) : ℤ)+(tb : ℤ)=b := by exact_mod_cast Nat.sub_add_cancel hb'
      have h2 : ((c-tc : ℕ) : ℤ)+(tc : ℤ)=c := by exact_mod_cast Nat.sub_add_cancel hc'
      have hm := nonsymmetric_grid_mem R a (b-tb) (c-tc)
      convert hm using 1
      simp only [Nat.cast_add,Nat.cast_mul] at hd ⊢
      nlinarith only [heZ,hd,h1,h2]
    have useX (hx : (if i < nsP R then nsC3 R-j else nsQ R-j) ≤ c) :=
      divBC (nonsymmetricX R i depth) 0 _ (by simpa only [zero_mul,zero_add] using hs.2.1) (by omega) hx
    have useY (hy : (if j < nsQ R then nsC2 R-i else nsP R-i) ≤ b) :=
      divBC (nonsymmetricY R j depth) _ 0 (by simpa only [zero_mul,add_zero] using hs.2.2.1) hy (by omega)
    rcases ht with ht | ht | ht | ⟨htb,htc⟩
    · left
      have h1 : ((a-depth : ℕ) : ℤ)+(depth : ℤ)=a := by exact_mod_cast Nat.sub_add_cancel ht
      have hm := nonsymmetric_grid_mem R (a-depth) b c
      have hd := hs.1
      convert hm using 1; simp only [Nat.cast_add,Nat.cast_mul] at hd ⊢
      nlinarith only [heZ,hd,h1]
    · right; right; left
      apply useY
      split_ifs <;> have := (nonsymmetric_coefficients R).2.2.2.2.2.2.2.1 <;> omega
    · right; left
      apply useX
      split_ifs <;> have := (nonsymmetric_coefficients R).2.2.2.2.2.2.2.2 <;> omega
    · by_cases hi : i < nsP R
      · by_cases hj : j < nsQ R
        · right; right; right
          exact ⟨hi,hj,divBC _ _ _ (hs.2.2.2 hi hj) (by omega) (by omega)⟩
        · right; right; left
          apply useY; simp only [if_neg hj]; omega
      · right; left
        apply useX; simp only [if_neg hi]; omega
  · intro hz
    have hm := nonsymmetric_single_return_sources_mem R hB hp hdom hb
    rcases hz with hf | hx | hy | ⟨hi,hj,ho⟩
    · simpa only [add_sub_cancel] using add_int_mem _ hm.1 hf
    · simpa only [add_sub_cancel] using add_int_mem _ hm.2.1 hx
    · simpa only [add_sub_cancel] using add_int_mem _ hm.2.2.1 hy
    · simpa only [add_sub_cancel] using add_int_mem _ (hm.2.2.2 hi hj) ho

theorem nonsymmetric_canonical_a_predecessor_not_mem (R : SectorBCriticalRoleBranchB P)
    {x y : ℕ} (hdom : NonsymmetricLDomain R x y) :
    ((x*nsB R+y*nsC R : ℕ) : ℤ)-nsA R ∉ (nsH R).asRelativeIdeal := by
  intro hm
  have he : ((x*nsB R+y*nsC R : ℕ) : ℤ)-nsA R=
      (-1 : ℤ)*nsA R+x*nsB R+y*nsC R := by push_cast; ring
  rw [he] at hm
  have := (nonsymmetric_signed_height_mem_iff R hdom (-1)).mp hm
  omega

private theorem grid_positive_a_predecessor (R : SectorBCriticalRoleBranchB P)
    {h x y : ℕ} (hp : 0 < h) :
    ((h*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)-nsA R ∈ (nsH R).asRelativeIdeal := by
  have he : ((h-1 : ℕ) : ℤ)+1=h := by omega
  convert nonsymmetric_grid_mem R (h-1) x y using 1
  simp only [Nat.cast_add,Nat.cast_mul]
  nlinarith only [he]

theorem nonsymmetric_nonF_source_a_predecessors (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hdom : NonsymmetricLDomain R i j)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    (nonsymmetricX R i depth : ℤ)-nsA R ∈ (nsH R).asRelativeIdeal ∧
    (nonsymmetricY R j depth : ℤ)-nsA R ∈ (nsH R).asRelativeIdeal ∧
    (nonsymmetricO R depth : ℤ)-nsA R ∈ (nsH R).asRelativeIdeal := by
  have ha := nonsymmetric_single_return_admission R hB hp hdom hb
  have hd := nonsymmetric_return_depth_lt_c1 R hB hp hdom hb
  refine ⟨?_,?_,?_⟩
  · unfold nonsymmetricX; split_ifs with hi
    · simpa only [zero_mul,add_zero] using
        grid_positive_a_predecessor R (x:=i+nsZ R) (y:=0) (by have := ha.2.2.1 hi; omega : 0 < nsW R-depth)
    · simpa only [zero_mul,add_zero] using
        grid_positive_a_predecessor R (x:=i-nsP R) (y:=0) (by omega : 0 < nsC1 R-depth)
  · unfold nonsymmetricY; split_ifs with hj
    · simpa only [zero_mul,zero_add,add_zero] using
        grid_positive_a_predecessor R (x:=0) (y:=j+nsV R) (by have := ha.2.2.2 hj; omega : 0 < nsU R-depth)
    · simpa only [zero_mul,zero_add,add_zero] using
        grid_positive_a_predecessor R (x:=0) (y:=j-nsQ R) (by omega : 0 < nsC1 R-depth)
  · simpa only [zero_mul,add_zero] using
      grid_positive_a_predecessor R (x:=0) (y:=0) (by omega : 0 < nsC1 R-depth)

/-- Dominance for a canonical actual F-divisor; the Herzog reduction cannot
hide a positive a-carry in a zero-height Apéry point. -/
theorem nonsymmetric_canonical_F_divisor_coordinates (R : SectorBCriticalRoleBranchB P)
    {x y i j : ℕ} (hdom : NonsymmetricLDomain R x y)
    (hdiv : ((x*nsB R+y*nsC R : ℕ) : ℤ)-(i*nsB R+j*nsC R : ℕ) ∈ (nsH R).asRelativeIdeal) :
    i ≤ x ∧ j ≤ y := by
  obtain ⟨w,hw,he⟩ := hdiv
  obtain ⟨a,b,c,hf⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) hw
  change w=a*nsA R+b*nsB R+c*nsC R at hf
  have heN : x*nsB R+y*nsC R=a*nsA R+(i+b)*nsB R+(j+c)*nsC R := by
    rw [hf] at he
    simp only [Nat.cast_add,Nat.cast_mul] at he
    exact_mod_cast (show (x : ℤ)*nsB R+y*nsC R=
      (a : ℤ)*nsA R+(i+b)*nsB R+(j+c)*nsC R by nlinarith only [he])
  have hn := nonsymmetric_canonical_a_predecessor_not_mem R hdom
  have ha : a=0 := by
    by_contra ha
    apply hn
    rw [heN]
    exact grid_positive_a_predecessor R (by omega)
  have heN' : x*nsB R+y*nsC R=(i+b)*nsB R+(j+c)*nsC R := by simpa only [ha,zero_mul,zero_add] using heN
  have hsum : NonsymmetricLDomain R (i+b) (j+c) := by
    by_contra hnot
    have hnot' : ¬ L5A2C4OR5.HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) (i+b) (j+c) := by
      simpa only [NonsymmetricLDomain,L5A2C4OR5.HerzogLShapeDomain,
        branchB_inactive_coherent_c2,branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12,branchB_inactive_coherent_cr13] using hnot
    obtain ⟨I,J,K,_,hk,hr⟩ := branchB_coherent_exists_positive_reduction_of_not_domain
      P.M.base (nsReindex R) (branchB_inactive_coherentHerzogData R) (i+b) (j+c) hnot'
    change (i+b)*nsB R+(j+c)*nsC R=I*nsB R+J*nsC R+K*nsA R at hr
    apply hn
    have he' : x*nsB R+y*nsC R=K*nsA R+I*nsB R+J*nsC R := by rw [heN',hr]; ring
    rw [he']
    exact grid_positive_a_predecessor R hk
  have hu := nonsymmetric_lShape_degree_injective R hdom hsum (h:=0) (h':=0)
    (by simpa only [zero_mul,zero_add] using heN')
  omega

/-- N3's actual canonical prefix dictionary. No unrestricted claim off L. -/
theorem nonsymmetric_canonical_prefix_coordinates (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {x y : ℕ} (hdom : NonsymmetricLDomain R x y) :
    ((x*nsB R+y*nsC R : ℕ) : ℤ) ∈ nonsymmetricPrefixIdeal R hQ ↔
    ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 ≤ x ∧
      (nonsymmetricReturnTuple R hB ell).2.1 ≤ y := by
  constructor
  · rintro ⟨ell,hp,hl,hz⟩
    let k : NonsymmetricReturnIndex R := ⟨ell,hp,hl⟩
    have S := nonsymmetricReturnTuple_spec R hB k
    have hm := nonsymmetric_single_return_four_sources R hB hp S.1 S.2.2.2.2.2.2 ((x*nsB R+y*nsC R : ℕ) : ℤ)
    rcases hm.mp hz with hf | hx | hy | ⟨_,_,ho⟩
    · exact ⟨k,nonsymmetric_canonical_F_divisor_coordinates R hdom hf⟩
    all_goals
      exfalso
      apply nonsymmetric_canonical_a_predecessor_not_mem R hdom
      have hn := nonsymmetric_nonF_source_a_predecessors R hB hp S.1 S.2.2.2.2.2.2
    · have hh := add_int_mem (nsH R).asRelativeIdeal hn.1 hx
      convert hh using 1; ring
    · have hh := add_int_mem (nsH R).asRelativeIdeal hn.2.1 hy
      convert hh using 1; ring
    · have hh := add_int_mem (nsH R).asRelativeIdeal hn.2.2 ho
      convert hh using 1; ring
  · rintro ⟨ell,hi,hj⟩
    have S := nonsymmetricReturnTuple_spec R hB ell
    have hF := (nonsymmetric_single_return_sources_mem R hB ell.property.1 S.1 S.2.2.2.2.2.2).1
    have hd := nonsymmetric_grid_mem R 0 (x-(nonsymmetricReturnTuple R hB ell).1)
      (y-(nonsymmetricReturnTuple R hB ell).2.1)
    have hm := add_int_mem (returnIdeal (nsH R) (ell.val*normalizedM P.M.base)) hF hd
    refine ⟨ell.val,ell.property.1,ell.property.2,?_⟩
    convert hm using 1
    have h1 : (x-(nonsymmetricReturnTuple R hB ell).1)+(nonsymmetricReturnTuple R hB ell).1=x := Nat.sub_add_cancel hi
    have h2 : (y-(nonsymmetricReturnTuple R hB ell).2.1)+(nonsymmetricReturnTuple R hB ell).2.1=y := Nat.sub_add_cancel hj
    exact_mod_cast (show x*nsB R+y*nsC R=
      nonsymmetricF R (nonsymmetricReturnTuple R hB ell).1 (nonsymmetricReturnTuple R hB ell).2.1+
        (0*nsA R+(x-(nonsymmetricReturnTuple R hB ell).1)*nsB R+(y-(nonsymmetricReturnTuple R hB ell).2.1)*nsC R) by
          dsimp [nonsymmetricF]; nlinarith only [congrArg (fun n => n*nsB R) h1,congrArg (fun n => n*nsC R) h2])

theorem nonsymmetric_prefix_four_sources (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (z : ℤ) :
    z ∈ nonsymmetricPrefixIdeal R hQ ↔
    ∃ ell : NonsymmetricReturnIndex R,
      let t := nonsymmetricReturnTuple R hB ell
      z-(nonsymmetricF R t.1 t.2.1 : ℕ) ∈ (nsH R).asRelativeIdeal ∨
      z-(nonsymmetricX R t.1 t.2.2 : ℕ) ∈ (nsH R).asRelativeIdeal ∨
      z-(nonsymmetricY R t.2.1 t.2.2 : ℕ) ∈ (nsH R).asRelativeIdeal ∨
      (t.1 < nsP R ∧ t.2.1 < nsQ R ∧ z-(nonsymmetricO R t.2.2 : ℕ) ∈ (nsH R).asRelativeIdeal) := by
  constructor
  · rintro ⟨ell,hp,hl,hz⟩
    let k : NonsymmetricReturnIndex R := ⟨ell,hp,hl⟩
    have S := nonsymmetricReturnTuple_spec R hB k
    exact ⟨k,(nonsymmetric_single_return_four_sources R hB hp S.1 S.2.2.2.2.2.2 z).mp hz⟩
  · rintro ⟨ell,hz⟩
    have S := nonsymmetricReturnTuple_spec R hB ell
    exact ⟨ell.val,ell.property.1,ell.property.2,
      (nonsymmetric_single_return_four_sources R hB ell.property.1 S.1 S.2.2.2.2.2.2 z).mpr hz⟩

/-- Actual minimal sources are values in the proven list, independent of
chosen support or return provenance uniqueness. -/
theorem nonsymmetric_prefix_minimal_source_value (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {s : ℤ}
    (hs : (nonsymmetricPrefixIdeal R hQ).IsMinimalGenerator s) :
    ∃ ell : NonsymmetricReturnIndex R,
      let t := nonsymmetricReturnTuple R hB ell
      s=(nonsymmetricF R t.1 t.2.1 : ℕ) ∨
      s=(nonsymmetricX R t.1 t.2.2 : ℕ) ∨
      s=(nonsymmetricY R t.2.1 t.2.2 : ℕ) ∨
      (t.1 < nsP R ∧ t.2.1 < nsQ R ∧ s=(nonsymmetricO R t.2.2 : ℕ)) := by
  obtain ⟨ell,hz⟩ := (nonsymmetric_prefix_four_sources R hB hQ s).mp hs.1
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hm := nonsymmetric_single_return_sources_mem R hB ell.property.1 S.1 S.2.2.2.2.2.2
  have eqgen (g : ℕ) (hg : (g : ℤ) ∈ returnIdeal (nsH R) (ell.val*normalizedM P.M.base))
      (hd : s-(g : ℕ) ∈ (nsH R).asRelativeIdeal) : s=(g : ℕ) := by
    obtain ⟨w,hw,he⟩ := hd
    by_cases hw0 : w=0
    · simp only [hw0,Nat.cast_zero] at he; omega
    · have hno := hs.2 w hw hw0
      apply (hno ?_).elim
      have he' : s-(w : ℕ)=(g : ℕ) := by omega
      rw [he']
      exact ⟨ell.val,ell.property.1,ell.property.2,hg⟩
  refine ⟨ell,?_⟩
  rcases hz with hf | hx | hy | ⟨hi,hj,ho⟩
  · exact Or.inl (eqgen _ hm.1 hf)
  · exact Or.inr (Or.inl (eqgen _ hm.2.1 hx))
  · exact Or.inr (Or.inr (Or.inl (eqgen _ hm.2.2.1 hy)))
  · exact Or.inr (Or.inr (Or.inr ⟨hi,hj,eqgen _ (hm.2.2.2 hi hj) ho⟩))

end NS25Lean.L5A2BFinalRepair
