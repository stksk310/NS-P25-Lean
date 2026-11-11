import NS25Lean.MonomialActualRigidity
set_option linter.style.header false
noncomputable section
namespace NS25Lean.MonomialPivotStrictness
open ChosenBase L2B L2B2A L2B2A2 L3A L3B L3C L5A1 L5A2R49First
open MvPolynomial
variable {Gamma : NumericalSemigroup}
private theorem third_axis_exists (ix iy : Fin 3) (hxy : ix ≠ iy) :
    ∃ iz : Fin 3, iz ≠ ix ∧ iz ≠ iy := by
  fin_cases ix <;> fin_cases iy <;> simp_all <;>
    first | exact ⟨0, by decide, by decide⟩
          | exact ⟨1, by decide, by decide⟩
          | exact ⟨2, by decide, by decide⟩

private theorem fin3_eq_one_of_axes (ix iy iz j : Fin 3)
    (hxy : ix ≠ iy) (hzx : iz ≠ ix) (hzy : iz ≠ iy) :
    j = ix ∨ j = iy ∨ j = iz := by
  fin_cases ix <;> fin_cases iy <;> fin_cases iz <;> fin_cases j <;> simp_all

private theorem exponent_three_axes (ix iy iz : Fin 3)
    (hxy : ix ≠ iy) (hzx : iz ≠ ix) (hzy : iz ≠ iy) (u : Exponent) :
    u = Finsupp.single ix (u ix) + Finsupp.single iy (u iy) +
      Finsupp.single iz (u iz) := by
  ext j
  rcases fin3_eq_one_of_axes ix iy iz j hxy hzx hzy with rfl | rfl | rfl
  · simp [hxy, Ne.symm hzx]
  · simp [Ne.symm hxy, Ne.symm hzy]
  · simp [hzx, hzy]

/-- Outside factorizations on two axes, at distinct numerical degrees,
force mixed transverse terms below the opposite minimal border. No killed
component assumption occurs in this statement or its proof. -/
theorem two_axis_gate_geometry (k : Type*) [Field k]
    (D : Data Gamma) (hJ : IsMonomialIdeal k (D.J k))
    (ix iy : Fin 3) (A B : ℕ) (hA : 0<A) (hB : 0<B) (hxy : ix≠iy)
    (hne : A*weights D ix ≠ B*weights D iy)
    (huA : Finsupp.single ix A ∈ minimalExponents (D.J k))
    (huB : Finsupp.single iy B ∈ minimalExponents (D.J k))
    (vx vy : Exponent) (hvxzero : vx ix=0) (hvyzero : vy iy=0)
    (hvx : weight D vx=A*weights D ix) (hvy : weight D vy=B*weights D iy) :
    ∃ (iz : Fin 3) (lambda mu nu omega : ℕ),
      iz≠ix ∧ iz≠iy ∧
      A*weights D ix=lambda*weights D iy+mu*weights D iz ∧
      B*weights D iy=nu*weights D ix+omega*weights D iz ∧
      lambda<B ∧ nu<A ∧ 0<mu ∧ 0<omega := by
  classical
  let h := A*weights D ix
  let g := B*weights D iy
  have hAh : h=A*weights D ix := rfl
  have hBg : g=B*weights D iy := rfl
  obtain ⟨iz, hzx, hzy⟩ := third_axis_exists ix iy hxy
  have hexH : ∃ l : ℕ, ∃ v : FactorizationFiber D h,
      v.val ix = 0 ∧ v.val iy = l := ⟨vx iy, ⟨vx,hvx⟩, hvxzero, rfl⟩
  have hexG : ∃ n : ℕ, ∃ v : FactorizationFiber D g,
      v.val iy = 0 ∧ v.val ix = n := ⟨vy ix, ⟨vy,hvy⟩, hvyzero, rfl⟩
  let lambda := Nat.find hexH
  let nu := Nat.find hexG
  obtain ⟨vh, hvhix', hvhiy⟩ := Nat.find_spec hexH
  obtain ⟨vg, hvgiy', hvgix⟩ := Nat.find_spec hexG
  let mu := vh.val iz
  let omega := vg.val iz
  have hvhform : vh.val = Finsupp.single iy lambda + Finsupp.single iz mu := by
    rw [exponent_three_axes ix iy iz hxy hzx hzy vh.val]
    simp [hvhix', hvhiy, lambda, mu]
  have hvgform : vg.val = Finsupp.single ix nu + Finsupp.single iz omega := by
    rw [exponent_three_axes ix iy iz hxy hzx hzy vg.val]
    simp [hvgiy', hvgix, nu, omega]
  have hgate1 : A * weights D ix =
      lambda * weights D iy + mu * weights D iz := by
    rw [← hAh, ← vh.property, hvhform, map_add, weight_single, weight_single]
  have hgate2 : B * weights D iy =
      nu * weights D ix + omega * weights D iz := by
    rw [← hBg, ← vg.property, hvgform, map_add, weight_single, weight_single]
  let ux : FactorizationFiber D h := ⟨Finsupp.single ix A, by rw [weight_single, ← hAh]⟩
  let uy : FactorizationFiber D g := ⟨Finsupp.single iy B, by rw [weight_single, ← hBg]⟩
  have hlambda : lambda < B := by
    by_contra hn
    have hBl : B ≤ lambda := by omega
    let wval := (vh.val - Finsupp.single iy B) + vg.val
    have hwweight : weight D wval = h := by
      simp only [wval, map_add]
      have hvhrem : weight D (vh.val - Finsupp.single iy B) =
          (lambda - B) * weights D iy + mu * weights D iz := by
        have hvhsub : vh.val - Finsupp.single iy B =
            Finsupp.single iy (lambda - B) + Finsupp.single iz mu := by
          rw [hvhform]
          ext j
          rcases fin3_eq_one_of_axes ix iy iz j hxy hzx hzy with rfl | rfl | rfl
          · simp [hxy, Ne.symm hzx]
          · simp [Ne.symm hxy, Ne.symm hzy]
          · simp [hzx, hzy]
        rw [hvhsub, map_add, weight_single, weight_single]
      rw [hvhrem, vg.property, hBg]
      calc
        (lambda - B) * weights D iy + mu * weights D iz +
            B * weights D iy =
            ((lambda - B) + B) * weights D iy +
              mu * weights D iz := by ring
        _ = lambda * weights D iy + mu * weights D iz := by
          rw [Nat.sub_add_cancel hBl]
        _ = A * weights D ix := hgate1.symm
        _ = h := hAh.symm
    let w : FactorizationFiber D h := ⟨wval, hwweight⟩
    have hwix : w.val ix = nu := by simp [w, wval, hvhform, hvgform, hxy, hzx]
    have hwiy : w.val iy = lambda - B := by
      simp [w, wval, hvhform, hvgform, hxy, hzy]
    have hwiz : w.val iz = mu + omega := by
      simp [w, wval, hvhform, hvgform, hzx, hzy]
    by_cases hnu : nu = 0
    · have hmin := Nat.find_min' hexH ⟨w, by simpa [hwix, hnu], hwiy⟩
      omega
    · have hnupos : 0 < nu := Nat.pos_of_ne_zero hnu
      have he : w.val = ux.val := by
        by_contra hne'
        have hz := minimal_factorization_disjoint k D hJ (Finsupp.single ix A) w.val huA
          (by rw [w.property,weight_single,←hAh]) hne' ix (by simpa using hA)
        rw [hwix] at hz
        omega
      have heix := congrArg (fun z : Exponent => z ix) he
      have heiy := congrArg (fun z : Exponent => z iy) he
      have heiz := congrArg (fun z : Exponent => z iz) he
      simp [w, ux, hwix, hwiy, hwiz, hxy, hzx, hzy] at heix heiy heiz
      have hmu0 : mu = 0 := by omega
      have homega0 : omega = 0 := by omega
      have hlB : lambda = B := by omega
      apply hne
      rw [hgate1, hlB, hmu0, zero_mul, add_zero]
  have hnuA : nu < A := by
    by_contra hn
    have hAn : A ≤ nu := by omega
    let wval := (vg.val - Finsupp.single ix A) + vh.val
    have hwweight : weight D wval = g := by
      simp only [wval, map_add]
      have hvgrem : weight D (vg.val - Finsupp.single ix A) =
          (nu - A) * weights D ix + omega * weights D iz := by
        have hvgsub : vg.val - Finsupp.single ix A =
            Finsupp.single ix (nu - A) + Finsupp.single iz omega := by
          rw [hvgform]
          ext j
          rcases fin3_eq_one_of_axes ix iy iz j hxy hzx hzy with rfl | rfl | rfl
          · simp [hxy, hzx]
          · simp [Ne.symm hxy, Ne.symm hzy]
          · simp [hzx, hzy]
        rw [hvgsub, map_add, weight_single, weight_single]
      rw [hvgrem, vh.property, hAh]
      calc
        (nu - A) * weights D ix + omega * weights D iz +
            A * weights D ix =
            ((nu - A) + A) * weights D ix +
              omega * weights D iz := by ring
        _ = nu * weights D ix + omega * weights D iz := by
          rw [Nat.sub_add_cancel hAn]
        _ = B * weights D iy := hgate2.symm
        _ = g := hBg.symm
    let w : FactorizationFiber D g := ⟨wval, hwweight⟩
    have hwiy : w.val iy = lambda := by simp [w, wval, hvhform, hvgform, hxy, hzy]
    have hwix : w.val ix = nu - A := by simp [w, wval, hvhform, hvgform, hxy, hzx]
    have hwiz : w.val iz = omega + mu := by simp [w, wval, hvhform, hvgform, hzx, hzy]
    by_cases hlam : lambda = 0
    · have hmin := Nat.find_min' hexG ⟨w, by simpa [hwiy, hlam], hwix⟩
      omega
    · have hlampos : 0 < lambda := Nat.pos_of_ne_zero hlam
      have he : w.val = uy.val := by
        by_contra hne'
        have hz := minimal_factorization_disjoint k D hJ (Finsupp.single iy B) w.val huB
          (by rw [w.property,weight_single,←hBg]) hne' iy (by simpa using hB)
        rw [hwiy] at hz
        omega
      have heix := congrArg (fun z : Exponent => z ix) he
      have heiy := congrArg (fun z : Exponent => z iy) he
      have heiz := congrArg (fun z : Exponent => z iz) he
      simp [w, uy, hwix, hwiy, hwiz, hxy, hzx, hzy] at heix heiy heiz
      have hmu0 : mu = 0 := by omega
      have homega0 : omega = 0 := by omega
      have hnA : nu = A := by omega
      have hlB : lambda = B := heiy
      apply hne
      calc
        h = A * weights D ix := hAh
        _ = lambda * weights D iy + mu * weights D iz := hgate1
        _ = B * weights D iy := by rw [hlB, hmu0]; simp
        _ = g := hBg.symm
  have hmu : 0 < mu := by
    by_contra hn
    have hmu0 : mu = 0 := by omega
    have hvhEq : vh.val = Finsupp.single iy lambda := by simp [hvhform, hmu0]
    have hhK : h ∈ D.K := by
      simpa only [hAh,weight_single] using (monomial_mem_chosen_iff_boundary k D _).mp huA.1
    have hvhJ : MvPolynomial.monomial vh.val (1 : k) ∈ D.J k :=
      boundary_monomial_mem_J k D vh.val (vh.property.symm ▸ hhK)
    have hvhle : vh.val ≤ Finsupp.single iy B := by
      rw [hvhEq]
      intro j
      by_cases hji : j = iy
      · subst j; simp; omega
      · simp [hji]
    have hle := huB.2 hvhJ hvhle
    have := hle iy
    simp [hvhEq] at this
    omega
  have homega : 0 < omega := by
    by_contra hn
    have homega0 : omega = 0 := by omega
    have hvgEq : vg.val = Finsupp.single ix nu := by simp [hvgform, homega0]
    have hgK : g ∈ D.K := by
      simpa only [hBg,weight_single] using (monomial_mem_chosen_iff_boundary k D _).mp huB.1
    have hvgJ : MvPolynomial.monomial vg.val (1 : k) ∈ D.J k :=
      boundary_monomial_mem_J k D vg.val (vg.property.symm ▸ hgK)
    have hvgle : vg.val ≤ Finsupp.single ix A := by
      rw [hvgEq]
      intro j
      by_cases hji : j = ix
      · subst j; simp; omega
      · simp [hji]
    have hle := huA.2 hvgJ hvgle
    have := hle ix
    simp [hvgEq] at this
    omega
  exact ⟨iz,lambda,mu,nu,omega,hzx,hzy,hgate1,hgate2,hlambda,hnuA,hmu,homega⟩

set_option maxHeartbeats 800000 in
theorem one_gate_reaches_third_axis (k : Type*) [Field k]
    (D : Data Gamma) (hJ : IsMonomialIdeal k (D.J k))
    (hJM : D.J k = D.MK k)
    (hunique : ∀ d, d ∈ D.apery → Subsingleton (FactorizationFiber D d))
    (hq : q_fs (D.J k) = 1)
    (ix iy iz : Fin 3) (A B C lambda mu : ℕ)
    (hxy : ix ≠ iy) (hzx : iz ≠ ix) (hzy : iz ≠ iy)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hgate : A * weights D ix =
      lambda * weights D iy + mu * weights D iz)
    (hlambda : lambda < B) (hmu : 0 < mu)
    (huA : Finsupp.single ix A ∈ minimalExponents (D.J k))
    (huB : Finsupp.single iy B ∈ minimalExponents (D.J k))
    (huC : Finsupp.single iz C ∈ minimalExponents (D.J k)) :
    C ≤ mu := by
  classical
  rw [q_fs] at hq
  obtain ⟨g, hgset⟩ := Set.ncard_eq_one.mp hq
  have hg : g ∈ fullSupportGenerators (D.J k) := by simp [hgset]
  let u : Exponent := Finsupp.single ix A
  have hug : u ≠ g := by
    intro he
    have hgy := hg.2 iy
    rw [← he] at hgy
    simp [u, Ne.symm hxy] at hgy
  have huA' : u ∈ minimalExponents (D.J k) := by simpa [u] using huA
  obtain ⟨r, ell, _hrA, hdepth, hsupport, hell, helllt, _hrne⟩ :=
    minimal_boundary_depth k D hJ hJM hunique g u hg huA' hug
  have huix : 0 < u ix := by simpa [u] using hA
  have hrix : r ix = 0 := hsupport ix huix
  have hrform : r = Finsupp.single iy (r iy) + Finsupp.single iz (r iz) := by
    calc
      r = Finsupp.single ix (r ix) + Finsupp.single iy (r iy) +
          Finsupp.single iz (r iz) := exponent_three_axes ix iy iz hxy hzx hzy r
      _ = Finsupp.single iy (r iy) + Finsupp.single iz (r iz) := by rw [hrix]; simp
  have hdepth' : A * weights D ix =
      r iy * weights D iy + r iz * weights D iz +
        ell * D.q.val := by
    have hwr := congrArg (weight D) hrform
    simp only [map_add, weight_single] at hwr
    calc
      A * weights D ix = weight D r + ell * D.q.val := by
        simpa [u, weight_single] using hdepth
      _ = r iy * weights D iy + r iz * weights D iz +
          ell * D.q.val := by rw [hwr]
  have hellq : 0 < ell * D.q.val := Nat.mul_pos hell D.q_positive
  have hriy : lambda < r iy := by
    by_contra hn
    have hryle : r iy ≤ lambda := by omega
    by_cases hrzle : r iz ≤ mu
    · let rem : Exponent := Finsupp.single iy (lambda - r iy) +
          Finsupp.single iz (mu - r iz)
      have hdiff : weight D rem = ell * D.q.val := by
        have hly := Nat.sub_add_cancel hryle
        have hmz := Nat.sub_add_cancel hrzle
        simp only [rem, map_add, weight_single]
        nlinarith
      have hreturn : ell * D.q.val ∈ D.H := by
        rw [← hdiff]
        exact weight_mem_H D rem
      have hmin := firstReturnMultiplier_minimal D hell hreturn
      omega
    · have hmurz : mu < r iz := by omega
      let pred : Exponent := Finsupp.single iy (lambda - r iy)
      let rem : Exponent := Finsupp.single iz (r iz - mu)
      have hcoef : 0 < lambda - r iy := by
        have hly := Nat.sub_add_cancel hryle
        have hz := Nat.sub_add_cancel hmurz.le
        nlinarith [hgate, hdepth', hellq, weights_positive D iz]
      have heq : weight D pred =
          weight D rem + ell * D.q.val := by
        have hly := Nat.sub_add_cancel hryle
        have hmz := Nat.sub_add_cancel hmurz.le
        simp only [pred, rem, weight_single]
        nlinarith
      have hpredK : weight D pred ∈ D.K :=
        degree_in_K_of_positive_pivot D pred (weight D rem) ell
          (D.H_le (weight_mem_H D rem)) hell heq
      have hpredJ : MvPolynomial.monomial pred (1 : k) ∈ D.J k :=
        boundary_monomial_mem_J k D pred hpredK
      have hpredle : pred ≤ Finsupp.single iy B := by
        intro j
        by_cases hji : j = iy
        · subst j; simp [pred]; omega
        · simp [pred, hji]
      have hminle := huB.2 hpredJ hpredle
      have := hminle iy
      simp [pred] at this
      omega
  have hriz : r iz < mu := by
    by_contra hn
    have hmule : mu ≤ r iz := by omega
    have hrypos : 0 < r iy - lambda := Nat.sub_pos_of_lt hriy
    have hrz := Nat.sub_add_cancel hmule
    have hry := Nat.sub_add_cancel hriy.le
    nlinarith [weights_positive D iy]
  let pred : Exponent := Finsupp.single iz (mu - r iz)
  let rem : Exponent := Finsupp.single iy (r iy - lambda)
  have heq : weight D pred =
      weight D rem + ell * D.q.val := by
    have hry := Nat.sub_add_cancel hriy.le
    have hmz := Nat.sub_add_cancel hriz.le
    simp only [pred, rem, weight_single]
    nlinarith
  have hpredK : weight D pred ∈ D.K :=
    degree_in_K_of_positive_pivot D pred (weight D rem) ell
      (D.H_le (weight_mem_H D rem)) hell heq
  have hpredJ : MvPolynomial.monomial pred (1 : k) ∈ D.J k :=
    boundary_monomial_mem_J k D pred hpredK
  by_contra hn
  have hcoeflt : mu - r iz < C := by omega
  have hpredle : pred ≤ Finsupp.single iz C := by
    intro j
    by_cases hji : j = iz
    · subst j; simpa [pred] using hcoeflt.le
    · simp [pred, hji]
  have hminle := huC.2 hpredJ hpredle
  have hc := hminle iz
  simp [pred] at hc
  omega


set_option maxHeartbeats 800000 in
/-- Two nonunique pure minimal exponents cannot occur at distinct numerical
weights in an actual monomial cut admitting a full-support minimal exponent. -/
theorem two_axis_distinct_degree_impossible (k : Type*) [Field k]
    (D : Data Gamma) (hJ : IsMonomialIdeal k (D.J k))
    (g : Exponent) (hg : g∈fullSupportGenerators (D.J k))
    (ix iy : Fin 3) (A B : ℕ) (hA : 0<A) (hB : 0<B) (hxy : ix≠iy)
    (hne : A*weights D ix ≠ B*weights D iy)
    (huA : Finsupp.single ix A∈minimalExponents (D.J k))
    (huB : Finsupp.single iy B∈minimalExponents (D.J k))
    (vx vy : Exponent) (hvxzero : vx ix=0) (hvyzero : vy iy=0)
    (hvx : weight D vx=A*weights D ix) (hvy : weight D vy=B*weights D iy) : False := by
  classical
  have hJM := monomial_eq_MK k D hJ
  have hunique := monomial_apery_unique k D hJ
  have hqle := chosen_q_fs_le_one D MonomialOrder.degLex hJ
  have hqpos : 0<q_fs (D.J k) :=
    Set.ncard_pos (fullSupportGenerators_finite _) |>.mpr ⟨g,hg⟩
  have hq : q_fs (D.J k)=1 := by omega
  obtain ⟨iz,lambda,mu,nu,omega,hzx,hzy,hgate1,hgate2,hlB,hnA,hmu,homega⟩ :=
    two_axis_gate_geometry k D hJ ix iy A B hA hB hxy hne huA huB vx vy hvxzero hvyzero hvx hvy
  let Art := chosenArtinianMonomial D MonomialOrder.degLex hJ
  obtain ⟨uz,huz,huzpos,huzoff⟩ := L3A.Staircase.pure_minimal Art iz
  let C := uz iz
  have huzform : uz=Finsupp.single iz C := by
    ext j
    by_cases hji : j=iz
    · subst j; simp [C]
    · simp [hji,huzoff j hji]
  have hC : 0<C := huzpos
  have huC : Finsupp.single iz C∈minimalExponents (D.J k) := by
    change uz∈minimalExponents (D.J k) at huz
    rwa [huzform] at huz
  have hCmu := one_gate_reaches_third_axis k D hJ hJM hunique hq
    ix iy iz A B C lambda mu hxy hzx hzy hA hB hC hgate1 hlB hmu huA huB huC
  have hComega := one_gate_reaches_third_axis k D hJ hJM hunique hq
    iy ix iz B A C nu omega (Ne.symm hxy) hzy hzx hB hA hC hgate2 hnA homega huB huA huC
  let u : Exponent := Finsupp.single iz C
  have hug : u ≠ g := by
    intro he
    have hgx := hg.2 ix
    rw [← he] at hgx
    simp [u, hzx] at hgx
  have huC' : u ∈ minimalExponents (D.J k) := by simpa [u] using huC
  obtain ⟨r, ell, _hrA, hdepth, hsupport, hell, _helllt, hrne⟩ :=
    minimal_boundary_depth k D hJ hJM hunique g u hg huC' hug
  have huiz : 0 < u iz := by simpa [u] using hC
  have hriz : r iz = 0 := hsupport iz huiz
  have hrform : r = Finsupp.single ix (r ix) + Finsupp.single iy (r iy) := by
    calc
      r = Finsupp.single ix (r ix) + Finsupp.single iy (r iy) +
          Finsupp.single iz (r iz) := exponent_three_axes ix iy iz hxy hzx hzy r
      _ = Finsupp.single ix (r ix) + Finsupp.single iy (r iy) := by rw [hriz]; simp
  have hdepth' : C * weights D iz =
      r ix * weights D ix + r iy * weights D iy +
        ell * D.q.val := by
    have hwr := congrArg (weight D) hrform
    simp only [map_add, weight_single] at hwr
    calc
      C * weights D iz = weight D r + ell * D.q.val := by
        simpa [u, weight_single] using hdepth
      _ = r ix * weights D ix + r iy * weights D iy +
          ell * D.q.val := by rw [hwr]
  have hrix : r ix = 0 := by
    by_contra hn
    have hrixpos : 0 < r ix := Nat.pos_of_ne_zero hn
    let pred : Exponent := Finsupp.single ix (A - 1)
    let rem : Exponent := Finsupp.single ix (r ix - 1) +
      Finsupp.single iy (lambda + r iy) + Finsupp.single iz (mu - C)
    have hAone := Nat.sub_add_cancel hA
    have hrone := Nat.sub_add_cancel hrixpos
    have hmC := Nat.sub_add_cancel hCmu
    have heq : weight D pred =
        weight D rem + ell * D.q.val := by
      simp only [pred, rem, map_add, weight_single]
      nlinarith
    have hpredK : weight D pred ∈ D.K :=
      degree_in_K_of_positive_pivot D pred (weight D rem) ell
        (D.H_le (weight_mem_H D rem)) hell heq
    have hap := minimal_boundary_remove_apery k D hJM
      (Finsupp.single ix A) huA ix (by simpa using hA)
    have hpredEq : weight D pred =
        weight D (Finsupp.single ix A) - weights D ix := by
      simp only [pred, weight_single]
      rw [Nat.sub_mul]
      simp
    exact (D.apery_eq_compl ▸ hap).2 (hpredEq ▸ hpredK)
  have hriy : r iy = 0 := by
    by_contra hn
    have hriypos : 0 < r iy := Nat.pos_of_ne_zero hn
    let pred : Exponent := Finsupp.single iy (B - 1)
    let rem : Exponent := Finsupp.single ix (nu + r ix) +
      Finsupp.single iy (r iy - 1) + Finsupp.single iz (omega - C)
    have hBone := Nat.sub_add_cancel hB
    have hrone := Nat.sub_add_cancel hriypos
    have hoC := Nat.sub_add_cancel hComega
    have heq : weight D pred =
        weight D rem + ell * D.q.val := by
      simp only [pred, rem, map_add, weight_single]
      nlinarith
    have hpredK : weight D pred ∈ D.K :=
      degree_in_K_of_positive_pivot D pred (weight D rem) ell
        (D.H_le (weight_mem_H D rem)) hell heq
    have hap := minimal_boundary_remove_apery k D hJM
      (Finsupp.single iy B) huB iy (by simpa using hB)
    have hpredEq : weight D pred =
        weight D (Finsupp.single iy B) - weights D iy := by
      simp only [pred, weight_single]
      rw [Nat.sub_mul]
      simp
    exact (D.apery_eq_compl ▸ hap).2 (hpredEq ▸ hpredK)
  apply hrne
  ext j
  rcases fin3_eq_one_of_axes ix iy iz j hxy hzx hzy with rfl | rfl | rfl
  · exact hrix
  · exact hriy
  · exact hriz


end NS25Lean.MonomialPivotStrictness
