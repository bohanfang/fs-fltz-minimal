import FsFltz.Analysis.AngularExclusionGap

/-!
# Active coefficients in conormal limits

Source: `geometric-part-fsf-proof.tex`, `lem:bad`, lines 1418–1426.
The native open-star condition gives a direct proof of the limiting
contradiction: a gradient represented on the active normals cannot have
a zero coefficient at an active normal. No face minimum is assumed.
-/

noncomputable section

open Set
open scoped Topology BigOperators

namespace FsFltz

variable {n : ℕ}

/-- A nonzero face generator belongs to every proper face whose cone contains it. -/
theorem ToricInput.mem_face_of_latticeReal_mem_positiveCone (I : ToricInput n)
    {s r : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsproper : s ≠ I.vertices) (hr : IsPolytopeFace I.vertices r)
    (hrproper : r ≠ I.vertices) {v : Lattice n} (hv : v ∈ s) (hv0 : v ≠ 0)
    (hvc : latticeReal v ∈ positiveCone r) : v ∈ r := by
  classical
  have hsingle : {v} ⊆ s := Finset.singleton_subset_iff.mpr hv
  have hsingleface := I.isPolytopeFace_subset hs hsproper hsingle
  have hsingleproper : ({v} : Finset (Lattice n)) ≠ I.vertices := by
    intro he
    exact hsproper (Finset.Subset.antisymm hs.1 (he ▸ hsingle))
  by_contra hvr
  have hempty : r ∩ {v} = ∅ := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_singleton]
    simp
    intro hw he
    subst w
    exact hvr hw
  have hmem : latticeReal v ∈ positiveCone (r ∩ {v}) := by
    rw [← I.positiveCone_inter hr hsingleface hrproper hsingleproper]
    exact ⟨hvc, latticeReal_mem_positiveCone (by simp)⟩
  rw [hempty, positiveCone_empty, Set.mem_singleton_iff] at hmem
  apply hv0
  ext j
  have hj : (v j : ℝ) = 0 := by simpa only [latticeReal, Pi.zero_apply] using congrFun hmem j
  exact_mod_cast hj

private theorem exists_facetCoordinate {t : Finset (Lattice n)}
    (b : Module.Basis {v // v ∈ t} ℤ (Lattice n)) (hb : ∀ v, b v = v.val)
    (w : {v // v ∈ t}) :
    ∃ L : RealSpace n →ₗ[ℝ] ℝ, ∀ v ∈ t,
      L (latticeReal v) = if v = w.val then 1 else 0 := by
  classical
  let M : Lattice n →ₗ[ℤ] ℝ := b.constr ℝ fun z => if z = w then 1 else 0
  refine ⟨realExtension M, ?_⟩
  intro v hv
  rw [realExtension_latticeReal]
  simpa only [M, hb, Subtype.ext_iff] using
    b.constr_basis ℝ (fun z => if z = w then (1 : ℝ) else 0) ⟨v, hv⟩

/-- At a polar boundary point, every active coefficient in an active-normal
representation of the actual compatible gradient is strictly positive. The coefficients
in the proposed representation may have either sign. -/
theorem IsStronglyCompatibleEndPotential.active_gradient_coefficient_pos
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {x : RealSpace n}
    (hx : x ∈ polarPolytope I) (hlevel : supportHeight I x = 1)
    (q : Lattice n → ℝ)
    (hp : coordinateGradient φ x =
      ∑ v ∈ maximizingVertexFace I x, q v • latticeReal v)
    {a : Lattice n} (ha : a ∈ I.vertices) (hax : pairing a x = 1) :
    0 < q a := by
  classical
  have hx₀ : x ≠ 0 := ne_zero_of_mem_polarFacet I a ⟨hx, hax⟩
  let A := maximizingVertexFace I x
  obtain ⟨hA, hAne⟩ := I.maximizingVertexFace_isPolytopeFace x
  have hAproper := I.maximizingVertexFace_ne_vertices hx₀
  have haA : a ∈ A := (mem_maximizingVertexFace I x a).mpr ⟨ha, hax.trans hlevel.symm⟩
  have hactive (v : Lattice n) (hv : v ∈ A) : pairing v x = 1 :=
    ((mem_maximizingVertexFace I x v).mp hv).2.trans hlevel
  have hstar (v : Lattice n) (hv : v ∈ A) :
      coordinateGradient φ x ∈ interior (rayStar I v) :=
    hφ.facet_star v ((mem_maximizingVertexFace I x v).mp hv).1 ⟨hx, hactive v hv⟩
  obtain ⟨σ, hσ, hpσ⟩ := I.exists_mem_faceFan (coordinateGradient φ x)
  obtain ⟨r, hr, hrproper, rfl⟩ := I.exists_proper_face_of_mem_faceFan hσ
  have hAr : A ⊆ r := by
    intro v hv
    have hvc := (I.mem_interior_rayStar_iff v _).mp (hstar v hv) _ hσ hpσ
    apply I.mem_face_of_latticeReal_mem_positiveCone hA hAproper hr hrproper hv _ hvc
    intro he
    simpa [he, pairing] using hactive v hv
  obtain ⟨t, ht, hrt, b, hb⟩ :=
    I.exists_facet_basis_containing_face hr (hAne.mono hAr) hrproper
  obtain ⟨c, hc, hpc⟩ := hpσ
  obtain ⟨L, hL⟩ := exists_facetCoordinate b hb ⟨a, hrt (hAr haA)⟩
  have hLc : L (coordinateGradient φ x) = c a := by
    rw [hpc]
    simp only [map_sum, map_smul, smul_eq_mul]
    calc
      ∑ v ∈ r, c v * L (latticeReal v) =
          ∑ v ∈ r, c v * (if v = a then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hL v (hrt hv)]
      _ = c a := by simp [hAr haA]
  have hLq : L (coordinateGradient φ x) = q a := by
    rw [hp]
    simp only [map_sum, map_smul, smul_eq_mul]
    calc
      ∑ v ∈ A, q v * L (latticeReal v) =
          ∑ v ∈ A, q v * (if v = a then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hL v (hrt (hAr hv))]
      _ = q a := by simp [haA]
  have hnonneg : 0 ≤ q a := by
    rw [← hLq, hLc]
    exact hc a (hAr haA)
  apply lt_of_le_of_ne hnonneg
  intro hqa'
  have hqa : q a = 0 := hqa'.symm
  have hca : c a = 0 := hLc.symm.trans (hLq.trans hqa)
  have hpErase : coordinateGradient φ x ∈ positiveCone (r.erase a) := by
    refine ⟨c, fun w hw => hc w (Finset.mem_erase.mp hw).2, ?_⟩
    rw [hpc]
    symm
    apply Finset.sum_subset (Finset.erase_subset a r)
    intro w hw hwe
    have hwa : w = a := by
      by_contra hne
      exact hwe (Finset.mem_erase.mpr ⟨hne, hw⟩)
    simp [hwa, hca]
  have hErase : positiveCone (r.erase a) ∈ faceFan I :=
    I.positiveCone_subset_mem_faceFan hr hrproper (Finset.erase_subset a r)
  have haErase := (I.mem_interior_rayStar_iff a _).mp (hstar a haA) _ hErase hpErase
  have heraseproper : r.erase a ≠ I.vertices := by
    intro he
    exact hrproper (Finset.Subset.antisymm hr.1 (he ▸ Finset.erase_subset a r))
  have ha₀ : a ≠ 0 := by intro he; simp [he, pairing] at hax
  have hae := I.mem_face_of_latticeReal_mem_positiveCone hA hAproper
    (I.isPolytopeFace_subset hr hrproper (Finset.erase_subset a r)) heraseproper haA ha₀ haErase
  exact (Finset.mem_erase.mp hae).1 rfl

/-- Retained interface for nonvanishing active gradient coefficients. -/
theorem IsStronglyCompatibleEndPotential.active_gradient_coefficient_ne_zero
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {x : RealSpace n}
    (hx : x ∈ polarPolytope I) (hlevel : supportHeight I x = 1)
    (q : Lattice n → ℝ)
    (hp : coordinateGradient φ x =
      ∑ v ∈ maximizingVertexFace I x, q v • latticeReal v)
    {a : Lattice n} (ha : a ∈ I.vertices) (hax : pairing a x = 1) :
    q a ≠ 0 :=
  (hφ.active_gradient_coefficient_pos hx hlevel q hp ha hax).ne'

/-- The actual real compatible gradient cannot be a complex multiple of a
normal sum that omits an active polar facet. -/
theorem IsStronglyCompatibleEndPotential.active_complex_conormal_coefficient_ne_zero
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {x : RealSpace n}
    (hx : x ∈ polarPolytope I) (hlevel : supportHeight I x = 1)
    (q : Lattice n → ℂ) (t : ℂ)
    (hq : ∀ v ∈ I.vertices, pairing v x < 1 → q v = 0)
    (hp : (fun j => (coordinateGradient φ x j : ℂ)) =
      t • ∑ v ∈ I.vertices, q v • latticeComplex v)
    {a : Lattice n} (ha : a ∈ I.vertices) (hax : pairing a x = 1) :
    q a ≠ 0 := by
  classical
  have hreal : coordinateGradient φ x = ∑ v ∈ I.vertices, (t * q v).re • latticeReal v := by
    ext j
    have hj := congrArg (fun z : Fin n → ℂ => (z j).re) hp
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      latticeComplex, latticeReal, Complex.mul_re, sub_mul, mul_assoc,
      Finset.sum_sub_distrib] using hj
  have hactive : coordinateGradient φ x =
      ∑ v ∈ maximizingVertexFace I x, (t * q v).re • latticeReal v := by
    rw [hreal]
    symm
    apply Finset.sum_subset (I.maximizingVertexFace_isPolytopeFace x).1.1
    intro v hv hvA
    have hvlt : pairing v x < 1 := lt_of_le_of_ne
      ((mem_polarPolytope_iff I x).mp hx v hv)
      (fun he => hvA ((mem_maximizingVertexFace I x v).mpr ⟨hv, he.trans hlevel.symm⟩))
    simp [hq v hv hvlt]
  have hne := hφ.active_gradient_coefficient_ne_zero hx hlevel
    (fun v => (t * q v).re) hactive ha hax
  intro hqa
  exact hne (by simp [hqa])

/-- A normalized complex conormal representation at the polar boundary
has a positive real multiplier and positive real coefficients on every
active facet. No sign or reality of these coefficients is assumed. -/
theorem IsStronglyCompatibleEndPotential.active_complex_conormal_positive
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {x : RealSpace n}
    (hx : x ∈ polarPolytope I) (hlevel : supportHeight I x = 1)
    (q : Lattice n → ℂ) (t : ℂ)
    (hq : ∀ v ∈ I.vertices, pairing v x < 1 → q v = 0)
    (hsum : ∑ v ∈ I.vertices, q v = 1)
    (hp : (fun j => (coordinateGradient φ x j : ℂ)) =
      t • ∑ v ∈ I.vertices, q v • latticeComplex v) :
    t.im = 0 ∧ 0 < t.re ∧ ∀ a ∈ I.vertices, pairing a x = 1 →
      (q a).im = 0 ∧ 0 < (q a).re := by
  classical
  let A := maximizingVertexFace I x
  have hA := (I.maximizingVertexFace_isPolytopeFace x).1
  have hAne := (I.maximizingVertexFace_isPolytopeFace x).2
  have hx0 : x ≠ 0 := by
    intro he
    obtain ⟨v, hv⟩ := hAne
    have hpair := ((mem_maximizingVertexFace I x v).mp hv).2.trans hlevel
    simp [he, pairing] at hpair
  have hApr := I.maximizingVertexFace_ne_vertices hx0
  have hoff (v) (hv : v ∈ I.vertices) (hvA : v ∉ A) : q v = 0 := by
    apply hq v hv
    exact lt_of_le_of_ne ((mem_polarPolytope_iff I x).mp hx v hv)
      (fun he => hvA ((mem_maximizingVertexFace I x v).mpr ⟨hv, he.trans hlevel.symm⟩))
  have hsumA : ∑ v ∈ A, q v = 1 := by
    rw [← hsum]
    exact Finset.sum_subset hA.1 (fun v hv hvA => hoff v hv hvA)
  have hpA : (fun j => (coordinateGradient φ x j : ℂ)) =
      t • ∑ v ∈ A, q v • latticeComplex v := by
    rw [hp]
    congr 1
    symm
    exact Finset.sum_subset hA.1 (fun v hv hvA => by simp [hoff v hv hvA])
  have hreal : coordinateGradient φ x = ∑ v ∈ A, (t * q v).re • latticeReal v := by
    ext j
    have hj := congrArg (fun z : Fin n → ℂ => (z j).re) hpA
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      latticeComplex, latticeReal, Complex.mul_re, sub_mul, mul_assoc,
      Finset.sum_sub_distrib] using hj
  have himag : (0 : RealSpace n) = ∑ v ∈ A, (t * q v).im • latticeReal v := by
    ext j
    have hj := congrArg (fun z : Fin n → ℂ => (z j).im) hpA
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      latticeComplex, latticeReal, Complex.mul_im, add_mul, mul_assoc,
      Finset.sum_add_distrib] using hj
  obtain ⟨F, hF, hAF, b, hb⟩ := I.exists_facet_basis_containing_face hA hAne hApr
  have hprod (a) (ha : a ∈ A) : (t * q a).im = 0 ∧ 0 < (t * q a).re := by
    obtain ⟨L, hL⟩ := exists_facetCoordinate b hb ⟨a, hAF ha⟩
    have hLzero := congrArg L himag
    have hLsum : L (∑ v ∈ A, (t * q v).im • latticeReal v) = (t * q a).im := by
      simp only [map_sum, map_smul, smul_eq_mul]
      calc
        ∑ v ∈ A, (t * q v).im * L (latticeReal v) =
            ∑ v ∈ A, (t * q v).im * (if v = a then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hL v (hAF hv)]
        _ = _ := by simp [ha]
    have ha' := (mem_maximizingVertexFace I x a).mp ha
    refine ⟨?_, hφ.active_gradient_coefficient_pos hx hlevel _ hreal ha'.1 (ha'.2.trans hlevel)⟩
    rw [map_zero, hLsum] at hLzero
    exact hLzero.symm
  have hsumprod : ∑ v ∈ A, t * q v = t := by rw [← Finset.mul_sum, hsumA, mul_one]
  have htim : t.im = 0 := by
    rw [← hsumprod, Complex.im_sum]
    exact Finset.sum_eq_zero (fun a ha => (hprod a ha).1)
  have htpos : 0 < t.re := by
    rw [← hsumprod, Complex.re_sum]
    exact Finset.sum_pos (fun a ha => (hprod a ha).2) hAne
  refine ⟨htim, htpos, ?_⟩
  intro a ha hax
  have haA : a ∈ A := (mem_maximizingVertexFace I x a).mpr ⟨ha, hax.trans hlevel.symm⟩
  obtain ⟨hi, hr⟩ := hprod a haA
  simp only [Complex.mul_im, htim, zero_mul, add_zero] at hi
  simp only [Complex.mul_re, htim, zero_mul, sub_zero] at hr
  exact ⟨(mul_eq_zero.mp hi).resolve_left htpos.ne', (mul_pos_iff_of_pos_left htpos).mp hr⟩

end FsFltz
