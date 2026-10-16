import FsFltz.Analysis.AngularExclusionGap
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Minima on literal polar faces

Source: `geometric-part-fsf-proof.tex`, `lem:gap`, lines 645–650,
and its face-minimum proof, lines 660–669. A finite normal support defines
the actual intersection of polar facets; no minimizer or boundary condition
is part of that definition.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace FsFltz

variable {n : ℕ}

/-- The actual intersection of polar facets with the given finite normals. -/
def polarFace (I : ToricInput n) (s : Finset (Lattice n)) : Set (RealSpace n) :=
  {x | x ∈ polarPolytope I ∧ ∀ v ∈ s, pairing v x = 1}

/-- The affine equations imposed by the face's prescribed normals. -/
def polarFaceAffine (s : Finset (Lattice n)) : AffineSubspace ℝ (RealSpace n) where
  carrier := {x | ∀ v ∈ s, pairing v x = 1}
  smul_vsub_vadd_mem' := by
    intro c x y z hx hy hz v hv
    change pairing v (c • (x - y) + z) = 1
    have h := (pairingCLM v).map_add (c • (x - y)) z
    have hsub : pairing v (x - y) = 0 := by
      simpa [hx v hv, hy v hv] using (pairingCLM v).map_sub x y
    simpa [hsub, hz v hv] using h

theorem polarFace_eq_iInter (I : ToricInput n) {s : Finset (Lattice n)}
    (hs : s.Nonempty) : polarFace I s = ⋂ v ∈ s, polarFacet I v := by
  ext x
  constructor
  · intro hx
    exact mem_iInter.mpr fun v => mem_iInter.mpr fun hv => ⟨hx.1, hx.2 v hv⟩
  · intro hx
    obtain ⟨v, hv⟩ := hs
    refine ⟨(mem_iInter.mp (mem_iInter.mp hx v) hv).1, ?_⟩
    intro w hw
    exact (mem_iInter.mp (mem_iInter.mp hx w) hw).2

theorem isClosed_polarFace (I : ToricInput n) (s : Finset (Lattice n)) :
    IsClosed (polarFace I s) := by
  unfold polarFace
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_polarPolytope I).inter (isClosed_iInter fun v =>
    isClosed_iInter fun _ => isClosed_eq (by unfold pairing; fun_prop) continuous_const)

theorem isCompact_polarFace (I : ToricInput n) (s : Finset (Lattice n)) :
    IsCompact (polarFace I s) :=
  (isCompact_polarPolytope I).of_isClosed_subset (isClosed_polarFace I s)
    (fun _ hx => hx.1)

theorem convex_polarFace (I : ToricInput n) (s : Finset (Lattice n)) :
    Convex ℝ (polarFace I s) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · have hP : Convex ℝ (polarPolytope I) := by
      simpa [polarPolytope] using I.supportHeight_convex.convex_le 1
    exact hP hx.1 hy.1 ha hb hab
  · intro v hv
    have h := (pairingCLM v).map_add (a • x) (b • y)
    simpa [hx.2 v hv, hy.2 v hv, hab] using h

/-- Any nonempty proper facet intersection has a native proper face
support. The condition on the normals is derived from its actual points. -/
theorem ToricInput.isPolytopeFace_of_polarFace_nonempty (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices) (hsne : s.Nonempty)
    (hF : (polarFace I s).Nonempty) :
    IsPolytopeFace I.vertices s ∧ s ≠ I.vertices := by
  obtain ⟨x, hx⟩ := hF
  obtain ⟨v, hv⟩ := hsne
  have hx₀ := ne_zero_of_mem_polarFacet I v (show x ∈ polarFacet I v from ⟨hx.1, hx.2 v hv⟩)
  have hq : supportHeight I x = 1 :=
    supportHeight_eq_one_of_mem_polarFacet I (hs hv) ⟨hx.1, hx.2 v hv⟩
  have hsub : s ⊆ maximizingVertexFace I x := by
    intro w hw
    exact (mem_maximizingVertexFace I x w).mpr ⟨hs hw, (hx.2 w hw).trans hq.symm⟩
  have hproper := I.maximizingVertexFace_ne_vertices hx₀
  refine ⟨I.isPolytopeFace_subset (I.maximizingVertexFace_isPolytopeFace x).1 hproper hsub, ?_⟩
  intro he
  exact hproper (Finset.Subset.antisymm
    (I.maximizingVertexFace_isPolytopeFace x).1.1 (he ▸ hsub))

/-- Every proper source face has an actual polar point at which precisely
its prescribed normals are active. The point comes from its exposing
functional and the proved positive supporting level. -/
theorem ToricInput.exists_strict_polarFace_point (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hproper : s ≠ I.vertices) :
    ∃ x ∈ polarFace I s, ∀ v ∈ I.vertices, v ∉ s → pairing v x < 1 := by
  obtain ⟨L, a, ha, hbound, heq⟩ := I.face_supporting_slice_pos hs hproper
  let u : RealSpace n := fun j => L ((Pi.basisFun ℝ (Fin n)) j)
  have hpair (v : Lattice n) : L (latticeReal v) = pairing v u := by
    rw [← (Pi.basisFun ℝ (Fin n)).sum_repr (latticeReal v)]
    simp only [map_sum, map_smul, Pi.basisFun_repr, latticeReal, pairing, u, smul_eq_mul]
  have hlevel : ∀ v ∈ I.vertices, v ∈ s ↔ L (latticeReal v) = a := by
    intro v hv
    rw [← hs.mem_latticePolytope_iff hv, heq]
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨subset_convexHull ℝ _ ⟨v, hv, rfl⟩, h⟩⟩
  let x := a⁻¹ • u
  have hle (v : Lattice n) (hv : v ∈ I.vertices) : pairing v x ≤ 1 := by
    dsimp [x]
    rw [pairing_smul_real, ← hpair]
    have h := mul_le_mul_of_nonneg_left
      (hbound _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)) (inv_pos.mpr ha).le
    simpa only [inv_mul_cancel₀ ha.ne'] using h
  refine ⟨x, ⟨(mem_polarPolytope_iff I x).mpr hle, ?_⟩, ?_⟩
  · intro v hv
    dsimp [x]
    rw [pairing_smul_real, ← hpair, (hlevel v (hs.1 hv)).mp hv]
    exact inv_mul_cancel₀ ha.ne'
  · intro v hv hvs
    have hlt : L (latticeReal v) < a := lt_of_le_of_ne
      (hbound _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩))
      (fun h => hvs ((hlevel v hv).mpr h))
    dsimp [x]
    rw [pairing_smul_real, ← hpair]
    simpa only [inv_mul_cancel₀ ha.ne'] using mul_lt_mul_of_pos_left hlt (inv_pos.mpr ha)

/-- Strict inequalities at the unprescribed normals give membership in
Mathlib's actual intrinsic interior, inside the affine span of the face. -/
theorem mem_intrinsicInterior_polarFace_of_strict (I : ToricInput n)
    {s : Finset (Lattice n)} {x : RealSpace n} (hx : x ∈ polarFace I s)
    (hstrict : ∀ v ∈ I.vertices, v ∉ s → pairing v x < 1) :
    x ∈ intrinsicInterior ℝ (polarFace I s) := by
  classical
  let A := affineSpan ℝ (polarFace I s)
  have hA : A ≤ polarFaceAffine s := affineSpan_le.mpr (fun _ hy => hy.2)
  let U : Set A := {y | ∀ v : {v // v ∈ I.vertices}, v.val ∉ s → pairing v.val y.val < 1}
  have hUopen : IsOpen U := by
    dsimp [U]
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_iInter_of_finite fun _ =>
      isOpen_lt (by simpa only [Function.comp_def, pairingCLM_apply] using
        (pairingCLM v.val).continuous.comp continuous_subtype_val) continuous_const
  have hUsub : U ⊆ Subtype.val ⁻¹' polarFace I s := by
    intro y hy
    have hnormal : ∀ v ∈ s, pairing v y.val = 1 := hA y.property
    refine ⟨(mem_polarPolytope_iff I y.val).mpr ?_, hnormal⟩
    intro v hv
    by_cases hvs : v ∈ s
    · exact (hnormal v hvs).le
    · exact (hy ⟨v, hv⟩ hvs).le
  let z : A := ⟨x, subset_affineSpan ℝ (polarFace I s) hx⟩
  have hzU : z ∈ U := fun v hv => hstrict v.val v.property hv
  exact mem_intrinsicInterior.mpr ⟨z,
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hUopen.mem_nhds hzU) hUsub), rfl⟩

/-- A direction annihilating every active normal admits a two-sided local
line in the face. Only finitely many inactive strict inequalities matter. -/
theorem eventually_mem_polarFace_add_smul (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices) {x d : RealSpace n}
    (hx : x ∈ polarFace I s)
    (hd : ∀ v ∈ I.vertices, pairing v x = 1 → pairing v d = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ polarFace I s := by
  classical
  have heach : ∀ v : {v // v ∈ I.vertices},
      ∀ᶠ t : ℝ in 𝓝 0, pairing v.val (x + t • d) ≤ 1 := by
    intro v
    by_cases hv : pairing v.val x = 1
    · exact Filter.Eventually.of_forall fun t => by
        have h := (pairingCLM v.val).map_add x (t • d)
        simpa [hv, hd v.val v.property hv] using h.le
    · have hlt : pairing v.val x < 1 := lt_of_le_of_ne
        ((mem_polarPolytope_iff I x).mp hx.1 v.val v.property) hv
      have hc : ContinuousAt (fun t : ℝ => pairing v.val (x + t • d)) 0 := by
        have hline : ContinuousAt (fun t : ℝ => x + t • d) 0 := by fun_prop
        simpa only [Function.comp_def, pairingCLM_apply] using
          (pairingCLM v.val).continuous.continuousAt.comp hline
      have he := hc.eventually (gt_mem_nhds (by simpa using hlt))
      exact he.mono fun _ ht => ht.le
  filter_upwards [Filter.eventually_all.mpr heach] with t ht
  refine ⟨(mem_polarPolytope_iff I _).mpr (fun v hv => ht ⟨v, hv⟩), ?_⟩
  intro v hv
  have h := (pairingCLM v).map_add x (t • d)
  simpa [hx.2 v hv, hd v (hs hv) (hx.2 v hv)] using h

/-- Stationarity along all directions annihilating the active facet normals
is derived from a literal face minimum and the two-sided feasible line. -/
theorem fderiv_eq_zero_of_polarFace_minimum (I : ToricInput n)
    {φ : RealSpace n → ℝ} {s : Finset (Lattice n)} (hs : s ⊆ I.vertices)
    {x d : RealSpace n} (hx : x ∈ polarFace I s)
    (hm : IsMinOn φ (polarFace I s) x) (hφ : DifferentiableAt ℝ φ x)
    (hd : ∀ v ∈ I.vertices, pairing v x = 1 → pairing v d = 0) :
    fderiv ℝ φ x d = 0 := by
  have hlocal : IsLocalMin (fun t : ℝ => φ (x + t • d)) 0 := by
    filter_upwards [eventually_mem_polarFace_add_smul I hs hx hd] with t ht
    simpa using hm ht
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hderiv : HasDerivAt (fun t : ℝ => φ (x + t • d)) (fderiv ℝ φ x d) 0 := by
    have hf : HasFDerivAt φ (fderiv ℝ φ x) (x + (0 : ℝ) • d) := by
      simpa only [zero_smul, add_zero] using hφ.hasFDerivAt
    exact hf.comp_hasDerivAt 0 hline
  exact hderiv.deriv.symm.trans hlocal.deriv_eq_zero

private def linearFunctionalDirection (L : RealSpace n →ₗ[ℝ] ℝ) : RealSpace n :=
  fun j => L ((Pi.basisFun ℝ (Fin n)) j)

private theorem pairing_linearFunctionalDirection (L : RealSpace n →ₗ[ℝ] ℝ)
    (v : Lattice n) : pairing v (linearFunctionalDirection L) = L (latticeReal v) := by
  rw [← (Pi.basisFun ℝ (Fin n)).sum_repr (latticeReal v)]
  simp only [map_sum, map_smul, Pi.basisFun_repr, latticeReal,
    linearFunctionalDirection, pairing, smul_eq_mul]

private theorem fderiv_linearFunctionalDirection {φ : RealSpace n → ℝ}
    (x : RealSpace n) (L : RealSpace n →ₗ[ℝ] ℝ) :
    fderiv ℝ φ x (linearFunctionalDirection L) = L (coordinateGradient φ x) := by
  conv_lhs => rw [← (Pi.basisFun ℝ (Fin n)).sum_repr (linearFunctionalDirection L)]
  conv_rhs => rw [← (Pi.basisFun ℝ (Fin n)).sum_repr (coordinateGradient φ x)]
  simp only [map_sum, map_smul, Pi.basisFun_repr, linearFunctionalDirection,
    coordinateGradient, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.basisFun_apply]
  exact mul_comm _ _

private theorem exists_facetCoefficient {t : Finset (Lattice n)}
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

private theorem mem_support_of_latticeReal_mem_positiveCone (I : ToricInput n)
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

/-- At a face minimum, the gradient is a strictly positive combination of
all active facet normals. Stationarity removes every other coefficient
in a containing native simplex cone, and open stars force positivity. -/
theorem IsStronglyCompatibleEndPotential.positive_active_gradient_of_polarFace_minimum
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {s : Finset (Lattice n)}
    (hs : s ⊆ I.vertices) (hsne : s.Nonempty) {x : RealSpace n}
    (hx : x ∈ polarFace I s) (hm : IsMinOn φ (polarFace I s) x) :
    ∃ a : Lattice n → ℝ,
      (∀ v ∈ maximizingVertexFace I x, 0 < a v) ∧
      coordinateGradient φ x =
        ∑ v ∈ maximizingVertexFace I x, a v • latticeReal v := by
  classical
  obtain ⟨v₀, hv₀⟩ := hsne
  have hx₀ : x ≠ 0 := ne_zero_of_mem_polarFacet I v₀ ⟨hx.1, hx.2 v₀ hv₀⟩
  have hq : supportHeight I x = 1 :=
    supportHeight_eq_one_of_mem_polarFacet I (hs hv₀) ⟨hx.1, hx.2 v₀ hv₀⟩
  let A := maximizingVertexFace I x
  obtain ⟨hA, hAne⟩ := I.maximizingVertexFace_isPolytopeFace x
  have hAproper := I.maximizingVertexFace_ne_vertices hx₀
  have hactive (v : Lattice n) (hv : v ∈ A) : pairing v x = 1 := by
    exact ((mem_maximizingVertexFace I x v).mp hv).2.trans hq
  have hstar (v : Lattice n) (hv : v ∈ A) :
      coordinateGradient φ x ∈ interior (rayStar I v) :=
    hφ.facet_star v ((mem_maximizingVertexFace I x v).mp hv).1 ⟨hx.1, hactive v hv⟩
  obtain ⟨σ, hσ, hpσ⟩ := I.exists_mem_faceFan (coordinateGradient φ x)
  obtain ⟨r, hr, hrproper, rfl⟩ := I.exists_proper_face_of_mem_faceFan hσ
  have hAr : A ⊆ r := by
    intro v hv
    have hvc := (I.mem_interior_rayStar_iff v _).mp (hstar v hv) _ hσ hpσ
    apply mem_support_of_latticeReal_mem_positiveCone I hA hAproper hr hrproper hv _ hvc
    intro he
    simpa [he, pairing] using hactive v hv
  have hrne : r.Nonempty := hAne.mono hAr
  obtain ⟨t, ht, hrt, b, hb⟩ := I.exists_facet_basis_containing_face hr hrne hrproper
  obtain ⟨a, ha, hp⟩ := hpσ
  have hcoeff (w : Lattice n) (hw : w ∈ r) :
      ∃ L : RealSpace n →ₗ[ℝ] ℝ,
        (∀ v ∈ t, L (latticeReal v) = if v = w then 1 else 0) ∧
        L (coordinateGradient φ x) = a w := by
    obtain ⟨L, hL⟩ := exists_facetCoefficient b hb ⟨w, hrt hw⟩
    refine ⟨L, hL, ?_⟩
    rw [hp]
    simp only [map_sum, map_smul, smul_eq_mul]
    calc
      ∑ v ∈ r, a v * L (latticeReal v) =
          ∑ v ∈ r, a v * (if v = w then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hL v (hrt hv)]
      _ = a w := by simp [hw]
  have hoff : ∀ w ∈ r, w ∉ A → a w = 0 := by
    intro w hw hwA
    obtain ⟨L, hL, hLa⟩ := hcoeff w hw
    have hd : ∀ v ∈ I.vertices, pairing v x = 1 →
        pairing v (linearFunctionalDirection L) = 0 := by
      intro v hv hvx
      have hvA : v ∈ A := (mem_maximizingVertexFace I x v).mpr ⟨hv, hvx.trans hq.symm⟩
      rw [pairing_linearFunctionalDirection, hL v (hrt (hAr hvA))]
      split_ifs with he
      · exact (hwA (he ▸ hvA)).elim
      · rfl
    have hD := fderiv_eq_zero_of_polarFace_minimum I hs hx hm
      ((hφ.smooth x hx₀).differentiableAt (by simp)) hd
    rw [fderiv_linearFunctionalDirection] at hD
    exact hLa.symm.trans hD
  have hpsum : coordinateGradient φ x = ∑ v ∈ A, a v • latticeReal v := by
    rw [hp]
    symm
    exact Finset.sum_subset hAr (fun w hw hwA => by rw [hoff w hw hwA, zero_smul])
  refine ⟨a, ?_, hpsum⟩
  intro v hv
  have hvr := hAr hv
  refine lt_of_le_of_ne (ha v hvr) ?_
  intro he
  have hav : a v = 0 := he.symm
  have hpErase : coordinateGradient φ x ∈ positiveCone (r.erase v) := by
    refine ⟨a, fun w hw => ha w (Finset.mem_erase.mp hw).2, ?_⟩
    rw [hp]
    symm
    apply Finset.sum_subset (Finset.erase_subset v r)
    intro w hw hwe
    have hwv : w = v := by
      by_contra hne
      exact hwe (Finset.mem_erase.mpr ⟨hne, hw⟩)
    simp [hwv, hav]
  have hErase : positiveCone (r.erase v) ∈ faceFan I :=
    I.positiveCone_subset_mem_faceFan hr hrproper (Finset.erase_subset v r)
  have hvErase := (I.mem_interior_rayStar_iff v _).mp (hstar v hv) _ hErase hpErase
  have heraseproper : r.erase v ≠ I.vertices := by
    intro he
    exact hrproper (Finset.Subset.antisymm hr.1 (he ▸ Finset.erase_subset v r))
  have hv0 : v ≠ 0 := by intro he; simpa [he, pairing] using hactive v hv
  have hve := mem_support_of_latticeReal_mem_positiveCone I hA hAproper
    (I.isPolytopeFace_subset hr hrproper (Finset.erase_subset v r)) heraseproper hv hv0 hvErase
  exact (Finset.mem_erase.mp hve).1 rfl

private theorem fderiv_apply_of_coordinateGradient_eq_sum {φ : RealSpace n → ℝ}
    {x : RealSpace n} {s : Finset (Lattice n)} {a : Lattice n → ℝ}
    (hp : coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v) (d : RealSpace n) :
    fderiv ℝ φ x d = ∑ v ∈ s, a v * pairing v d := by
  let L : RealSpace n →ₗ[ℝ] ℝ := (Pi.basisFun ℝ (Fin n)).constr ℝ fun j => d j
  have hdir : linearFunctionalDirection L = d := by
    ext j
    exact (Pi.basisFun ℝ (Fin n)).constr_basis ℝ (fun j => d j) j
  rw [← hdir, fderiv_linearFunctionalDirection, hp]
  simp only [map_sum, map_smul, smul_eq_mul, pairing_linearFunctionalDirection]

set_option backward.isDefEq.respectTransparency false in
/-- Adding back a nonnegative Euclidean quadratic recovers native convexity. -/
theorem convexOn_of_euclidean_convex_quadratic {φ : RealSpace n → ℝ}
    {c : ℝ} (hc : 0 ≤ c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2)) :
    ConvexOn ℝ univ φ := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hnorm : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) => c * ‖u‖ ^ 2) :=
    (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2).smul hc
  have hfull : ConvexOn ℝ univ (φ ∘ e) := by
    simpa only [Pi.add_def, sub_add_cancel, Function.comp_def, e] using hconv.add hnorm
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hfull.2 (mem_univ (e.symm x)) (mem_univ (e.symm y)) ha hb hab
  simpa only [Function.comp_apply, map_add, map_smul, e.apply_symm_apply] using h

set_option backward.isDefEq.respectTransparency false in
/-- A real normal representation makes a face point a true constrained
minimum. The stationarity is converted to a global inequality by convexity. -/
theorem isMinOn_polarFace_of_coordinateGradient_eq_sum
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) (hconv : ConvexOn ℝ univ φ)
    {s : Finset (Lattice n)} {x : RealSpace n} (hx : x ∈ polarFace I s)
    {a : Lattice n → ℝ}
    (hp : coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v) :
    IsMinOn φ (polarFace I s) x := by
  intro y hy
  have hD : fderiv ℝ φ x (y - x) = 0 := by
    rw [fderiv_apply_of_coordinateGradient_eq_sum hp]
    apply Finset.sum_eq_zero
    intro v hv
    have hpair : pairing v (y - x) = 0 := by
      simpa [hx.2 v hv, hy.2 v hv] using (pairingCLM v).map_sub y x
    rw [hpair, mul_zero]
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hconvE : ConvexOn ℝ univ (φ ∘ e) := by
    refine ⟨convex_univ, ?_⟩
    intro u _ v _ a b ha hb hab
    have h := hconv.2 (mem_univ (e u)) (mem_univ (e v)) ha hb hab
    simpa only [Function.comp_apply, map_add, map_smul] using h
  have hineq := fderiv_le_sub_of_convex hconvE (hd.comp e.differentiable)
    (e.symm x) (e.symm y)
  rw [fderiv_comp _ (hd _) e.differentiableAt, e.fderiv] at hineq
  change fderiv ℝ φ (e (e.symm x)) (e (e.symm y - e.symm x)) ≤ _ at hineq
  simp only [map_sub, e.apply_symm_apply, Function.comp_apply, hD] at hineq
  exact sub_nonneg.mp hineq

/-- The quantitative convexity retained by the constructed potential
suffices for the stationary-normal minimum criterion. -/
theorem isMinOn_polarFace_of_convex_quadratic_normal
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 ≤ c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} {x : RealSpace n} (hx : x ∈ polarFace I s)
    {a : Lattice n → ℝ}
    (hp : coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v) :
    IsMinOn φ (polarFace I s) x :=
  isMinOn_polarFace_of_coordinateGradient_eq_sum I (hφ1.differentiable (by simp))
    (convexOn_of_euclidean_convex_quadratic hc hconv) hx hp

/-- The minimum has no active normal beyond the prescribed face normals.
A direction toward the explicitly exposed face point would otherwise
have a strictly negative derivative, contradicting constrained minimality. -/
theorem IsStronglyCompatibleEndPotential.strict_of_polarFace_minimum
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {s : Finset (Lattice n)}
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    {x : RealSpace n} (hx : x ∈ polarFace I s) (hm : IsMinOn φ (polarFace I s) x) :
    ∀ v ∈ I.vertices, v ∉ s → pairing v x < 1 := by
  classical
  obtain ⟨v₀, hv₀⟩ := hsne
  have hx₀ := ne_zero_of_mem_polarFacet I v₀ (show x ∈ polarFacet I v₀ from ⟨hx.1, hx.2 v₀ hv₀⟩)
  have hq : supportHeight I x = 1 :=
    supportHeight_eq_one_of_mem_polarFacet I (hs.1 hv₀) ⟨hx.1, hx.2 v₀ hv₀⟩
  obtain ⟨y, hy, hystrict⟩ := I.exists_strict_polarFace_point hs hsproper
  obtain ⟨a, ha, hp⟩ := hφ.positive_active_gradient_of_polarFace_minimum hs.1
    ⟨v₀, hv₀⟩ hx hm
  intro v hv hvs
  refine lt_of_le_of_ne ((mem_polarPolytope_iff I x).mp hx.1 v hv) ?_
  intro hvx
  have hvA : v ∈ maximizingVertexFace I x :=
    (mem_maximizingVertexFace I x v).mpr ⟨hv, hvx.trans hq.symm⟩
  have hpair (w : Lattice n) : pairing w (y - x) = pairing w y - pairing w x := by
    simpa only [pairingCLM_apply] using (pairingCLM w).map_sub y x
  have hnonpos : ∀ w ∈ maximizingVertexFace I x, a w * pairing w (y - x) ≤ 0 := by
    intro w hw
    have hwinfo := (mem_maximizingVertexFace I x w).mp hw
    rw [hpair, hwinfo.2, hq]
    exact mul_nonpos_of_nonneg_of_nonpos (ha w hw).le
      (sub_nonpos.mpr ((mem_polarPolytope_iff I y).mp hy.1 w hwinfo.1))
  have hneg : a v * pairing v (y - x) < 0 := by
    rw [hpair, hvx]
    exact mul_neg_of_pos_of_neg (ha v hvA) (sub_neg.mpr (hystrict v hv hvs))
  have hDneg : fderiv ℝ φ x (y - x) < 0 := by
    rw [fderiv_apply_of_coordinateGradient_eq_sum hp]
    exact Finset.sum_neg' hnonpos ⟨v, hvA, hneg⟩
  have hDnonneg : 0 ≤ fderiv ℝ φ x (y - x) :=
    hm.isLocalMinOn.hasFDerivWithinAt_nonneg
      ((hφ.smooth x hx₀).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset ((convex_polarFace I s).segment_subset hx hy))
  exact (not_lt_of_ge hDnonneg hDneg).elim

/-- Every literal face minimum lies in the actual relative interior and
has a strictly positive combination of exactly the prescribed normals. -/
theorem IsStronglyCompatibleEndPotential.intrinsicInterior_and_positive_gradient_of_minimum
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {s : Finset (Lattice n)}
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    {x : RealSpace n} (hx : x ∈ polarFace I s) (hm : IsMinOn φ (polarFace I s) x) :
    x ∈ intrinsicInterior ℝ (polarFace I s) ∧
      ∃ a : Lattice n → ℝ, (∀ v ∈ s, 0 < a v) ∧
        coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v := by
  have hstrict := hφ.strict_of_polarFace_minimum hs hsne hsproper hx hm
  refine ⟨mem_intrinsicInterior_polarFace_of_strict I hx hstrict, ?_⟩
  obtain ⟨v, hv⟩ := hsne
  have hq : supportHeight I x = 1 :=
    supportHeight_eq_one_of_mem_polarFacet I (hs.1 hv) ⟨hx.1, hx.2 v hv⟩
  have hAeq : maximizingVertexFace I x = s := by
    apply Finset.Subset.antisymm
    · intro w hw
      have hwinfo := (mem_maximizingVertexFace I x w).mp hw
      by_contra hws
      exact (ne_of_lt (hstrict w hwinfo.1 hws)) (hwinfo.2.trans hq)
    · intro w hw
      exact (mem_maximizingVertexFace I x w).mpr ⟨hs.1 hw, (hx.2 w hw).trans hq.symm⟩
  simpa only [hAeq] using hφ.positive_active_gradient_of_polarFace_minimum hs.1 ⟨v, hv⟩ hx hm

/-- The quantitative positive quadratic convexity bound makes the literal
face minimum unique. Both normal combinations annihilate the difference
of two face points, while strong gradient monotonicity forbids equality. -/
theorem IsStronglyCompatibleEndPotential.eq_of_polarFace_minima
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    {x y : RealSpace n} (hx : x ∈ polarFace I s) (hy : y ∈ polarFace I s)
    (hmx : IsMinOn φ (polarFace I s) x) (hmy : IsMinOn φ (polarFace I s) y) : x = y := by
  obtain ⟨a, _, hpx⟩ := (hφ.intrinsicInterior_and_positive_gradient_of_minimum
    hs hsne hsproper hx hmx).2
  obtain ⟨b, _, hpy⟩ := (hφ.intrinsicInterior_and_positive_gradient_of_minimum
    hs hsne hsproper hy hmy).2
  have hpair : ∀ v ∈ s, pairing v (y - x) = 0 := by
    intro v hv
    simpa [hx.2 v hv, hy.2 v hv] using (pairingCLM v).map_sub y x
  have hDx : fderiv ℝ φ x (y - x) = 0 := by
    rw [fderiv_apply_of_coordinateGradient_eq_sum hpx]
    apply Finset.sum_eq_zero
    intro v hv
    rw [hpair v hv, mul_zero]
  have hDy : fderiv ℝ φ y (y - x) = 0 := by
    rw [fderiv_apply_of_coordinateGradient_eq_sum hpy]
    apply Finset.sum_eq_zero
    intro v hv
    rw [hpair v hv, mul_zero]
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hfd (z d : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (φ ∘ e) z d = fderiv ℝ φ (e z) (e d) := by
    rw [fderiv_comp z (hφ1.differentiable (by simp) _) e.differentiableAt, e.fderiv]
    rfl
  have hinner : inner ℝ (gradient (φ ∘ e) (e.symm y) -
      gradient (φ ∘ e) (e.symm x)) (e.symm y - e.symm x) = 0 := by
    rw [inner_sub_left, inner_gradient_left, inner_gradient_left, hfd, hfd]
    simp only [map_sub, e.apply_symm_apply, hDx, hDy, sub_self]
  have hbound := mul_norm_sq_le_inner_gradient_sub_of_convex_quadratic
    ((hφ1.comp e.contDiff).differentiable (by simp)) hconv (e.symm x) (e.symm y)
  rw [hinner] at hbound
  have hzero : e.symm y - e.symm x = 0 := by
    apply norm_eq_zero.mp
    have hsq : ‖e.symm y - e.symm x‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_left₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc)).mp
        (by simpa only [mul_zero, zero_mul, mul_comm] using hbound)
    nlinarith [norm_nonneg (e.symm y - e.symm x)]
  exact e.symm.injective (sub_eq_zero.mp hzero).symm

/-- A unique actual minimizer exists on every nonempty proper polar face,
lies in its relative interior, and has the source's positive normal sum. -/
theorem IsStronglyCompatibleEndPotential.exists_unique_polarFace_minimum
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x ∈ polarFace I s, IsMinOn φ (polarFace I s) x ∧
      (∀ y ∈ polarFace I s, IsMinOn φ (polarFace I s) y → y = x) ∧
      x ∈ intrinsicInterior ℝ (polarFace I s) ∧
      ∃ a : Lattice n → ℝ, (∀ v ∈ s, 0 < a v) ∧
        coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v := by
  obtain ⟨y, hy, _⟩ := I.exists_strict_polarFace_point hs hsproper
  obtain ⟨x, hx, hm⟩ := (isCompact_polarFace I s).exists_isMinOn ⟨y, hy⟩
    hφ1.continuous.continuousOn
  obtain ⟨hrel, hcoeff⟩ := hφ.intrinsicInterior_and_positive_gradient_of_minimum
    hs hsne hsproper hx hm
  exact ⟨x, hx, hm, fun y hy hmy =>
    hφ.eq_of_polarFace_minima hφ1 hc hconv hs hsne hsproper hy hx hmy hm, hrel, hcoeff⟩

/-- The potential constructed from the original finite toric input has
the full face-minimum conclusion simultaneously on all actual polar faces. -/
theorem ToricInput.exists_stronglyCompatibleEndPotential_with_faceMinima (I : ToricInput n) :
    ∃ φ : RealSpace n → ℝ, IsStronglyCompatibleEndPotential I φ ∧
      ContDiff ℝ 1 φ ∧ φ 0 = 0 ∧
      ∀ s, IsPolytopeFace I.vertices s → s.Nonempty → s ≠ I.vertices →
      ∃ x ∈ polarFace I s, IsMinOn φ (polarFace I s) x ∧
        (∀ y ∈ polarFace I s, IsMinOn φ (polarFace I s) y → y = x) ∧
        x ∈ intrinsicInterior ℝ (polarFace I s) ∧
        ∃ a : Lattice n → ℝ, (∀ v ∈ s, 0 < a v) ∧
          coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v := by
  obtain ⟨φ, hφ, hφ1, hφ0, c, hc, hconv, _, _⟩ := I.exists_stronglyCompatibleEndPotential
  exact ⟨φ, hφ, hφ1, hφ0, fun _ hs hsne hsproper =>
    hφ.exists_unique_polarFace_minimum hφ1 hc hconv hs hsne hsproper⟩

/-- Source-facing coverage of every nonempty intersection of actual polar
facets, with the native simplex support proved from that intersection. -/
theorem ToricInput.exists_stronglyCompatibleEndPotential_with_polarFacetIntersection_minima
    (I : ToricInput n) :
    ∃ φ : RealSpace n → ℝ, IsStronglyCompatibleEndPotential I φ ∧
      ContDiff ℝ 1 φ ∧ φ 0 = 0 ∧
      ∀ s, s ⊆ I.vertices → s.Nonempty → (polarFace I s).Nonempty →
      ∃ x ∈ polarFace I s, IsMinOn φ (polarFace I s) x ∧
        (∀ y ∈ polarFace I s, IsMinOn φ (polarFace I s) y → y = x) ∧
        x ∈ intrinsicInterior ℝ (polarFace I s) ∧
        ∃ a : Lattice n → ℝ, (∀ v ∈ s, 0 < a v) ∧
          coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v := by
  obtain ⟨φ, hφ, hφ1, hφ0, hmin⟩ := I.exists_stronglyCompatibleEndPotential_with_faceMinima
  refine ⟨φ, hφ, hφ1, hφ0, ?_⟩
  intro s hs hsne hF
  obtain ⟨hface, hproper⟩ := I.isPolytopeFace_of_polarFace_nonempty hs hsne hF
  exact hmin s hface hsne hproper

end FsFltz
