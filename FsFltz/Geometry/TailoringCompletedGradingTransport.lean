import FsFltz.Geometry.TailoringCompletedGradingFamily
import FsFltz.Geometry.MaslovHomotopy
import FsFltz.Geometry.MaslovClassPullback
import FsFltz.Geometry.LocalGermMaslovFamilyPullback
import FsFltz.Geometry.SmoothEmbeddingRange

/-!
# Joint canonical-square transport under the cylindrical weight

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030.
Open restriction and positive primitive rescaling preserve actual Maslov
families, including smooth real extensions at the interval endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothNearInterval
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_slice {V : Set E} {f : ℝ × E → F}
    (hf : SmoothNearInterval V f) {t : ℝ} (ht : t ∈ parameterInterval) :
    ContDiffOn ℝ ∞ (fun x => f (t, x)) V := by
  obtain ⟨U, hU, hcover, hs⟩ := hf
  intro x hx
  exact ((hs.contDiffAt (hU.mem_nhds (hcover ⟨ht, hx⟩))).comp x
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

theorem rankTwoShearComplex {n : ℕ} {V : Set E}
    {p : ℝ × E → Model (2 * n) →L[ℝ] ℝ}
    {X : ℝ × E → Model (2 * n)}
    {J : ℝ × E → Model (2 * n) →L[ℝ] Model (2 * n)} (K : ℝ)
    (hp : SmoothNearInterval V p) (hX : SmoothNearInterval V X)
    (hJ : SmoothNearInterval V J)
    (hden : ∀ z ∈ parameterInterval ×ˢ V, 1 + K * p z (X z) ≠ 0) :
    SmoothNearInterval V (fun z => FsFltz.Geometry.rankTwoShearComplex (p z) (X z) K (J z)) := by
  obtain ⟨P, hP, hPi, hp⟩ := hp
  obtain ⟨A, hA, hAi, hX⟩ := hX
  obtain ⟨B, hB, hBi, hJ⟩ := hJ
  let U := (P ∩ A) ∩ B
  have hpU := hp.mono (show U ⊆ P from fun _ hz => hz.1.1)
  have hXU := hX.mono (show U ⊆ A from fun _ hz => hz.1.2)
  have hJU := hJ.mono (show U ⊆ B from inter_subset_right)
  let D := fun z => 1 + K * p z (X z)
  have hD : ContDiffOn ℝ ∞ D U := contDiffOn_const.add (contDiffOn_const.mul (hpU.clm_apply hXU))
  let W := U ∩ D ⁻¹' {r : ℝ | r ≠ 0}
  refine ⟨W, hD.continuousOn.isOpen_inter_preimage ((hP.inter hA).inter hB) isOpen_ne,
    fun z hz => ⟨⟨⟨hPi hz, hAi hz⟩, hBi hz⟩, hden z hz⟩, ?_⟩
  exact contDiffOn_rankTwoShearComplex (hpU.mono inter_subset_left)
    (hXU.mono inter_subset_left) contDiffOn_const (hJU.mono inter_subset_left)
    (fun _ hz => hz.2)

theorem rankTwoShearTensor {n : ℕ} {V : Set E}
    {p : ℝ × E → Model (2 * n) →L[ℝ] ℝ}
    {X : ℝ × E → Model (2 * n)} {s : ℝ × E → SquaredCanonicalTensor n} (K : ℝ)
    (hp : SmoothNearInterval V p) (hX : SmoothNearInterval V X)
    (hs : SmoothNearInterval V s) :
    SmoothNearInterval V (fun z => FsFltz.Geometry.rankTwoShearTensor (p z) (X z) K (s z)) := by
  obtain ⟨P, hP, hPi, hp⟩ := hp
  obtain ⟨A, hA, hAi, hX⟩ := hX
  obtain ⟨B, hB, hBi, hs⟩ := hs
  refine ⟨(P ∩ A) ∩ B, (hP.inter hA).inter hB,
    fun z hz => ⟨⟨hPi hz, hAi hz⟩, hBi hz⟩, ?_⟩
  exact contDiffOn_rankTwoShearTensor (hp.mono (fun _ hz => hz.1.1))
    (hX.mono (fun _ hz => hz.1.2)) contDiffOn_const (hs.mono inter_subset_right)

end SmoothNearInterval

/-- Nondegeneracy of the actual stretched two-form proves the shear
denominator condition; it is not extra completion data. -/
theorem normalizedWeightDifferential_denominator_ne_zero {n : ℕ}
    {M : SmoothManifold (2 * n)} {α : M.Form 1} (hα : M.IsSmoothForm α)
    (w : M.Point → ℝ) (hw : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ w)
    (x : M.Point) (hwx : w x ≠ 0)
    (hnd : M.Nondegenerate (M.exteriorDerivative α) x)
    (hwnd : M.Nondegenerate (M.exteriorDerivative (fun y => w y • α y)) x)
    (Z : M.Tangent x)
    (hcon : ∀ v, evalTwo (M.exteriorDerivative α) x Z v = evalOne α x v) :
    1 + normalizedWeightDifferential (M := M) w x Z ≠ 0 := by
  let p := normalizedWeightDifferential (M := M) w
  let q : (y : M.Point) → M.Tangent y →L[ℝ] ℝ := fun y =>
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Model (2 * n))
      (F := ℝ) (0 : Fin 1)).symm (α y)
  have hq (y : M.Point) (v : M.Tangent y) : q y v = evalOne α y v := rfl
  have hform (v u : M.Tangent x) :
      evalTwo (M.exteriorDerivative (fun y => w y • α y)) x v u =
        w x * evalTwo (M.rankTwoForm (M.exteriorDerivative α) p q 1) x v u := by
    rw [M.evalTwo_exteriorDerivative_smul w α hw hα, M.evalTwo_rankTwoForm]
    simp only [p, normalizedWeightDifferential, smul_apply, smul_eq_mul, hq, one_mul]
    change w x * _ + _ - _ = w x * (_ +
      ((w x)⁻¹ * M.scalarDerivative w x v * _ - _ * ((w x)⁻¹ * M.scalarDerivative w x u)))
    field_simp [hwx]
    ring
  have hnd' : M.Nondegenerate (M.rankTwoForm (M.exteriorDerivative α) p q 1) x := by
    intro v hv
    apply hwnd v
    intro u
    rw [hform, hv u, mul_zero]
  have hH : M.hamiltonianVector (M.exteriorDerivative α) x hnd (q x) = Z :=
    M.liouvilleEquation_unique α x hnd
      (fun v => (M.hamiltonianVector_contraction _ x hnd (q x) v).trans (hq x v)) hcon
  have hd := (M.nondegenerate_rankTwoForm_iff (M.exteriorDerivative α) p q 1 x hnd).mp hnd'
  simpa only [rankTwoPairing, hH, one_mul] using hd

namespace MaslovFamily
variable {n : ℕ} {M : SmoothManifold (2 * n)}

/-- Pointwise real smooth map germs suffice for the same actual family
pullback; a global smooth real time extension is unnecessary. -/
theorem exists_localGermPullback {N : SmoothManifold (2 * n)}
    {η : ℝ → N.Form 2} (s : MaslovFamily N η)
    (e : Parameter → M.SmoothEquiv N)
    (he : IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn M N univ (fun t x => e t x))
    (η' : ℝ → M.Form 2)
    (hform : ∀ t : Parameter, M.pullback N (e t) (η t.val) = η' t.val) :
    ∃ g : MaslovFamily M η',
      (∀ t : Parameter, g.J t.val = pullbackAlmostComplex M N (e t) (s.J t.val)) ∧
      ∀ t : Parameter, g.tensor t.val = pullbackSquaredTensor M N (e t) (s.tensor t.val) := by
  let J := intervalPullbackAlmostComplex M N e s.J
  have hcompatible : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M (η' t) (J t) := by
    intro t ht
    dsimp only [J]
    rw [intervalPullbackAlmostComplex_apply M N e s.J ⟨t, ht⟩, ← hform ⟨t, ht⟩]
    exact isCompatibleAlmostComplex_pullback M N (e ⟨t, ht⟩) (η t)
      (s.J t) (s.compatible t ht)
  obtain ⟨g, hgJ, hgT⟩ := exists_maslovFamily_of_localExtensions J hcompatible
    (s.localSmoothComplexExtensions_intervalPullback_of_localGerms e he)
    (s.intervalPullbackTensorSection e) (s.intervalPullbackTensorSection_ne_zero e)
    (s.localSmoothTensorCoefficients_intervalPullback_of_localGerms e he)
  refine ⟨g, fun t => (hgJ t).trans (intervalPullbackAlmostComplex_apply M N e s.J t), ?_⟩
  intro t
  funext x
  exact (hgT (t, x)).trans (s.canonicalSquareMap_intervalPullbackTensorSection e (t, x))

/-- Smooth interval diffeomorphisms pull back actual native families;
only geometric map regularity and the equality of two-form indices enter. -/
theorem exists_intervalPullback {N : SmoothManifold (2 * n)}
    {η : ℝ → N.Form 2} (s : MaslovFamily N η)
    (e : Parameter → M.SmoothEquiv N)
    (he : M.IsSmoothIntervalMapFamily N (fun t => e t))
    (η' : ℝ → M.Form 2)
    (hform : ∀ t : Parameter, M.pullback N (e t) (η t.val) = η' t.val) :
    ∃ g : MaslovFamily M η',
      (∀ t : Parameter, g.J t.val = pullbackAlmostComplex M N (e t) (s.J t.val)) ∧
      ∀ t : Parameter, g.tensor t.val = pullbackSquaredTensor M N (e t) (s.tensor t.val) := by
  let J := intervalPullbackAlmostComplex M N e s.J
  have hcompatible : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M (η' t) (J t) := by
    intro t ht
    dsimp only [J]
    rw [intervalPullbackAlmostComplex_apply M N e s.J ⟨t, ht⟩, ← hform ⟨t, ht⟩]
    exact isCompatibleAlmostComplex_pullback M N (e ⟨t, ht⟩) (η t)
      (s.J t) (s.compatible t ht)
  obtain ⟨g, hgJ, hgT⟩ := exists_maslovFamily_of_localExtensions J hcompatible
    (s.localSmoothComplexExtensions_intervalPullback e he)
    (s.intervalPullbackTensorSection e) (s.intervalPullbackTensorSection_ne_zero e)
    (s.localSmoothTensorCoefficients_intervalPullback e he)
  refine ⟨g, fun t => (hgJ t).trans (intervalPullbackAlmostComplex_apply M N e s.J t), ?_⟩
  intro t
  funext x
  exact (hgT (t, x)).trans (s.canonicalSquareMap_intervalPullbackTensorSection e (t, x))

/-- Open restriction retains the actual parameter-dependent complex field
and tensor in their native tangent coordinates. -/
def restrict {η : ℝ → M.Form 2} (s : MaslovFamily M η)
    (U : TopologicalSpace.Opens M.Point) :
    MaslovFamily (M.restrict U) (fun t x => η t x.val) where
  J := fun t x => s.J t x.val
  tensor := fun t x => s.tensor t x.val
  compatible := by
    intro t ht
    refine ⟨?_, fun x => (s.compatible t ht).2.1 x.val,
      fun x => (s.compatible t ht).2.2.1 x.val, fun x => (s.compatible t ht).2.2.2 x.val⟩
    intro a
    exact (((s.compatible t ht).1 a.val).mono
      ((chartAt (Model (2 * n)) a.val).subtypeRestr_target_subset ⟨a⟩)).congr
      (fun _ hy => almostComplexInChart_restrict U (s.J t) a hy)
  canonical := fun t ht x => s.canonical t ht x.val
  nowhereZero := fun t ht x => s.nowhereZero t ht x.val
  smoothJ := by
    intro a
    obtain ⟨V, hV, hVi, hs⟩ := s.smoothJ a.val
    let B := V ∩ (univ ×ˢ (chartAt (Model (2 * n)) a).target)
    refine ⟨B, hV.inter (isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target), ?_, ?_⟩
    · intro z hz
      exact ⟨hVi ⟨hz.1, (chartAt (Model (2 * n)) a.val).subtypeRestr_target_subset ⟨a⟩ hz.2⟩,
        ⟨mem_univ _, hz.2⟩⟩
    · exact (hs.mono (show B ⊆ V from inter_subset_left)).congr
        (fun z hz => almostComplexInChart_restrict U (s.J z.1) a hz.2.2)
  smoothSection := by
    intro a
    obtain ⟨V, hV, hVi, hs⟩ := s.smoothSection a.val
    let B := V ∩ (univ ×ˢ (chartAt (Model (2 * n)) a).target)
    refine ⟨B, hV.inter (isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target), ?_, ?_⟩
    · intro z hz
      exact ⟨hVi ⟨hz.1, (chartAt (Model (2 * n)) a.val).subtypeRestr_target_subset ⟨a⟩ hz.2⟩,
        ⟨mem_univ _, hz.2⟩⟩
    · exact (hs.mono (show B ⊆ V from inter_subset_left)).congr
        (fun z hz => squaredTensorInChart_restrict U (s.tensor z.1) a hz.2.2)

/-- Open restriction respects the actual exterior derivatives of a
primitive family while retaining literal field values. -/
def restrictPrimitive {α : ℝ → M.Form 1}
    (s : MaslovFamily M (fun t => M.exteriorDerivative (α t)))
    (hα : ∀ t ∈ parameterInterval, M.IsSmoothForm (α t))
    (U : TopologicalSpace.Opens M.Point) :
    MaslovFamily (M.restrict U) (fun t =>
      (M.restrict U).exteriorDerivative ((M.restrict U).pullback M Subtype.val (α t))) where
  J := (s.restrict U).J
  tensor := (s.restrict U).tensor
  compatible := by
    intro t ht
    rw [funext (M.exteriorDerivative_restrict U (α t) (hα t ht))]
    exact (s.restrict U).compatible t ht
  canonical := (s.restrict U).canonical
  nowhereZero := (s.restrict U).nowhereZero
  smoothJ := (s.restrict U).smoothJ
  smoothSection := (s.restrict U).smoothSection

/-- A same-dimensional actual smooth embedding pulls a native primitive
family back through its constructed open-image diffeomorphism. -/
def pullbackPrimitiveEmbedding {N : SmoothManifold (2 * n)} {α : ℝ → N.Form 1}
    (s : MaslovFamily N (fun t => N.exteriorDerivative (α t)))
    (hα : ∀ t ∈ parameterInterval, N.IsSmoothForm (α t))
    (j : M.SmoothEmbedding N) :
    MaslovFamily M (fun t => M.exteriorDerivative (M.pullback N j.map (α t))) := by
  let U := j.openRange
  let R := N.restrict U
  let αr := fun t => R.pullback N Subtype.val (α t)
  let sr := (s.restrictPrimitive hα U).pullback j.rangeDiffeomorph
  refine { sr with compatible := ?_ }
  intro t ht
  have hαr : R.IsSmoothForm (αr t) := R.isSmoothForm_pullback_one N
    ⟨Subtype.val, contMDiff_subtype_val⟩ (α t) (hα t ht)
  have hd := M.exteriorDerivative_pullback R j.rangeDiffeomorph.toContMDiffMap (αr t) hαr
  have hp : M.pullback R j.rangeDiffeomorph (αr t) = M.pullback N j.map (α t) := by
    change M.pullback R j.rangeDiffeomorph (R.pullback N Subtype.val (α t)) = _
    rw [← M.pullback_comp R N (j.rangeDiffeomorph.mdifferentiable (by simp))
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n))) (n := ∞)).mdifferentiable (by simp))]
    rfl
  change M.exteriorDerivative (M.pullback R j.rangeDiffeomorph (αr t)) =
    M.pullback R j.rangeDiffeomorph (R.exteriorDerivative (αr t)) at hd
  rw [hp] at hd
  rw [hd]
  exact sr.compatible t ht

/-- A positive fixed spatial weight stretches a native primitive family
and constructs its jointly smooth canonical square. -/
def rescalePrimitive {α : ℝ → M.Form 1}
    (s : MaslovFamily M (fun t => M.exteriorDerivative (α t)))
    (hα : ∀ t ∈ parameterInterval, M.IsSmoothForm (α t))
    (Z : ℝ → (x : M.Point) → M.Tangent x) (hZ : M.IsSmoothVectorFieldFamily Z)
    (hcon : ∀ t ∈ parameterInterval, ∀ x v,
      evalTwo (M.exteriorDerivative (α t)) x (Z t x) v = evalOne (α t) x v)
    (w : M.Point → ℝ) (hw : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ w)
    (hwpos : ∀ x, 0 < w x)
    (hden : ∀ t ∈ parameterInterval, ∀ x,
      1 + normalizedWeightDifferential (M := M) w x (Z t x) ≠ 0) :
    MaslovFamily M (fun t => M.exteriorDerivative (fun x => w x • α t x)) := by
  let p := normalizedWeightDifferential (M := M) w
  have hp := isSmoothForm_normalizedWeightDifferential (M := M) w hw (fun x => (hwpos x).ne')
  have hd : ∀ t ∈ parameterInterval, ∀ x, 1 + 1 * p x (Z t x) ≠ 0 := by
    simpa only [one_mul] using hden
  let point (t : ℝ) (ht : t ∈ parameterInterval) : MaslovRepresentative M
      (M.exteriorDerivative (α t)) :=
    { J := s.J t, tensor := s.tensor t, compatible := s.compatible t ht
      canonical := s.canonical t ht, nowhereZero := s.nowhereZero t ht
      smooth := fun a => (s.smoothSection a).contDiffOn_slice ht }
  refine { J := fun t x => FsFltz.Geometry.rankTwoShearComplex (p x) (Z t x) 1 (s.J t x)
           tensor := fun t x => FsFltz.Geometry.rankTwoShearTensor (p x) (Z t x) 1 (s.tensor t x)
           compatible := fun t ht => ((point t ht).rescalePrimitive (hα t ht) (Z t)
             (fun a => (hZ a).contDiffOn_slice ht) (hcon t ht) w hw hwpos (hden t ht)).compatible
           canonical := fun t ht x => rankTwoShearTensor_canonical (n := n) (p x) (Z t x) 1
             (hd t ht x) (s.J t x) (s.tensor t x) (s.canonical t ht x)
           nowhereZero := fun t ht x => rankTwoShearTensor_ne_zero (n := n) (p x) (Z t x) 1
             (hd t ht x) (s.tensor t x) (s.nowhereZero t ht x)
           smoothJ := ?_, smoothSection := ?_ }
  · intro a
    have hp' := SmoothNearInterval.constant (chartAt (Model (2 * n)) a).open_target
      (contDiffOn_covector_comp_inverseChart M p hp a)
    have hd : ∀ z ∈ parameterInterval ×ˢ (chartAt (Model (2 * n)) a).target,
        1 + 1 * ((p ((chartAt (Model (2 * n)) a).symm z.2)).comp
          (M.inverseChartTangentMap a z.2)) (M.vectorInChart a (Z z.1) z.2) ≠ 0 := by
      intro z hz
      change 1 + 1 * p _ (M.inverseChartTangentMap a z.2 (M.vectorInChart a (Z z.1) z.2)) ≠ 0
      rw [M.inverseChart_vectorInChart (Z z.1) a hz.2, one_mul]
      exact hden z.1 hz.1 _
    obtain ⟨V, hV, hVi, hs⟩ := hp'.rankTwoShearComplex 1 (hZ a) (s.smoothJ a) hd
    let B := V ∩ (univ ×ˢ (chartAt (Model (2 * n)) a).target)
    refine ⟨B, hV.inter (isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target),
      fun z hz => ⟨hVi hz, ⟨mem_univ _, hz.2⟩⟩, ?_⟩
    exact (hs.mono (show B ⊆ V from inter_subset_left)).congr
      (fun z hz => almostComplexInChart_rankTwoShearComplex M p (Z z.1) 1 (s.J z.1) a hz.2.2)
  · intro a
    have hp' := SmoothNearInterval.constant (chartAt (Model (2 * n)) a).open_target
      (contDiffOn_covector_comp_inverseChart M p hp a)
    obtain ⟨V, hV, hVi, hs⟩ := hp'.rankTwoShearTensor 1 (hZ a) (s.smoothSection a)
    let B := V ∩ (univ ×ˢ (chartAt (Model (2 * n)) a).target)
    refine ⟨B, hV.inter (isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target),
      fun z hz => ⟨hVi hz, ⟨mem_univ _, hz.2⟩⟩, ?_⟩
    exact (hs.mono (show B ⊆ V from inter_subset_left)).congr
      (fun z hz => squaredTensorInChart_rankTwoShearTensor M p (Z z.1) 1 (s.tensor z.1) a hz.2.2)

end MaslovFamily
end FsFltz.Geometry
