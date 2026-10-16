import FsFltz.Geometry.PrescribedMaslovSectionExtension

/-!
# Local extensions of prescribed complex structures

Source: `geoemtric-part-fsf.tex`, `sec:pairs`, lines 120–123;
`def:maslov`, lines 212–232; `sec:lean`, lines 794–814.

The smooth ambient extension in `MaslovFamily.smoothJ` need only square to
minus identity on the parameter interval. Projecting a coframe chosen at
one interval point gives a smooth invertible coframe on an open neighborhood.
It intertwines the original structure at every interval point of that
neighborhood. Conjugating the standard complex structure through this
coframe gives a true complex extension with literal agreement there.

The prescribed two-form and time parameter are unchanged. Compatibility
with a two-form outside the interval is not asserted. The local coframes
also supply coordinates for the canonical bundle directly over the interval;
different corrected complex extensions need not agree outside it.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

/-- Conjugation through a coframe. The inverse is used in the theorems only
on the proved invertibility locus. -/
def coframeComplexStructure {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) :
    Model (2 * n) →L[ℝ] Model (2 * n) :=
  C.inverse.comp ((coordinateComplexStructure n).comp C)

theorem coframeComplexStructure_sq {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible)
    (v : Model (2 * n)) :
    coframeComplexStructure C (coframeComplexStructure C v) = -v := by
  simp only [coframeComplexStructure, ContinuousLinearMap.comp_apply,
    hC.self_apply_inverse, coordinateComplexStructure_sq, map_neg,
    hC.inverse_apply_self]

theorem coframeComplexStructure_intertwines {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible)
    (v : Model (2 * n)) :
    C (coframeComplexStructure C v) = coordinateComplexStructure n (C v) := by
  simp only [coframeComplexStructure, ContinuousLinearMap.comp_apply,
    hC.self_apply_inverse]

/-- An intertwining coframe recovers the given structure exactly. -/
theorem coframeComplexStructure_eq {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    coframeComplexStructure C = J := by
  ext v
  simp only [coframeComplexStructure, ContinuousLinearMap.comp_apply]
  rw [← hCJ, hC.inverse_apply_self]

theorem contDiffOn_coframeComplexStructure {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {C : E → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C U) (hinv : ∀ x ∈ U, (C x).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => coframeComplexStructure (C x)) U :=
  (contDiffOn_coframe_inverse hC hinv).clm_comp
    ((contDiffOn_const (c := coordinateComplexStructure n)).clm_comp hC)

/-- A raw smooth extension produces local coframes without assuming that
it remains a complex structure outside the prescribed locus. -/
theorem exists_smooth_local_prescribedComplexCoframe {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U A : Set E} {p : E} (hU : IsOpen U) (hpU : p ∈ U) (hpA : p ∈ A)
    {J : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    (hJ : ContDiffOn ℝ ∞ J U)
    (hJsq : ∀ x ∈ U ∩ A, ∀ v, J x (J x v) = -v) :
    ∃ C₀ : Model (2 * n) ≃L[ℝ] TangentCoordinates n,
      ∃ V ⊆ U, IsOpen V ∧ p ∈ V ∧
        ContDiffOn ℝ ∞ (fun x => projectedComplexCoframe C₀ (J x)) V ∧
        (∀ x ∈ V, (projectedComplexCoframe C₀ (J x)).IsInvertible) ∧
        (∀ x ∈ V ∩ A, ∀ v, projectedComplexCoframe C₀ (J x) (J x v) =
          coordinateComplexStructure n (projectedComplexCoframe C₀ (J x) v)) := by
  obtain ⟨C₀, hC₀⟩ := exists_complexCoframe (J p) (hJsq p ⟨hpU, hpA⟩)
  have hi := projectedComplexCoframe_eventually_invertible hU hpU C₀ hJ hC₀
  obtain ⟨N, hN, hNo, hpN⟩ := mem_nhds_iff.mp hi
  refine ⟨C₀, N ∩ U, inter_subset_right, hNo.inter hU, ⟨hpN, hpU⟩, ?_, ?_, ?_⟩
  · exact (contDiffOn_projectedComplexCoframe C₀ hJ).mono inter_subset_right
  · intro x hx
    exact hN hx.1
  · intro x hx
    exact projectedComplexCoframe_intertwines C₀ (J x) (hJsq x ⟨hx.1.2, hx.2⟩)

/-- The original structure is fixed at every prescribed point of the
constructed open neighborhood, including parameter endpoints. -/
theorem exists_smooth_local_prescribedComplexExtension {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U A : Set E} {p : E} (hU : IsOpen U) (hpU : p ∈ U) (hpA : p ∈ A)
    {J : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    (hJ : ContDiffOn ℝ ∞ J U)
    (hJsq : ∀ x ∈ U ∩ A, ∀ v, J x (J x v) = -v) :
    ∃ V ⊆ U, IsOpen V ∧ p ∈ V ∧
      ∃ K : E → Model (2 * n) →L[ℝ] Model (2 * n),
        ContDiffOn ℝ ∞ K V ∧ (∀ x ∈ V, ∀ v, K x (K x v) = -v) ∧
          EqOn K J (V ∩ A) := by
  obtain ⟨C₀, V, hVU, hVo, hpV, hC, hinv, hCJ⟩ :=
    exists_smooth_local_prescribedComplexCoframe hU hpU hpA hJ hJsq
  refine ⟨V, hVU, hVo, hpV,
    fun x => coframeComplexStructure (projectedComplexCoframe C₀ (J x)),
    contDiffOn_coframeComplexStructure hC hinv, ?_, ?_⟩
  · intro x hx v
    exact coframeComplexStructure_sq _ (hinv x hx) v
  · intro x hx
    exact coframeComplexStructure_eq _ (hinv x hx.1) (J x) (hCJ x hx)

namespace MaslovFamily

set_option backward.isDefEq.respectTransparency false in
/-- Every encoded Maslov family supplies actual smooth invertible coframes
near each interval point, intertwining its original complex structure on
the interval. No coframe family or corrected structure is an input. -/
theorem exists_local_prescribedComplexCoframe {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (f : MaslovFamily M eta) (a : M.Point) {p : ℝ × Model (2 * n)}
    (hp : p ∈ parameterInterval ×ˢ (chartAt (Model (2 * n)) a).target) :
    ∃ C₀ : Model (2 * n) ≃L[ℝ] TangentCoordinates n,
      ∃ V ⊆ (univ ×ˢ (chartAt (Model (2 * n)) a).target),
        IsOpen V ∧ p ∈ V ∧
        ContDiffOn ℝ ∞ (fun z => projectedComplexCoframe C₀
          (almostComplexInChart M a (f.J z.1) z.2)) V ∧
        (∀ z ∈ V, (projectedComplexCoframe C₀
          (almostComplexInChart M a (f.J z.1) z.2)).IsInvertible) ∧
        (∀ z ∈ V ∩ (parameterInterval ×ˢ (chartAt (Model (2 * n)) a).target),
          ∀ v, projectedComplexCoframe C₀
              (almostComplexInChart M a (f.J z.1) z.2)
              (almostComplexInChart M a (f.J z.1) z.2 v) =
            coordinateComplexStructure n (projectedComplexCoframe C₀
              (almostComplexInChart M a (f.J z.1) z.2) v)) := by
  obtain ⟨U, hUo, hslab, hJ⟩ := f.smoothJ a
  let W := U ∩ (univ ×ˢ (chartAt (Model (2 * n)) a).target)
  have hWo : IsOpen W := hUo.inter
    (isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target)
  obtain ⟨C₀, V, hVW, hVo, hpV, hC, hinv, hCJ⟩ :=
    exists_smooth_local_prescribedComplexCoframe hWo
      (show p ∈ W from ⟨hslab hp, mem_univ _, hp.2⟩) hp
      (hJ.mono inter_subset_left)
      (fun z hz => almostComplexInChart_sq M a (f.J z.1)
        (f.compatible z.1 hz.2.1).2.1 z.2 hz.2.2)
  exact ⟨C₀, V, fun z hz => (hVW hz).2, hVo, hpV, hC, hinv, hCJ⟩

set_option backward.isDefEq.respectTransparency false in
/-- A prescribed family produces its local true-complex and nonvanishing
canonical section extensions together. Both original interval functions
are preserved literally; the given two-form is never reparametrized.

This consumes the formerly conditional local section-extension theorem
with the complex correction constructed from `smoothJ`. -/
theorem exists_local_prescribedComplexAndSectionExtension {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (f : MaslovFamily M eta) (a : M.Point) {p : ℝ × Model (2 * n)}
    (hp : p ∈ parameterInterval ×ˢ (chartAt (Model (2 * n)) a).target) :
    ∃ V ⊆ (univ ×ˢ (chartAt (Model (2 * n)) a).target),
      IsOpen V ∧ p ∈ V ∧
      ∃ K : (ℝ × Model (2 * n)) → Model (2 * n) →L[ℝ] Model (2 * n),
      ∃ q : (ℝ × Model (2 * n)) → SquaredCanonicalTensor n,
        ContDiffOn ℝ ∞ K V ∧
        (∀ z ∈ V, ∀ v, K z (K z v) = -v) ∧
        (∀ z ∈ V ∩ (parameterInterval ×ˢ (chartAt (Model (2 * n)) a).target),
          K z = almostComplexInChart M a (f.J z.1) z.2) ∧
        ContDiffOn ℝ ∞ q V ∧
        (∀ z ∈ V, IsSquaredCanonicalTensor (K z) (q z)) ∧
        (∀ z ∈ V, q z ≠ 0) ∧
        (∀ z ∈ V ∩ (parameterInterval ×ˢ (chartAt (Model (2 * n)) a).target),
          q z = squaredTensorInChart M a (f.tensor z.1) z.2) := by
  obtain ⟨C₀, U, hUchart, hUo, hpU, hC, hinv, hCJ⟩ :=
    f.exists_local_prescribedComplexCoframe a hp
  let K : (ℝ × Model (2 * n)) → Model (2 * n) →L[ℝ] Model (2 * n) :=
    fun z => coframeComplexStructure (projectedComplexCoframe C₀
      (almostComplexInChart M a (f.J z.1) z.2))
  have hK : ContDiffOn ℝ ∞ K U := contDiffOn_coframeComplexStructure hC hinv
  have hKsq : ∀ z ∈ U, ∀ v, K z (K z v) = -v :=
    fun z hz => coframeComplexStructure_sq _ (hinv z hz)
  have hagree : ∀ z ∈ U ∩
      (parameterInterval ×ˢ (chartAt (Model (2 * n)) a).target),
      K z = almostComplexInChart M a (f.J z.1) z.2 :=
    fun z hz => coframeComplexStructure_eq _ (hinv z hz.1) _ (hCJ z hz)
  obtain ⟨V, hVU, hVo, hpV, q, hq, hqcan, hqnz, heq⟩ :=
    f.exists_local_prescribedSectionExtension a hUo hK hKsq hagree hpU hp
  refine ⟨V, fun z hz => (hVU hz).2, hVo, hpV, K, q,
    hK.mono (fun z hz => (hVU hz).1), ?_, ?_, hq, hqcan, hqnz, heq⟩
  · intro z hz
    exact hKsq z (hVU hz).1
  · intro z hz
    exact hagree z ⟨(hVU hz.1).1, hz.2⟩

end MaslovFamily

end FsFltz.Geometry
