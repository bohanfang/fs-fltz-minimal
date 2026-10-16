import FsFltz.Geometry.CompletionFormExtension
import FsFltz.Geometry.CollarExtension

/-!
# Compatible completion-family extensions from a closed-time collar

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.

Spatial cutoffs correct compact coefficient extensions near the completion
seam. The correction is cylindrical beyond the parameter endpoints while
preserving the actual compact-interior and boundary coefficients on the
closed interval. Coherent collar presentations are separate geometric input;
neither completed-family regularity nor open-time primitive overlap is input.

On a common collar, the compact presentation square and compact coverage
give the completed map's end square at negative radius. Together with its
nonnegative square this is an equality on an open spatial strip. Its
differential and the target completion's strict primitive formula give the
compact primitive overlap. A smooth cutoff supported in this strip replaces
the real coefficient extension by its cylindrical expression near the seam.
The closed-time overlap preserves the compact interior on the interval, and
the cylindrical expression preserves every boundary restriction. Boundary
compactness gives a smaller uniform collar where the cutoff is one; there
the corrected extension is cylindrical at every real time. Completion-form
uniqueness identifies the constructed smooth completed forms with the actual
transported primitives. Symplecticity and contraction then give smoothness
of the actual transported fields. The final constructor glues the supplied
compact presentations to their cylindrical maps and applies this route.
It constructs no intrinsic completion or coherent compact collar family,
and asserts none of the geometric conclusions of `thm:target` (352–415).
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

private theorem formInChart_function_smul {d k : ℕ} (M : SmoothManifold d)
    (a : M.Point) (χ : M.Point → ℝ) (α : M.Form k) (y : Model d) :
    M.formInChart a (fun x => χ x • α x) y =
      χ ((chartAt (Model d) a).symm y) • M.formInChart a α y := by
  ext vs
  rfl

private theorem isSmoothFormFamily_add {d k : ℕ} (M : SmoothManifold d)
    (α β : ℝ → M.Form k) (hα : M.IsSmoothFormFamily α)
    (hβ : M.IsSmoothFormFamily β) :
    M.IsSmoothFormFamily (fun t => α t + β t) := by
  intro a
  obtain ⟨A, hA, hIA, hαA⟩ := hα a
  obtain ⟨B, hB, hIB, hβB⟩ := hβ a
  refine ⟨A ∩ B, hA.inter hB, subset_inter hIA hIB,
    ((hαA.mono inter_subset_left).add (hβB.mono inter_subset_right)).congr ?_⟩
  intro p _
  exact congrFun (M.formInChart_add a (α p.1) (β p.1)) p.2

private theorem isSmoothFormFamily_sub {d k : ℕ} (M : SmoothManifold d)
    (α β : ℝ → M.Form k) (hα : M.IsSmoothFormFamily α)
    (hβ : M.IsSmoothFormFamily β) :
    M.IsSmoothFormFamily (fun t => α t - β t) := by
  intro a
  obtain ⟨A, hA, hIA, hαA⟩ := hα a
  obtain ⟨B, hB, hIB, hβB⟩ := hβ a
  refine ⟨A ∩ B, hA.inter hB, subset_inter hIA hIB,
    ((hαA.mono inter_subset_left).sub (hβB.mono inter_subset_right)).congr ?_⟩
  intro p _
  exact congrFun (M.formInChart_sub a (α p.1) (β p.1)) p.2

/-- A local form family multiplied by a smooth cutoff supported in its open
regularity domain extends smoothly by zero. Only actual local coefficient
regularity is required, including near the interval endpoints. -/
theorem isSmoothFormFamily_cutoff {d k : ℕ} (M : SmoothManifold d)
    (γ : ℝ → M.Form k) (U : Set M.Point)
    (χ : M.Point → ℝ) (hχ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ U)
    (hγ : ∀ a t, t ∈ parameterInterval → ∀ y,
      y ∈ (chartAt (Model d) a).target → (chartAt (Model d) a).symm y ∈ U →
      ∃ A : Set (ℝ × Model d), IsOpen A ∧ (t, y) ∈ A ∧
        ContDiffOn ℝ ∞ (fun p => M.formInChart a (γ p.1) p.2) A) :
    M.IsSmoothFormFamily (fun t x => χ x • γ t x) := by
  intro a
  apply smoothNearInterval_of_local
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  let c := chartAt (Model d) a
  have hχc : ContDiffOn ℝ ∞ (χ ∘ c.symm) c.target :=
    (hχ.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d))
      (x := a))).contDiffOn
  by_cases hx : c.symm y ∈ U
  · obtain ⟨A, hA, hpA, hγA⟩ := hγ a t ht y hy hx
    refine ⟨A ∩ (univ ×ˢ c.target), hA.inter (isOpen_univ.prod c.open_target),
      ⟨hpA, mem_univ _, hy⟩,
      ((hχc.comp contDiffOn_snd (fun _ hp => hp.2.2)).smul
        (hγA.mono inter_subset_left)).congr ?_⟩
    intro p _
    exact M.formInChart_function_smul a χ (γ p.1) p.2
  · have hz : c.symm y ∉ tsupport χ := fun hp => hx (hsupp hp)
    let V := c.target ∩ c.symm ⁻¹' (tsupport χ)ᶜ
    have hV : IsOpen V := c.continuousOn_symm.isOpen_inter_preimage c.open_target
      (isClosed_tsupport χ).isOpen_compl
    refine ⟨univ ×ˢ V, isOpen_univ.prod hV, ⟨mem_univ _, hy, hz⟩,
      (contDiffOn_const (c := (0 : Model d [⋀^Fin k]→L[ℝ] ℝ))).congr ?_⟩
    intro p hp
    have he : χ (c.symm p.2) = 0 := image_eq_zero_of_notMem_tsupport hp.2.2
    rw [M.formInChart_function_smul, he, zero_smul]

end SmoothManifold

namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- Total intrinsic compact collar coordinates. Only their actual open
domain is used; the fallback is immaterial after the spatial cutoff. -/
def compactEndCoordinates [Nonempty D.domain.boundary.Point]
    (x : D.domain.extension.Point) : D.domain.boundary.Point × ℝ :=
  if hx : x ∈ C.extensionCollarDomain then
    C.extensionCollarCoordinates ⟨x, hx⟩
  else (Classical.choice inferInstance, 0)

theorem contMDiffOn_compactEndCoordinates [Nonempty D.domain.boundary.Point] :
    ContMDiffOn 𝓘(ℝ, Model d)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ C.compactEndCoordinates
      C.extensionCollarDomain := by
  have he : (fun x : C.extensionCollarDomain => C.compactEndCoordinates x.val) =
      C.extensionCollarCoordinates := by
    funext x
    simp only [compactEndCoordinates, dite_eq_left x.property]
  intro x hx
  have hs := C.contMDiff_extensionCollarCoordinates ⟨x, hx⟩
  rw [← he] at hs
  exact (contMDiffAt_subtype_iff.mp hs).contMDiffWithinAt

theorem endMap_compactEndCoordinates [Nonempty D.domain.boundary.Point]
    (x : D.domain.extension.Point) (hx : x ∈ C.extensionCollarDomain) :
    C.endMap (C.compactEndCoordinates x) = C.inclusion.map x := by
  rw [compactEndCoordinates, dite_eq_left hx]
  exact C.endMap_extensionCollarCoordinates ⟨x, hx⟩

/-- The cylindrical expression pulled back to the compact extension's
intrinsic collar. It uses the supplied coefficient family's boundary form. -/
def cylindricalCompactForm [Nonempty D.domain.boundary.Point]
    (α : D.domain.extension.Form 1) : D.domain.extension.Form 1 :=
  fun x => Real.exp (C.compactEndCoordinates x).2 •
    D.domain.extension.pullback D.domain.boundary
      (fun y => (C.compactEndCoordinates y).1) (D.domain.boundaryForm α) x

/-- Cylindrical compact coefficients are jointly smooth on their genuine
open collar domain; no primitive-overlap equality is used. -/
theorem local_cylindricalCompactForm_family [Nonempty D.domain.boundary.Point]
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (a : D.domain.extension.Point) (t : ℝ) (ht : t ∈ parameterInterval)
    (y : Model d) (hy : y ∈ (chartAt (Model d) a).target)
    (hx : (chartAt (Model d) a).symm y ∈ C.extensionCollarDomain) :
    ∃ A : Set (ℝ × Model d), IsOpen A ∧ (t, y) ∈ A ∧
      ContDiffOn ℝ ∞ (fun p => D.domain.extension.formInChart a
        (C.cylindricalCompactForm (α p.1)) p.2) A := by
  have hb := D.domain.boundary.isSmoothFormFamily_pullback_one D.domain.extension
    D.domain.boundaryInclusion.map α hα
  have hf := contMDiff_fst.comp_contMDiffOn C.contMDiffOn_compactEndCoordinates
  have hr := Real.contDiff_exp.contMDiff.comp_contMDiffOn
    (contMDiff_snd.comp_contMDiffOn C.contMDiffOn_compactEndCoordinates)
  exact D.domain.extension.local_formFamily_scaled D.domain.boundary
    (fun t => C.cylindricalCompactForm (α t)) (fun t => D.domain.boundaryForm (α t))
    hb (fun x => (C.compactEndCoordinates x).1)
    (fun x => Real.exp (C.compactEndCoordinates x).2)
    C.extensionCollarDomain C.extensionCollarDomain.isOpen hf hr
    (univ ×ˢ C.extensionCollarDomain) (isOpen_univ.prod C.extensionCollarDomain.isOpen)
    Subset.rfl (fun _ _ => rfl) a t ht y hy ⟨mem_univ _, hx⟩

set_option backward.isDefEq.respectTransparency false in
/-- The cylindrical compact expression has its literal exponential
coefficients on every intrinsic overlap, including negative radii. -/
theorem cylindricalCompactForm_eval [Nonempty D.domain.boundary.Point]
    (α : D.domain.extension.Form 1) (x : D.domain.extension.Point)
    (q : D.domain.boundary.Point × ℝ) (he : C.inclusion.map x = C.endMap q)
    (w : Model d) (v : Model (d - 1)) (s : ℝ)
    (hd : mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap q (v, s)) :
    evalOne (C.cylindricalCompactForm α) x w =
      Real.exp q.2 * evalOne (D.domain.boundaryForm α) q.1 v := by
  have hx : x ∈ C.extensionCollarDomain := by
    change C.inclusion.map x ∈ C.escapingBasin
    exact ⟨q, he.symm⟩
  have hq : C.compactEndCoordinates x = q :=
    C.endMap_injective ((C.endMap_compactEndCoordinates x hx).trans he)
  have hg := (C.contMDiffOn_compactEndCoordinates.contMDiffAt
    (C.extensionCollarDomain.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
  have heq : (C.endMap ∘ C.compactEndCoordinates : D.domain.extension.Point →
      C.ambient.manifold.Point) =ᶠ[𝓝 x] C.inclusion.map := by
    filter_upwards [C.extensionCollarDomain.isOpen.mem_nhds hx] with y hy
    exact C.endMap_compactEndCoordinates y hy
  have hc := mfderiv_comp x (C.smooth_endMap.mdifferentiableAt (by simp)) hg
  rw [heq.mfderiv_eq, hq] at hc
  have hcv := congrArg (fun L => L w) hc
  have hcoord : mfderiv 𝓘(ℝ, Model d)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) C.compactEndCoordinates x w = (v, s) := by
    apply C.end_immersion q
    exact hcv.symm.trans hd
  have hf := mfderiv_comp x mdifferentiableAt_fst hg
  rw [mfderiv_fst] at hf
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (d - 1))
    (fun y => (C.compactEndCoordinates y).1) x =
      (ContinuousLinearMap.fst ℝ (Model (d - 1)) ℝ).comp
        (mfderiv 𝓘(ℝ, Model d)
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) C.compactEndCoordinates x) at hf
  change Real.exp (C.compactEndCoordinates x).2 *
    (D.domain.boundaryForm α (C.compactEndCoordinates x).1)
      (fun _ => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (d - 1))
        (fun y => (C.compactEndCoordinates y).1) x w) = _
  rw [hq, hf]
  change Real.exp q.2 * (D.domain.boundaryForm α q.1)
    (fun _ => (mfderiv 𝓘(ℝ, Model d)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) C.compactEndCoordinates x w).1) = _
  rw [hcoord]
  rfl

/-- The actual compact coefficient correction. Its cylindrical summand is
used only where the smooth cutoff is supported in the intrinsic collar. -/
def collarCorrectedForm [Nonempty D.domain.boundary.Point]
    (χ : D.domain.extension.Point → ℝ) (α : D.domain.extension.Form 1) :
    D.domain.extension.Form 1 :=
  fun x => α x + χ x • C.cylindricalCompactForm α x - χ x • α x

/-- Spatial correction preserves joint regularity of the compact family,
using the constructed cylindrical coefficients on the cutoff's support. -/
theorem isSmoothFormFamily_collarCorrectedForm [Nonempty D.domain.boundary.Point]
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (χ : D.domain.extension.Point → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ C.extensionCollarDomain) :
    D.domain.extension.IsSmoothFormFamily (fun t => C.collarCorrectedForm χ (α t)) := by
  have hγ := D.domain.extension.isSmoothFormFamily_cutoff
    (fun t => C.cylindricalCompactForm (α t)) C.extensionCollarDomain χ hχ hsupp
    (C.local_cylindricalCompactForm_family α hα)
  have hχα := D.domain.extension.isSmoothFormFamily_cutoff α univ χ hχ (subset_univ _)
    (fun a t ht y hy _ => by
      obtain ⟨A, hA, hIA, hαA⟩ := hα a
      exact ⟨A, hA, hIA ⟨ht, hy⟩, hαA⟩)
  exact D.domain.extension.isSmoothFormFamily_sub _ _
    (D.domain.extension.isSmoothFormFamily_add α _ hα hγ) hχα

theorem collarCorrectedForm_eq_of_cutoff_zero [Nonempty D.domain.boundary.Point]
    (χ : D.domain.extension.Point → ℝ) (α : D.domain.extension.Form 1)
    (x : D.domain.extension.Point) (hx : χ x = 0) :
    C.collarCorrectedForm χ α x = α x := by
  simp only [collarCorrectedForm, hx, zero_smul, add_zero, sub_zero]

theorem collarCorrectedForm_eq_of_cutoff_one [Nonempty D.domain.boundary.Point]
    (χ : D.domain.extension.Point → ℝ) (α : D.domain.extension.Form 1)
    (x : D.domain.extension.Point) (hx : χ x = 1) :
    C.collarCorrectedForm χ α x = C.cylindricalCompactForm α x := by
  simp only [collarCorrectedForm, hx, one_smul, add_sub_cancel_left]

theorem compactEndCoordinates_boundary [Nonempty D.domain.boundary.Point]
    (x : D.domain.boundary.Point) :
    C.compactEndCoordinates (D.domain.boundaryInclusion.map x) = (x, 0) := by
  have hx : D.domain.boundaryInclusion.map x ∈ C.extensionCollarDomain := by
    change C.inclusion.map (D.domain.boundaryInclusion.map x) ∈ C.escapingBasin
    exact ⟨(x, 0), C.endMap_zero x⟩
  apply C.endMap_injective
  rw [C.endMap_compactEndCoordinates _ hx, C.endMap_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The cylindrical compact expression has the original boundary
restriction for every coefficient form, without a radial coefficient premise. -/
theorem boundaryForm_cylindricalCompactForm [Nonempty D.domain.boundary.Point]
    (α : D.domain.extension.Form 1) :
    D.domain.boundaryForm (C.cylindricalCompactForm α) = D.domain.boundaryForm α := by
  let f : D.domain.extension.Point → D.domain.boundary.Point :=
    fun x => (C.compactEndCoordinates x).1
  have hf : ∀ x : D.domain.boundary.Point,
      MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model (d - 1)) f
        (D.domain.boundaryInclusion.map x) := by
    intro x
    have hx : D.domain.boundaryInclusion.map x ∈ C.extensionCollarDomain := by
      change C.inclusion.map (D.domain.boundaryInclusion.map x) ∈ C.escapingBasin
      exact ⟨(x, 0), C.endMap_zero x⟩
    exact ((contMDiff_fst.comp_contMDiffOn C.contMDiffOn_compactEndCoordinates).contMDiffAt
      (C.extensionCollarDomain.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
  have he : (f ∘ D.domain.boundaryInclusion.map :
      D.domain.boundary.Point → D.domain.boundary.Point) = id :=
    funext (fun x => congrArg Prod.fst (C.compactEndCoordinates_boundary x))
  funext x
  have hd := mfderiv_comp x (hf x)
    (D.domain.boundaryInclusion.map.contMDiff.mdifferentiableAt (by simp))
  rw [he, mfderiv_id] at hd
  ext vs
  change (Real.exp (C.compactEndCoordinates (D.domain.boundaryInclusion.map x)).2 •
    (D.domain.boundaryForm α (C.compactEndCoordinates
      (D.domain.boundaryInclusion.map x)).1).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (d - 1)) f
          (D.domain.boundaryInclusion.map x)))
      (fun i => mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
        D.domain.boundaryInclusion.map x (vs i)) = D.domain.boundaryForm α x vs
  rw [C.compactEndCoordinates_boundary]
  simp only [Real.exp_zero, one_smul]
  change D.domain.boundaryForm α x (fun i =>
    ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (d - 1)) f
      (D.domain.boundaryInclusion.map x)).comp
        (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
          D.domain.boundaryInclusion.map x)) (vs i)) = _
  rw [← hd]
  rfl

/-- The correction fixes the boundary restriction for all real parameters,
even when off-interval extension data have arbitrary radial coefficients. -/
theorem boundaryForm_collarCorrectedForm [Nonempty D.domain.boundary.Point]
    (χ : D.domain.extension.Point → ℝ) (α : D.domain.extension.Form 1) :
    D.domain.boundaryForm (C.collarCorrectedForm χ α) = D.domain.boundaryForm α := by
  have hb := C.boundaryForm_cylindricalCompactForm α
  funext x
  have hbx := congrFun hb x
  ext vs
  have he := congrArg (fun A => A vs) hbx
  change α (D.domain.boundaryInclusion.map x) (fun i =>
      mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
        D.domain.boundaryInclusion.map x (vs i)) +
    χ (D.domain.boundaryInclusion.map x) *
      (C.cylindricalCompactForm α (D.domain.boundaryInclusion.map x)) (fun i =>
        mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
          D.domain.boundaryInclusion.map x (vs i)) -
    χ (D.domain.boundaryInclusion.map x) *
      α (D.domain.boundaryInclusion.map x) (fun i =>
        mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
          D.domain.boundaryInclusion.map x (vs i)) = _
  change (C.cylindricalCompactForm α (D.domain.boundaryInclusion.map x)) (fun i =>
      mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
        D.domain.boundaryInclusion.map x (vs i)) =
    α (D.domain.boundaryInclusion.map x) (fun i =>
      mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
        D.domain.boundaryInclusion.map x (vs i)) at he
  rw [he, add_sub_cancel_right]
  rfl

/-- The part of the actual compact extension lying in a specified
two-sided intrinsic collar strip. -/
def compactEndStrip [Nonempty D.domain.boundary.Point] (δ : ℝ) :
    TopologicalSpace.Opens D.domain.extension.Point where
  carrier := (C.extensionCollarDomain : Set D.domain.extension.Point) ∩
    C.compactEndCoordinates ⁻¹' (univ ×ˢ Ioo (-δ) δ)
  is_open' := C.contMDiffOn_compactEndCoordinates.continuousOn.isOpen_inter_preimage
    C.extensionCollarDomain.isOpen (isOpen_univ.prod isOpen_Ioo)

theorem boundary_mem_compactEndStrip [Nonempty D.domain.boundary.Point]
    (δ : ℝ) (hδ : 0 < δ) (x : D.domain.boundary.Point) :
    D.domain.boundaryInclusion.map x ∈ C.compactEndStrip δ := by
  constructor
  · change C.inclusion.map (D.domain.boundaryInclusion.map x) ∈ C.escapingBasin
    exact ⟨(x, 0), C.endMap_zero x⟩
  · change C.compactEndCoordinates (D.domain.boundaryInclusion.map x) ∈ univ ×ˢ Ioo (-δ) δ
    rw [C.compactEndCoordinates_boundary]
    exact ⟨mem_univ _, by constructor <;> linarith⟩

set_option backward.isDefEq.respectTransparency false in
/-- Closed-interval collar equations suffice to construct compact extensions
with an open-time overlap equation. A spatial cutoff supplies that extension;
the original interval coefficients are preserved on the compact interior,
and the boundary restriction is preserved at every real time. -/
theorem exists_compatible_compactExtension [Nonempty D.domain.boundary.Point]
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (δ : ℝ) (hδ : 0 < δ)
    (hclosed : ∀ t ∈ parameterInterval, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      ∀ x ∈ interior D.domain.carrier, C.inclusion.map x = C.endMap q →
      ∀ (w : Model d) (v : Model (d - 1)) (s : ℝ),
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
          mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
            C.endMap q (v, s) →
        evalOne (α t) x w = Real.exp q.2 * evalOne (D.domain.boundaryForm (α t)) q.1 v) :
    ∃ (α' : ℝ → D.domain.extension.Form 1) (ε : ℝ), 0 < ε ∧
      D.domain.extension.IsSmoothFormFamily α' ∧
      (∀ t ∈ parameterInterval, ∀ x ∈ interior D.domain.carrier, α' t x = α t x) ∧
      (∀ t, D.domain.boundaryForm (α' t) = D.domain.boundaryForm (α t)) ∧
      ∀ t q, -ε < q.2 → ∀ x ∈ interior D.domain.carrier,
        C.inclusion.map x = C.endMap q →
        ∀ (w : Model d) (v : Model (d - 1)) (s : ℝ),
          mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
            mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
              C.endMap q (v, s) →
          evalOne (α' t) x w = Real.exp q.2 * evalOne (D.domain.boundaryForm (α' t)) q.1 v := by
  let K : Set D.domain.extension.Point := range D.domain.boundaryInclusion.map
  have hK : IsCompact K := by
    simpa only [K, image_univ] using D.domain.isCompact_boundary.image
      D.domain.boundaryInclusion.map.contMDiff.continuous
  obtain ⟨χ, V, hχ, hKV, hχV, _, hsupp⟩ :=
    CollarExtension.exists_smooth_compact_cutoff (I := 𝓘(ℝ, Model d))
      hK (C.compactEndStrip δ).isOpen (by
        rintro _ ⟨x, rfl⟩
        exact C.boundary_mem_compactEndStrip δ hδ x)
  let α' : ℝ → D.domain.extension.Form 1 := fun t => C.collarCorrectedForm χ (α t)
  have hα' := C.isSmoothFormFamily_collarCorrectedForm α hα χ hχ
    (hsupp.trans inter_subset_left)
  have hpreserve : ∀ t ∈ parameterInterval, ∀ x ∈ interior D.domain.carrier,
      α' t x = α t x := by
    intro t ht x hx
    by_cases hχx : χ x = 0
    · exact C.collarCorrectedForm_eq_of_cutoff_zero χ (α t) x hχx
    · have hstrip := hsupp (subset_tsupport χ (show x ∈ Function.support χ from hχx))
      let q := C.compactEndCoordinates x
      have he : C.inclusion.map x = C.endMap q :=
        (C.endMap_compactEndCoordinates x hstrip.1).symm
      have hforms : C.cylindricalCompactForm (α t) x = α t x := by
        ext vs
        have hv : vs = fun _ : Fin 1 => vs 0 := by
          funext i
          rw [Fin.eq_zero i]
        rw [hv]
        obtain ⟨⟨v, s⟩, hd⟩ :=
          ((C.endMap_isLocalDiffeomorph q).mfderivToContinuousLinearEquiv
            (by simp)).surjective
              (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x (vs 0))
        change mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap q (v, s) = _ at hd
        exact (C.cylindricalCompactForm_eval (α t) x q he (vs 0) v s hd.symm).trans
          (hclosed t ht q hstrip.2 x hx he (vs 0) v s hd.symm).symm
      change α t x + χ x • C.cylindricalCompactForm (α t) x - χ x • α t x = α t x
      rw [hforms, add_sub_cancel_right]
  let W : Set (D.domain.boundary.Point × ℝ) :=
    (C.presentationCollarSourceDomain : Set (D.domain.boundary.Point × ℝ)) ∩
      C.presentationCollarPoint ⁻¹' V
  have hW : IsOpen W := C.contMDiffOn_presentationCollarPoint.continuousOn.isOpen_inter_preimage
    C.presentationCollarSourceDomain.isOpen V.isOpen
  have hseam : Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ ({0} : Set ℝ)) ⊆ univ ×ˢ W := by
    rintro ⟨t, x, r⟩ ⟨_, _, hr⟩
    have hr0 : r = 0 := hr
    subst r
    refine ⟨mem_univ _, ?_, ?_⟩
    · exact ⟨D.domain.boundaryInclusion.map x, (C.endMap_zero x).symm⟩
    · rw [mem_preimage, C.presentationCollarPoint_zero]
      exact hKV ⟨x, rfl⟩
  obtain ⟨ε, hε, hwidth⟩ := CollarExtension.exists_uniform_width
    D.domain.isCompact_boundary (isOpen_univ.prod hW) hseam
  refine ⟨α', ε, hε, hα', hpreserve,
    fun t => C.boundaryForm_collarCorrectedForm χ (α t), ?_⟩
  intro t q hr x hx he w v s hd
  have hqr : q.2 ≤ 0 := (C.endMap_mem_compact_iff q).mp ⟨x, interior_subset hx, he⟩
  have hqW : q ∈ W := (hwidth (show ((0 : ℝ), q) ∈ Icc (0 : ℝ) 1 ×ˢ
      (univ ×ˢ Ioo (-ε) ε) from
        ⟨⟨le_rfl, zero_le_one⟩, mem_univ _, hr, lt_of_le_of_lt hqr hε⟩)).2
  have hpoint : C.presentationCollarPoint q = x :=
    C.inclusion.embedding.injective
      ((C.inclusionMap_presentationCollarPoint q hqW.1).trans he.symm)
  have hχx : χ x = 1 := by
    apply hχV x
    change x ∈ (V : Set D.domain.extension.Point)
    have hv : C.presentationCollarPoint q ∈ (V : Set D.domain.extension.Point) := hqW.2
    rwa [hpoint] at hv
  change (C.collarCorrectedForm χ (α t) x) (fun _ => w) =
    Real.exp q.2 * evalOne (D.domain.boundaryForm (C.collarCorrectedForm χ (α t))) q.1 v
  rw [show C.collarCorrectedForm χ (α t) x = C.cylindricalCompactForm (α t) x from
    C.collarCorrectedForm_eq_of_cutoff_one χ (α t) x hχx]
  rw [C.boundaryForm_collarCorrectedForm]
  exact C.cylindricalCompactForm_eval (α t) x q he w v s hd

/-- The actual presented completed primitive family is smooth from compact
regularity and a common collar equation on the closed time interval. The
open-time overlap is produced by `exists_compatible_compactExtension`.
The auxiliary compact extension may change outside the compact carrier;
the completed forms on the parameter interval are literally unchanged.
Empty boundaries, including dimension-zero domains, need no collar patch. -/
theorem isSmoothIntervalFormFamily_pullback_of_closed_collar
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val =
      D.domain.extension.pullback (E t).domain.extension (h t).extensionEquiv
        (E t).liouville.primitive)
    (δ : ℝ) (hδ : 0 < δ)
    (hclosed : ∀ t ∈ parameterInterval, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      ∀ x ∈ interior D.domain.carrier, C.inclusion.map x = C.endMap q →
      ∀ (w : Model d) (v : Model (d - 1)) (s : ℝ),
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
          mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
            C.endMap q (v, s) →
        evalOne (α t) x w = Real.exp q.2 * evalOne (D.domain.boundaryForm (α t)) q.1 v) :
    C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive) := by
  by_cases hb : Nonempty D.domain.boundary.Point
  · let _ := hb
    obtain ⟨α', ε, hε, hα', hcompact, hboundary, hoverlap⟩ :=
      C.exists_compatible_compactExtension α hα δ hδ hclosed
    let U : Set (ℝ × (D.domain.boundary.Point × ℝ)) :=
      univ ×ˢ (univ ×ˢ Ioi (-ε))
    have hU : IsOpen U := isOpen_univ.prod (isOpen_univ.prod isOpen_Ioi)
    have hpos : parameterInterval ×ˢ (univ ×ˢ Ici (0 : ℝ)) ⊆ U := by
      intro q hq
      refine ⟨mem_univ _, mem_univ _, ?_⟩
      have hr : 0 ≤ q.2.2 := hq.2.2
      change -ε < q.2.2
      linarith
    refine ⟨fun t => C.extendCompactForm (α' t),
      C.isSmoothFormFamily_extendCompactForm α' hα' U hU hpos
        (fun q hq => hoverlap q.1 q.2 hq.2.2), ?_⟩
    intro t
    apply C.form_eq_pullback_of_compactInterior_end (C' t) (h t) (p t)
    · intro x hx
      rw [C.extendCompactForm_compact_interior (α' t.val) x hx,
        hcompact t.val t.property x hx, hαeq t]
    · intro x r hr v s
      rw [C.extendCompactForm_end (α' t.val) x r hr v s,
        hboundary t.val, hαeq t]
  · let _ : IsEmpty D.domain.boundary.Point := ⟨fun x => hb ⟨x⟩⟩
    exact C.isSmoothIntervalFormFamily_pullback_of_compact_overlap E C' h p
      α hα hαeq univ isOpen_univ (subset_univ _) (fun q _ => isEmptyElim q.2.1)

/-- The same closed-time collar input produces joint regularity of both
actual transported completed primitives and actual Liouville fields. No
completed-family regularity or open-time coefficient equation is assumed. -/
theorem isSmoothIntervalPrimitiveAndFieldFamily_of_closed_collar
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val =
      D.domain.extension.pullback (E t).domain.extension (h t).extensionEquiv
        (E t).liouville.primitive)
    (δ : ℝ) (hδ : 0 < δ)
    (hclosed : ∀ t ∈ parameterInterval, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      ∀ x ∈ interior D.domain.carrier, C.inclusion.map x = C.endMap q →
      ∀ (w : Model d) (v : Model (d - 1)) (s : ℝ),
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
          mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
            C.endMap q (v, s) →
        evalOne (α t) x w = Real.exp q.2 * evalOne (D.domain.boundaryForm (α t)) q.1 v) :
    C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive) ∧
    C.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
      C.ambient.manifold.pullbackVectorField (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.field) := by
  have hp := C.isSmoothIntervalFormFamily_pullback_of_closed_collar E C' h p
    α hα hαeq δ hδ hclosed
  exact ⟨hp, C.isSmoothIntervalVectorFieldFamily_pullback_of_primitive_smooth E C' h p hp⟩

end Completion

namespace CompletionPresentationEquiv

variable {d : ℕ} {D E : LiouvilleDomain d}
  {C : Completion D} {C' : Completion E}
  {h : DomainPresentationEquiv D.domain E.domain}

/-- A compact collar square forces the actual completed presentation's end
square throughout that collar. Its negative-radius part uses compact
coverage and the presentation's compact square; its other part uses the
defining nonnegative end square. -/
theorem end_square_of_compact_collar (p : CompletionPresentationEquiv C C' h)
    (U : Set (D.domain.boundary.Point × ℝ))
    (hcollar : ∀ q ∈ U, ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
      C'.inclusion.map (h.extensionEquiv x) = C'.endMap (h.boundaryEquiv q.1, q.2))
    (q : D.domain.boundary.Point × ℝ) (hq : q ∈ U) :
    p.equiv (C.endMap q) = C'.endMap (h.boundaryEquiv q.1, q.2) := by
  by_cases hr : 0 ≤ q.2
  · exact p.end_square q.1 q.2 hr
  · obtain ⟨x, hx, he⟩ := (C.endMap_mem_compact_iff q).mpr (le_of_lt (lt_of_not_ge hr))
    rw [← he, p.compact_square x hx]
    exact hcollar q hq x hx he

set_option backward.isDefEq.respectTransparency false in
/-- Exact compact collar geometry yields the primitive-overlap coefficient
equation. Differentiating the derived actual end square uses its open
spatial neighborhood; the completion's strict primitive formula then
supplies the exponential factor. No coefficient equation is extra input. -/
theorem compact_primitive_overlap_of_collar_square
    (p : CompletionPresentationEquiv C C' h)
    (U : Set (D.domain.boundary.Point × ℝ)) (hU : IsOpen U)
    (hcollar : ∀ q ∈ U, ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
      C'.inclusion.map (h.extensionEquiv x) = C'.endMap (h.boundaryEquiv q.1, q.2))
    (q : D.domain.boundary.Point × ℝ) (hq : q ∈ U)
    (x : D.domain.extension.Point) (hx : x ∈ interior D.domain.carrier)
    (he : C.inclusion.map x = C.endMap q)
    (w : Model d) (v : Model (d - 1)) (s : ℝ)
    (hd : mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w =
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap q (v, s)) :
    evalOne (D.domain.extension.pullback E.domain.extension h.extensionEquiv
      E.liouville.primitive) x w = Real.exp q.2 * evalOne
        (D.domain.boundaryForm (D.domain.extension.pullback E.domain.extension
          h.extensionEquiv E.liouville.primitive)) q.1 v := by
  have hsq := p.end_square_of_compact_collar U hcollar q hq
  have heq : (p.equiv ∘ C.endMap) =ᶠ[𝓝 q]
      (fun z : D.domain.boundary.Point × ℝ => C'.endMap (h.boundaryEquiv z.1, z.2)) := by
    filter_upwards [hU.mem_nhds hq] with z hz
    exact p.end_square_of_compact_collar U hcollar z hz
  have hder : mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (p.equiv ∘ C.endMap) q =
      mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        (fun z : D.domain.boundary.Point × ℝ => C'.endMap (h.boundaryEquiv z.1, z.2)) q := by
    ext u
    exact congrArg (fun L => L u) (heq.mfderiv_eq
      (I := (𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model d)))
  let η := C.ambient.manifold.pullback C'.ambient.manifold p.equiv C'.ambient.primitive
  calc
    _ = evalOne η (C.inclusion.map x)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map x w) :=
      congrArg (fun A => A (fun _ => w)) (p.compact_primitive_interior x hx).symm
    _ = evalOne η (C.endMap q)
        (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
          C.endMap q (v, s)) := by
      let a : C.ambient.manifold.Point → Model d [⋀^Fin 1]→L[ℝ] ℝ := η
      change a (C.inclusion.map x) (fun _ => _) = a (C.endMap q) (fun _ => _)
      rw [he]
      exact congrArg (fun u : Model d => a (C.endMap q) (fun _ => u)) hd
    _ = _ := p.end_primitive_of_end_mfderiv q.1 q.2 hsq hder v s

end CompletionPresentationEquiv

namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- A common geometric compact collar square and smooth compact primitive
coefficients produce both completed regularity clauses. The primitive
overlap is derived from the presentation maps on the closed interval, and
its open-time extension is constructed by spatial correction. Coherent
collar maps and their common width remain explicit geometric inputs. -/
theorem isSmoothIntervalPrimitiveAndFieldFamily_of_collar_presentations
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (α : ℝ → D.domain.extension.Form 1)
    (hα : D.domain.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val =
      D.domain.extension.pullback (E t).domain.extension (h t).extensionEquiv
        (E t).liouville.primitive)
    (δ : ℝ) (hδ : 0 < δ)
    (hcollar : ∀ t : Parameter, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
        (C' t).inclusion.map ((h t).extensionEquiv x) =
          (C' t).endMap ((h t).boundaryEquiv q.1, q.2)) :
    C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive) ∧
    C.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
      C.ambient.manifold.pullbackVectorField (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.field) := by
  apply C.isSmoothIntervalPrimitiveAndFieldFamily_of_closed_collar E C' h p
    α hα hαeq δ hδ
  intro t ht q hq x hx he w v s hd
  simpa only [hαeq ⟨t, ht⟩] using
    (p ⟨t, ht⟩).compact_primitive_overlap_of_collar_square
      (univ ×ˢ Ioo (-δ) δ) (isOpen_univ.prod isOpen_Ioo)
      (hcollar ⟨t, ht⟩) q hq x hx he w v s hd

/-- For supplied completions, coherently collar-adapted compact presentations extend to actual
completion presentations whose transported primitives and Liouville fields
are jointly smooth. The completed presentations and their regularity are
outputs. Inputs supply only the compact primitive family's regularity and
an actual common geometric collar square on the closed parameter interval.
Construction of such coherent compact presentations remains separate. -/
theorem exists_smooth_completionFamily_of_collar_presentations
    (E : Parameter → LiouvilleDomain d) (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (hα : D.domain.extension.IsSmoothIntervalFormFamily (fun t =>
      D.domain.extension.pullback (E t).domain.extension (h t).extensionEquiv
        (E t).liouville.primitive))
    (δ : ℝ) (hδ : 0 < δ)
    (hcollar : ∀ t : Parameter, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
        (C' t).inclusion.map ((h t).extensionEquiv x) =
          (C' t).endMap ((h t).boundaryEquiv q.1, q.2)) :
    ∃ p : ∀ t, CompletionPresentationEquiv C (C' t) (h t),
      C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
        C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
          (C' t).ambient.primitive) ∧
      C.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
        C.ambient.manifold.pullbackVectorField (C' t).ambient.manifold (p t).equiv
          (C' t).ambient.field) := by
  let U : Set (D.domain.boundary.Point × ℝ) := univ ×ˢ Ioi (-δ)
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioi
  have hpos : univ ×ˢ Ici (0 : ℝ) ⊆ U := by
    intro q hq
    refine ⟨mem_univ _, ?_⟩
    have hr : 0 ≤ q.2 := hq.2
    change -δ < q.2
    linarith
  have hglue : ∀ t : Parameter, ∀ q ∈ U, ∀ x ∈ D.domain.carrier,
      C.inclusion.map x = C.endMap q →
        (C' t).inclusion.map ((h t).extensionEquiv x) =
          (C' t).endMap ((h t).boundaryEquiv q.1, q.2) := by
    intro t q hq x hx he
    have hr : q.2 ≤ 0 := (C.endMap_mem_compact_iff q).mp ⟨x, hx, he⟩
    exact hcollar t q ⟨mem_univ _, hq.2, lt_of_le_of_lt hr hδ⟩ x hx he
  let p : ∀ t, CompletionPresentationEquiv C (C' t) (h t) :=
    fun t => C.presentationEquivOfCollar (C' t) (h t) U hU hpos (hglue t)
  obtain ⟨α, hs, heq⟩ := hα
  exact ⟨p, C.isSmoothIntervalPrimitiveAndFieldFamily_of_collar_presentations
    E C' h p α hs heq δ hδ hcollar⟩

end Completion
end FsFltz.Geometry
