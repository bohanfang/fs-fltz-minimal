import FsFltz.Geometry.TailoringHittingRibbon
import FsFltz.Geometry.TailoringHittingOuterFamily

/-!
# Completed pair families of the same retained hitting ribbon

Source: `geometric-part-fsf-proof.tex`, `eq:ribbonprimitive` and the following
paragraph, lines 1867–1875; `subsec:junction`, lines 1918–1924. The coefficient
runs from K to zero. Both localized completions are constructed on the same
retained outer domain and the same shrinking endpoint.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry.SmoothManifold

/-- A jointly smooth family on an open real parameter set restricts along
any smooth parameter path through that set, with open extensions at endpoints.
The off-neighborhood value uses a fixed slice, without a target nonemptiness
assumption. -/
theorem isSmoothIntervalMapFamily_of_open_parameter {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (V : TopologicalSpace.Opens ℝ) (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c)
    (hV : ∀ t : Parameter, c t.val ∈ V)
    (j : V → M.SmoothEmbedding N)
    (hj : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p : V × M.Point => (j p.1).map p.2)) :
    M.IsSmoothIntervalMapFamily N (fun t => (j ⟨c t.val, hV t⟩).map) := by
  classical
  let r : ℝ → V := fun s =>
    if hs : c s ∈ V then ⟨c s, hs⟩ else ⟨c 0, hV parameterZero⟩
  let Ω : Set ℝ := c ⁻¹' (V : Set ℝ)
  have hΩ : IsOpen Ω := V.isOpen.preimage hc.continuous
  refine ⟨fun s x => (j (r s)).map x,
    ⟨Ω ×ˢ univ, hΩ.prod isOpen_univ, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact ⟨hV ⟨p.1, hp.1⟩, mem_univ _⟩
  · intro p hp
    have hr : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ r p.1 := by
      apply (ContMDiffAt.subtypeVal_comp_iff V r p.1).mp
      apply hc.contMDiff.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [hΩ.mem_nhds hp.1] with s hs
      change c s ∈ V at hs
      simp only [Function.comp_apply, r, dite_eq_left hs]
    have hpre : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × M.Point => (r p.1, p.2)) p :=
      (hr.comp p contMDiff_fst.contMDiffAt).prodMk contMDiff_snd.contMDiffAt
    exact ((hj _).comp p hpre).contMDiffWithinAt
  · intro t
    funext x
    simp only [r, dite_eq_left (hV t)]

end FsFltz.Geometry.SmoothManifold

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- The actual decreasing coefficient, including the literal two endpoints. -/
def decreasingHittingParameter (K : ℝ) (hK : 0 ≤ K) (t : Parameter) : Icc (0 : ℝ) K :=
  ⟨K * (1 - t.val), ⟨mul_nonneg hK (sub_nonneg.mpr t.property.2), by
    nlinarith [t.property.1]⟩⟩

@[simp] theorem decreasingHittingParameter_zero (K : ℝ) (hK : 0 ≤ K) :
    (decreasingHittingParameter K hK parameterZero).val = K := by
  simp [decreasingHittingParameter, parameterZero]

@[simp] theorem decreasingHittingParameter_one (K : ℝ) (hK : 0 ≤ K) :
    (decreasingHittingParameter K hK parameterOne).val = 0 := by
  simp [decreasingHittingParameter, parameterOne]

/-- The actual assembled hitting deformation, retaining both families of
collars and completions. Its pair formula is definitionally the same supplied
hitting embedding and witness on each localized compact presentation. -/
structure CompletedHittingRibbonFamily {n : ℕ}
    (D : CompactDomain (2 * n)) (F : LiouvilleDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D)
    (j : Parameter → F.domain.extension.SmoothEmbedding D.boundary)
    (b : Parameter → D.boundary.Point → ℝ) where
  ambient_smooth : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)
  ribbon_smooth : F.domain.extension.IsSmoothIntervalFormFamily (fun _ : Parameter => F.liouville.primitive)
  embedding_smooth : F.domain.extension.IsSmoothIntervalMapFamily D.boundary (fun t => (j t).map)
  witness_smooth : D.boundary.IsSmoothIntervalScalarFamily b
  positive : ∀ t x, 0 < b t x
  primitive : ∀ t x, x ∈ F.domain.carrier →
    F.domain.extension.pullback D.boundary (j t).map
      (fun y => b t y • D.boundaryForm (L t).primitive y) x = F.liouville.primitive x
  ambient : LocalizedCompletionFamily D L
  ribbon : LocalizedCompletionFamily F.domain (fun _ => F.liouville)

/-- Construct both completed families on the specified same compact data. -/
theorem exists_completedHittingRibbonFamily {n : ℕ}
    (D : CompactDomain (2 * n)) (F : LiouvilleDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (j : Parameter → F.domain.extension.SmoothEmbedding D.boundary)
    (hj : F.domain.extension.IsSmoothIntervalMapFamily D.boundary (fun t => (j t).map))
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsSmoothIntervalScalarFamily b) (hpos : ∀ t x, 0 < b t x)
    (hp : ∀ t x, x ∈ F.domain.carrier →
      F.domain.extension.pullback D.boundary (j t).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x = F.liouville.primitive x) :
    Nonempty (CompletedHittingRibbonFamily D F L j b) := by
  have hM := F.domain.extension.isSmoothIntervalFormFamily_constant
    F.liouville.primitive F.liouville.smooth_primitive
  exact ⟨⟨hL, hM, hj, hb, hpos, hp, D.localizedCompletionFamily L hL,
    F.domain.localizedCompletionFamily (fun _ => F.liouville) hM⟩⟩

namespace CompletedHittingRibbonFamily

/-- The actual pair deformation is computed from the retained hitting
embeddings, witnesses, primitives and both constructed completion families. -/
def deformation {n : ℕ}
    {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
    {L : Parameter → LiouvilleStructure D}
    {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D F L j b) : PairDeformation n :=
  D.localizedPairDeformation F.domain L (fun _ => F.liouville) j b
    H.ambient_smooth H.ribbon_smooth H.embedding_smooth H.witness_smooth
    H.positive H.ambient H.ribbon H.primitive

/-- The computed deformation is made from these same hitting data and collars,
so its equation exposes the actual witnessed-pair tuple at every parameter. -/
theorem pair_eq {n : ℕ}
    {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
    {L : Parameter → LiouvilleStructure D}
    {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D F L j b) (t : Parameter) :
    H.deformation.pair t = localizedWitnessedPair ⟨D, L t⟩ F
      (H.ambient.collars t) (H.ribbon.collars t) (j t) (b t)
      (H.witness_smooth.contMDiff_slice t) (H.positive t) (H.primitive t) := rfl

end CompletedHittingRibbonFamily
/-- Analytic native data and the exact retained ribbon law assemble the
actual decreasing-coefficient family on that same marked outer domain. -/
theorem OuterAmbientInclusionMarkingFamily.exists_completed_hitting_ribbon_family {n : ℕ}
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {α : Parameter → (lgManifold n).Form 1}
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β A K : ℝ) (hK : 0 ≤ K)
    (O : OuterAmbientInclusionMarkingFamily Q J (fun y => φ y.1 - A) α)
    (hboundary : range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map =
      {y | φ y.1 = A})
    (hnd : ∀ k ∈ Icc (0 : ℝ) K, ∀ y,
      (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) k)) y)
    (hout : ∀ k ∈ Icc (0 : ℝ) K, ∀ y, φ y.1 = A →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y))
    (F : LiouvilleDomain (2 * n - 2)) (V : TopologicalSpace.Opens ℝ)
    (hPV : Icc (0 : ℝ) K ⊆ V)
    (j : V → F.domain.extension.SmoothEmbedding O.domain.boundary)
    (hj : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n - 1)) ∞
      (fun p : V × F.domain.extension.Point => (j p.1).map p.2))
    (w : ℝ × O.domain.boundary.Point → ℝ)
    (hw : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 1))) 𝓘(ℝ, ℝ) ∞ w)
    (hpos : ∀ p, 0 < w p)
    (hp : ∀ k (hk : k ∈ Icc (0 : ℝ) K), ∀ x ∈ F.domain.carrier,
      F.domain.extension.pullback O.domain.boundary (j ⟨k, hPV hk⟩).map
        (fun y => w (k, y) • O.domain.boundaryForm
          (O.domain.extension.pullback (lgManifold n) O.nativeEmbedding.map
            ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
              (tailoringFamily I β 1) k)) y) x = F.liouville.primitive x) :
    ∃ L : Parameter → LiouvilleStructure O.domain,
      (∀ t, (L t).primitive = O.domain.extension.pullback (lgManifold n)
        O.nativeEmbedding.map ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
          (tailoringFamily I β 1) (K * (1 - t.val)))) ∧
      Nonempty (CompletedHittingRibbonFamily O.domain F L
        (fun t => j ⟨(decreasingHittingParameter K hK t).val,
          hPV (decreasingHittingParameter K hK t).property⟩)
        (fun t y => w (K * (1 - t.val), y))) := by
  obtain ⟨L, hL, hsmooth, _hfields, _hsymplectic, _hcompleted⟩ :=
    O.exists_hitting_coefficient_family I hφ β A K hK hboundary hnd hout
  let jt : Parameter → F.domain.extension.SmoothEmbedding O.domain.boundary :=
    fun t => j ⟨(decreasingHittingParameter K hK t).val,
      hPV (decreasingHittingParameter K hK t).property⟩
  let b : Parameter → O.domain.boundary.Point → ℝ := fun t y => w (K * (1 - t.val), y)
  have hjs : F.domain.extension.IsSmoothIntervalMapFamily O.domain.boundary
      (fun t => (jt t).map) :=
    F.domain.extension.isSmoothIntervalMapFamily_of_open_parameter O.domain.boundary
      V (fun s => K * (1 - s)) (contDiff_const.mul (contDiff_const.sub contDiff_id))
      (fun t => hPV (decreasingHittingParameter K hK t).property) j hj
  have hws : O.domain.boundary.IsSmoothIntervalScalarFamily b := by
    refine ⟨fun s y => w (K * (1 - s), y), ?_, fun _ => rfl⟩
    apply O.domain.boundary.isSmoothScalarFamily_of_contMDiff
    exact hw.comp
      ((contMDiff_const.mul (contMDiff_const.sub contMDiff_fst)).prodMk contMDiff_snd)
  have hprimitive : ∀ t x, x ∈ F.domain.carrier →
      F.domain.extension.pullback O.domain.boundary (jt t).map
        (fun y => b t y • O.domain.boundaryForm (L t).primitive y) x = F.liouville.primitive x := by
    intro t x hx
    rw [hL t]
    exact hp _ (decreasingHittingParameter K hK t).property x hx
  exact ⟨L, hL, exists_completedHittingRibbonFamily O.domain F L hsmooth jt hjs b hws
    (fun t y => hpos (K * (1 - t.val), y)) hprimitive⟩

end FsFltz
