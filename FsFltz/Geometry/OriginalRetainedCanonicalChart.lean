import FsFltz.Geometry.IntrinsicNativeCompletionInteriorCanonicalBundle
import FsFltz.Geometry.IntrinsicNativeCompletionEndCanonicalBundle

/-!
# Canonical charts from germs on a retained parameter base

Source: `geoemtric-part-fsf.tex`, smooth-extension convention, lines 119–122;
`def:maslov`, lines 212–244; and `sec:lean`, lines 788–814.
A real-open extension of the original complex field at a retained point
produces a canonical coframe chart with any specified covering spatial anchor.
Its domain is shrunk so every actual interval parameter in it lies in the
retained relative-open base. Complex laws and germ matching are required
only there. No section, global cutoff grading, or global field extension is
an input. The full signed cylinder and its actual differential are retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (B : Set Parameter) (hB : IsOpen B)
  (hJsq : ∀ s ∈ B, ∀ x v, J s x (J s x v) = -v)

/-- Raw real-open extensions of the original interior complex field at
retained points in every covering spatial chart. No coframe or section is
included, and matching is confined to the retained parameter base. -/
def HasOriginalInteriorComplexExtensionsOn : Prop :=
  ∀ (s : Parameter), s ∈ B → ∀ (u w : IntrinsicInterior.Point k M),
    w ∈ (chartAt (Model (k + 1)) u).source →
    ∃ (U : TopologicalSpace.Opens (ℝ × Model (k + 1)))
      (K : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] Model (k + 1)),
      (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧ ContDiffOn ℝ ∞ K U ∧
      ∀ (v : Parameter), v ∈ B → ∀ (z : IntrinsicInterior.Point k M),
        z ∈ (chartAt (Model (k + 1)) u).source →
        (v.val, chartAt (Model (k + 1)) u z) ∈ U →
        K (v.val, chartAt (Model (k + 1)) u z) =
          originalInteriorComplexInChart hδ C hemb hboundary hzero J u (v, z)

include hC hinv hB hJsq in
/-- A single retained field germ produces an actual original interior chart.
The resulting real-open domain contains only retained actual parameters. -/
theorem exists_originalInteriorCanonicalChart_on
    (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (u : IntrinsicInterior.Point k M) (s : Parameter) (hs : s ∈ B)
    (w : IntrinsicInterior.Point k M) (hw : w ∈ (chartAt (Model (k + 1)) u).source)
    (U : TopologicalSpace.Opens (ℝ × Model (k + 1)))
    (K : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] Model (k + 1))
    (hpU : (s.val, chartAt (Model (k + 1)) u w) ∈ U)
    (hK : ContDiffOn ℝ ∞ K U)
    (heK : ∀ (v : Parameter), v ∈ B → ∀ (z : IntrinsicInterior.Point k M),
      z ∈ (chartAt (Model (k + 1)) u).source →
      (v.val, chartAt (Model (k + 1)) u z) ∈ U →
      K (v.val, chartAt (Model (k + 1)) u z) =
        originalInteriorComplexInChart hδ C hemb hboundary hzero J u (v, z)) :
    ∃ c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n),
      c.anchor = u ∧ (s, w) ∈ c.baseDomain ∧
        ∀ (v : Parameter) y, (v.val, y) ∈ c.domain → v ∈ B := by
  obtain ⟨A, hA, htrace⟩ := isOpen_induced_iff.mp hB
  have hsA : s.val ∈ A := by
    change s ∈ Subtype.val ⁻¹' A
    rw [htrace]
    exact hs
  let e := chartAt (Model (k + 1)) u
  let V : Set (ℝ × Model (k + 1)) := (U : Set _) ∩ (A ×ˢ e.target)
  have hV : IsOpen V := U.isOpen.inter (hA.prod e.open_target)
  have hpV : (s.val, e w) ∈ V := ⟨hpU, hsA, e.map_source hw⟩
  have hretain (v : Parameter) (y : Model (k + 1)) (hy : (v.val, y) ∈ V) : v ∈ B := by
    rw [← htrace]
    exact hy.2.1
  have hsq : ∀ z ∈ V ∩ (parameterInterval ×ˢ (univ : Set (Model (k + 1)))),
      ∀ v, K z (K z v) = -v := by
    intro z hz v
    let t : Parameter := ⟨z.1, hz.2.1⟩
    let q := e.symm z.2
    have hq : q ∈ e.source := e.map_target hz.1.2.2
    have heq : chartAt (Model (k + 1)) u q = z.2 := e.right_inv hz.1.2.2
    have htB : t ∈ B := hretain t z.2 hz.1
    have hm := heK t htB q hq (by
      change (t.val, chartAt (Model (k + 1)) u q) ∈ U.carrier
      rw [heq]
      exact hz.1.1)
    have hm' : K z = originalInteriorComplexInChart hδ C hemb hboundary hzero J u (t, q) := by
      simpa only [t, heq, Prod.mk.eta] using hm
    rw [hm']
    let H := originalInteriorCanonicalDifferential hδ (C t) (hemb t) (hboundary t) (hzero t) u q
    have hHi : H.IsInvertible := isInvertible_originalInteriorCanonicalDifferential
      hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t) u q hq
    change H (J t _ (H.inverse (H (J t _ (H.inverse v))))) = -v
    rw [hHi.inverse_apply_self, hJsq t htB, map_neg, hHi.self_apply_inverse]
  obtain ⟨b, hbV, hpb⟩ := exists_nativeCoordinateCanonicalPatch N hV hpV
    (show (s.val, e w) ∈ parameterInterval ×ˢ (univ : Set (Model (k + 1))) from
      ⟨s.property, mem_univ _⟩) (hK.mono inter_subset_left) hsq
  let c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n) := {
    anchor := u
    domain := b.domain
    subset_target := fun _ hz => ⟨mem_univ _, (hbV hz).2.2⟩
    coframe := b.coframe
    smooth_coframe := b.smooth_coframe
    invertible_coframe := b.invertible_coframe
    intertwines := by
      intro t q hq hqb v
      rw [← heK t (hretain t _ (hbV hqb)) q hq (hbV hqb).1]
      exact b.intertwines _ ⟨hqb, t.property, mem_univ _⟩ v }
  exact ⟨c, rfl, ⟨⟨mem_univ _, hw⟩, hpb⟩, fun v y hy => hretain v y (hbV hy)⟩

local instance retainedChartProductSpace :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance retainedChartProductManifold :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

/-- Raw real-open extensions of the actual complex field on the full
signed cylinder in every covering boundary–radius chart, only at retained
parameters. No whole-cutoff complex law or canonical chart is assumed. -/
def HasOriginalEndComplexExtensionsOn : Prop :=
  ∀ (s : Parameter), s ∈ B → ∀ (u : IntrinsicBoundary.Point k M × ℝ)
    (w : Band δ (IntrinsicBoundary.Point k M)),
    endBandCoordinates w ∈ (chartAt (Model k × ℝ) u).source →
    ∃ (U : TopologicalSpace.Opens (ℝ × (Model k × ℝ)))
      (K : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] (Model k × ℝ)),
      (s.val, chartAt (Model k × ℝ) u (endBandCoordinates w)) ∈ U ∧
        ContDiffOn ℝ ∞ K U ∧
      ∀ (v : Parameter), v ∈ B → ∀ (z : Band δ (IntrinsicBoundary.Point k M)),
        endBandCoordinates z ∈ (chartAt (Model k × ℝ) u).source →
        (v.val, chartAt (Model k × ℝ) u (endBandCoordinates z)) ∈ U →
        K (v.val, chartAt (Model k × ℝ) u (endBandCoordinates z)) =
          originalEndComplexInChart hδ C hemb hboundary hzero J u (v, z)

include hC hinv hB hJsq in
/-- The same retained construction on every point of the full signed cylinder,
including its seam, uses the actual cylinder coordinate differential. -/
theorem exists_originalEndCanonicalChart_on
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (u : IntrinsicBoundary.Point k M × ℝ) (s : Parameter) (hs : s ∈ B)
    (w : Band δ (IntrinsicBoundary.Point k M))
    (hw : endBandCoordinates w ∈ (chartAt (Model k × ℝ) u).source)
    (U : TopologicalSpace.Opens (ℝ × (Model k × ℝ)))
    (K : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] (Model k × ℝ))
    (hpU : (s.val, chartAt (Model k × ℝ) u (endBandCoordinates w)) ∈ U)
    (hK : ContDiffOn ℝ ∞ K U)
    (heK : ∀ (v : Parameter), v ∈ B → ∀ (z : Band δ (IntrinsicBoundary.Point k M)),
      endBandCoordinates z ∈ (chartAt (Model k × ℝ) u).source →
      (v.val, chartAt (Model k × ℝ) u (endBandCoordinates z)) ∈ U →
      K (v.val, chartAt (Model k × ℝ) u (endBandCoordinates z)) =
        originalEndComplexInChart hδ C hemb hboundary hzero J u (v, z)) :
    ∃ c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n),
      c.anchor = u ∧ (s, w) ∈ c.baseDomain ∧
        ∀ (v : Parameter) y, (v.val, y) ∈ c.domain → v ∈ B := by
  obtain ⟨A, hA, htrace⟩ := isOpen_induced_iff.mp hB
  have hsA : s.val ∈ A := by
    change s ∈ Subtype.val ⁻¹' A
    rw [htrace]
    exact hs
  let e := chartAt (Model k × ℝ) u
  let V : Set (ℝ × (Model k × ℝ)) :=
    (U : Set _) ∩ (A ×ˢ originalEndChartBandTarget (δ := δ) u)
  have hV : IsOpen V := U.isOpen.inter (hA.prod (isOpen_originalEndChartBandTarget u))
  have hpV : (s.val, e (endBandCoordinates w)) ∈ V := by
    refine ⟨hpU, hsA, e.map_source hw, ?_⟩
    change -(e.symm (e (endBandCoordinates w))).2 < δ
    rw [e.left_inv hw]
    change -(-w.val.1) < δ
    simpa only [neg_neg] using (show w.val.1 < δ from w.property.1)
  have hretain (v : Parameter) (y : Model k × ℝ) (hy : (v.val, y) ∈ V) : v ∈ B := by
    rw [← htrace]
    exact hy.2.1
  have hsq : ∀ z ∈ V ∩ (parameterInterval ×ˢ (univ : Set (Model k × ℝ))),
      ∀ v, K z (K z v) = -v := by
    intro z hz v
    let t : Parameter := ⟨z.1, hz.2.1⟩
    let q₀ := e.symm z.2
    let q : Band δ (IntrinsicBoundary.Point k M) := ⟨(-q₀.2, q₀.1), hz.1.2.2.2, mem_univ _⟩
    have hq₀ : endBandCoordinates q = q₀ := by
      simp only [endBandCoordinates, q, neg_neg, Prod.mk.eta]
    have hq : endBandCoordinates q ∈ e.source := hq₀ ▸ e.map_target hz.1.2.2.1
    have heq : chartAt (Model k × ℝ) u (endBandCoordinates q) = z.2 := by
      rw [hq₀]
      exact e.right_inv hz.1.2.2.1
    have htB : t ∈ B := hretain t z.2 hz.1
    have hm := heK t htB q hq (by
      change (t.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ U.carrier
      rw [heq]
      exact hz.1.1)
    have hm' : K z = originalEndComplexInChart hδ C hemb hboundary hzero J u (t, q) := by
      change K (z.1, chartAt (Model k × ℝ) u (endBandCoordinates q)) = _ at hm
      rw [heq] at hm
      exact hm
    rw [hm']
    let H := originalEndCanonicalDifferential hδ (C t) (hemb t) (hboundary t) (hzero t) u q
    have hHi : H.IsInvertible := isInvertible_originalEndCanonicalDifferential
      hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t) u q hq
    change H (J t _ (H.inverse (H (J t _ (H.inverse v))))) = -v
    rw [hHi.inverse_apply_self, hJsq t htB, map_neg, hHi.self_apply_inverse]
  obtain ⟨b, hbV, hpb⟩ := exists_nativeCoordinateCanonicalPatch P hV hpV
    (show (s.val, e (endBandCoordinates w)) ∈ parameterInterval ×ˢ (univ : Set (Model k × ℝ)) from
      ⟨s.property, mem_univ _⟩) (hK.mono inter_subset_left) hsq
  let c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n) := {
    anchor := u
    domain := b.domain
    subset_target := fun _ hz => ⟨mem_univ _, (hbV hz).2.2⟩
    coframe := b.coframe
    smooth_coframe := b.smooth_coframe
    invertible_coframe := b.invertible_coframe
    intertwines := by
      intro t q hq hqb v
      rw [← heK t (hretain t _ (hbV hqb)) q hq (hbV hqb).1]
      exact b.intertwines _ ⟨hqb, t.property, mem_univ _⟩ v }
  exact ⟨c, rfl, ⟨⟨mem_univ _, hw⟩, hpb⟩, fun v y hy => hretain v y (hbV hy)⟩

end FsFltz.Geometry.IntrinsicCompletionGluing
