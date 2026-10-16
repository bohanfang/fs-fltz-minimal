import FsFltz.Geometry.IntrinsicCollarLocal

/-!
# The one-sided collar is relatively open at its seam

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. The two-sided coordinate collar is injective
and locally diffeomorphic on an open rectangle. Restricting its target
to the native half-space preserves relative openness. The proved normal
sign identity identifies its preimage with the nonnegative-time rectangle.
This supplies an actual open embedding at the seam, without an ambient
extension manifold or an assumed collar.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollar

/-- An injective local diffeomorphism on an open rectangle is an open
embedding of that rectangle into its Euclidean target. -/
theorem isOpenEmbedding_rectangle {k : ℕ} {δ : ℝ} {V : Set (Model k)}
    {c : ℝ × Model k → Model (k + 1)} (hV : IsOpen V)
    (hinj : InjOn c (Ioo (-δ) δ ×ˢ V))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) ∞ c
      (Ioo (-δ) δ ×ˢ V)) :
    IsOpenEmbedding ((Ioo (-δ) δ ×ˢ V).domRestrict c) := by
  let R : Set (ℝ × Model k) := Ioo (-δ) δ ×ˢ V
  have hR : IsOpen R := isOpen_Ioo.prod hV
  have hhomeo : IsLocalHomeomorphOn c R := hloc.isLocalHomeomorphOn
  have hmap (p : R) : map (R.domRestrict c) (𝓝 p) = 𝓝 (c p.val) := by
    change map (c ∘ Subtype.val) (𝓝 p) = _
    rw [← map_map, hR.isOpenEmbedding_subtypeVal.map_nhds_eq p,
      hhomeo.map_nhds_eq p.property]
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuousOn_iff_continuous_domRestrict.mp hhomeo.continuousOn)
    (fun p q hpq => Subtype.ext (hinj p.property q.property hpq))
    (IsOpenMap.of_nhds_le (fun p => (hmap p).symm.le))

/-- Restricting the coordinate collar to nonnegative time is an open
embedding in the native half-space, including relative openness at time
zero. The normal sign identity determines the entire one-sided preimage. -/
theorem isOpenEmbedding_halfSpace_restrict {k : ℕ} {δ : ℝ} {V : Set (Model k)}
    {c : ℝ × Model k → Model (k + 1)} (hδ : 0 < δ) (hV : IsOpen V)
    (hinj : InjOn c (Ioo (-δ) δ ×ˢ V))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) ∞ c
      (Ioo (-δ) δ ×ˢ V))
    (hside : ∀ p ∈ Ioo (-δ) δ ×ˢ V, 0 ≤ c p 0 ↔ 0 ≤ p.1) :
    IsOpenEmbedding (fun p : Ico 0 δ ×ˢ V => (𝓡∂ (k + 1)).symm (c p.val)) := by
  let R : Set (ℝ × Model k) := Ioo (-δ) δ ×ˢ V
  let S : Set (ℝ × Model k) := Ico 0 δ ×ˢ V
  let H : Set (Model (k + 1)) := {y | 0 ≤ y 0}
  let f : R → Model (k + 1) := R.domRestrict c
  have hSR : S ⊆ R := by
    intro p hp
    exact ⟨⟨lt_of_lt_of_le (neg_neg_of_pos hδ) hp.1.1, hp.1.2⟩, hp.2⟩
  let e : S ≃ₜ (f ⁻¹' H) :=
    { toFun := fun p => ⟨⟨p.val, hSR p.property⟩,
        (hside p.val (hSR p.property)).mpr p.property.1.1⟩
      invFun := fun p => ⟨p.val.val,
        ⟨⟨(hside p.val.val p.val.property).mp p.property, p.val.property.1.2⟩,
          p.val.property.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_val.subtype_mk _ }
  have hemb : IsOpenEmbedding (H.restrictPreimage f ∘ e) :=
    ((isOpenEmbedding_rectangle hV hinj hloc).restrictPreimage H).comp e.isOpenEmbedding
  have hfun : (fun p : S => (𝓡∂ (k + 1)).symm (c p.val)) = H.restrictPreimage f ∘ e := by
    funext p
    change (𝓡∂ (k + 1)).symm (c p.val) =
      (⟨c p.val, (hside p.val (hSR p.property)).mpr p.property.1.1⟩ :
        EuclideanHalfSpace (k + 1))
    exact (𝓡∂ (k + 1)).left_inv
      ⟨c p.val, (hside p.val (hSR p.property)).mpr p.property.1.1⟩
  change IsOpenEmbedding (fun p : S => (𝓡∂ (k + 1)).symm (c p.val))
  rw [hfun]
  exact hemb

end FsFltz.Geometry.IntrinsicCollar
