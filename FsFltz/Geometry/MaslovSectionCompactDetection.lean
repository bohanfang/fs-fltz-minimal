import FsFltz.Geometry.MaslovSectionRatio
import FsFltz.Geometry.FlowCollarCompactCompression
import FsFltz.Geometry.MaslovSameTensor

/-!
# Detecting completion grading classes from their actual compact section

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2089.
The derived nonzero scalar ratio is composed with the actual smooth
negative-flow compression. No section-ratio certificate or completed
grading homotopy is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace MaslovRepresentative

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}

/-- A jointly smooth compression to a section-agreement locus detects
the class of two actual sections with one fixed compatible structure. -/
theorem homotopic_of_tensor_eq_on_compression
    (s r : MaslovRepresentative M eta) (hJ : r.J = s.J)
    (A : Set M.Point) (H : ℝ → M.Point → M.Point)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × M.Point => H p.1 p.2))
    (hH0 : ∀ x, H 0 x = x) (hH1 : ∀ x, H 1 x ∈ A)
    (he : ∀ x ∈ A, r.tensor x = s.tensor x) : MaslovHomotopic s r := by
  let T : ℝ → M.Point → SquaredCanonicalTensor n :=
    fun t x => s.sectionRatio r hJ (H (1 - t) x) • s.tensor x
  have hs (a : M.Point) : SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => squaredTensorInChart M a (T p.1) p.2) := by
    let c := chartAt (Model (2 * n)) a
    let U : Set (ℝ × Model (2 * n)) := univ ×ˢ c.target
    have hcs : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × Model (2 * n) => c.symm p.2) U :=
      contMDiffOn_chart_symm.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2)
    have hpair : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞
        (fun p : ℝ × Model (2 * n) => (1 - p.1, c.symm p.2)) U :=
      (contMDiff_const.sub contMDiff_fst).contMDiffOn.prodMk hcs
    have hscalar : ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
        s.sectionRatio r hJ (H (1 - p.1) (c.symm p.2))) U := by
      have hm := (s.sectionRatio_smooth r hJ).comp_contMDiffOn (hH.comp_contMDiffOn hpair)
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
      exact hm.contDiffOn
    have hsection : ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
        squaredTensorInChart M a s.tensor p.2) U :=
      (s.smooth a).comp contDiff_snd.contDiffOn (fun _ hp => hp.2)
    refine ⟨U, isOpen_univ.prod c.open_target, fun p hp => ⟨mem_univ _, hp.2⟩, ?_⟩
    apply (hscalar.smul hsection).congr
    intro p hp
    ext v
    rfl
  refine ⟨{
    family := {
      J := fun _ => s.J
      tensor := T
      compatible := fun _ _ => s.compatible
      canonical := fun _ _ x => (squaredCanonicalSubmodule (s.J x)).smul_mem _ (s.canonical x)
      nowhereZero := fun _ _ x => smul_ne_zero (s.sectionRatio_ne_zero r hJ _) (s.nowhereZero x)
      smoothJ := fun a => SmoothNearInterval.constant
        (chartAt (Model (2 * n)) a).open_target (s.compatible.1 a)
      smoothSection := hs }
    sourceJ := rfl
    targetJ := hJ.symm
    sourceSection := ?_
    targetSection := ?_ }⟩
  · funext x
    change s.sectionRatio r hJ (H (1 - 0) x) • s.tensor x = s.tensor x
    rw [sub_zero, s.sectionRatio_eq_one_of_tensor_eq r hJ _ (he _ (hH1 x)), one_smul]
  · funext x
    change s.sectionRatio r hJ (H (1 - 1) x) • s.tensor x = r.tensor x
    rw [sub_self, hH0]
    exact (s.sectionRatio_spec r hJ x).symm

/-- Agreement of the actual tensors on the compressed locus suffices.
The common tensor is canonical for both structures, so normalized
transport fixes it without assuming equality of those structures. -/
theorem homotopic_of_eq_on_compression
    (s r : MaslovRepresentative M eta)
    (A : Set M.Point) (H : ℝ → M.Point → M.Point)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × M.Point => H p.1 p.2))
    (hH0 : ∀ x, H 0 x = x) (hH1 : ∀ x, H 1 x ∈ A)
    (he : ∀ x ∈ A, r.tensor x = s.tensor x) : MaslovHomotopic s r := by
  let R := r.changeCompatibleStructure s.J s.compatible
  have ht (x) (hx : x ∈ A) : R.tensor x = s.tensor x := by
    change transportSquaredTensor (r.J x) (s.J x) (r.tensor x) = s.tensor x
    have hc : IsSquaredCanonicalTensor (s.J x) (r.tensor x) := by
      rw [he x hx]
      exact s.canonical x
    exact (transportSquaredTensor_eq_self_of_canonical (r.J x) (s.J x) (r.tensor x)
      (r.canonical x) hc).trans (he x hx)
  exact (s.homotopic_of_tensor_eq_on_compression R rfl A H hH hH0 hH1 ht).trans
    (r.homotopic_changeCompatibleStructure s.J s.compatible).symm

end MaslovRepresentative

namespace LiouvilleDomain.FlowCollar

variable {n : ℕ} {D : LiouvilleDomain (2 * n)} (C : FlowCollar D)

/-- On the actual cylindrical completion, agreement of the native compact
grading sections determines their ambient class. The smooth compression
is constructed from this same collar's radial weight and Liouville flow. -/
theorem maslovHomotopic_of_eq_on_carrier
    (s r : MaslovRepresentative C.cylindricalCompletion.ambient.manifold
      (C.cylindricalCompletion.ambient.manifold.exteriorDerivative
        C.cylindricalCompletion.ambient.primitive))
    (he : ∀ x ∈ C.localizedDomain.domain.carrier, r.tensor x = s.tensor x) :
    MaslovHomotopic s r :=
  s.homotopic_of_eq_on_compression r C.localizedDomain.domain.carrier C.compactCompression
    C.compactCompression_smooth C.compactCompression_zero C.compactCompression_one_mem he

end LiouvilleDomain.FlowCollar
end FsFltz.Geometry
