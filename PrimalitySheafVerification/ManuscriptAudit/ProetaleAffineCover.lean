import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! Covering sieves of an affine object in the native pro-étale site
admit a finite, jointly surjective refinement by affine objects. -/

namespace ManuscriptAudit.ProetaleAffineCover

open AlgebraicGeometry CategoryTheory

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {T : S.ProEt}

/-- Compactness in the fpqc part of the topology gives finitely many
affine objects even though weakly étale maps need not be open. -/
theorem exists_finite_refinement [IsAffine T.left] (R : Sieve T)
    (hR : R ∈ Scheme.ProEt.topology S T) :
    ∃ (n : ℕ) (V : Fin n → S.ProEt) (a : ∀ i, V i ⟶ T),
      (∀ i, IsAffine (V i).left) ∧
      (∀ i, WeaklyEtale (a i).left) ∧
      (∀ i, R (a i)) ∧
      (∀ x : T.left, ∃ i, ∃ y : (V i).left, (a i).left y = x) := by
  let J := Scheme.ProEt.precoverage S
  let G := Scheme.ProEt.forget S ⋙ Over.forget S
  letI : J.IsStableUnderComposition := by
    change (Scheme.proetalePrecoverage.comap G).IsStableUnderComposition
    infer_instance
  letI : J.IsStableUnderBaseChange := by
    change (Scheme.proetalePrecoverage.comap G).IsStableUnderBaseChange
    infer_instance
  letI : J.HasIsos := by
    change (Scheme.proetalePrecoverage.comap G).HasIsos
    infer_instance
  obtain ⟨P, hP, hPR⟩ := (J.mem_toGrothendieck_iff_of_isStableUnderComposition).mp hR
  obtain ⟨ι, W, b, rfl⟩ := P.exists_eq_ofArrows
  have hG : (Presieve.ofArrows W b).map G ∈ Scheme.proetalePrecoverage T.left := hP
  rw [Presieve.map_ofArrows] at hG
  let E : PreZeroHypercover T.left :=
    { I₀ := ι
      X := fun i ↦ (W i).left
      f := fun i ↦ (b i).left }
  change E.presieve₀ ∈ Scheme.proetalePrecoverage T.left at hG
  letI : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.mp hG.1
  have hWeak (i : ι) : WeaklyEtale (b i).left :=
    (Scheme.presieve₀_mem_precoverage_iff.mp hG.2).2 i
  obtain ⟨n, k, O, hO, hTop⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (show IsCompact (⊤ : TopologicalSpace.Opens T.left).carrier from isCompact_univ)
  let t (i : Fin n) := (hO i).fromSpec
  let V (i : Fin n) : S.ProEt := Scheme.ProEt.mk (t i ≫ (W (k i)).hom)
  let a₀ (i : Fin n) : V i ⟶ W (k i) := MorphismProperty.Over.homMk (t i) rfl
  let a (i : Fin n) : V i ⟶ T := a₀ i ≫ b (k i)
  refine ⟨n, V, a, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩
  · change IsAffine (Spec _)
    infer_instance
  · change WeaklyEtale (t i ≫ (b (k i)).left)
    letI := hWeak (k i)
    infer_instance
  · exact R.downward_closed (hPR _ (b (k i)) ⟨k i⟩) (a₀ i)
  · have hx : x ∈ ⋃ i, E.f (k i) '' (O i) := by
      rw [hTop]
      exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy, he⟩ := hi
    refine ⟨i, (hO i).isoSpec.hom.base ⟨y, hy⟩, ?_⟩
    change (t i ≫ E.f (k i)) ((hO i).isoSpec.hom.base ⟨y, hy⟩) = x
    rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
      Iso.hom_inv_id_assoc]
    simpa using he

end
end ManuscriptAudit.ProetaleAffineCover

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAffineCover.exists_finite_refinement
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
