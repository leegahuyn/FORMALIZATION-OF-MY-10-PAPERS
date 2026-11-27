import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! Two native pro-étale covering criteria used for support: finite
jointly surjective quasi-compact families and restriction to affine charts. -/

namespace ManuscriptAudit.ProetaleFiniteQuasiCompactCover

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {T : X.ProEt}

theorem covering {ι : Type u} [Finite ι] (V : ι → X.ProEt) (a : ∀ i, V i ⟶ T)
    (hQC : ∀ i, QuasiCompact (a i).left)
    (hCov : ∀ x : T.left, ∃ i, ∃ y : (V i).left, (a i).left y = x) :
    Sieve.ofArrows V a ∈ Scheme.ProEt.topology X T := by
  let G := Scheme.ProEt.forget X ⋙ Over.forget X
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows V a).map G ∈ Scheme.proetalePrecoverage T.left
  rw [Presieve.map_ofArrows]
  let P : PreZeroHypercover T.left :=
    { I₀ := ι
      X := fun i ↦ (V i).left
      f := fun i ↦ (a i).left }
  have hWeak (i : ι) : WeaklyEtale (a i).left := by
    letI : WeaklyEtale T.hom := T.prop
    letI : WeaklyEtale ((a i).left ≫ T.hom) := by
      rw [MorphismProperty.Over.w (a i)]
      exact (V i).prop
    exact WeaklyEtale.of_comp (a i).left T.hom
  have hp : P.presieve₀ ∈ Scheme.precoverage @WeaklyEtale T.left :=
    (Scheme.ofArrows_mem_precoverage_iff @WeaklyEtale).mpr ⟨hCov, hWeak⟩
  let C : T.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨P, hp⟩
  letI (i : C.I₀) : QuasiCompact (C.f i) := hQC i
  letI : Finite C.I₀ := inferInstanceAs (Finite ι)
  have hq : QuasiCompactCover C.toPreZeroHypercover := QuasiCompactCover.of_finite
  change P.presieve₀ ∈ Scheme.proetalePrecoverage T.left
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hq, hp⟩

/-- Covering membership can be verified on the actual affine open cover of the target chart. -/
theorem of_affine_pullbacks (R : Sieve T)
    (h : ∀ {V : X.ProEt} [IsAffine V.left] (f : V ⟶ T),
      R.pullback f ∈ Scheme.ProEt.topology X V) :
    R ∈ Scheme.ProEt.topology X T := by
  let C := T.left.affineCover
  letI : WeaklyEtale T.hom := T.prop
  let V (i : C.I₀) : X.ProEt := Scheme.ProEt.mk (C.f i ≫ T.hom)
  let a (i : C.I₀) : V i ⟶ T := MorphismProperty.Over.homMk (C.f i) rfl
  let J := Scheme.ProEt.topology X
  have hCover : Sieve.ofArrows V a ∈ J T := by
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.ofArrows V a).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage T.left
    rw [Presieve.map_ofArrows]
    apply Scheme.etalePrecoverage_le_proetalePrecoverage _
    change Presieve.ofArrows C.X C.f ∈ Scheme.precoverage @Etale T.left
    exact (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨C.exists_eq, fun _ ↦ inferInstance⟩
  apply J.transitive hCover R
  intro W f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff V a f).mp hf
  letI : IsAffine (V i).left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  rw [Sieve.pullback_comp]
  exact J.pullback_stable g (h (a i))

end

end ManuscriptAudit.ProetaleFiniteQuasiCompactCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleFiniteQuasiCompactCover.covering,
      ``ManuscriptAudit.ProetaleFiniteQuasiCompactCover.of_affine_pullbacks] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
