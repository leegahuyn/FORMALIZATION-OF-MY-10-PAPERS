import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedPairSupport
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageGlobal
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicCompactHZero
import PrimalitySheafVerification.ManuscriptAudit.ExtZeroProductCoordinates

/-! For a preconnected scheme, the degree-zero restriction to two
field-valued points is the literal diagonal in the two adic coordinates. -/

namespace ManuscriptAudit.ProetaleAdicBoundaryPairCoordinates

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleContinuousDirectImageGlobal (HZeroEquiv terminalEquiv)
open ProetaleAdicClosedPairSupport (boundary pairRestriction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} (L : Type) [Field L]
variable (i₀ i₁ : Spec (CommRingCat.of L) ⟶ X)
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))
private abbrev hT := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X

private def evalPoint : C(Spec (CommRingCat.of L), M ℓ) ≃+ M ℓ where
  toFun f := f (IsLocalRing.closedPoint L)
  invFun x := ContinuousMap.const _ x
  left_inv f := by
    apply ContinuousMap.ext
    intro x
    exact congrArg f (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl

private def pointEquiv (i : Spec (CommRingCat.of L) ⟶ X) :
    Sheaf.H (functionsOver (M ℓ) i) 0 ≃+ M ℓ :=
  (HZeroEquiv (M ℓ) i).trans (evalPoint L ℓ)

private theorem pointEquiv_map (i : Spec (CommRingCat.of L) ⟶ X)
    (x : Sheaf.H (functions (M ℓ) X) 0) :
    pointEquiv L ℓ i (Sheaf.H.map (diagonal (M ℓ) i) 0 x) =
      (show C(X, M ℓ) from ((Sheaf.H.equiv₀ (functions (M ℓ) X) (hT (X := X))) x).down)
        (i (IsLocalRing.closedPoint L)) := by
  let p := pullback.snd (𝟙 X) i
  let q := pullback.fst (𝟙 X) i
  let e := Sheaf.H.equiv₀ (functions (M ℓ) X) (hT (X := X))
  change terminalEquiv (M ℓ) i ((Sheaf.H.equiv₀ (functionsOver (M ℓ) i) (hT (X := X)))
    (Sheaf.H.map (diagonal (M ℓ) i) 0 x)) (IsLocalRing.closedPoint L) =
    (show C(X, M ℓ) from (e x).down) (i (IsLocalRing.closedPoint L))
  rw [← Sheaf.H.equiv₀_naturality]
  let f : C(X, M ℓ) := (e x).down
  change f ((inv p ≫ q) (IsLocalRing.closedPoint L)) = f (i (IsLocalRing.closedPoint L))
  have hp : inv p ≫ q = i := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact (Category.comp_id q).symm.trans (pullback.condition (f := 𝟙 X) (g := i))
  rw [hp]

/-- Degree zero of the actual product direct image, identified with its two point values. -/
def boundaryEquiv : Sheaf.H (boundary i₀ i₁ ℓ) 0 ≃+ M ℓ × M ℓ :=
  (ExtZeroProductCoordinates.equiv integers (functionsOver (M ℓ) i₀) (functionsOver (M ℓ) i₁)).trans
    ((pointEquiv L ℓ i₀).prodCongr (pointEquiv L ℓ i₁))

private theorem boundaryEquiv_map (x : Sheaf.H (functions (M ℓ) X) 0) :
    boundaryEquiv L i₀ i₁ ℓ (Sheaf.H.map (pairRestriction i₀ i₁ ℓ) 0 x) =
      ((show C(X, M ℓ) from ((Sheaf.H.equiv₀ (functions (M ℓ) X) (hT (X := X))) x).down)
          (i₀ (IsLocalRing.closedPoint L)),
        (show C(X, M ℓ) from ((Sheaf.H.equiv₀ (functions (M ℓ) X) (hT (X := X))) x).down)
          (i₁ (IsLocalRing.closedPoint L))) := by
  let d := pairRestriction i₀ i₁ ℓ
  let F₀ := functionsOver (M ℓ) i₀
  let F₁ := functionsOver (M ℓ) i₁
  apply Prod.ext
  · change pointEquiv L ℓ i₀ ((ExtZeroProductCoordinates.equiv integers F₀ F₁
      (Sheaf.H.map d 0 x)).1) = _
    rw [ExtZeroProductCoordinates.fst_apply]
    change pointEquiv L ℓ i₀ (Sheaf.H.map (prod.fst : F₀ ⨯ F₁ ⟶ F₀) 0
      (Sheaf.H.map d 0 x)) = _
    rw [← Sheaf.H.map_comp_apply, show d ≫ (prod.fst : F₀ ⨯ F₁ ⟶ F₀) = diagonal (M ℓ) i₀ from
      prod.lift_fst _ _]
    exact pointEquiv_map L ℓ i₀ x
  · change pointEquiv L ℓ i₁ ((ExtZeroProductCoordinates.equiv integers F₀ F₁
      (Sheaf.H.map d 0 x)).2) = _
    rw [ExtZeroProductCoordinates.snd_apply]
    change pointEquiv L ℓ i₁ (Sheaf.H.map (prod.snd : F₀ ⨯ F₁ ⟶ F₁) 0
      (Sheaf.H.map d 0 x)) = _
    rw [← Sheaf.H.map_comp_apply, show d ≫ (prod.snd : F₀ ⨯ F₁ ⟶ F₁) = diagonal (M ℓ) i₁ from
      prod.lift_snd _ _]
    exact pointEquiv_map L ℓ i₁ x

variable [PreconnectedSpace X]

/-- The image of ambient degree zero in the two genuine boundary values is precisely the diagonal. -/
theorem range_iff_diag (a : M ℓ × M ℓ) :
    (∃ x : Sheaf.H (functions (M ℓ) X) 0,
      boundaryEquiv L i₀ i₁ ℓ (Sheaf.H.map (pairRestriction i₀ i₁ ℓ) 0 x) = a) ↔ a.1 = a.2 := by
  let e := Sheaf.H.equiv₀ (functions (M ℓ) X) (hT (X := X))
  constructor
  · rintro ⟨x, rfl⟩
    rw [boundaryEquiv_map]
    exact ProetaleAdicCompactHZero.continuous_value_eq ℓ (show C(X, M ℓ) from (e x).down)
      (i₀ (IsLocalRing.closedPoint L)) (i₁ (IsLocalRing.closedPoint L))
  · intro ha
    refine ⟨e.symm ⟨ContinuousMap.const X a.1⟩, ?_⟩
    rw [boundaryEquiv_map]
    change ((show C(X, M ℓ) from (e (e.symm ⟨ContinuousMap.const X a.1⟩)).down)
        (i₀ (IsLocalRing.closedPoint L)),
      (show C(X, M ℓ) from (e (e.symm ⟨ContinuousMap.const X a.1⟩)).down)
        (i₁ (IsLocalRing.closedPoint L))) = a
    rw [e.apply_symm_apply]
    exact Prod.ext rfl ha

end

end ManuscriptAudit.ProetaleAdicBoundaryPairCoordinates

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicBoundaryPairCoordinates.range_iff_diag
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
