import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Nonzero geometric skyscraper sheaves on the small étale site

Evaluation at the identity étale object exhibits the coefficient group as
a retract of the sections of the actual skyscraper sheaf.
-/

namespace ManuscriptAudit.SmallEtaleSkyscraper

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The geometric skyscraper sheaf with nonzero abelian-group coefficients is nonzero. -/
theorem skyscraper_not_isZero {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ S) (A : AddCommGrpCat.{u}) (hA : ¬ IsZero A) :
    ¬ IsZero ((Scheme.pointSmallEtale s).skyscraperSheaf A) := by
  let T : S.Etale := Scheme.Etale.mk (𝟙 S)
  let Φ := Scheme.pointSmallEtale s
  let x : Φ.fiber.obj T := CategoryTheory.Over.homMk s (Category.comp_id s)
  let F := Φ.skyscraperSheaf A
  let ev := (sheafSections S.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)
  letI : ev.Additive := ⟨by intros; rfl⟩
  intro hF
  have hEval : IsZero (ev.obj F) := by
    apply (IsZero.iff_id_eq_zero _).2
    have hId : 𝟙 F = 0 := hF.eq_of_src _ _
    calc
      𝟙 (ev.obj F) = ev.map (𝟙 F) := (ev.map_id F).symm
      _ = ev.map 0 := congrArg (fun g : F ⟶ F => ev.map g) hId
      _ = 0 := ev.map_zero F F
  let family : Φ.fiber.obj T → AddCommGrpCat.{u} := fun _ => A
  change IsZero (∏ᶜ family) at hEval
  let diagonal : A ⟶ ∏ᶜ family := Pi.lift fun _ => 𝟙 A
  let projection : ∏ᶜ family ⟶ A := Pi.π family x
  have hDiagonal : diagonal = 0 := hEval.eq_of_tgt _ _
  apply hA
  apply (IsZero.iff_id_eq_zero A).2
  calc
    𝟙 A = diagonal ≫ projection := (Pi.lift_π (fun _ : Φ.fiber.obj T => 𝟙 A) x).symm
    _ = 0 := by rw [hDiagonal, zero_comp]

end

end ManuscriptAudit.SmallEtaleSkyscraper

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SmallEtaleSkyscraper.skyscraper_not_isZero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
