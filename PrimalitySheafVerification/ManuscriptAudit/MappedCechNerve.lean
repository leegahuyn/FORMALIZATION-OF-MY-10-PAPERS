import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.Point.Basic

/-! Finite-limit functors preserve the actual Čech nerve of a covering arrow. -/

namespace ManuscriptAudit.MappedCechNerve

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [HasFiniteLimits C] [HasFiniteLimits D]
variable (F : C ⥤ D) [PreservesFiniteLimits F]
variable {U T : C} (f : U ⟶ T)

private abbrev diagram (n : ℕ) :=
  WidePullbackShape.wideCospan T (fun _ : Fin (n + 1) ↦ U) (fun _ ↦ f)

private abbrev diagramIso (n : ℕ) :
    diagram f n ⋙ F ≅ diagram (F.map f) n :=
  WidePullbackShape.diagramIsoWideCospan (diagram f n ⋙ F)

/-- The componentwise comparison of the finite wide pullbacks in the Čech nerve. -/
def componentIso (n : ℕ) :
    F.obj (limit (diagram f n)) ≅ limit (diagram (F.map f) n) :=
  (isLimitOfPreserves F (limit.isLimit (diagram f n))).conePointUniqueUpToIso
    (limit.isLimit (diagram f n ⋙ F)) ≪≫ HasLimit.isoOfNatIso (diagramIso F f n)

@[reassoc]
private theorem component_hom_π (n : ℕ) (i : Fin (n + 1)) :
    (componentIso F f n).hom ≫ WidePullback.π (fun _ ↦ F.map f) i =
      F.map (WidePullback.π (fun _ ↦ f) i) := by
  change (componentIso F f n).hom ≫ limit.π (diagram (F.map f) n) (some i) =
    F.map (limit.π (diagram f n) (some i))
  unfold componentIso
  rw [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
    IsLimit.conePointUniqueUpToIso_hom_comp]
  simp [diagramIso, WidePullbackShape.diagramIsoWideCospan]

@[reassoc]
private theorem component_hom_base (n : ℕ) :
    (componentIso F f n).hom ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ F.map f) =
      F.map (WidePullback.base (fun _ : Fin (n + 1) ↦ f)) := by
  change (componentIso F f n).hom ≫ limit.π (diagram (F.map f) n) none =
    F.map (limit.π (diagram f n) none)
  unfold componentIso
  rw [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
    IsLimit.conePointUniqueUpToIso_hom_comp]
  simp [diagramIso, WidePullbackShape.diagramIsoWideCospan]

/-- The actual Čech nerve commutes with the application of a native
finite-limit-preserving functor. -/
def mapCechNerveIso :
    (Arrow.mk f).cechNerve ⋙ F ≅ (Arrow.mk (F.map f)).cechNerve :=
  NatIso.ofComponents (fun n ↦ componentIso F f n.unop.len) (fun {m n} g ↦ by
    apply WidePullback.hom_ext
    · intro i
      simp only [CategoryTheory.Functor.comp_map, Category.assoc, component_hom_π,
        Arrow.cechNerve_map, WidePullback.lift_π, ← CategoryTheory.Functor.map_comp]
    · simp only [CategoryTheory.Functor.comp_map, Category.assoc, component_hom_base,
        Arrow.cechNerve_map, WidePullback.lift_base, ← CategoryTheory.Functor.map_comp])

end

section Cover

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/-- A singleton covering arrow induces a surjection on the actual
fiber of every point of the site. -/
theorem pointFiber_cover_surjective (Φ : J.Point) {U T : C} (f : U ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J T) :
    Function.Surjective (Φ.fiber.map f) := by
  intro x
  obtain ⟨V, g, ⟨W, h, d, hd, rfl⟩, y, hy⟩ :=
    Φ.jointly_surjective (Sieve.generate (Presieve.singleton f)) hf x
  cases hd
  refine ⟨Φ.fiber.map h y, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  exact hy

end Cover

end ManuscriptAudit.MappedCechNerve

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MappedCechNerve.mapCechNerveIso,
      ``ManuscriptAudit.MappedCechNerve.pointFiber_cover_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
