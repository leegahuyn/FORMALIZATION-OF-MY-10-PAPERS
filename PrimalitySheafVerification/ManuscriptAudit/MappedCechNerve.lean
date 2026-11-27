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

private theorem component_hom_projection (n : ℕ) (j : WidePullbackShape (Fin (n + 1))) :
    (componentIso F f n).hom ≫ limit.π (diagram (F.map f) n) j =
      F.map (limit.π (diagram f n) j) := by
  let L := isLimitOfPreserves F (limit.isLimit (diagram f n))
  let M := limit.isLimit (diagram f n ⋙ F)
  let e := diagramIso F f n
  have h : (L.conePointUniqueUpToIso M).hom ≫ limit.π (diagram f n ⋙ F) j =
      F.map (limit.π (diagram f n) j) :=
    IsLimit.conePointUniqueUpToIso_hom_comp L M j
  calc
    _ = ((L.conePointUniqueUpToIso M).hom ≫ limit.π (diagram f n ⋙ F) j) ≫
        e.hom.app j := by
      change ((L.conePointUniqueUpToIso M) ≪≫ HasLimit.isoOfNatIso e).hom ≫ _ = _
      rw [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
    _ = F.map (limit.π (diagram f n) j) ≫ e.hom.app j :=
      congrArg (fun a ↦ a ≫ e.hom.app j) h
    _ = _ := by
      cases j <;> simp [e, diagramIso, WidePullbackShape.diagramIsoWideCospan]

private theorem component_hom_π (n : ℕ) (i : Fin (n + 1)) :
    (componentIso F f n).hom ≫ WidePullback.π (fun _ ↦ F.map f) i =
      F.map (WidePullback.π (fun _ ↦ f) i) :=
  component_hom_projection F f n (some i)

private theorem component_hom_base (n : ℕ) :
    (componentIso F f n).hom ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ F.map f) =
      F.map (WidePullback.base (fun _ : Fin (n + 1) ↦ f)) :=
  component_hom_projection F f n none

private theorem cechMap_π {m n : SimplexCategoryᵒᵖ} (g : m ⟶ n)
    (i : Fin (n.unop.len + 1)) :
    (Arrow.mk f).cechNerve.map g ≫ WidePullback.π (fun _ ↦ f) i =
      WidePullback.π (fun _ ↦ f) (g.unop.toOrderHom i) := by
  rw [Arrow.cechNerve_map]
  exact WidePullback.lift_π _ _ _ _ _

private theorem cechMap_base {m n : SimplexCategoryᵒᵖ} (g : m ⟶ n) :
    (Arrow.mk f).cechNerve.map g ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f) =
      WidePullback.base (fun _ : Fin (m.unop.len + 1) ↦ f) := by
  rw [Arrow.cechNerve_map]
  exact WidePullback.lift_base _ _ _ _

/-- The actual Čech nerve commutes with the application of a native
finite-limit-preserving functor. -/
def mapCechNerveIso :
    (Arrow.mk f).cechNerve ⋙ F ≅ (Arrow.mk (F.map f)).cechNerve :=
  NatIso.ofComponents (fun n ↦ componentIso F f n.unop.len) (fun {m n} g ↦ by
    apply WidePullback.hom_ext
    · intro i
      change (F.map ((Arrow.mk f).cechNerve.map g) ≫ (componentIso F f n.unop.len).hom) ≫
          WidePullback.π (fun _ ↦ F.map f) i =
        ((componentIso F f m.unop.len).hom ≫ (Arrow.mk (F.map f)).cechNerve.map g) ≫
          WidePullback.π (fun _ ↦ F.map f) i
      rw [Category.assoc, Category.assoc, component_hom_π, ← CategoryTheory.Functor.map_comp,
        cechMap_π, cechMap_π, component_hom_π]
    · change (F.map ((Arrow.mk f).cechNerve.map g) ≫ (componentIso F f n.unop.len).hom) ≫
          WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ F.map f) =
        ((componentIso F f m.unop.len).hom ≫ (Arrow.mk (F.map f)).cechNerve.map g) ≫
          WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ F.map f)
      rw [Category.assoc, Category.assoc, component_hom_base, ← CategoryTheory.Functor.map_comp,
        cechMap_base, cechMap_base, component_hom_base])

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
