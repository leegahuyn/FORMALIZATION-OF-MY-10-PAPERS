import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.LeftDerived

/-! Additivity of the actual derived functor follows from adding the
genuine chain lifts of the two morphisms. -/

namespace ManuscriptAudit.NativeLeftDerivedAdditive

open CategoryTheory

theorem additive {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasProjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (n : ℕ) : (F.leftDerived n).Additive where
  map_add {X Y} f g := by
    let P := projectiveResolution X
    let Q := projectiveResolution Y
    let a := ProjectiveResolution.lift f P Q
    let b := ProjectiveResolution.lift g P Q
    have ha := ProjectiveResolution.lift_commutes f P Q
    have hb := ProjectiveResolution.lift_commutes g P Q
    have hsum : (a + b) ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map (f + g) := by
      simp only [Preadditive.add_comp, Functor.map_add, Preadditive.comp_add]
      exact congrArg₂ (· + ·) ha hb
    rw [Functor.leftDerived_map_eq F n (f + g) (a + b) hsum,
      Functor.leftDerived_map_eq F n f a ha, Functor.leftDerived_map_eq F n g b hb]
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

end ManuscriptAudit.NativeLeftDerivedAdditive

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeLeftDerivedAdditive.additive
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
