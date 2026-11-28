import Lean.Util.CollectAxioms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.InjectiveLiftedYonedaCech
import PrimalitySheafVerification.ManuscriptAudit.NativeCechNerve

/-! An injective abelian sheaf is Čech-exact in degree one on the
actual nerve of a single arrow to a terminal object. -/

namespace ManuscriptAudit.InjectiveTerminalCech

open CategoryTheory CategoryTheory.Limits Opposite
open CechNerveLowDegrees (N vertex face face_vertex zeroIso)
open NativeCechNerve (Cech cochainExactAt_succ_iff)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {U T : C} (f : U ⟶ T) (hT : IsTerminal T)

private def tupleMap {W : C} (n : ℕ) (a : Fin (n + 1) → (W ⟶ U)) : W ⟶ N f n :=
  WidePullback.lift (hT.from W) a (fun i ↦ hT.hom_ext _ _)

private theorem tupleMap_natural {W V : C} (r : V ⟶ W) (n : ℕ)
    (a : Fin (n + 1) → (W ⟶ U)) :
    r ≫ tupleMap f hT n a = tupleMap f hT n (fun i ↦ r ≫ a i) := by
  apply WidePullback.hom_ext
  · intro i
    simp only [Category.assoc, tupleMap, WidePullback.lift_π]
  · exact hT.hom_ext _ _

private theorem tupleMap_face {W : C} (n : ℕ) (i : Fin (n+2))
    (a : Fin (n+2) → (W ⟶ U)) :
    tupleMap f hT (n+1) a ≫ face f n i =
      tupleMap f hT n (fun j ↦ a ((SimplexCategory.δ i).toOrderHom j)) := by
  apply WidePullback.hom_ext
  · intro j
    change (tupleMap f hT (n + 1) a ≫ face f n i) ≫ vertex f n j =
      tupleMap f hT n (fun k ↦ a ((SimplexCategory.δ i).toOrderHom k)) ≫ vertex f n j
    rw [Category.assoc, face_vertex]
    simp only [tupleMap, vertex, WidePullback.lift_π]
  · exact hT.hom_ext _ _

private theorem tupleMap_vertices (n : ℕ) :
    tupleMap f hT n (vertex f n) = 𝟙 (N f n) := by
  apply WidePullback.hom_ext
  · intro i
    rw [Category.id_comp]
    simp only [tupleMap, vertex, WidePullback.lift_π] <;> rfl
  · exact hT.hom_ext _ _

variable {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max v w}]
  (I : Sheaf J AddCommGrpCat.{max v w}) [Injective I]

private theorem restrict_restrict {A B D : C} (a : A ⟶ B) (b : B ⟶ D)
    (z : I.obj.obj (op D)) :
    I.obj.map a.op (I.obj.map b.op z) = I.obj.map (a ≫ b).op z := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

include hT in
set_option maxHeartbeats 2200000 in
/-- Positive degree-one Čech exactness of the native injective coefficients. -/
theorem exactAt_one : (Cech f I.obj).ExactAt 1 := by
  apply (cochainExactAt_succ_iff _ 0).mpr
  intro z hz
  change I.obj.obj (op (N f 1)) at z
  let c {W : C} (a b : W ⟶ U) := I.obj.map (tupleMap f hT 1 ![a,b]).op z
  have hNat {W V : C} (r : V ⟶ W) (a b : W ⟶ U) :
      I.obj.map r.op (c a b) = c (r ≫ a) (r ≫ b) := by
    have h : (fun k : Fin 2 ↦ r ≫ ![a,b] k) = ![r ≫ a, r ≫ b] := by
      funext k
      fin_cases k <;> rfl
    change I.obj.map r.op (I.obj.map (tupleMap f hT 1 ![a,b]).op z) = _
    rw [restrict_restrict, tupleMap_natural, h] <;> rfl
  have hC {W : C} (a b d : W ⟶ U) : c b d - c a d + c a b = 0 := by
    let t := tupleMap f hT 2 ![a,b,d]
    have h₀ : (fun k : Fin 2 ↦ ![a,b,d] ((SimplexCategory.δ (0 : Fin 3)).toOrderHom k)) = ![b,d] := by
      funext k
      fin_cases k <;> rfl
    have h₁ : (fun k : Fin 2 ↦ ![a,b,d] ((SimplexCategory.δ (1 : Fin 3)).toOrderHom k)) = ![a,d] := by
      funext k
      fin_cases k <;> rfl
    have h₂ : (fun k : Fin 2 ↦ ![a,b,d] ((SimplexCategory.δ (2 : Fin 3)).toOrderHom k)) = ![a,b] := by
      funext k
      fin_cases k <;> rfl
    have h := congrArg (fun x : I.obj.obj (op (N f 2)) ↦ (I.obj.map t.op).hom x)
      ((NativeCechNerve.d₁ f I.obj z).symm.trans hz)
    simp only [map_add, map_sub, map_zero] at h
    change I.obj.map t.op (I.obj.map (face f 1 0).op z) -
      I.obj.map t.op (I.obj.map (face f 1 1).op z) +
      I.obj.map t.op (I.obj.map (face f 1 2).op z) = 0 at h
    have hv (i : Fin 3) : I.obj.map t.op (I.obj.map (face f 1 i).op z) =
        I.obj.map (tupleMap f hT 1 (fun k ↦ ![a,b,d] ((SimplexCategory.δ i).toOrderHom k))).op z := by
      rw [restrict_restrict I]
      exact congrArg (fun u : W ⟶ N f 1 ↦ I.obj.map u.op z) (tupleMap_face f hT 1 i ![a,b,d])
    rw [hv 0, hv 1, hv 2, h₀, h₁, h₂] at h
    exact h
  obtain ⟨b, hb⟩ :=
    InjectiveLiftedYonedaCech.exists_coboundary J U I (fun {_} a d ↦ c a d) hNat hC
  have hTuple : (![vertex f 1 0, vertex f 1 1] : Fin 2 → (N f 1 ⟶ U)) = vertex f 1 := by
    funext i
    fin_cases i <;> rfl
  have he := hb (vertex f 1 0) (vertex f 1 1)
  change I.obj.map (tupleMap f hT 1 ![vertex f 1 0, vertex f 1 1]).op z = _ at he
  rw [hTuple, tupleMap_vertices, op_id, CategoryTheory.Functor.map_id] at he
  let a := I.obj.map (zeroIso f).hom.op b
  refine ⟨a, ?_⟩
  rw [NativeCechNerve.d₀]
  change I.obj.map (face f 0 0).op (I.obj.map (zeroIso f).hom.op b) -
    I.obj.map (face f 0 1).op (I.obj.map (zeroIso f).hom.op b) = z
  rw [restrict_restrict, restrict_restrict]
  change I.obj.map (face f 0 0 ≫ vertex f 0 0).op b -
    I.obj.map (face f 0 1 ≫ vertex f 0 0).op b = z
  rw [face_vertex, face_vertex]
  exact he.symm

end
end ManuscriptAudit.InjectiveTerminalCech

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.InjectiveTerminalCech.exactAt_one
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
